{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DeriveGeneric #-}
module Data.HKD.Records (
  FLabels(..), gflabels,
  Dict(..), FDicts(..), gfdicts,
  HkdProd(..), LkdProd(..), End,
  fzipManyWith, ftoList, Lens', FLens(..),
  FLenses(..), gflenses) where
import Data.HKD
import Data.Text (Text)
import Data.Functor.Const
import GHC.Generics
import GHC.TypeLits
import Data.Coerce
import qualified Data.Text as Text
import Data.Proxy
import Data.Monoid
import Data.Functor.Identity
import Data.List

class FLabels t where
  -- | get the labels from each field as a (Const Text).
  flabels :: t (Const Text)

class GLabels t where
  genFlabels :: t
  
instance (GLabels (f ()), GLabels (g ())) => GLabels ((f :*: g) ()) where
  genFlabels = genFlabels :*: genFlabels
  {-# INLINE genFlabels #-}

instance KnownSymbol label =>
         (GLabels (S1 ('MetaSel ('Just label) _x _x2 _x3)
                    (Rec0 (Const Text b))
                    ())) where
  genFlabels = M1 $ K1 $ Const (Text.pack $ symbolVal (Proxy @label))
  {-# INLINE genFlabels #-}
  
instance GLabels (b ()) => (GLabels ((D1 meta (C1 meta2 b)) ())) where
  genFlabels = M1 $ M1 $ genFlabels
  {-# INLINE genFlabels #-}

-- | Automatically derive flabels using generics.  This only requires
-- a Generic instance for your datatype.
gflabels :: forall t . (Generic (t (Const Text)),
                        GLabels (Rep (t (Const Text)) ()))
         => t (Const Text)
gflabels = to (genFlabels :: Rep (t (Const Text)) ())
    
data Dict c (t :: k) where
  -- | reified type class dictionary.  You need to put the constructor
  -- in scope in order to use the contained typeclass dictionaries.
  Dict :: c t => Dict c t

class FDicts c t where
  -- | hkd record containing the reified type class dictionaries for
  -- each field.
  fdicts :: t (Dict c)

class GFDicts t where
  genFdict :: t

instance (GFDicts (f ()), GFDicts (g ())) => GFDicts ((f :*: g) ()) where
  genFdict = genFdict :*: genFdict
  {-# INLINE genFdict #-}

instance c b =>
         GFDicts (S1 ('MetaSel _x1 _x2 _x3 _x4)
                   (Rec0 (Dict c b))
                   ()) where
  genFdict = M1 $ K1 $ Dict
  {-# INLINE genFdict #-}

instance GFDicts (b ()) => (GFDicts ((D1 meta (C1 meta2 b)) ())) where
  genFdict = M1 $ M1 $ genFdict
  {-# INLINE genFdict #-}

-- | Automatically derive fdict using generics.  This only requires a
-- Generic instance for your datatype.
gfdicts :: forall t c . (Generic (t (Dict c)),
                        GFDicts (Rep (t (Dict c)) ()))
         => t (Dict c)
gfdicts = to (genFdict :: Rep (t (Dict c)) ())

infixr 5 :>
infixr 5 :~>

-- | A heterogenous list of higher kinded records.  Use `:~>` to
-- separate the items, and `End` to terminate them.
data HkdProd (f :: a -> *) g t = t f :~> g t
-- | A heterogenous list of fields.  Use `:>` to separate the items,
-- and `End` to terminate them.
data LkdProd f g (x :: a) = f x :> g x
-- | The terminator.
data End (t :: k) = End

class GFTranspose x t (f :: a -> *) | x -> f where
  gftranspose :: x t -> t f

instance FRepeat t => GFTranspose End t End where
  gftranspose End = frepeat End

instance (FZip t, GFTranspose g t g') => 
  GFTranspose (HkdProd f g) t (LkdProd f g') where
  gftranspose (tf :~> tg) = fzipWith (:>) tf $ gftranspose tg

-- | zip over many arguments.  The function must take a heterogenous
-- list of fields, separated using `:>` and terminated by `End`,
-- while the argument must be a heterogenous list of records,
-- separated by `:~>`, end terminated by `End`.
--
-- For example:
--
-- @
-- zipShow :: (FFoldable t, FRepeat t, FLabels t, FDicts Show t, FZip t) =>
--            t Identity -> Text
-- zipShow t =
--   Text.concat $
--   intersperse "&" $
--   ftoList $ 
--   fzipManyWith
--   (\(Identity y :> Const lbl :> Dict :> End) ->
--       Const $ lbl <> "=" <> Text.pack (show y))
--   (t :~> flabels :~> fdicts @Show :~> End)
-- @

fzipManyWith :: ( FFunctor t, GFTranspose x t f) =>
                 (forall a. f a -> i a) ->
                 (x t -> t i)
fzipManyWith f tuple = ffmap f $ gftranspose tuple

type Lens' a s = forall f . Functor f => (a -> f a) -> s -> f s

-- | A lens for targetting a field of a higher kinded structure.  This
-- must be a newtype in order to be partially applied.
newtype FLens g s a = FLens (Lens' (g a) (s g))

iso :: (a -> s) -> (s -> a) -> Lens' a s
iso wrap unwrap f g =  wrap <$> f (unwrap g)
{-# INLINE iso #-}

compFLens :: Lens' (s g) (t g) -> FLens g s a -> FLens g t a
compFLens l (FLens m) = FLens (l . m)
{-# INLINE compFLens #-}

compIsoFLens :: (s g -> t g) -> (t g -> s g) -> FLens g s a -> FLens g t a
compIsoFLens wrap unwrap = compFLens (iso wrap unwrap)
{-# INLINE compIsoFLens #-}

class FLenses t where
  -- A record of lenses into the record.
  flenses :: t (FLens g t)

-- newtype to get rid of the extra type variable
newtype Tupled f (a :: k) = Tupled {unTupled :: f a ()}

-- these newtypes just rearrange the type variables so they 
newtype FunctorS1 label _x _x2 _x3 a g k =
  FunctorS1 { getFunctorS1 :: (S1 ('MetaSel label _x _x2 _x3)
                               (Rec0 (g a))
                               k)}

newtype FunctorD1 meta meta2 f l k =
  FunctorD1 { getFunctorD1 ::D1 meta (C1 meta2 (f l)) k }

newtype FunctorProd f g a k = FunctorProd ((f a :*: g a) k)

instance FFunctor (Tupled (FunctorS1 label _x _x2 _x3 a)) where
  ffmap f (Tupled (FunctorS1 (M1 (K1 x))))
    = Tupled $ FunctorS1 $ M1 $ K1 $ f x
  {-# INLINE ffmap #-}

instance FFunctor (Tupled f)
         => FFunctor (Tupled (FunctorD1 meta meta2 f)) where
  ffmap f (Tupled (FunctorD1 (M1 (M1 x)))) =
    Tupled $ FunctorD1 $ M1 $ M1 $ unTupled $ ffmap f $ Tupled x
  {-# INLINE ffmap #-}

instance ( FFunctor (Tupled f)
         , FFunctor (Tupled g)
         ) =>
         FFunctor (Tupled (FunctorProd f g)) where
  ffmap f (Tupled (FunctorProd (x :*: y))) =
    Tupled $ FunctorProd $
    unTupled (ffmap f (Tupled x)) :*:
    unTupled (ffmap f (Tupled y))
  {-# INLINE ffmap #-}

class Coercible (x ()) (Tupled r g) =>
  GFLenses (x :: * -> *) k (r :: (k -> *) -> * -> *) g | x -> k, x -> r where
  genflenses :: Tupled r (FLens g (Tupled r))
  
instance GFLenses ((S1 ('MetaSel label _x _x2 _x3)
                    (Rec0 (g (a :: k))) :: * -> *))
                   k
                  (FunctorS1 label _x _x2 _x3 a)
                  g where
  genflenses = Tupled $ FunctorS1 $ M1 $ K1 $ FLens $ \f g ->
    ( Tupled . FunctorS1  . M1 . K1 ) <$>
    f (unK1 . unM1 . getFunctorS1 .  unTupled $ g)
  {-# INLINE genflenses #-}

instance
  ( FFunctor (Tupled r)
  , GFLenses x k r g
  ) =>
  GFLenses (D1 meta (C1 meta2 x)) k (FunctorD1 meta meta2 r) g where
  genflenses = Tupled $ FunctorD1 $ M1 $ M1 $
               unTupled $
               ffmap (compIsoFLens
                      (Tupled . FunctorD1 . M1 . M1 . unTupled)
                      (Tupled . unM1 . unM1 . getFunctorD1 . unTupled)) $
               (genflenses @x)
  {-# INLINE genflenses #-}

instance ( FFunctor (Tupled r1)
         , FFunctor (Tupled r2)
         , Coercible ((x :*: y) ())  (Tupled (FunctorProd r1 r2) g)
         , GFLenses x k r1 g
         , GFLenses y k r2 g
         ) =>
         GFLenses (x :*: y) k (FunctorProd r1 r2) g
         where
  genflenses = Tupled $ FunctorProd $
               unTupled (ffmap (compFLens $
                                \f (Tupled (FunctorProd (a :*: b))) ->
                                  (Tupled . FunctorProd . (:*: b) . unTupled)
                                  <$> f (Tupled a))
                         (genflenses @x)) :*:
               unTupled (ffmap (compFLens $
                                \f (Tupled (FunctorProd (a :*: b))) ->
                                  (Tupled . FunctorProd . (a :*:) . unTupled)
                                  <$> f (Tupled b))
                         (genflenses @y))
        
  {-# INLINE genflenses #-}

type GFlensesMachinery k t r g =
  ( Generic (t g)
  , Generic (t (FLens g (Tupled r)))
  , Coercible (r (FLens g (Tupled r)) ())
    (Rep (t (FLens g (Tupled r))) ())
  , FFunctor (t :: (k -> *) -> *)
  , FFunctor (Tupled r)
  , GFLenses (Rep (t g)) k (r :: (k -> *) -> * -> *) g
  )

-- | Autogenerate lenses using generics.  You only need to derive
-- Generic for the datatype.
gflenses :: forall k t r g . GFlensesMachinery k t r g
         => t (FLens g t)
gflenses = ffmap (compIsoFLens toHkd fromHkd) $
           toHkd (genflenses @(Rep (t g)) @k @r)
{-# INLINE gflenses #-}

toHkd :: forall t g r.
         ( Generic (t g)
         , Coercible (r g ()) (Rep (t g) ())
         ) =>
         Tupled r g -> t g
toHkd t = to (coerce t :: Rep (t g) ())
{-# INLINE toHkd #-}          

fromHkd :: forall t g r.
         ( Generic (t g)
         , Coercible (r g ()) (Rep (t g) ())
         ) =>
         t g -> Tupled r g
fromHkd r = coerce (from r :: Rep (t g) ())
{-# INLINE fromHkd #-}

-- | collect (Const) elements into a list efficiently.
ftoList :: FFoldable t => t (Const a) -> [a]
ftoList = flip appEndo [] . ffoldMap (Endo . (:) . getConst)


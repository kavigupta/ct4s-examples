{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
module Category (

    ) where

import Prelude hiding (id, (.))

{-
    This is equivalent to Prelude's Category, but with a name that makes more sense.
    This represents morphisms where the objects are types in Haskell
-}
class (Morphism m) where
    id :: m a a
    (.) :: m b c -> m a b -> m a c

instance Morphism (->) where
    id x = x
    (f . g) x = f (g x)

{-
    Represents a class, or a generalized Set.
-}
class (Class c a) where
    contains :: c a -> a -> Bool

class (Class s a) => (Set s a) where
    empty :: s a
    cardinality :: (Integral u) => s a -> u
    u :: s a -> s a -> s a
    (&) :: s a -> s a -> s a
    (\\) :: s a -> s a -> s a

{-
    Represents a category within Haskell. Objects are from a given Haskell type
        and can be limited by the `ob` function.
-}

class (Category ob morph) | morph -> ob, ob -> morph where
    ob :: (Class c ob) => c ob
    morph :: (Set morphset morph) => ob -> ob -> morphset morph
    idcat :: ob -> morph
    (|>) :: morph -> morph -> morph

categoryLaw1 :: (Category ob morph, Eq morph) => ob -> morph -> Bool
categoryLaw1 ob f = idcat ob == f

categoryLaw2 :: (Category ob morph, Eq morph) => ob -> morph -> Bool
categoryLaw2 ob f = f == idcat ob

categoryLaw3 :: (Category ob morph, Eq morph) => morph -> morph -> morph -> Bool
categoryLaw3 f g h = (f |> g) |> h == f |> (g |> h)
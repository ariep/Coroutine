{-# OPTIONS_HADDOCK ignore-exports #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}
module Control.Monad.Indexed (
    module Prelude,
    IxMonad(..),
    IxCont(..),
    mapCont
) where
import Prelude hiding (Monad(..))

-- | IxMonad (Indexed Monad) carries type-level state through a
-- computation.  For an IxMonad m, m px py a represents a computation
-- with precondition px, postcondition py, and result value a.
-- "px" and "py" can be thought of as type-level propositions
-- that hold at the beginning and end of the computation.
class IxMonad m where
    return :: a -> m x x a
    (>>=)  :: m x y a -> (a -> m y z b) -> m x z b
    (>>)   :: m x y a -> m y z b -> m x z b
    fail   :: String -> m x y a

    m >> n = m >>= const n
    fail = error

-- | IxCont is a continuation monad that supports changing
-- of the answer type during the computation.  The result
-- is a functor "s x", where the caller of the computation
-- controls the type held inside the functor.
newtype IxCont s x y a = IxCont { runIxCont ::  forall b. (a -> s y b) -> s x b }

-- | mapCont changes the answer type of an IxCont, given a function
-- that maps any (s x) to a (s y).
mapCont :: (forall a. s x a -> s y a) -> IxCont s x z a -> IxCont s y z a
mapCont f (IxCont k) = IxCont (f . k)

instance IxMonad (IxCont s) where
    return x = IxCont $ \k -> k x
    m >>= g  = IxCont $ \k -> runIxCont m $ \a -> runIxCont (g a) k

{-

-------------------------------------------
- Derivation of bind operator in System F -
- /\r. = type lambda      @r = type apply -
- (haskell: forall r)  (haskell: omitted) -
-------------------------------------------

m >>= g  {pattern}

{from type of >>=}
m :: IxCont s x y a
g :: a -> IxCont s y z b

runIxCont m :: /\c. (a -> s y c) -> s x c {newtype}

IxCont ?1 :: IxCont s x z b

    ?1 :: /\r. (b -> s z r) -> s x r
    ?1 = /\r. \k -> ...
        k :: b -> s z r
        runIxCont m @r ?2 :: s x r
    ?1 = /\r. \k -> f @r ?2

    ?2 :: a -> s y r
    ?2 = \a -> ...
        a :: a
        g a :: IxCont s y z b
        runIxCont (g a) :: /\c. (b -> s z c) -> s y c
        runIxCont (g a) @r k :: s y r
    ?2 = \a -> runIxCont (g a) @r k

-}

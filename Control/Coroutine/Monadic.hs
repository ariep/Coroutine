{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies, EmptyDataDecls, TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
This module allows you to implement coroutines that communicate in a type-safe manner
using lightweight session types.  An abstract group of session \"type-combinators\" are
offered, and implementations are indexed by those types.

Indexed monads are used to thread the session state through the computation.  We
generally use them to implement \"type-level substitution\"; also known as
\"big lambda\".  For example, consider a session

>  session1 :: forall r. Session (Int :?: String :!: r) r Int

This represents a session that reads an Int, then writes a String, and delivers
an Int which can be used in the remainder of the session @r@.  A way to write it
with full type functions (not legal Haskell) would be

>  session1 :: Session (/\r. Int :?: String :!: r) Float

Using the indexed monad bind operator, we can do, for example:

@
  session2 = do
      x <- session1
      put x
@

Now session2 has the type @forall r. (Int :?: String :!: Float :!: r) r ()@

Connecting two sessions is easy; if they are the dual of each other (one reads
where the other writes), just call "connects s1 s2".  If the sessions are not
compatible, you'll get a reasonably readable compile-time error.
-}

module Control.Coroutine.Monadic
  ( module Control.Monad.Indexed
  , WM(..)
  , Eps
  , (:?:), (:!:)
  , (:&:), (:|:)
  , (:?*), (:!*)
  , (:++:), (:*)
  , Repeat
  , Session(..)

  , InSession(..)
    -- R, W, O, CL, CAT, StarC, StarS, Stop, Go,
  , Cat(Cat)
    
  , close, get, put, cat, offer, sel1, sel2
  , Loop(..), loopC, loopS, repeat, loop
  , MonadicSession, pre, pre_
  , runSession
    
  -- , Dual, Connect(..), connects
  ) where

import Control.Coroutine (Eps, (:?:), (:!:), (:&:), (:|:), (:?*), (:!*), (:++:), (:*))
import Control.Monad.Indexed

import qualified Control.Monad as P
import           Data.Functor.Compose (Compose)
import qualified Prelude as P
import           Prelude ((.), ($), (<$>), (<*>), Functor, Applicative, Either(..), flip)

-- | WM stands for "wrapped monad"; it wraps any Prelude monad.
-- This doesn't really belong in this module, but exporting it
-- correctly from IxMonad is a real pain.
-- This allows you to use NoImplicitPrelude when writing
-- "main" in the following way:
--
-- @
-- module Main where
-- import Control.Coroutine
-- main = runWM $ do
--           LiftWM $ putStrLn "hello world"
-- @

newtype WM m x y a = LiftWM { runWM :: m a }
instance P.Monad m => IxMonad (WM m) where
  return x = LiftWM (P.return x)
  m >>= f  = LiftWM (runWM m P.>>= runWM . f)
  m >> n   = LiftWM (runWM m P.>> runWM n)
  fail s   = LiftWM (P.fail s)

data Repeat s      -- ^ @Repeat a@ is the session @a@ repeated ad infinitum.

-- | @InSession m s v@ is a functor type representing a session that results
-- in the value @v@ being computed by the session, running in the monad @m@.
-- @s@ should be indexed by one of the session types above, although you can
-- extended the session type system by adding additional instances
-- here and to @Dual@ and @Connect@ below.
data family InSession (m :: * -> *) s v

newtype instance InSession m Eps v
  = Eps (m v)
newtype instance InSession m (a :?: r) v
  = R (a -> m (InSession m r v))
newtype instance InSession m (a :!: r) v
  = W (m (a, InSession m r v))
newtype instance InSession m (a :&: b) v
  = O (m (InSession m a v, InSession m b v))
newtype instance InSession m (a :|: b) v
  = C (m (Either (InSession m a v) (InSession m b v)))
newtype instance InSession m (a :++: b) v
  = CAT (m (Cat m a b v))
data Cat m a b v
  = forall z. Cat (InSession m a z) (z -> InSession m b v)
newtype instance InSession m (a :!* r) v
  = StarC (InSession m (r :|: (a :++: (a :!* r))) v)
newtype instance InSession m (a :?* r) v
  = StarS (InSession m (r :&: (a :++: (a :?* r))) v)
data    instance InSession m (a :* r) v
  = Stop (InSession m r v)
  | Go   (InSession m (r :&: (a :++: (a :* r))) v)
newtype instance InSession m (Repeat s) v
  = Repeat (InSession m (s :++: Repeat s) v)

-- | By indexing using a data family, we get an untagged representation of
-- the session; resolving how to link sessions together with "connect" can
-- happen at compile-time. A similar encoding is possible using GADTs, but
-- it requires runtime branching based on the GADT tag.
--
-- @IxCont s x y a@ == @forall b. (a -> s y b) -> s x b@; that is, if you
-- give us a continuation function that takes an @a@ and outputs the rest of
-- the session, we can give you a representation of the full session. When
-- a session is complete, @y@ is @Eps@, the empty session, so getting the
-- full session out is just @runIxCont (getSession session) Eps@ which gives
-- you the result of type @InSession session_type a@.
newtype Session m x y a
  = Session { getSession :: IxCont (InSession m) x y a }
  deriving (IxMonad)

mkSession :: (forall b. (a -> InSession m y b) -> InSession m x b)
  -> Session m x y a
mkSession = Session . IxCont

unSession :: Session m x y a -> (a -> InSession m y b) -> InSession m x b
unSession = runIxCont . getSession

-- | runSession converts a session computation into a "connectable"
-- session.
runSession :: (P.Monad m) => Session m c Eps a -> InSession m c a
runSession m = unSession m (Eps . P.return)

mapSession :: (Functor m)
  => (forall a. InSession m s1 a -> InSession m s2 a)
  -> Session m s1 r b -> Session m s2 r b
mapSession f m = Session $ mapCont f $ getSession m

-- | You never /need/ to explicitly call close; doing so just seals the
-- \"rest-of-computation\" parameter of the session.
close :: Session m Eps Eps ()
close = return ()

class MonadicSession s where
  preI :: (P.Monad m) => m x -> (x -> InSession m s y) -> InSession m s y

pre :: (MonadicSession s, P.Monad m)
  => m x -> (x -> Session m s Eps b) -> Session m s Eps b
pre h f = mkSession $ \ k -> preI h (flip unSession k . f)

pre_ :: (MonadicSession s, P.Monad m)
  => m () -> Session m s Eps y -> Session m s Eps y
pre_ h s = pre h (P.const s)

instance MonadicSession Eps where
  preI h f = Eps $ h P.>>= \ x -> case f x of Eps y -> y
instance MonadicSession (a :?: r) where
  preI h f = R $ \ a -> h P.>>= \ x -> case f x of R g -> g a
instance MonadicSession (a :!: r) where
  preI h f = W $ h P.>>= \ x -> case f x of W j -> j
instance MonadicSession (r :&: s) where
  preI h f = O $ h P.>>= \ x -> case f x of O j -> j
instance MonadicSession (r :|: s) where
  preI h f = C $ h P.>>= \ x -> case f x of C j -> j
instance MonadicSession (r :++: s) where
  preI h f = CAT $ h P.>>= \ x -> case f x of CAT j -> j

-- | @get@ reads an element from the connected coroutine.
get :: (P.Monad m) => Session m (a :?: r) r a
get = mkSession $ \ k -> R $ \ a -> P.return $ k a

-- | @put x@ sends the value x to the connected coroutine.
put :: (P.Monad m) => a -> Session m (a :!: r) r ()
put a = mkSession $ \ k -> W $ P.return (a, k ())

-- | @cat m@ takes a completed session and connects it at
-- the beginning of a sequence inside another session.
cat :: (P.Monad m) => Session m a Eps v -> Session m (a :++: r) r v
cat s = mkSession $ \ k -> CAT . P.return $
  Cat (runSession s) k

-- | @offer s1 s2@ gives the other side the choice of whether
-- to continue with session s1 or s2.
offer :: (P.Monad m) =>
  Session m a r v -> Session m b r v -> Session m (a :&: b) r v
offer sa sb = mkSession $ \k -> O . P.return $
  (unSession sa k, unSession sb k)

-- | @sel1@ chooses the first branch of an offer.
sel1 :: (P.Monad m) => Session m (a :|: b) a ()
sel1 = mkSession $ \k -> C . P.return . Left $ k ()

-- | @sel2@ chooses the second branch of an offer.
sel2 :: (P.Monad m) => Session m (a :|: b) b ()
sel2 = mkSession $ \k -> C . P.return . Right $ k ()

-- | @Loop@ is just nicely-named Either; it is used for
-- choosing whether or not to loop in these simplified looping
-- primitives.
data Loop a b = Loop a | Done b

-- | loopC is the client side of a "while" loop; it takes the current
-- loop state, and a computation that figures out the next loop state,
-- and loops until the computation returns "Done".
loopC :: (P.Monad m) => Loop a b        -- ^ Initial loop state
  -> (a -> Session m x Eps (Loop a b))  -- ^ Session for the loop
  -> Session m (x :!* r) r b            -- ^ Result of the loop
loopC (Done b) _ = mapSession StarC $ do
  sel1
  return b
loopC (Loop a) f = mapSession StarC $ do
  sel2
  a' <- cat (f a)
  loopC a' f

-- | loopS is the server side of a "while" loop; it must always offer
-- the client the option to terminate the loop at each iteration, or
-- to continue the loop.
loopS :: (P.Monad m) => a     -- ^ Initial loop state
  -> (a -> Session m x Eps a) -- ^ Session for the loop
  -> Session m (x :?* r) r a  -- ^ Result of the loop
loopS a f = mapSession StarS $ offer (return a) $ do
  a' <- cat (f a)
  loopS a' f

repeat :: (P.Monad m)
  => Session m r Eps ()
  -> Session m (Repeat r) Eps ()
repeat s = mapSession Repeat $ do
  cat s
  repeat s

-- | loop is a slightly more complicated looping primitive where either
-- side of the loop may choose to terminate the loop at each iteration.
-- It is useful for a server that has a fixed amount of data to give out,
-- when the client can also choose to escape early.

loop :: (P.Monad m) => Loop a b        -- ^ Initial loop state
  -> (a -> Session m x Eps (Loop a b)) -- ^ Session for the loop
  -> Session m (x :* r) r (Either a b) -- ^ Result of the loop
loop (Done b) _ = mapSession Stop $ return (Right b)
loop (Loop a) f = mapSession Go $ offer (return (Left a)) $ do
  a' <- cat (f a)
  loop a' f

-- Connection logic follows; it requires the "Dual" type-logic
-- that connects "reads" to "writes" in the type system.

type family Dual a
type instance Dual Eps        = Eps
type instance Dual (a :?: r)  = a :!: Dual r
type instance Dual (a :!: r)  = a :?: Dual r
type instance Dual (r :&: s)  = Dual r :|: Dual s
type instance Dual (r :|: s)  = Dual r :&: Dual s
type instance Dual (r :++: s) = Dual r :++: Dual s
type instance Dual (r :?* s)  = Dual r :!* Dual s
type instance Dual (r :!* s)  = Dual r :?* Dual s
type instance Dual (r :* s)   = Dual r :*  Dual s
type instance Dual (Repeat r) = Repeat (Dual r)

-- would like to put
-- class (Dual (Dual s) ~ s) => Connect s where ...
-- but that doesn't work with GHC 6.10.
-- class Connect s where
--   connect :: forall m a b c. (s ~ Dual c, c ~ Dual s, P.Monad m)
--     => InSession m s a -> InSession m c b -> m (a, b)

-- instance Connect Eps where
--   connect (Eps a) (Eps b) = P.return (a, b)
-- instance Connect s => Connect (a :?: s) where
--   connect (R k) (W a c) = flip connect c P.=<< k a
-- instance Connect s => Connect (a :!: s) where
--   connect (W a s) (R k) = connect s P.=<< k a
-- instance (Connect s1, Connect s2) => Connect (s1 :&: s2) where
--   connect (O s _) (CL c) = connect s c
--   connect (O _ s) (CR c) = connect s c
-- instance (Connect s1, Connect s2) => Connect (s1 :|: s2) where
--   connect (CL s) (O c _) = connect s c
--   connect (CR s) (O _ c) = connect s c
-- instance (Connect s1, Connect s2) => Connect (s1 :++: s2) where
--   connect (CAT s ks) (CAT c kc) =
--     P.join (connect <$> s <*> c) P.>>= \case
--       (vs, vc) -> P.join $ connect <$> ks vs <*> kc vc
-- instance (Connect s1, Connect s2) => Connect (s1 :?* s2) where
--   connect (StarS s) (StarC c) = connect s c
-- instance (Connect s1, Connect s2) => Connect (s1 :!* s2) where
--   connect (StarC s) (StarS c) = connect s c
-- instance (Connect s1, Connect s2) => Connect (s1 :* s2) where
--   connect (Stop s)     (Stop c)     = connect s c
--   connect (Stop s)     (Go (O c _)) = connect s c
--   connect (Go (O s _)) (Stop c)     = connect s c
--   connect (Go (O _ s)) (Go (O _ c)) = connect s c

-- | connect two completed sessions to each other
-- connects :: (P.Monad m) => (Connect s, Dual s ~ c, Dual c ~ s)
--   => Session m s Eps a -> Session m c Eps b -> m (a,b)
-- connects s c = P.join $ connect <$> runSession s <*> runSession c

-- some tests
{-
add_server n = runSession $ do
  loopS n $ \n -> do
    x <- get
    let n' = n + x
    put n'
    return n'
  close

mul_server n = runSession $ do
  loopS n $ \n -> do
    x <- get
    let n' = n * x
    put n'
    return n'
  close

num_client k = runSession $ do
  x <- loopC (Loop (2,[])) $ \(n,l) -> do
    put n
    n' <- get
    let l' = n' : l
    if n' > k then return (Done l')
              else return (Loop (n', l'))
  close
  return x

list_server l = loop (listdata l) listserv >> close
  where
    listdata []     = Done ()
    listdata (x:xs) = Loop (x,xs)
    
    listserv (x,xs) = put x >> return (listdata xs)
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NondecreasingIndentation #-}
module UnionFind (
    Point,
    fresh,
    find,
    union,
    equivalent,
) where

import Data.IORef
import Control.Monad

-- Based off of the implementation in "The Essence of ML Type Inference".
-- (N.B. union-find is also based off of this.)

newtype Point a = Point (IORef (Link a))
    deriving (Eq)

writePoint :: Point a -> Link a -> IO ()
writePoint (Point v) = writeIORef v

readPoint :: Point a -> IO (Link a)
readPoint (Point v) = readIORef v

data Link a
    -- NB: it is too bad we can't say IORef Int#; the weights remain boxed
    = Info {-# UNPACK #-} !(IORef Int) {-# UNPACK #-} !(IORef a)
    | Link {-# UNPACK #-} !(Point a)

fresh :: a -> IO (Point a)
fresh desc = do
    weight <- newIORef 1
    descriptor <- newIORef desc
    Point `fmap` newIORef (Info weight descriptor)

repr :: Point a -> IO (Point a)
repr point = readPoint point >>= \case
    Link point' -> do
        point'' <- repr point'
        when (point'' /= point') $ do
            writePoint point =<< readPoint point'
        return point''
    Info _ _ -> return point

find :: Point a -> IO a
find point =
    -- Optimize length 0 and 1 case at expense of
    -- general case
    readPoint point >>= \case
        Info _ d_ref -> readIORef d_ref
        Link point' -> readPoint point' >>= \case
            Info _ d_ref -> readIORef d_ref
            Link _ -> repr point >>= find

-- Keeps the descriptor of point2
union :: Point a -> Point a -> IO ()
union point1 point2 = do
    point1 <- repr point1
    point2 <- repr point2
    when (point1 /= point2) $ do
    l1 <- readPoint point1
    l2 <- readPoint point2
    case (l1, l2) of
        (Info wref1 dref1, Info wref2 dref2) -> do
            weight1 <- readIORef wref1
            weight2 <- readIORef wref2
            -- Should be able to optimize the == case separately
            if weight1 >= weight2
                then do
                    writePoint point2 (Link point1)
                    -- The weight calculation here seems a bit dodgy
                    writeIORef wref1 (weight1 + weight2)
                    writeIORef dref1 =<< readIORef dref2
                else do
                    writePoint point1 (Link point2)
                    writeIORef wref2 (weight1 + weight2)
        _ -> error "UnionFind.union: repr invariant broken"

equivalent :: Point a -> Point a -> IO Bool
equivalent point1 point2 = liftM2 (==) (repr point1) (repr point2)

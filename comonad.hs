{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-methods #-}
import Data.Monoid (Monoid, mempty, (<>))
import Control.Applicative ((<$>))
import Data.Array
import Data.Bits
import Data.Word
import Control.Monad (forM_)
import Control.Concurrent (threadDelay)

class Functor w => Comonad w where
    extract :: w a -> a
    extend :: (w a -> b) -> w a -> w b
    duplicate :: w a -> w (w a)
    duplicate = extend id
    extend f = fmap f . duplicate

(=>>) :: Comonad w => w a -> (w a -> b) -> w b
(=>>) = flip extend

-------------------------------------------------------------------------------

newtype Identity a = Identity { getId :: a }

instance Functor Identity where
    fmap f = Identity . f . getId

instance Comonad Identity where
    extract = getId
    extend f = Identity . f

-------------------------------------------------------------------------------

-- CoReader
data Product c a = Product c a

instance Functor (Product c) where
    fmap f (Product c a) = Product c (f a)

instance Comonad (Product c) where
    extract (Product _ a) = a
    extend f w@(Product c _) = Product c (f w)

-------------------------------------------------------------------------------

-- CoWriter
newtype Function m a = Function ( m -> a )

instance Functor (Function m) where
    fmap f (Function g) = Function $ f . g

instance Monoid m => Comonad (Function m) where
    extract (Function f) = f mempty
    extend f (Function g) = Function $ \m -> f (Function (\m' -> g (m <> m')))

-------------------------------------------------------------------------------

data Costate s a = Costate (s -> a) s

instance Functor (Costate s) where
    fmap f (Costate g s) = Costate (f . g) s

instance Comonad (Costate s) where
    extract (Costate f s) = f s
    extend f (Costate g s) = Costate (f . Costate g) s

------------------------------------------------------------------------------

data Stream a = Cons a (Stream a)

instance Functor Stream where
    fmap f (Cons x xs) = Cons (f x) (fmap f xs)

instance Comonad Stream where
    extract (Cons x _) = x
    duplicate xs@(Cons _ xs') = Cons xs (duplicate xs')
    extend f xs@(Cons _ xs') = Cons (f xs) (extend f xs')

-------------------------------------------------------------------

-------------------------------------------------------------------


-- CoReader as tuple

instance Comonad ((,) e) where
    extract = snd
    extend f w = (fst w, f w)

askC :: (e, a) -> e
askC = fst

askask :: (e, a) -> e
askask w = extract $ w =>> askC =>> askC

-- testCoReader :: (int, int) -> int
-- testCoReader w = extract $ w =>> \(e, a) -> e + a =>> \(e, a) -> e * a

data CArray i a = CA (Array i a) i

instance Ix i => Functor (CArray i) where
    fmap f (CA a i) = CA (fmap f a) i

instance Ix i => Comonad (CArray i) where
    extract (CA a i) = a ! i
    duplicate (CA a i) =
        let es' = map (\j -> (j, CA a j)) (indices a)
        in CA (array (bounds a) es') i
    extend f (CA a i) =
        let es' = map (\j -> (j, f (CA a j))) (indices a)
        in CA (array (bounds a) es') i

-------------------------------------------------------------------

data Z a = Z [a] a [a]

left, right :: Z a -> Z a
left (Z (l:ls) a rs) = Z ls l (a:rs)
left z = z
right (Z ls a (r:rs)) = Z (a:ls) r rs
right z = z

iterate1 :: (a -> a) -> a -> [a]
iterate1 f = tail . iterate f

instance Functor Z where
    fmap f (Z l a r) = Z (fmap f l) (f a) (fmap f r)

instance Comonad Z where
    extract (Z _ a _) = a
    duplicate z = Z (iterate1 left z) z (iterate1 right z)
    extend f z = Z (f <$> iterate1 left z) (f z) (f <$> iterate1 right z)

rule :: Word8 -> Z Bool -> Bool
rule w (Z (a:_) b (c:_)) = testBit w (sb 2 a .|. sb 1 b .|. sb 0 c) where
    sb _ False = 0
    sb n True = bit n
rule _ _ = False

move :: Int -> Z a -> Z a
move i u = iterate (if i < 0 then left else right) u !! abs i

toList :: Int -> Int -> Z a -> [a]
toList i j u = take (j - i) $ half $ move i u where
   half (Z _ b c) = b : c

testRule :: Word8 -> IO ()
testRule w = let u = Z (repeat False) True (repeat False)
      in putStr $
         unlines $
         take 20 $
         map (map (\x -> if x then '#' else ' ') . toList (-20) 20) $
         iterate (=>> rule w) u

data Z2 a = Z2 (Z (Z a))

instance Functor Z2 where
    fmap f (Z2 z) = Z2 (fmap (fmap f) z)

instance Comonad Z2 where
    extract (Z2 z) = extract (extract z)
    duplicate (Z2 z) = fmap Z2 $ Z2 $ roll $ roll z where
        roll a = Z (iterate1 (fmap left) a) a (iterate1 (fmap right) a)

countNeighbours :: Z2 Bool -> Int
countNeighbours (Z2 (Z
    (Z (n0:_) n1 (n2:_):_)
    (Z (n3:_) _  (n4:_))
    (Z (n5:_) n6 (n7:_):_))) = length $ filter id [n0, n1, n2, n3, n4, n5, n6, n7]
countNeighbours _ = 0

life :: Z2 Bool -> Bool
life z = a && (n == 2 || n == 3) || not a && n == 3 where
    a = extract z
    n = countNeighbours z

emptyRow :: Z Bool
emptyRow = Z (repeat False) False (repeat False)

emptyLife :: Z2 Bool
emptyLife = Z2 $ Z (repeat emptyRow) emptyRow (repeat emptyRow)

toZ :: [Bool] -> Z Bool
toZ xs = Z (repeat False) False (xs ++ repeat False)

toZ2 :: [[Bool]] -> Z2 Bool
toZ2 xss = Z2 $ Z (repeat emptyRow) emptyRow (fmap toZ xss ++ repeat emptyRow)

blinker :: Z2 Bool
blinker = toZ2 [[True, True, True]]

glider :: Z2 Bool
glider = toZ2 [
            [False, True],
            [False, False, True],
            [True,  True,  True]]

fromZ :: Z a -> [a]
fromZ (Z _ x xs) = x:xs

fromZ2 :: Z2 a -> [[a]]
fromZ2 (Z2 (Z _ x z)) = fromZ x : fmap fromZ z

display :: Int -> Int -> Z2 Bool -> String
display x y z = unlines $ take y $ fmap (take x) $ fromZ2 $ fmap (\b -> if b then 'X' else ' ') z

animation :: Z2 Bool -> [Z2 Bool]
animation = iterate $ extend life

clear :: IO ()
clear = putStr "\x1B[2J\x1B[;H"

animate :: Z2 Bool -> IO ()
animate z2 = forM_ (animation z2) $ \step -> do
    clear
    putStrLn $ display 80 25 step
    threadDelay 500000

-------------------------------------------------------------------

type Env e a = (e, a)

ask :: Env e a -> e
ask = fst

local :: (e -> e') -> Env e a -> Env e' a
local f (e, a) = (f e, a)

initial :: Env Int Int
initial = (n, n) where n = 0

experiment :: Env Int Int
experiment = fmap (+ 10) initial

result :: Int
result = extract experiment

initialValue :: Int
initialValue = extract (experiment =>> ask)
        
-------------------------------------------------------------------

instance (Num a, Num b) => Num (a, b) where
    (a, b) + (c, d) = (a + c, b + d)

laplace2D :: CArray (Int, Int) Float -> Float
laplace2D a = a ? (-1, 0)
            + a ? (0, -1)
            + a ? (0, 1)
            + a ? (1, 0)
            - 4 * a ? (0, 0)

(?) :: (Ix i, Num a, Num i) => CArray i a -> i -> a
CA a i ? i' = if inRange (bounds a) (i + i') then a ! (i + i') else 0


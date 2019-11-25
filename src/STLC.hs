module STLC where

import qualified Prelude as P
import           Prelude      hiding (lookup)

data Ty = Nat | Ty :→: Ty deriving (Show, Eq)

data Tm = Vr Int | Lm Tm | Tm :·: Tm deriving (Show, Eq)

data Sm = Tm Tm | Fn (Sm -> Sm)

instance Show Sm where
  show (Tm t) = "Tm " ++ show t
  show (Fn _) = "<Fun>"

reflect :: Int -> Ty -> Tm -> Sm
reflect n Nat       t = Tm t
reflect n (a :→: b) t = Fn $ \x -> reflect n b $ t :·: reify n a x

reify :: Int -> Ty -> Sm -> Tm
reify n Nat       (Tm t) = t
reify n Nat       (Fn _) = error "Nat, Fun"
reify n (a :→: b) (Tm _) = error ":→:, Tm"
reify n (a :→: b) (Fn f) = Lm $ reify (n + 1) b $ f $ reflect (n + 1) a (Vr n)

newtype Env = Env { lookup :: Int -> Sm }

empty :: Env
empty = Env (\i -> undefined)

extend :: Int -> Env -> Sm -> Env
extend n env x = Env lookup'
  where
    lookup' i | i <  n = lookup env i
              | i == n = x

eval' :: Int -> Tm -> Env -> Sm
eval' n (Vr i)    env                         = lookup env i
eval' n (Lm t)    env                         = Fn $ \x -> eval' (n + 1) t (extend n env x)
eval' n (t :·: u) env | Fn f <- eval' n t env = f $ eval' n u env
                      | otherwise             = error ":·:, Tm"

eval :: Tm -> Sm
eval t = eval' 0 t empty

norm :: Ty -> Tm -> Tm
norm a t = reify 0 a $ eval t

-- Scratchpad

ity :: Ty -> Ty
ity a = a :→: a

i :: Tm
i = Lm $ Vr 0

kty :: Ty -> Ty -> Ty
kty a b = a :→: (b :→: a)

k :: Tm
k = Lm $ Lm $ Vr 0

sty :: Ty -> Ty -> Ty -> Ty
sty a b c = (a :→: (b :→: c)) :→: ((a :→: b) :→: (a :→: c))

s :: Tm
s = Lm $ Lm $ Lm $ Vr 0 :·: Vr 2 :·: (Vr 1 :·: Vr 2)

cn :: Ty
cn = (Nat :→: Nat) :→: (Nat :→: Nat)

zero :: Tm
zero = Lm $ Lm $ Vr 1

one :: Tm
one = Lm $ Lm $ Vr 0 :·: Vr 1

two :: Tm
two = Lm $ Lm $ Vr 0 :·: (Vr 0 :·: Vr 1)

add :: Tm
add = Lm $ Lm $ Lm $ Lm $ Vr 0 :·: Vr 2 :·: (Vr 1 :·: Vr 2 :·: Vr 3)

mul :: Tm
mul = Lm $ Lm $ Lm $ Lm $ Vr 0 :·: (Lm $ Vr 1 :·: Vr 2 :·: Vr 4) :·: Vr 3

{-# OPTIONS --no-positivity-check #-}
module Gravy where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin as Fin renaming (zero to zeroF; suc to sucF; _+_ to _+F_)
open import Data.Fin.Patterns

infix 6 _ℕ-suc_
_ℕ-suc_ : (n : ℕ) → Fin n → Fin n
x ℕ-suc y = inject≤ (x Fin.ℕ- sucF y) (m∸n≤m x (toℕ y))

data Exp (n : ℕ) : Set where
  ind : (i   : Fin n)       → Exp n
  lam : (t   : Exp (1 + n)) → Exp n
  app : (r s : Exp n)       → Exp n

-- shift : ℕ → ℕ
-- shift n = suc n

shift : ∀ {n} → Fin n → Fin (1 + n)
shift = Fin.suc

-- lift : (ℕ → ℕ) → (ℕ → ℕ)
-- lift σ zero    = zero
-- lift σ (suc n) = suc (σ n)

ren : ∀ {n m} → (Fin n → Fin m) → Exp n → Exp m
ren σ (ind i)   = ind (σ i)
ren σ (lam t)   = lam (ren (lift 1 σ) t)
ren σ (app r s) = app (ren σ r) (ren σ s)

wkExp : ∀ {n} → Exp n → Exp (1 + n)
wkExp = ren shift

mutual
  data Ne (n : ℕ) : Set where
    ind : (i : Fin n) → Ne n
    app : (u : Ne n) → (v : Nf n) → Ne n

  data Nf (n : ℕ) : Set where
    neu : (u : Ne n) → Nf n
    lam : (v : Nf (1 + n)) → Nf n

mutual
  inc^Ne : ∀ {n} → Ne n → Exp n
  inc^Ne (ind i)   = ind i
  inc^Ne (app u v) = app (inc^Ne u) (inc^Nf v)

  inc^Nf : ∀ {n} → Nf n → Exp n
  inc^Nf (neu u) = inc^Ne u
  inc^Nf (lam v) = lam (inc^Nf v)

mutual
  data D (n : ℕ) : Set where
    lam : (f : ∀ {m} → m ≥ n → D m → D m) → D n
    neu : (e : D^ne n) → D n

  data D^ne (n : ℕ) : Set where
    lev : (k : Fin n) → D^ne n
    app : (e : D^ne n) → (d : D n) → D^ne n

mutual
  wkD : ∀ {n m} → m ≥ n → D n → D m
  wkD m≥n (lam f) = lam λ k≥m → f (≤-trans m≥n k≥m)
  wkD m≥n (neu e) = neu (wkD^ne m≥n e)

  wkD^ne : ∀ {n m} → m ≥ n → D^ne n → D^ne m
  wkD^ne m≥n (lev k)   = lev (inject≤ k m≥n)
  wkD^ne m≥n (app e d) = app (wkD^ne m≥n e) (wkD m≥n d)

appsem : ∀ {n} → D n → D n → D n
appsem (lam f) d = f ≤-refl d
appsem (neu e) d = neu (app e d)

Env = λ n m → Fin n → D m

wkEnv : (n : ℕ) → ∀ {m k} → k ≥ m → Env n m → Env n k
wkEnv n k≥m ρ i = wkD k≥m (ρ i)

_,_ : ∀ {n m} → Env n m → D m → Env (1 + n) m
(ρ , d) zeroF    = d
(ρ , d) (sucF i) = ρ i

ρ : (n : ℕ) → Env n n
-- ρ n i = neu (lev (n Fin.ℕ- (Fin.suc i)))
ρ (suc n) i = (wkEnv n (n≤1+n n) (ρ n) , neu (lev (fromℕ n))) i

⟦_⟧_ : ∀ {n} → Exp n → ∀ {m} → Env n m → D m
⟦ ind i   ⟧ ρ = ρ i
⟦ lam t   ⟧ ρ = {- let f d = ⟦ t ⟧ (ρ , d) in -} lam λ m'≥m x → ⟦ t ⟧ (wkEnv _ m'≥m ρ , x)
⟦ app r s ⟧ ρ = appsem (⟦ r ⟧ ρ) (⟦ s ⟧ ρ)

mutual
  reflect : (n : ℕ) → Ne n → D n
  reflect n u = ⟦ inc^Ne u ⟧ ρ n

  R^nf : (n : ℕ) → D n → Nf n
  R^nf n (lam f) = lam (R^nf (1 + n) (f (n≤1+n n) (reflect (1 + n) (ind 0F))))
  R^nf n (neu e) = neu (R^ne n e)

  R^ne : (n : ℕ) → D^ne n → Ne n
  R^ne n (lev k)   = ind (n ℕ-suc k)
  R^ne n (app e d) = app (R^ne n e) (R^nf n d)

reify : (n : ℕ) → D n → Nf n
reify = R^nf

nf : (n : ℕ) → Exp n → Nf n
nf n t = R^nf n (⟦ t ⟧ ρ n )

module Scratchpad where
  infix  19 ƛ_
  infixl 20 _·_
  v   : ∀ {n} → Fin n → Exp n
  ƛ_  : ∀ {n} → Exp (1 + n) → Exp n
  _·_ : ∀ {n} → Exp n → Exp n → Exp n
  v   = ind
  ƛ_  = lam
  _·_ = app

  private
    openn : ∀ {n} → Exp n → Exp (2 + n)
    openn t = wkExp (wkExp t) · v 1F · v 0F

    close : ∀ {n} → Exp (2 + n) → Exp n
    close t = ƛ ƛ t

    num' : ℕ → Exp 2
    num' zero    = v 0F
    num' (suc n) = v 1F · num' n

  num : ℕ → Exp 0
  num n = close (num' n)

  add : Exp 0
  add = ƛ ƛ ƛ ƛ wkExp (wkExp (v 1F)) · v 1F · openn (v 0F)

  mul : Exp 0
  mul = ƛ ƛ ƛ ƛ wkExp (wkExp (v 1F)) · (ƛ wkExp (wkExp (wkExp (v 0F))) · v 2F · v 0F) · v 0F

  tru : Exp 0
  tru = ƛ ƛ v 1F

  fal : Exp 0
  fal = ƛ ƛ v 0F

  con : Exp 0
  con = ƛ ƛ ƛ v 2F · v 1F · v 0F

  Y = ƛ (ƛ v (fromℕ 1) · (v 0F · v 0F)) · (ƛ v (fromℕ 1) · (v 0F · v 0F))

  I : Exp 0
  I = ƛ v 0F

  Ω : Exp 0
  Ω = Y · I

  ⊥ : Nf 0
  ⊥ = nf 0 Ω

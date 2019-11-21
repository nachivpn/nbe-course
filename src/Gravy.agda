{-# OPTIONS --no-positivity-check #-}
module Gravy where

open import Data.Nat

data Exp : Set where
  ind : (i   : ℕ)   → Exp
  lam : (t   : Exp) → Exp
  app : (r s : Exp) → Exp

shift : ℕ → ℕ
shift n = suc n

lift : (ℕ → ℕ) → (ℕ → ℕ)
lift σ zero    = zero
lift σ (suc n) = suc (σ n)

ren : (ℕ → ℕ) → Exp → Exp
ren σ (ind i)   = ind (σ i)
ren σ (lam t)   = lam (ren (lift σ) t)
ren σ (app r s) = app (ren σ r) (ren σ s)

mutual
  data Ne : Set where
    ind : (i : ℕ) → Ne
    app : (u : Ne) → (v : Nf) → Ne

  data Nf : Set where
    neu : (u : Ne) → Nf
    lam : (v : Nf) → Nf

mutual
  inc^Ne : Ne → Exp
  inc^Ne (ind i)   = ind i
  inc^Ne (app u v) = app (inc^Ne u) (inc^Nf v)

  inc^Nf : Nf → Exp
  inc^Nf (neu u) = inc^Ne u
  inc^Nf (lam v) = lam (inc^Nf v)

mutual
  data D : Set where
    lam : (f : D → D) → D
    neu : (e : D^ne) → D

  data D^ne : Set where
    lev : (k : ℕ) → D^ne
    app : (e : D^ne) → (d : D) → D^ne

appsem : D → D → D
appsem (lam f) d = f d
appsem (neu e) d = neu (app e d)

Env = ℕ → D

_,_ : Env → D → Env
(ρ , d) zero    = d
(ρ , d) (suc i) = ρ i

ρ : ℕ → Env
ρ n i = neu (lev (n ∸ (i + 1)))

⟦_⟧_ : Exp → Env → D
⟦ ind i   ⟧ ρ = ρ i
⟦ lam t   ⟧ ρ = let f d = ⟦ t ⟧ (ρ , d) in lam f
⟦ app r s ⟧ ρ = appsem (⟦ r ⟧ ρ) (⟦ s ⟧ ρ)

mutual
  reflect : ℕ → Ne → D
  reflect n u = ⟦ inc^Ne u ⟧ ρ n

  R^nf : ℕ → D → Nf
  R^nf n (lam f) = lam (R^nf (n + 1) (f (reflect (n + 1) (ind 0))))
  R^nf n (neu e) = neu (R^ne n e)

  R^ne : ℕ → D^ne → Ne
  R^ne n (lev k)   = ind (n ∸ (k + 1))
  R^ne n (app e d) = app (R^ne n e) (R^nf n d)

reify : ℕ → D → Nf
reify = R^nf

nf : ℕ → Exp → Nf
nf n t = R^nf n (⟦ t ⟧ (ρ n))

module Scratchpad where
  infix  19 ƛ_
  infixl 20 _·_
  v   : ℕ → Exp
  ƛ_  : Exp → Exp
  _·_ : Exp → Exp → Exp
  v   = ind
  ƛ_  = lam
  _·_ = app

  private
    record Opened : Set where
      constructor opened
      field
        t : Exp

    Closed = Exp

    openn : Closed → Opened
    openn t = opened (t · v 1 · v 0)

    close : Opened → Closed
    close (opened t) = ƛ ƛ t

    num' : ℕ → Opened
    num' zero    = opened (v 0)
    num' (suc n) = opened (v 1 · let opened t = num' n in t)

    add' : Closed → Opened → ℕ → ℕ → Opened
    add' t (opened u) s z = opened (t · v s · u)

    mul' : Closed → Closed → ℕ → ℕ → Opened
    mul' t u s z = opened (t · (ƛ let opened v = add' (ren shift u) (opened (v 0)) (shift s) (shift z) in v) · v z)

  num : ℕ → Exp
  num n = close (num' n)

  add : Exp
  add = ƛ ƛ close (add' (v 3) (openn (v 2)) 1 0)

  mul : Exp
  mul = ƛ ƛ close (mul' (v 3) (v 2) 1 0)

  tru : Exp
  tru = ƛ ƛ v 1

  fal : Exp
  fal = ƛ ƛ v 0

  con : Exp
  con = ƛ ƛ ƛ v 2 · v 1 · v 0

  Y = ƛ (ƛ v 1 · (v 0 · v 0)) · (ƛ v 1 · (v 0 · v 0))

  I = ƛ v 0

  Ω = Y · I

  ⊥ = nf 1 Ω

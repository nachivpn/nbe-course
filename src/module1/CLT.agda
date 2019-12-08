module CLT where

-- stdlib imports

open import Data.Nat
  using (ℕ ; zero ; suc) public
open import Data.Unit using (⊤ ; tt)
open import Data.Product
  using (∃ ; Σ ; _×_ ; _,_)
  renaming (proj₁ to π₁ ; proj₂ to π₂) public
open import Relation.Nullary using (¬_) public
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂ ; subst)
  renaming (refl to ≡-refl ; trans to ≡-trans ; sym to ≡-sym) public
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to trans) public
open import Relation.Binary.Construct.Closure.Equivalence
  using (EqClosure ; symmetric)
  renaming (isEquivalence to EqClosureIsEquivalence)
open import Data.Sum
  using ()
  renaming (inj₁ to fwd ; inj₂ to bwd)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂) public

open Star renaming (ε to refl) public

infixl 6 _+_
infixr 5 _⇒_

data Ty : Set where
  Nat : Ty
  _⇒_ _+_ : Ty →  Ty → Ty

private
  variable
    a b c : Ty

infixl 5 _∙_

data Tm : Ty → Set where
  K    : Tm (a ⇒ b ⇒ a)
  S    : Tm ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
  Zero : Tm Nat
  Succ : Tm (Nat ⇒ Nat)
  Rec  : Tm (a ⇒ (Nat ⇒ a ⇒ a) ⇒ Nat ⇒ a)
  _∙_  : Tm (a ⇒ b) → Tm a → Tm b
  Inl  : Tm (a ⇒ a + b)
  Inr  : Tm (b ⇒ a + b)
  Case : Tm ((a ⇒ c) ⇒ (b ⇒ c) ⇒ (a + b) ⇒ c)

data Nf : Ty → Set where
  -- nats
  Zero  : Nf Nat
  Succ  : Nf (Nat ⇒ Nat)
  Succ∙ : (n : Nf Nat) → Nf Nat
  -- K-terms
  K     : Nf (a ⇒ b ⇒ a)
  K∙    : (n : Nf a) → Nf (b ⇒ a)
  -- S-terms
  S     : Nf ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
  S∙    : (n : Nf (a ⇒ b ⇒ c)) → Nf ((a ⇒ b) ⇒ a ⇒ c)
  S∙∙   : (m : Nf (a ⇒ b ⇒ c)) → (n : Nf (a ⇒ b)) → Nf (a ⇒ c)
  -- Rec-terms
  Rec   : Nf (a ⇒ (Nat ⇒ a ⇒ a) ⇒ Nat ⇒ a)
  Rec∙  : (n : Nf a) → Nf ((Nat ⇒ a ⇒ a) ⇒ Nat ⇒ a)
  Rec∙∙ : (m : Nf a) → (n : Nf (Nat ⇒ a ⇒ a)) → Nf (Nat ⇒ a)
  -- In*-terms
  Inl    : Nf (a ⇒ a + b)
  Inr    : Nf (b ⇒ a + b)
  Inl∙   : Nf a → Nf (a + b)
  Inr∙   : Nf b → Nf (a + b)
  -- Case-terms
  Case   : Nf ((a ⇒ c) ⇒ (b ⇒ c) ⇒ (a + b) ⇒ c)
  Case∙  : Nf (a ⇒ c) → Nf ((b ⇒ c) ⇒ (a + b) ⇒ c)
  Case∙∙ : Nf (a ⇒ c) → Nf (b ⇒ c) → Nf (a + b ⇒ c)

-- embed normal forms to terms
em : Nf a → Tm a
em Zero         = Zero
em Succ         = Succ
em (Succ∙ n)    = Succ ∙ em n
em K            = K
em (K∙ n)       = K ∙ (em n)
em S            = S
em (S∙ n)       = S ∙ (em n)
em (S∙∙ m n)    = S ∙ (em m) ∙ (em n)
em Rec          = Rec
em (Rec∙ n)     = Rec ∙ (em n)
em (Rec∙∙ m n)  = Rec ∙ (em m) ∙ (em n)
em Inl          = Inl
em Inr          = Inr
em (Inl∙ n)     = Inl ∙ em n
em (Inr∙ n)     = Inr ∙ em n
em Case         = Case
em (Case∙ n)    = Case ∙ (em n)
em (Case∙∙ m n) = Case ∙ (em m) ∙ (em n)

-- small-step reduction relation
data _⟶_ : Tm a → Tm a → Set where
  redk : {e : Tm a} {e' : Tm b}
     → (K ∙ e ∙ e') ⟶ e
  reds : {g : Tm (a ⇒ b ⇒ c)} {f : Tm (a ⇒ b)} {e : Tm a}
     → (S ∙ g ∙ f ∙ e) ⟶ (g ∙ e ∙ (f ∙ e))
  rec0 : {e : Tm a} {f : Tm (Nat ⇒ a ⇒ a)}
     → (Rec ∙ e ∙ f ∙ Zero) ⟶ e
  recs : {e : Tm a} {f : Tm (Nat ⇒ a ⇒ a)} {n : Tm Nat}
     → (Rec ∙ e ∙ f ∙ (Succ ∙ n)) ⟶ (f ∙ n ∙ (Rec ∙ e ∙ f ∙ n))
  app1  : {t t' : Tm (a ⇒ b)} {u : Tm a}
    → t ⟶ t'
    → (t ∙ u) ⟶ (t' ∙ u)
  app2  : {t : Tm (a ⇒ b)} {u u' : Tm a}
    → u ⟶ u'
    → (t ∙ u) ⟶ (t ∙ u')
  redl : {s : Tm a} {f : Tm (a ⇒ c)} {g : Tm (b ⇒ c)}
    → (Case ∙ f ∙ g ∙ (Inl ∙ s)) ⟶ (f ∙ s)
  redr : {s : Tm b} {f : Tm (a ⇒ c)} {g : Tm (b ⇒ c)}
    → (Case ∙ f ∙ g ∙ (Inr ∙ s)) ⟶ (g ∙ s)
  inl  : {t t' : Tm a}
    → t ⟶ t'
    → (Inl {a} {b} ∙ t) ⟶ (Inl ∙ t')
  inr  : {t t' : Tm b}
    → t ⟶ t'
    → (Inr {b} {a} ∙ t) ⟶ (Inr ∙ t')

-- NOTE: The relation _⟶_ is *not* deterministic
-- since we can make a choice when we encounter `App`

infix 3 _⟶*_

-- zero or more steps of reduction
_⟶*_ : Tm a → Tm a → Set
_⟶*_ = Star (_⟶_)

infix 3 _≈_

-- conversion relation built from reduction steps
-- yields an equational theory for terms
_≈_    : Tm a → Tm a → Set
_≈_   = EqClosure _⟶_

module Norm where

  -- interpretation of types
  ⟦_⟧ : Ty → Set
  ⟦  Nat  ⟧ = ℕ
  ⟦ a ⇒ b ⟧ = Nf (a ⇒ b) × (⟦ a ⟧ → ⟦ b ⟧)
  ⟦ a + b ⟧ = ⟦ a ⟧ ⊎ ⟦ b ⟧

  reify : ⟦ a ⟧ → Nf a
  reify {Nat}   zero     = Zero
  reify {Nat}   (suc x)  = Succ∙ (reify x)
  reify {a ⇒ b} (t , _)  = t
  reify {a + b} (inj₁ x) = Inl∙ (reify x)
  reify {a + b} (inj₂ y) = Inr∙ (reify y)

  infixl 5 _∙'_

  -- semantic application
  _∙'_ : ⟦ a ⇒ b ⟧ → ⟦ a ⟧ → ⟦ b ⟧
  _∙'_ (_ , f) x = f x

  -- semantic recursion
  rec' : ⟦ a ⟧ → ⟦ Nat ⇒ a ⇒ a ⟧ → ⟦ Nat ⟧ → ⟦ a ⟧
  rec' b f zero = b
  rec' b f (suc n) = f ∙' n ∙' (rec' b f n)

  case' : ⟦ a ⇒ c ⟧ → ⟦ b ⇒ c ⟧ → ⟦ a + b ⟧ → ⟦ c ⟧
  case' f g (inj₁ x) = f ∙' x
  case' f g (inj₂ y) = g ∙' y

  -- interpretation of terms
  eval : Tm a → ⟦ a ⟧
  eval K    = K , λ x → (K∙ (reify x)) , λ _ → x
  eval S    = S , λ g →
    S∙ (reify g) , λ f →
      S∙∙ (reify g) (reify f) , λ x →
        (g ∙' x) ∙' (f ∙' x)
  eval Zero = zero
  eval Succ = Succ , suc
  eval Rec  = Rec , λ b →
    Rec∙ (reify b) , λ f  →
      Rec∙∙ (reify b) (reify f) , λ n →
        rec' b f n
  eval (t ∙ u) = (eval t) ∙' (eval u)
  eval Inl = Inl , inj₁
  eval Inr = Inr , inj₂
  eval (Case)  = Case , λ f →
    Case∙ (reify f) , λ g →
      Case∙∙ (reify f) (reify g) , λ s →
        case' f g s

  norm : Tm a → Nf a
  norm t = reify (eval t)

open Norm

module Utilities where

  sym : {t t' : Tm a} → t ≈ t' → t' ≈ t
  sym = symmetric _⟶_

  -- embed reduction relations into ≈

  ⟶→≈ : {e e' : Tm a}
    → e ⟶ e'
    → e ≈ e'
  ⟶→≈ p = fwd p ◅ refl

  ⟶*→≈ : {t u : Tm a} → t ⟶* u → t ≈ u
  ⟶*→≈ refl = refl
  ⟶*→≈ (x ◅ p) = trans (⟶→≈ x) (⟶*→≈ p)

  -- embed ⟶ to ⟶*
  lift : {e e' : Tm a}
    → e ⟶ e'
    → e ⟶* e'
  lift p = p ◅ refl

  -- congruence rule for `App` (in ⟶*)
  app*  : {t t' : Tm (a ⇒ b)} {u u' : Tm a}
      → t ⟶* t'
      → u ⟶* u'
      → t ∙ u ⟶* t' ∙ u'
  app* refl    refl    = refl
  app* refl    (x ◅ q) = (app2 x) ◅ (app* refl q)
  app* (x ◅ p) q       = (app1 x) ◅ (app* p q)

open Utilities

module SetoidUtil where

  open import Relation.Binary
    using (Setoid ; IsEquivalence)

  open Setoid
    renaming (_≈_ to _≈ₑ_)
    using (Carrier ; isEquivalence)

  -- Terms form a setoid
  Tms : (a : Ty) → Setoid _ _
  Tms a .Carrier = Tm a
  Tms a ._≈ₑ_     = _≈_
  Tms a .isEquivalence = EqClosureIsEquivalence _⟶_

  open import Relation.Binary.SetoidReasoning public

open SetoidUtil

module Soundness where

  -- soundness of reduction in the model
  sound-red : {t t' : Tm a} → t ⟶ t' → eval t ≡ eval t'
  sound-red redk = ≡-refl
  sound-red reds = ≡-refl
  sound-red rec0 = ≡-refl
  sound-red recs = ≡-refl
  sound-red (app1 p)
    = cong (λ x → x ∙' _) (sound-red p)
  sound-red (app2 {t = t} p)
    = cong (λ x → (eval t) ∙' x) (sound-red p)
  sound-red redl = ≡-refl
  sound-red redr = ≡-refl
  sound-red (inl p)
    = cong inj₁ (sound-red p)
  sound-red (inr p)
    = cong inj₂ (sound-red p)

  -- soundness of conversion in the model
  sound : {t t' : Tm a} → t ≈ t' → eval t ≡ eval t'
  sound refl = ≡-refl
  sound (fwd x ◅ p) = ≡-trans (sound-red x) (sound p)
  sound (bwd y ◅ p) = ≡-trans (≡-sym (sound-red y)) (sound p)

  -- convertible terms yield the same normal form
  unique-nf-forth : {t t' : Tm a} → t ≈ t' → norm t ≡ norm t'
  unique-nf-forth p = cong reify (sound p)

open Soundness

module Completeness where

  -- quote from model into terms
  -- p.s. cannot be named "quote" since it's an Agda keyword
  quot : ⟦ a ⟧ → Tm a
  quot v = em (reify v)

  -- a "submodel" (called glued model) equipped with a proof
  -- that quot is homomorphic on the reduction relation _⟶*_
  -- Note: this submodel acts as *necessary* technical device
  -- to prove consistency (see below)
  Gl : ⟦ a ⟧ → Set
  Gl {Nat}   n = ⊤
  Gl {a ⇒ b} f = ∀ (x : ⟦ a ⟧) → Gl x
    → (quot f ∙ quot x ⟶* quot (f ∙' x))
    × Gl (f ∙' x)
  Gl {a + b} (inj₁ x) = Gl x
  Gl {a + b} (inj₂ y) = Gl y

  -- application for glued values
  appg : {f : ⟦ a ⇒ b ⟧} {x : ⟦ a ⟧}
    → Gl f → Gl x
    → Gl (f ∙' x)
  appg fg xg = π₂ (fg _ xg)

  -- primitive recursion for glued values
  recg : {x : ⟦ a ⟧} {f :  ⟦ Nat ⇒ a ⇒ a ⟧ } {n : ⟦ Nat ⟧}
    → Gl x → Gl f → Gl n → Gl (rec' x f n)
  recg {n = zero}  xg fg ng = xg
  recg {n = suc n} xg fg ng =
    appg (appg fg ng) (recg {n = n} xg fg ng)

  caseg : {f : ⟦ a ⇒ c ⟧} → {g : ⟦ b ⇒ c ⟧} → {s : ⟦ a + b ⟧}
    → Gl f → Gl g → Gl s → Gl (case' f g s)
  caseg {s = inj₁ x} fg gg sg = appg fg sg
  caseg {s = inj₂ y} fg gg sg = appg gg sg

  -- homomorphism properties of quot

  hom-app : {f : ⟦ a ⇒ b ⟧} {x : ⟦ a ⟧}
    → Gl f → Gl x
    → quot f ∙ quot x ⟶* quot (f ∙' x)
  hom-app fg xg = π₁ (fg _ xg)

  hom-rec : {x : ⟦ a ⟧} {f : ⟦ Nat ⇒ a ⇒ a ⟧ } {n : ⟦ Nat ⟧}
      → Gl x → Gl f → Gl n
      → quot (eval Rec ∙' x ∙' f) ∙ quot n
      ⟶* quot (rec' x f n)
  hom-rec {n = zero}  xg fg ng = lift rec0
  hom-rec {x = x} {f} {n = suc n} xg fg ng =
        recs ◅ trans
          (app* (hom-app fg ng) (hom-rec {n = n} xg fg _))
          (hom-app (appg fg _) (recg {n = n} xg fg _))

  hom-case : {f : ⟦ a ⇒ c ⟧ } {g : ⟦ b ⇒ c ⟧} {s : ⟦ a + b ⟧}
      → Gl f → Gl g → Gl s
      → quot (eval Case ∙' f ∙' g) ∙ quot s
      ⟶* quot (case' f g s)
  hom-case {s = inj₁ x} fg gg sg = trans (lift redl) (hom-app fg sg)
  hom-case {s = inj₂ y} fg gg sg = trans (lift redr) (hom-app gg sg)

  open import Function

  -- interpretation of terms in the glued model
  -- Note: main challenge here is to provide a proof
  -- object that quot is a homomorphism in each case
  gl : (t : Tm a) →  Gl (eval t)
  gl K x xg    = refl , λ x _ → (lift redk) , xg
  gl Zero      = tt
  gl Succ      = λ x _ → refl , tt
  gl (t ∙ u) = π₂ (gl t _ (gl u))
  gl S g gg    = refl , λ f fg →
    refl , λ x xg →
         reds ◅ trans
           (app* (hom-app gg xg) (hom-app fg xg))
           (hom-app (appg gg xg) (appg fg xg))
        , appg (appg gg xg) (appg fg xg)
  gl Rec x xg   = refl , (λ f fg →
    refl , λ n ng →
      hom-rec {n = n} xg fg ng , (recg {n = n} xg fg ng))
  gl Inl x xg = refl , xg
  gl Inr x xg = refl , xg
  gl (Case) f fg = refl , λ g gg →
    refl , λ s sg → hom-case {s = s} fg gg sg , caseg {s = s} fg gg sg

  -- normalization is consistent with reduction (_⟶*_)
  -- or, loosely speaking, `norm` transforms by reduction
  consistent-red* : (t : Tm a) → t ⟶* em (norm t)
  consistent-red* K = refl
  consistent-red* S = refl
  consistent-red* Zero = refl
  consistent-red* Succ = refl
  consistent-red* Rec = refl
  consistent-red* (t ∙ u) = trans
    (app* (consistent-red* t) (consistent-red* u))
    (hom-app (gl t) (gl u))
  consistent-red* Inl  = refl
  consistent-red* Inr  = refl
  consistent-red* Case = refl

  -- normalization is consistent with conversion
  consistent : (t : Tm a) → t ≈ em (norm t)
  consistent t = ⟶*→≈ (consistent-red* t)

  -- syntactically identical terms are convertible
  ≡→≈ : {t t' : Tm a} → t ≡ t' → t ≈ t'
  ≡→≈ ≡-refl = refl

  -- if the normal forms are two terms are equal,
  -- then the terms must be convertible
  unique-nf-back : {t t' : Tm a} → norm t ≡ norm t' → t ≈ t'
  unique-nf-back {t = t} {t'} p =
    trans (consistent t) (trans (≡→≈ (cong em p)) (sym (consistent t')))

  -- completeness of interpretation in the model
  complete : {t t' : Tm a} → eval t ≡ eval t' → t ≈ t'
  complete p = unique-nf-back (cong reify p)

open Completeness

-- Random experiments below, might not make any sense

module _ where

  app : {t t' : Tm (a ⇒ b)} {u u' : Tm a}
    → t ≈ t'
    → u ≈ u'
    → t ∙ u ≈ t' ∙ u'
  app refl refl = refl
  app refl (fwd x ◅ q) = fwd (app2 x) ◅ app refl q
  app refl (bwd y ◅ q) = bwd (app2 y) ◅ app refl q
  app (fwd x ◅ p) refl = fwd (app1 x) ◅ app p refl
  app (bwd y ◅ p) refl = bwd (app1 y) ◅ app p refl
  app (fwd x ◅ p) (fwd y ◅ q)
    = trans (fwd (app1 x) ◅ fwd (app2 y) ◅ refl) (app p q)
  app (fwd x ◅ p) (bwd y ◅ q)
    = trans (fwd (app1 x) ◅ bwd (app2 y) ◅ refl) (app p q)
  app (bwd x ◅ p) (fwd y ◅ q)
    = trans (bwd (app1 x) ◅ fwd (app2 y) ◅ refl) (app p q)
  app (bwd x ◅ p) (bwd y ◅ q)
    = trans (bwd (app1 x) ◅ bwd (app2 y) ◅ refl) (app p q)

-----------------------------
-- Intensional normalization
-----------------------------

module _ where

  -- see pg. 1 of "Semantic analysis of normalisation by
  -- evaluation for typed lambda calculus" by M. Fiore 2002

  -- 1. stability
  stability : (n : Nf a) → norm (em n) ≡ n
  stability Zero = ≡-refl
  stability Succ = ≡-refl
  stability (Succ∙ n) = cong Succ∙ (stability n)
  stability K = ≡-refl
  stability (K∙ n) = cong K∙ (stability n)
  stability S = ≡-refl
  stability (S∙ n) = cong S∙ (stability n)
  stability (S∙∙ m n) = cong₂ S∙∙ (stability m) (stability n)
  stability Rec = ≡-refl
  stability (Rec∙ n) = cong Rec∙ (stability n)
  stability (Rec∙∙ m n) = cong₂ Rec∙∙ (stability m) (stability n)
  stability Inl = ≡-refl
  stability Inr = ≡-refl
  stability (Inl∙ n) = cong Inl∙ (stability n)
  stability (Inr∙ n) = cong Inr∙ (stability n)
  stability Case = ≡-refl
  stability (Case∙ n) = cong Case∙ (stability n)
  stability (Case∙∙ m n) = cong₂ Case∙∙ (stability m) (stability n)

  -- 2. consistency (above)
  -- 3. unique-nf-forth (above)

  -- corollaries
  private
    -- if and only if
    _↔_ : Set → Set → Set
    A ↔ B = (A → B) × (B → A)

  unique-nf : {t t' : Tm a} → (t ≈ t') ↔ (norm t ≡ norm t')
  unique-nf = unique-nf-forth {- 3 -} , unique-nf-back {- from 2 -}

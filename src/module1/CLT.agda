module CLT where

-- stdlib imports

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Unit using (⊤ ; tt)
open import Data.Product
  using (∃ ; Σ ; _×_ ; _,_)
  renaming (proj₁ to π₁ ; proj₂ to π₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂ ; subst)
  renaming (refl to ≡-refl ; trans to ≡-trans ; sym to ≡-sym)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to trans)
open import Relation.Binary.Construct.Closure.Equivalence
  using (EqClosure ; symmetric)
  renaming (isEquivalence to EqClosureIsEquivalence)
open import Data.Sum
  using ()
  renaming (inj₁ to fwd ; inj₂ to bwd)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)

open Star renaming (ε to refl)

infixl 6 _+_
infixr 5 _⇒_

data Ty : Set where
  Nat : Ty
  _⇒_ _+_ : Ty →  Ty → Ty

variable
  a b c : Ty

data Tm : Ty → Set where
  K    : Tm (a ⇒ b ⇒ a)
  S    : Tm ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
  Zero : Tm Nat
  Succ : Tm (Nat ⇒ Nat)
  Rec  : Tm (a ⇒ (Nat ⇒ a ⇒ a) ⇒ Nat ⇒ a)
  App  : Tm (a ⇒ b) → Tm a → Tm b
  Inl  : Tm (a ⇒ a + b)
  Inr  : Tm (b ⇒ a + b)
  Case : Tm ((a ⇒ c) ⇒ (b ⇒ c) ⇒ (a + b) ⇒ c)

infixl 5 _∙_

_∙_ : Tm (a ⇒ b) → Tm a → Tm b
_∙_ = App

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
em Zero = Zero
em Succ = Succ
em (Succ∙ n) = Succ ∙ em n
em K = K
em (K∙ n) = App K (em n)
em S = S
em (S∙ n) = S ∙ (em n)
em (S∙∙ m n) = S ∙ (em m) ∙ (em n)
em Rec = Rec
em (Rec∙ n) = Rec ∙ (em n)
em (Rec∙∙ m n) = Rec ∙ (em m) ∙ (em n)
em Inl      = Inl
em Inr      = Inr
em (Inl∙ n) = Inl ∙ em n
em (Inr∙ n) = Inr ∙ em n
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

  -- semantic application
  app' : ⟦ a ⇒ b ⟧ → ⟦ a ⟧ → ⟦ b ⟧
  app' (_ , f) x = f x

  -- semantic recursion
  rec' : ⟦ a ⟧ → ⟦ Nat ⇒ a ⇒ a ⟧ → ⟦ Nat ⟧ → ⟦ a ⟧
  rec' b f zero = b
  rec' b f (suc n) = app' (app' f n) (rec' b f n)

  case' : ⟦ a ⇒ c ⟧ → ⟦ b ⇒ c ⟧ → ⟦ a + b ⟧ → ⟦ c ⟧
  case' f g (inj₁ x) = app' f x
  case' f g (inj₂ y) = app' g y

  -- interpretation of terms
  eval : Tm a → ⟦ a ⟧
  eval K    = K , λ x → (K∙ (reify x)) , λ _ → x
  eval S    = S , λ g →
    S∙ (reify g) , λ f →
      S∙∙ (reify g) (reify f) , λ x →
        app' (app' g x) (app' f x)
  eval Zero = zero
  eval Succ = Succ , suc
  eval Rec  = Rec , λ b →
    Rec∙ (reify b) , λ f  →
      Rec∙∙ (reify b) (reify f) , λ n →
        rec' b f n
  eval (App t u) = app' (eval t) (eval u)
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
      → App t u ⟶* App t' u'
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
    = cong (λ x → app' x _) (sound-red p)
  sound-red (app2 {t = t} p)
    = cong (λ x → app' (eval t) x) (sound-red p)
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

  -- reify from model into terms (not just normal forms)
  reifyt : ⟦ a ⟧ → Tm a
  reifyt v = em (reify v)

  -- a "submodel" (called glued model) equipped with a proof
  -- that reify is homomorphic on the reduction relation _⟶*_
  -- Note: this submodel acts as *necessary* technical device
  -- to prove consistency (see below)
  Gl : ⟦ a ⟧ → Set
  Gl {Nat}   n = ⊤
  Gl {a ⇒ b} f = ∀ (x : ⟦ a ⟧) → Gl x
    → (reifyt f ∙ reifyt x ⟶* reifyt (app' f x))
    × Gl (app' f x)
  Gl {a + b} (inj₁ x) = Gl x
  Gl {a + b} (inj₂ y) = Gl y

  -- application for glued values
  appg : {f : ⟦ a ⇒ b ⟧} {x : ⟦ a ⟧}
    → Gl f → Gl x
    → Gl (app' f x)
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

  -- homomorphism properties of reify

  homReify-app : {f : ⟦ a ⇒ b ⟧} {x : ⟦ a ⟧}
    → Gl f → Gl x
    → reifyt f ∙ reifyt x ⟶* reifyt (app' f x)
  homReify-app fg xg = π₁ (fg _ xg)

  homReify-rec : {x : ⟦ a ⟧} {f : ⟦ Nat ⇒ a ⇒ a ⟧ } {n : ⟦ Nat ⟧}
      → Gl x → Gl f → Gl n
      → reifyt (app' (app' (eval Rec) x) f) ∙ reifyt n
      ⟶* reifyt (rec' x f n)
  homReify-rec {n = zero}  xg fg ng = lift rec0
  homReify-rec {x = x} {f} {n = suc n} xg fg ng =
        recs ◅ trans
          (app* (homReify-app fg ng) (homReify-rec {n = n} xg fg _))
          (homReify-app (appg fg _) (recg {n = n} xg fg _))

  open import Function

  -- interpretation of terms in the glued model
  -- Note: main challenge here is to provide a proof
  -- object that reify is a homomorphism in each case
  gl : (t : Tm a) →  Gl (eval t)
  gl K x xg    = refl , λ x _ → (lift redk) , xg
  gl Zero      = tt
  gl Succ      = λ x _ → refl , tt
  gl (App t u) = π₂ (gl t _ (gl u))
  gl S g gg    = refl , λ f fg →
    refl , λ x xg →
         reds ◅ trans
           (app* (homReify-app gg xg) (homReify-app fg xg))
           (homReify-app (appg gg xg) (appg fg xg))
        , appg (appg gg xg) (appg fg xg)
  gl Rec x xg   = refl , (λ f fg →
    refl , λ n ng →
      homReify-rec {n = n} xg fg ng , (recg {n = n} xg fg ng))
  gl Inl x xg = refl , xg
  gl Inr x xg = refl , xg
  gl (Case) f fg = refl , λ g gg →
    refl , λ s sg → {!!} , caseg {s = s} fg gg sg

  -- normalization is consistent with reduction (_⟶*_)
  -- or, loosely speaking, `norm` transforms by reduction
  consistent-red* : (t : Tm a) → t ⟶* em (norm t)
  consistent-red* K = refl
  consistent-red* S = refl
  consistent-red* Zero = refl
  consistent-red* Succ = refl
  consistent-red* Rec = refl
  consistent-red* (App t u) = trans
    (app* (consistent-red* t) (consistent-red* u))
    (homReify-app (gl t) (gl u))
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

module Decidability where

  open import Relation.Nullary using (Dec ; yes ; no)

  -- syntactic equality of types is decidable
  ≡-ty-dec : Dec (a ≡ b)
  ≡-ty-dec {Nat} {Nat} = yes ≡-refl
  ≡-ty-dec {Nat} {b ⇒ b₁} = no (λ ())
  ≡-ty-dec {a ⇒ a₁} {Nat} = no (λ ())
  ≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} with ≡-ty-dec {a} {b} | ≡-ty-dec {a₁} {b₁}
  ≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | yes p | yes q = yes (cong₂ _⇒_ p q)
  ≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | yes p | no ¬q = no (λ { ≡-refl → ¬q ≡-refl})
  ≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | no ¬p | yes q = no (λ { ≡-refl → ¬p ≡-refl})
  ≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | no ¬p | no ¬q = no λ { ≡-refl → ¬q ≡-refl}
  ≡-ty-dec {Nat} {b + b₁} = no (λ ())
  ≡-ty-dec {a ⇒ a₁} {b + b₁} = no (λ ())
  ≡-ty-dec {a + a₁} {Nat} = no (λ ())
  ≡-ty-dec {a + a₁} {b ⇒ b₁} = no (λ ())
  ≡-ty-dec {a + a₁} {b + b₁} with ≡-ty-dec {a} {b} | ≡-ty-dec {a₁} {b₁}
  ≡-ty-dec {a + a₁} {b + b₁} | yes p | yes q = yes (cong₂ _+_ p q)
  ≡-ty-dec {a + a₁} {b + b₁} | yes p | no ¬q = no (λ { ≡-refl → ¬q ≡-refl})
  ≡-ty-dec {a + a₁} {b + b₁} | no ¬p | yes q = no (λ { ≡-refl → ¬p ≡-refl})
  ≡-ty-dec {a + a₁} {b + b₁} | no ¬p | no ¬q = no (λ { ≡-refl → ¬q ≡-refl})

  -- syntactic equality of normal forms is decidable
  ≡-nf-dec : (n n' : Nf a) → Dec (n ≡ n')
  ≡-nf-dec Zero Zero = yes ≡-refl
  ≡-nf-dec Zero (Succ∙ n') = no (λ ())
  ≡-nf-dec Succ Succ = yes ≡-refl
  ≡-nf-dec Succ (K∙ n') = no (λ ())
  ≡-nf-dec Succ (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec Succ (Rec∙∙ n' n'') = no (λ ())
  ≡-nf-dec (Succ∙ n) Zero = no (λ ())
  ≡-nf-dec (Succ∙ n) (Succ∙ n') with (≡-nf-dec n n')
  ≡-nf-dec (Succ∙ n) (Succ∙ n') | yes p = yes (cong Succ∙ p)
  ≡-nf-dec (Succ∙ n) (Succ∙ n') | no ¬p = no λ { ≡-refl → ¬p ≡-refl}
  ≡-nf-dec K K = yes ≡-refl
  ≡-nf-dec K (K∙ n') = no (λ ())
  ≡-nf-dec K (S∙ n') = no (λ ())
  ≡-nf-dec K (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec K (Rec∙∙ n' n'') = no (λ ())
  ≡-nf-dec (K∙ n) Succ = no (λ ())
  ≡-nf-dec (K∙ n) K = no (λ ())
  ≡-nf-dec (K∙ n) (K∙ n') with (≡-nf-dec n n')
  ≡-nf-dec (K∙ n) (K∙ n') | yes p = yes (cong K∙ p )
  ≡-nf-dec (K∙ n) (K∙ n') | no ¬p = no λ { ≡-refl → ¬p ≡-refl }
  ≡-nf-dec (K∙ n) S = no (λ ())
  ≡-nf-dec (K∙ n) (S∙ n') = no (λ ())
  ≡-nf-dec (K∙ n) (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec (K∙ n) Rec = no (λ ())
  ≡-nf-dec (K∙ n) (Rec∙ n') = no (λ ())
  ≡-nf-dec (K∙ n) (Rec∙∙ n' n'') = no (λ ())
  ≡-nf-dec S (K∙ n') = no (λ ())
  ≡-nf-dec S S = yes ≡-refl
  ≡-nf-dec S (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec (S∙ n) K = no (λ ())
  ≡-nf-dec (S∙ n) (K∙ n') = no (λ ())
  ≡-nf-dec (S∙ n) (S∙ n') with (≡-nf-dec n n')
  ≡-nf-dec (S∙ n) (S∙ n') | yes p = yes (cong S∙ p )
  ≡-nf-dec (S∙ n) (S∙ n') | no ¬p = no λ {  ≡-refl → ¬p ≡-refl }
  ≡-nf-dec (S∙ n) (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec (S∙ n) (Rec∙ n') = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) Succ = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) K = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) (K∙ n') = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) S = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) (S∙ n') = no (λ ())
  ≡-nf-dec (S∙∙ {b = b} n m) (S∙∙ {b = b'} n' m') with ≡-ty-dec {b} {b'}
  ... | no ¬p = no λ { ≡-refl → ¬p ≡-refl }
  ... | yes ≡-refl with (≡-nf-dec n n') | (≡-nf-dec m m')
  ... | yes q | yes r = yes (cong₂ S∙∙ q r)
  ... | yes q | no ¬r = no λ { ≡-refl → ¬r ≡-refl }
  ... | no ¬q | r = no λ { ≡-refl → ¬q ≡-refl }
  ≡-nf-dec (S∙∙ n n₁) Rec = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) (Rec∙ n') = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) (Rec∙∙ n' n'') = no (λ ())
  ≡-nf-dec Rec (K∙ n') = no (λ ())
  ≡-nf-dec Rec (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec Rec Rec = yes ≡-refl
  ≡-nf-dec Rec (Rec∙∙ n' n'') = no (λ ())
  ≡-nf-dec (Rec∙ n) (K∙ n') = no (λ ())
  ≡-nf-dec (Rec∙ n) (S∙ n') = no (λ ())
  ≡-nf-dec (Rec∙ n) (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec (Rec∙ n) (Rec∙ n') with (≡-nf-dec n n')
  ≡-nf-dec (Rec∙ n) (Rec∙ n') | yes p = yes (cong Rec∙ p)
  ≡-nf-dec (Rec∙ n) (Rec∙ n') | no ¬p = no λ { ≡-refl → ¬p ≡-refl }
  ≡-nf-dec (Rec∙∙ n n₁) Succ = no (λ ())
  ≡-nf-dec (Rec∙∙ n n₁) K = no (λ ())
  ≡-nf-dec (Rec∙∙ n n₁) (K∙ n') = no (λ ())
  ≡-nf-dec (Rec∙∙ n n₁) (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec (Rec∙∙ n n₁) Rec = no (λ ())
  ≡-nf-dec (Rec∙∙ n m) (Rec∙∙ n' m') with (≡-nf-dec n n') | (≡-nf-dec m m')
  ≡-nf-dec (Rec∙∙ n m) (Rec∙∙ n' m') | yes p | yes q = yes (cong₂ Rec∙∙ p q)
  ≡-nf-dec (Rec∙∙ n m) (Rec∙∙ n' m') | yes p | no ¬p = no λ { ≡-refl → ¬p ≡-refl }
  ≡-nf-dec (Rec∙∙ n m) (Rec∙∙ n' m') | no ¬p | _     = no λ { ≡-refl → ¬p ≡-refl }
  ≡-nf-dec K (Case∙∙ n' n'') = no (λ ())
  ≡-nf-dec (K∙ n) Inl = no (λ ())
  ≡-nf-dec (K∙ n) Inr = no (λ ())
  ≡-nf-dec (K∙ n) Case = no (λ ())
  ≡-nf-dec (K∙ n) (Case∙ n') = no (λ ())
  ≡-nf-dec (K∙ n) (Case∙∙ n' n'') = no (λ ())
  ≡-nf-dec (S∙ n) Case = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) Inl = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) Inr = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) Case = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) (Case∙ n') = no (λ ())
  ≡-nf-dec (S∙∙ n n₁) (Case∙∙ n' n'') = no (λ ())
  ≡-nf-dec Rec (Case∙∙ n' n'') = no (λ ())
  ≡-nf-dec (Rec∙∙ n n₁) Inl = no (λ ())
  ≡-nf-dec (Rec∙∙ n n₁) Inr = no (λ ())
  ≡-nf-dec Inl (K∙ n') = no (λ ())
  ≡-nf-dec Inl (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec Inl (Rec∙∙ n' n'') = no (λ ())
  ≡-nf-dec Inl Inl = yes ≡-refl
  ≡-nf-dec Inl Inr = no (λ ())
  ≡-nf-dec Inl (Case∙∙ n' n'') = no (λ ())
  ≡-nf-dec Inr (K∙ n') = no (λ ())
  ≡-nf-dec Inr (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec Inr (Rec∙∙ n' n'') = no (λ ())
  ≡-nf-dec Inr Inl = no (λ ())
  ≡-nf-dec Inr Inr = yes ≡-refl
  ≡-nf-dec Inr (Case∙∙ n' n'') = no (λ ())
  ≡-nf-dec (Inl∙ n) (Inl∙ n') = {!!}
  ≡-nf-dec (Inl∙ n) (Inr∙ n') = no (λ ())
  ≡-nf-dec (Inr∙ n) (Inl∙ n') = no (λ ())
  ≡-nf-dec (Inr∙ n) (Inr∙ n') = {!!}
  ≡-nf-dec Case (K∙ n') = no (λ ())
  ≡-nf-dec Case (S∙ n') = no (λ ())
  ≡-nf-dec Case (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec Case Case = yes ≡-refl
  ≡-nf-dec (Case∙ n) (K∙ n') = no (λ ())
  ≡-nf-dec (Case∙ n) (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec (Case∙ n) (Case∙ n') = {!!}
  ≡-nf-dec (Case∙∙ n n₁) K = no (λ ())
  ≡-nf-dec (Case∙∙ n n₁) (K∙ n') = no (λ ())
  ≡-nf-dec (Case∙∙ n n₁) (S∙∙ n' n'') = no (λ ())
  ≡-nf-dec (Case∙∙ n n₁) Rec = no (λ ())
  ≡-nf-dec (Case∙∙ n n₁) Inl = no (λ ())
  ≡-nf-dec (Case∙∙ n n₁) Inr = no (λ ())
  ≡-nf-dec (Case∙∙ n n₁) (Case∙∙ n' n'') = {!!}

  -- convertibility of terms is decidable
  ≈-tm-dec : (t t' : Tm a) → Dec (t ≈ t')
  ≈-tm-dec t t' with (≡-nf-dec (norm t) (norm t'))
  ≈-tm-dec t t' | yes p = yes (unique-nf-back p)
  ≈-tm-dec t t' | no ¬p = no (λ { q → ¬p (unique-nf-forth q) })

----------------------
-- Weak normalization
----------------------

module WeakNorm where

  DoesntReduce : Tm a → Set
  DoesntReduce {a} t = {t' : Tm a} → ¬ (t ⟶ t')

  WeakNorm : Tm a → Set
  WeakNorm t = ∃ λ t' → (t ⟶* t') × DoesntReduce t'

  -- a normal form doesn't reduce further
  nfDoesntReduce : (n : Nf a) → DoesntReduce (em n)
  nfDoesntReduce Zero ()
  nfDoesntReduce Succ ()
  nfDoesntReduce (Succ∙ n) (app2 p) = nfDoesntReduce n p
  nfDoesntReduce K ()
  nfDoesntReduce (K∙ n) (app2 p) = nfDoesntReduce n p
  nfDoesntReduce S ()
  nfDoesntReduce (S∙ n) (app2 p) = nfDoesntReduce n p
  nfDoesntReduce (S∙∙ m n) (app1 (app2 p)) = nfDoesntReduce m p
  nfDoesntReduce (S∙∙ m n) (app2 p) = nfDoesntReduce n p
  nfDoesntReduce Rec ()
  nfDoesntReduce (Rec∙ n) (app2 p) = nfDoesntReduce n p
  nfDoesntReduce (Rec∙∙ m n) (app1 (app2 p)) = nfDoesntReduce m p
  nfDoesntReduce (Rec∙∙ m n) (app2 p) = nfDoesntReduce n p
  nfDoesntReduce (S∙∙ m n) (app1 p) = nfDoesntReduce (S∙ m) p
  nfDoesntReduce (Rec∙∙ m n) (app1 p) = nfDoesntReduce (Rec∙ m) p
  nfDoesntReduce Inl ()
  nfDoesntReduce Inr ()
  nfDoesntReduce (Inl∙ n) (app2 p) = nfDoesntReduce n p
  nfDoesntReduce (Inl∙ n) (inl p) = nfDoesntReduce n p
  nfDoesntReduce (Inr∙ n) (app2 p) = nfDoesntReduce n p
  nfDoesntReduce (Inr∙ n) (inr p) = nfDoesntReduce n p
  nfDoesntReduce Case ()
  nfDoesntReduce (Case∙ n) (app2 p) = nfDoesntReduce n p
  nfDoesntReduce (Case∙∙ m n) (app1 p) = nfDoesntReduce (Case∙ m) p
  nfDoesntReduce (Case∙∙ m n) (app2 p) = nfDoesntReduce n p

  weakNorm : ∀ (t : Tm a) → WeakNorm t
  weakNorm t = em (norm t) , consistent-red* _ , nfDoesntReduce _

  -- church-rosser (diamond) property
  church-rosser : {t u u' : Tm a}
    → t ⟶* u
    → t ⟶* u'
    → ∃ λ v → (u ⟶* v) × (u' ⟶* v)
  church-rosser {u = u} {u'} p q
    = em (norm u)
    , consistent-red* u
    , subst (λ n →  u' ⟶* em n) (≡-sym unique-norm) (consistent-red* u')
    where
    -- u ≈ u' since they are both residuals from t
    u≈u' : u ≈ u'
    u≈u' = trans (sym (⟶*→≈ p)) (⟶*→≈ q)
    -- u and u' normalize to a unique v
    unique-norm : norm u ≡ norm u'
    unique-norm = unique-nf-forth u≈u'


-- Random experiments below, might not make any sense

module _ where

  app : {t t' : Tm (a ⇒ b)} {u u' : Tm a}
    → t ≈ t'
    → u ≈ u'
    → App t u ≈ App t' u'
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

-----------------------------------------------
-- Proving consistency using logical relations
-----------------------------------------------

module _ where

  -- logical relations for proving consistency
  R : Tm a → ⟦ a ⟧ → Set
  R {Nat}   n m = n ⟶* reifyt m
  R {a ⇒ b} t f = t ⟶* reifyt f
    × ({u : Tm a} {u' : ⟦ a ⟧}
    → R u u'
    → R (t ∙ u) (app' f u'))
  R {a + b} t (inj₁ x)
    = ∃ (λ u → R u x × t ⟶* Inl ∙ reifyt x )
  R {a + b} t (inj₂ y)
    = ∃ (λ u → R u y × t ⟶* Inr ∙ reifyt y )

  -- R implies reduction by _⟶*_ (by reifying the value on right)
  -- (the whole purpose of R!)
  R-reduces : {t : Tm a} {x : ⟦ a ⟧}
    → R t x
    → t ⟶* reifyt x
  R-reduces {Nat}   p       = p
  R-reduces {a ⇒ b} (p , _) = p
  R-reduces {a + b} {x = inj₁ _} (_ , _ , p) = p
  R-reduces {a + b} {x = inj₂ _} (_ , _ , p) = p

  -- Note: Due to `R-reduces`, we may simply
  -- say "t reduces to v" for `R t v`
  -- instead of "t is related by R to v"

  -- invariance lemma
  R-resp-≈ : {f g : Tm a} {x : ⟦ a ⟧}
    → g ⟶* f
    → R f x
    → R g x
  R-resp-≈ {Nat} g≈f rfx
    = trans g≈f rfx
  R-resp-≈ {_ ⇒ _} p   (q , r)
    = trans p q , λ y → R-resp-≈ (app* p refl) (r y)
  R-resp-≈ {_ + _} {x = inj₁ _} p (u , q , r)
    = u , q , trans p r
  R-resp-≈ {_ + _} {x = inj₂ _} p (u , q , r)
    = u , q , trans p r

  -- syntactic application reduces to semantic application
  R-app : {t : Tm (a ⇒ b)} {f : ⟦ a ⇒ b ⟧}
    {u : Tm a} {x : ⟦ a ⟧}
    → R t f
    → R u x
    → R (t ∙ u) (app' f x)
  R-app (p , q) r = q r

  -- syntactic recursion reduces to semantic recursion
  R-rec : {e : Tm a} {v : ⟦ a ⟧}
    {t : Tm (Nat ⇒ a ⇒ a)} {f : ⟦ Nat ⇒ a ⇒ a ⟧}
    {n : Tm Nat} {m : ⟦ Nat ⟧}
    → R e v
    → R t f
    → R n m
    → R (Rec ∙ e ∙ t  ∙ n) (rec' v f m)
  R-rec {m = zero} p q r
    = R-resp-≈ (trans (app* refl r) (lift rec0)) p
  R-rec {m = suc m} p q r
    = R-resp-≈
        (trans (app* refl r) (lift recs))
        (R-app (R-app q refl) (R-rec {m = m} p q refl))

  -- fundamental theorem of R
  -- i.e., a term reduces to its interpretation
  fund : (t : Tm a) → R t (eval t)
  fund K = refl , λ p →
    (app* refl (R-reduces p)) , λ q →
      R-resp-≈ (lift redk) p
  fund S = refl , λ p →
    app* refl (R-reduces p) , λ q →
      (app* (app* refl (R-reduces p)) (R-reduces q)) , λ r →
        R-resp-≈ (lift reds) (R-app (R-app p r) (R-app q r))
  fund Zero = refl
  fund Succ
    = refl , λ p → (app* refl p)
  fund Rec
    = refl , λ p →
      (app* refl (R-reduces p)) , λ q →
        (app* (app* refl (R-reduces p)) (R-reduces q)) , λ {_} {n} r →
          R-rec {m = n} p q r
  fund (App t u) = R-app (fund t) (fund u)
  fund Inl = refl , λ p →
    _ , p , app* refl (R-reduces p)
  fund Inr = refl , λ p →
    _ , p , app* refl (R-reduces p)
  fund Case = {!!}

  -- proof of consistency by R

  consistency-red*-by-R : (t : Tm a) → t ⟶* em (norm t)
  consistency-red*-by-R t = R-reduces (fund t)

  consistency-by-R : (t : Tm a) → t ≈ em (norm t)
  consistency-by-R t = ⟶*→≈ (consistency-red*-by-R t)

---------------------------------------
-- Abstract specification of the story
---------------------------------------

module _ where

  ⟦_⟧ᵍ : Ty → Set
  ⟦ a ⟧ᵍ = Σ ⟦ a ⟧ Gl

  evalG : Tm a → ⟦ a ⟧ᵍ
  evalG {a} t = (eval t) , gl t

  _≡ᵍ_ : (x y : ⟦ a ⟧ᵍ) → Set
  _≡ᵍ_ x y = π₁ x ≡ π₁ y

  soundG : {t t' : Tm a} → t ≈ t' → (evalG t) ≡ᵍ evalG t'
  soundG p = sound p

  reifyG : ⟦ a ⟧ᵍ → Tm a
  reifyG v = reifyt (π₁ v)

  normG : Tm a → Tm a
  normG t = reifyG (evalG t)

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

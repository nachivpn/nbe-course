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

infixr 5 _⇒_

data Ty : Set where
  Nat : Ty
  _⇒_ : Ty →  Ty → Ty

variable
  a b c : Ty

data Tm : Ty → Set where
  K    : Tm (a ⇒ b ⇒ a)
  S    : Tm ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
  Zero : Tm Nat
  Succ : Tm (Nat ⇒ Nat)
  Rec  : Tm (a ⇒ (Nat ⇒ a ⇒ a) ⇒ Nat ⇒ a)
  App  : Tm (a ⇒ b) → Tm a → Tm b

infixl 5 _∙_

_∙_ : Tm (a ⇒ b) → Tm a → Tm b
_∙_ = App

infix 3 _≈_

data _≈_ : Tm a → Tm a → Set where
  refl  : {t : Tm a}
    → t ≈ t
  sym  : {t t' : Tm a}
    → t ≈ t' → t' ≈ t
  trans : {t₁ t₂ t₃ : Tm a}
    → t₁ ≈ t₂ → t₂ ≈ t₃ → t₁ ≈ t₃
  app   : {t t' : Tm (a ⇒ b)} {u u' : Tm a}
    → t ≈ t'
    → u ≈ u'
    → App t u ≈ App t' u'
  redk : {e : Tm a} {e' : Tm b}
    → (K ∙ e ∙ e') ≈ e
  reds : {g : Tm (a ⇒ b ⇒ c)} {f : Tm (a ⇒ b)} {e : Tm a}
    → (S ∙ g ∙ f ∙ e) ≈ (g ∙ e ∙ (f ∙ e))
  rec0 : {e : Tm a} {f : Tm (Nat ⇒ a ⇒ a)}
    → (Rec ∙ e ∙ f ∙ Zero) ≈ e
  recs : {e : Tm a} {f : Tm (Nat ⇒ a ⇒ a)} {n : Tm Nat}
    → (Rec ∙ e ∙ f ∙ (Succ ∙ n)) ≈ (f ∙ n ∙ (Rec ∙ e ∙ f ∙ n))

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

-- embed normal forms to terms
e : Nf a → Tm a
e Zero = Zero
e Succ = Succ
e (Succ∙ n) = Succ ∙ e n
e K = K
e (K∙ n) = App K (e n)
e S = S
e (S∙ n) = S ∙ (e n)
e (S∙∙ m n) = S ∙ (e m) ∙ (e n)
e Rec = Rec
e (Rec∙ n) = Rec ∙ (e n)
e (Rec∙∙ m n) = Rec ∙ (e m) ∙ (e n)

module SetoidUtil where

  open import Relation.Binary
    using (Setoid ; IsEquivalence)

  open Setoid
    renaming (_≈_ to _≈ₑ_)
    using (Carrier ; isEquivalence)

  Tms : (a : Ty) → Setoid _ _
  Tms a .Carrier = Tm a
  Tms a ._≈ₑ_     = _≈_
  Tms a .isEquivalence .IsEquivalence.refl  = refl
  Tms a .isEquivalence .IsEquivalence.sym   = sym
  Tms a .isEquivalence .IsEquivalence.trans = trans

  open import Relation.Binary.SetoidReasoning public

open  SetoidUtil

⟦_⟧ : Ty → Set
⟦  Nat  ⟧ = ℕ
⟦ a ⇒ b ⟧ = Nf (a ⇒ b) × (⟦ a ⟧ → ⟦ b ⟧)

reify : ⟦ a ⟧ → Nf a
reify {Nat}   zero    = Zero
reify {Nat}   (suc x) = Succ∙ (reify x)
reify {a ⇒ b} (t , _) = t

app' : ⟦ a ⇒ b ⟧ → ⟦ a ⟧ → ⟦ b ⟧
app' (_ , f) x = f x

rec' : ⟦ a ⟧ → ⟦ Nat ⇒ a ⇒ a ⟧ → ⟦ Nat ⟧ → ⟦ a ⟧
rec' b f zero = b
rec' b f (suc n) = app' (app' f n) (rec' b f n)

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

norm : Tm a → Nf a
norm t = reify (eval t)

-- soundess of interpretation, i.e., ⟦_⟧ and eval
sound : {t t' : Tm a} → t ≈ t' → eval t ≡ eval t'
sound refl        = ≡-refl
sound (sym p)     = ≡-sym (sound p)
sound (trans p q) = ≡-trans (sound p) (sound q)
sound (app p q)   = cong₂ app' (sound p) (sound q)
sound redk        = ≡-refl
sound reds        = ≡-refl
sound rec0        = ≡-refl
sound recs        = ≡-refl

unique-nf-forth : {t t' : Tm a} → t ≈ t' → norm t ≡ norm t'
unique-nf-forth p = cong reify (sound p)

open import Relation.Nullary using (Dec ; yes ; no)

reifyt : ⟦ a ⟧ → Tm a
reifyt v = e (reify v)

Gl : ⟦ a ⟧ → Set
Gl {Nat}   n = ⊤
Gl {a ⇒ b} f = ∀ (x : ⟦ a ⟧) → Gl x
  → (reifyt f ∙ reifyt x ≈ reifyt (app' f x))
  × Gl (app' f x)

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

-- homomorphism properties of reify

homReify-app : {f : ⟦ a ⇒ b ⟧} {x : ⟦ a ⟧}
  → Gl f → Gl x
  → reifyt f ∙ reifyt x ≈ reifyt (app' f x)
homReify-app fg xg = π₁ (fg _ xg)

homReify-rec : {x : ⟦ a ⟧} {f : ⟦ Nat ⇒ a ⇒ a ⟧ } {n : ⟦ Nat ⟧}
  → Gl x → Gl f → Gl n
  → reifyt (app' (app' (eval Rec) x) f) ∙ reifyt n
  ≈ reifyt (rec' x f n)
homReify-rec {n = zero}  xg fg ng = rec0
homReify-rec {x = x} {f} {n = suc n} xg fg ng =
  begin⟨ Tms _ ⟩
    reifyt (app' (app' (eval Rec) x) f) ∙ reifyt (suc n)
                ≈⟨ refl ⟩
    Rec ∙ (reifyt x) ∙ (reifyt f) ∙ (Succ ∙ (reifyt n))
                ≈⟨ recs ⟩
    (reifyt f ∙ reifyt n) ∙ (Rec ∙ reifyt x ∙ reifyt f ∙ reifyt n)
                ≈⟨  app (homReify-app fg ng) refl ⟩
    reifyt (app' f n) ∙ (reifyt (app' (app' (eval Rec) x) f) ∙ reifyt n)
                ≈⟨ app refl (homReify-rec {n = n} xg fg _) ⟩
    reifyt (app' f n) ∙ reifyt (rec' x f n)
                ≈⟨ homReify-app (appg fg _) (recg {n = n} xg fg _)⟩
    reifyt (rec' x f (suc n)) ∎

open import Function

-- evaluation produces a glued valus
gl : (t : Tm a) →  Gl (eval t)
gl K x xg    = refl , λ x _ → redk , xg
gl Zero      = tt
gl Succ      = λ x _ → refl , tt
gl (App t u) = π₂ (gl t _ (gl u))

gl S g gg    = refl , λ f fg → refl , λ x xg →
  (begin⟨ Tms _ ⟩
    reifyt (app' (app' (eval S) g) f) ∙ reifyt x
           ≈⟨ refl ⟩
    S  ∙ reifyt g ∙ reifyt f ∙ reifyt x
           ≈⟨ reds ⟩
    (reifyt g ∙ reifyt x) ∙ (reifyt f ∙ reifyt x)
           ≈⟨ app (homReify-app gg xg) (homReify-app fg xg) ⟩
    reifyt (app' g x) ∙ reifyt (app' f x)
           ≈⟨ homReify-app (appg gg xg) (appg fg xg) ⟩
    reifyt (app' (app' g x) (app' f x))
           ≈⟨ refl ⟩
    reifyt (app' (app' (app' (eval S) g) f) x)   ∎ )
  , appg (appg gg xg) (appg fg xg)

gl Rec x xg   = refl , (λ f fg → refl , λ n ng →
  (begin⟨ Tms _ ⟩
    reifyt (app' (app' (eval Rec) x) f) ∙ reifyt n   ≈⟨ homReify-rec {n = n} xg fg ng ⟩
    reifyt (rec' x f n)                             ≈⟨ refl ⟩
    reifyt (app' (app' (app' (eval Rec) x) f) n)    ∎)
  , recg {n = n} xg fg ng)

-- normalization is consistent w.r.t. ≈
consistent : (t : Tm a) → t ≈ e (norm t)
consistent K         = refl
consistent S         = refl
consistent Zero      = refl
consistent Succ      = refl
consistent Rec       = refl
consistent (App t u) = trans
  (app (consistent t) (consistent u))
  (homReify-app (gl t) (gl u))

≡→≈ : {t t' : Tm a} → t ≡ t' → t ≈ t'
≡→≈ ≡-refl = refl

unique-nf-back : {t t' : Tm a} → norm t ≡ norm t' → t ≈ t'
unique-nf-back {t = t} {t'} p =
  trans (consistent t) (trans (≡→≈ (cong e p)) (sym (consistent t')))

-- completeness of interpretation, i.e., ⟦_⟧ and eval
complete : {t t' : Tm a} → eval t ≡ eval t' → t ≈ t'
complete p = unique-nf-back (cong reify p)

≡-ty-dec : Dec (a ≡ b)
≡-ty-dec {Nat} {Nat} = yes ≡-refl
≡-ty-dec {Nat} {b ⇒ b₁} = no (λ ())
≡-ty-dec {a ⇒ a₁} {Nat} = no (λ ())
≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} with ≡-ty-dec {a} {b} | ≡-ty-dec {a₁} {b₁}
≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | yes p | yes q = yes (cong₂ _⇒_ p q)
≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | yes p | no ¬q = no (λ { ≡-refl → ¬q ≡-refl})
≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | no ¬p | yes q = no (λ { ≡-refl → ¬p ≡-refl})
≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | no ¬p | no ¬q = no λ { ≡-refl → ¬q ≡-refl}

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

≈-tm-dec : (t t' : Tm a) → Dec (t ≈ t')
≈-tm-dec t t' with (≡-nf-dec (norm t) (norm t'))
≈-tm-dec t t' | yes p = yes (unique-nf-back p)
≈-tm-dec t t' | no ¬p = no (λ { q → ¬p (unique-nf-forth q) })

-- NOTES:
-- * It looks like we get completeness from a stronger property (i.e., consistency)

----------------------
-- Weak normalization
----------------------

module _ where

  open import Relation.Binary.Construct.Closure.ReflexiveTransitive
    using (Star ; _◅◅_)
  open Star renaming (ε to refl)

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
      → App t u ⟶ App t' u
    app2  : {t : Tm (a ⇒ b)} {u u' : Tm a}
      → u ⟶ u'
      → App t u ⟶ App t u'

  infix 3 _⟶*_

  _⟶*_ : Tm a → Tm a → Set
  _⟶*_ = Star (_⟶_)

  DoesntReduce : Tm a → Set
  DoesntReduce {a} t = {t' : Tm a} → ¬ (t ⟶ t')

  WeakNorm : Tm a → Set
  WeakNorm t = ∃ λ t' → (t ⟶* t') × DoesntReduce t'

  nfDoesntReduce : (n : Nf a) → DoesntReduce (e n)
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

  lift : {e e' : Tm a}
    → e ⟶ e'
    → e ⟶* e'
  lift p =  p ◅ refl

  app*  : {t t' : Tm (a ⇒ b)} {u u' : Tm a}
      → t ⟶* t'
      → u ⟶* u'
      → App t u ⟶* App t' u'
  app* refl    refl    = refl
  app* refl    (x ◅ q) = (app2 x) ◅ (app* refl q)
  app* (x ◅ p) q       = (app1 x) ◅ (app* p q)

  Glr : ⟦ a ⟧ → Set
  Glr {Nat}   n = ⊤
  Glr {a ⇒ b} f = ∀ (x : ⟦ a ⟧) → Glr x
    → (reifyt f ∙ reifyt x) ⟶* reifyt (app' f x)
    × Glr (app' f x)

  -- application for glued values
  appgr : {f : ⟦ a ⇒ b ⟧} {x : ⟦ a ⟧}
    → Glr f → Glr x
    → Glr (app' f x)
  appgr fg xg = π₂ (fg _ xg)

  -- primitive recursion for glued values
  recgr : {x : ⟦ a ⟧} {f :  ⟦ Nat ⇒ a ⇒ a ⟧ } {n : ⟦ Nat ⟧}
    → Glr x → Glr f → Glr n → Glr (rec' x f n)
  recgr {n = zero}  xg fg ng = xg
  recgr {n = suc n} xg fg ng =
    appgr (appgr fg ng) (recgr {n = n} xg fg ng)

  homReify-appr : {f : ⟦ a ⇒ b ⟧} {x : ⟦ a ⟧}
    → Glr f → Glr x
    → reifyt f ∙ reifyt x ⟶* reifyt (app' f x)
  homReify-appr fg xg = π₁ (fg _ xg)

  homReify-recr : {x : ⟦ a ⟧} {f : ⟦ Nat ⇒ a ⇒ a ⟧ } {n : ⟦ Nat ⟧}
    → Glr x → Glr f → Glr n
    → reifyt (app' (app' (eval Rec) x) f) ∙ reifyt n
    ⟶* reifyt (rec' x f n)
  homReify-recr {n = zero}  xg fg ng = lift rec0
  homReify-recr {x = x} {f} {n = suc n} xg fg ng =
      recs
      ◅  (app* (homReify-appr fg ng) (homReify-recr {n = n} xg fg _))
      ◅◅ (homReify-appr (appgr fg _) (recgr {n = n} xg fg _))

  glr : (t : Tm a) →  Glr (eval t)
  glr K x xg    = refl , λ x _ → (lift redk) , xg
  glr Zero      = tt
  glr Succ      = λ x _ → refl , tt
  glr (App t u) = π₂ (glr t _ (glr u))
  glr S g gg    = refl , λ f fg →
    refl , λ x xg →
         reds
         ◅  (app* (homReify-appr gg xg) (homReify-appr fg xg))
         ◅◅ (homReify-appr (appgr gg xg) (appgr fg xg))
        , appgr (appgr gg xg) (appgr fg xg)
  glr Rec x xg   = refl , (λ f fg →
    refl , λ n ng →
      homReify-recr {n = n} xg fg ng , (recgr {n = n} xg fg ng))

  -- t reduces to the result of `norm`
  reducesToNorm : (t : Tm a) → t ⟶* e (norm t)
  reducesToNorm K = refl
  reducesToNorm S = refl
  reducesToNorm Zero = refl
  reducesToNorm Succ = refl
  reducesToNorm Rec = refl
  reducesToNorm (App t u) =
    app* (reducesToNorm t) (reducesToNorm u)
    ◅◅ (homReify-appr (glr t) (glr u))

  weakNorm : ∀ (t : Tm a) → WeakNorm t
  weakNorm t = e (norm t) , reducesToNorm _ , nfDoesntReduce _

  -- embed reduction relations to ≈

  ⟶→≈ : {t u : Tm a} → t ⟶ u → t ≈ u
  ⟶→≈ redk = redk
  ⟶→≈ reds = reds
  ⟶→≈ rec0 = rec0
  ⟶→≈ recs = recs
  ⟶→≈ (app1 p) = app (⟶→≈ p) refl
  ⟶→≈ (app2 p) = app refl (⟶→≈ p)

  ⟶*→≈ : {t u : Tm a} → t ⟶* u → t ≈ u
  ⟶*→≈ refl = refl
  ⟶*→≈ (x ◅ p) = trans (⟶→≈ x) (⟶*→≈ p)

  -- church-rosser diamond
  church-rosser : {t u u' : Tm a}
    → t ⟶* u
    → t ⟶* u'
    → ∃ λ v → (u ⟶* v) × (u' ⟶* v)
  church-rosser {u = u} {u'} p q
    = e (norm u)
    , reducesToNorm u
    , subst (λ n →  u' ⟶* e n) (≡-sym unique-norm) (reducesToNorm u')
    where
    -- u ≈ u' since they are both residuals from t
    u≈u' : u ≈ u'
    u≈u' = trans (sym (⟶*→≈ p)) (⟶*→≈ q)
    -- u and u' normalize to a unique v
    unique-norm : norm u ≡ norm u'
    unique-norm = unique-nf-forth u≈u'


-- Random experiments below, might not make any sense

-----------------------------------------------
-- Proving consistency using logical relations
-----------------------------------------------

module _ where

  R : Tm a → ⟦ a ⟧ → Set
  R {Nat}   n m = n ≈ reifyt m
  R {a ⇒ b} t f = (t ≈ reifyt f)
    × (∀ (u : Tm a) (u' : ⟦ a ⟧)
    → R u u'
    → R (t ∙ u) (app' f u'))

  R-resp-≈ : {f g : Tm a} {x : ⟦ a ⟧}
    → f ≈ g
    → R f x
    → R g x
  R-resp-≈ {Nat} f≈g rfx = trans (sym f≈g) rfx
  R-resp-≈ {a ⇒ a₁} p (q , r) = trans (sym p) q ,
    λ u u' y → R-resp-≈ (app p refl) (r u u' y)

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

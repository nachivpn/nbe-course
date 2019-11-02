module CLT where

-- stdlib imports

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Unit using (⊤ ; tt)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂)
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

infix 2 _≈_

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

⟦_⟧ : Ty → Set
⟦  Nat  ⟧ = ℕ
⟦ a ⇒ b ⟧ = Tm (a ⇒ b) × (⟦ a ⟧ → ⟦ b ⟧)

reify : ⟦ a ⟧ → Tm a
reify {Nat}   zero    = Zero
reify {Nat}   (suc x) = Succ ∙ reify x
reify {a ⇒ b} (t , _) = t

app' : ⟦ a ⇒ b ⟧ → ⟦ a ⟧ → ⟦ b ⟧
app' (_ , f) x = f x

rec' : ⟦ a ⟧ → (ℕ → ⟦ a ⟧ → ⟦ a ⟧) → ℕ → ⟦ a ⟧
rec' b f zero = b
rec' b f (suc n) = f n (rec' b f n)

eval : Tm a → ⟦ a ⟧
eval K    = K , λ x → (K ∙ reify x) , λ _ → x
eval S    = S , λ { (g , g') →
  (S ∙ g) , λ { (f , f') →
    (S ∙ g ∙ f) , λ x →
      app' (g' x) (f' x) } }
eval Zero = zero
eval Succ = Succ , suc
eval Rec  = Rec , λ b →
  (Rec ∙ reify b) , λ { (f , f')  →
    (Rec ∙ reify b ∙ f) , λ n →
      rec' b (λ x → app' (f' x)) n }
eval (App t u) = app' (eval t) (eval u)

norm : Tm a → Tm a
norm t = reify (eval t)

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

Gl : ⟦ a ⟧ → Set
Gl {Nat}   n = ⊤
Gl {a ⇒ b} f = ∀ (x : ⟦ a ⟧) → Gl x
  → (reify f ∙ reify x ≈ reify (app' f x))
  × Gl (app' f x)

⟦_⟧ᵍ : Ty → Set
⟦ a ⟧ᵍ = Σ ⟦ a ⟧ Gl

reifyIsHom : (fg : ⟦ a ⇒ b ⟧ᵍ) (ug : ⟦ a ⟧ᵍ)
  → let f = proj₁ fg ; u = proj₁ ug in
    reify f ∙ reify u ≈ reify (app' f u)
reifyIsHom (f , p) (u , q) = proj₁ (p u q)

appg : ⟦ a ⇒ b ⟧ᵍ → ⟦ a ⟧ᵍ → ⟦ b ⟧ᵍ
appg ((f , f') , p) (x , q) = (f' x) , proj₂ (p x q)

recg : ⟦ a ⟧ᵍ → ⟦ Nat ⇒ a ⇒ a ⟧ᵍ → ℕ → ⟦ a ⟧ᵍ
recg b f zero = b
recg b f (suc n) = appg (appg f (n , _)) (recg b f n)

gl : (t : Tm a) →  Gl (eval t)
gl K x p = refl , λ y q → redk , p
gl S g p = refl , λ {f q → refl , λ x r →
  -- pfffffttt... need to switch to eq. reasoning
  trans reds
    (trans
      (app
        (proj₁ (p _ r))
        (proj₁ (q _ r)))
      (proj₁ (proj₂ (p x r) (proj₂ f x) (proj₂ (q x r))))) , proj₂
    (appg
      (appg (g , p) (x , r))
      (appg (f , q) (x , r))) }
gl Zero      = tt
gl Succ      = λ x _ → refl , tt
gl Rec x p   = refl , λ f q → refl , λ n _ → {!!}
gl (App t u) = proj₂ (gl t _ (gl u))

evalG : Tm a → ⟦ a ⟧ᵍ
evalG {a} t = (eval t) , gl t

consistent : (t : Tm a) → t ≈ norm t
consistent K         = refl
consistent S         = refl
consistent Zero      = refl
consistent Succ      = refl
consistent Rec       = refl
consistent (App t u) = trans
  (app (consistent t) (consistent u))
  (reifyIsHom (evalG t) (evalG u))

≡→≈ : {t t' : Tm a} → t ≡ t' → t ≈ t'
≡→≈ ≡-refl = refl

unique-nf-back : {t t' : Tm a} → norm t ≡ norm t' → t ≈ t'
unique-nf-back {t = t} {t'} p = trans (consistent t) (trans (≡→≈ p) (sym (consistent t')))

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

≡-tm-dec : (t t' : Tm a) → Dec (t ≡ t')
≡-tm-dec K K = yes ≡-refl
≡-tm-dec K (App t' t'') = no (λ ())
≡-tm-dec S S = yes ≡-refl
≡-tm-dec S (App t' t'') = no (λ ())
≡-tm-dec Zero Zero = yes ≡-refl
≡-tm-dec Zero (App t' t'') = no (λ ())
≡-tm-dec Succ Succ = yes ≡-refl
≡-tm-dec Succ (App t' t'') = no (λ ())
≡-tm-dec Rec Rec = yes ≡-refl
≡-tm-dec Rec (App t' t'') = no (λ ())
≡-tm-dec (App t t₁) K = no (λ ())
≡-tm-dec (App t t₁) S = no (λ ())
≡-tm-dec (App t t₁) Zero = no (λ ())
≡-tm-dec (App t t₁) Succ = no (λ ())
≡-tm-dec (App t t₁) Rec = no (λ ())
≡-tm-dec (App {a} t t₁) (App {b} t' t₁') with ≡-ty-dec {a} {b}
... | no ¬p = no λ { ≡-refl → ¬p ≡-refl }
... | yes ≡-refl with ≡-tm-dec t t' | ≡-tm-dec t₁ t₁'
... | yes ≡-refl | yes ≡-refl = yes ≡-refl
... | yes ≡-refl | no ¬q = no λ { ≡-refl → ¬q ≡-refl}
... | no ¬p      | yes q = no λ { ≡-refl → ¬p ≡-refl}
... | no ¬p      | no ¬q = no λ { ≡-refl → ¬p ≡-refl}

≈-tm-dec : (t t' : Tm a) → Dec (t ≈ t')
≈-tm-dec t t' with (≡-tm-dec (norm t) (norm t'))
≈-tm-dec t t' | yes p = yes (unique-nf-back p)
≈-tm-dec t t' | no ¬p = no (λ { q → ¬p (unique-nf-forth q) })


-- Random experiments below, might not make any sense

-----------------------------------------------
-- Proving consistency using logical relations
-----------------------------------------------

module _ where

  R : Tm a → ⟦ a ⟧ → Set
  R {Nat}   n m = n ≈ reify m
  R {a ⇒ b} t f = (t ≈ proj₁ f)
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


-------------------------------------------------------------------
-- Machinery to simplify normal form construction during evaluation
-------------------------------------------------------------------

module _ where

  ⟦_⟧' : Ty → Set
  ⟦  Nat  ⟧' = ⟦ Nat ⟧
  ⟦ a ⇒ b ⟧' = ⟦ a ⟧ → ⟦ b ⟧'

  pack : Tm a → ⟦ a ⟧' → ⟦ a ⟧
  pack {Nat}    t v = v
  pack {a ⇒ a₁} t v = t , λ x → pack (t ∙ reify x) (v x)

  unpack : ⟦ a ⟧ → ⟦ a ⟧'
  unpack {Nat}   n       = n
  unpack {a ⇒ b} (_ , f) = λ x → unpack (f x)

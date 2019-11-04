-- Agda version: 2.6.1-ea02852
-- Agda Lib version: v1.1-g0ef8002c
module CL where

open import Relation.Binary using (IsEquivalence; Setoid)

module Setoid-Reasoning {C : Set} {_≈_ : C → C → Set} (≈-equiv : IsEquivalence _≈_) where
  open import Relation.Binary.Reasoning.Setoid (record { Carrier = C ; _≈_ = _≈_ ; isEquivalence = ≈-equiv }) public

  open IsEquivalence ≈-equiv renaming (refl to reflexivity; sym to symmetry; trans to transitivity) using () public
open Setoid-Reasoning {{...}}

open import Data.Nat                              renaming (ℕ to Nat; zero to zer)
open import Relation.Binary.PropositionalEquality

infixr 20 _⇒_
data Ty : Set where
  ℕ   : Ty
  _⇒_ : Ty → Ty → Ty

record CL-Structure (dom : Ty → Set) (E : {τ : Ty} → dom τ → dom τ → Set) : Set where
  private
    infix 19 _≈_
    _≈_ = E

  infixl 20 _·_
  field
    ≈-reflexivity  : ∀ {τ} {x : dom τ} → x ≈ x
    ≈-symmetry     : ∀ {τ} {x y : dom τ} → x ≈ y → y ≈ x
    ≈-transitivity : ∀ {τ} {x y z : dom τ} → x ≈ y → y ≈ z → x ≈ z

    _·_            : {τ₁ τ₂ : Ty} → dom (τ₁ ⇒ τ₂) → dom τ₁ → dom τ₂
    zero           : dom ℕ
    succ           : dom (ℕ ⇒ ℕ)
    K              : {τ₁ τ₂ : Ty} → dom (τ₁ ⇒ τ₂ ⇒ τ₁)

    ·-cong         : ∀ {τ₁ τ₂} {x x' : dom (τ₁ ⇒ τ₂)} {y y' : dom τ₁} → x ≈ x' → y ≈ y' → x · y ≈ x' · y'
    K-β            : ∀ {τ₁ τ₂} {x : dom τ₁} {u : dom τ₂} → K · x · u ≈ x

  instance
    ≈-equiv : ∀ {τ} → IsEquivalence (_≈_ {τ})
    ≈-equiv = record
                { refl  = ≈-reflexivity
                ; sym   = ≈-symmetry
                ; trans = ≈-transitivity
                }

  dom-setoid : Ty → Setoid _ _
  dom-setoid τ = record { Carrier = dom τ; _≈_ = _≈_; isEquivalence = ≈-equiv }

record CL : Set₁ where
  -- infix  19 _≈_
  field
    dom     : Ty → Set
    _≈_     : {τ : Ty} → dom τ → dom τ → Set
    i       : CL-Structure dom _≈_
  open CL-Structure i public

dom^     = CL.dom
infix 18 ≈-syntax
≈-syntax = CL._≈_
syntax ≈-syntax M x y = x ≈[ M ] y
infix 19 ·-syntax
·-syntax = CL._·_
syntax ·-syntax M x y = x ·[ M ] y
zero^    = CL.zero
succ^    = CL.succ
K^       = CL.K

record IsHom (M N : CL) (fun : {τ : Ty} → dom^ M τ → dom^ N τ) : Set where
  field
    pres-≈ : ∀ {τ} {x y : dom^ M τ} → x ≈[ M ] y → fun x ≈[ N ] fun y
    pres-· : ∀ {τ₁ τ₂} {x : dom^ M (τ₁ ⇒ τ₂)} {y : dom^ M τ₁} → fun (x ·[ M ] y) ≈[ N ] fun x ·[ N ] fun y
    pres-zero : fun (zero^ M) ≈[ N ] zero^ N
    pres-succ : fun (succ^ M) ≈[ N ] succ^ N
    pres-K    : ∀ {τ₁ τ₂} → fun (K^ M {τ₁} {τ₂}) ≈[ N ] K^ N

record Hom (M N : CL) : Set where
  field
    fun : {τ : Ty} → dom^ M τ → dom^ N τ
    isHom : IsHom M N fun

  open IsHom isHom public

‖_‖ = Hom.fun

id : {M : CL} → Hom M M
id {M} = let open CL M in
         record
           { fun   = λ x → x
           ; isHom = record
                       { pres-≈    = λ x≈y → x≈y
                       ; pres-·    = reflexivity
                       ; pres-zero = reflexivity
                       ; pres-succ = reflexivity
                       ; pres-K    = reflexivity
                       }
           }

_∘_ : {M N O : CL} → Hom N O → Hom M N → Hom M O
_∘_ {M} {N} {O} g f = let open CL M; open CL N; open CL O in
                      record
                        { fun   = λ x → ‖ g ‖ (‖ f ‖ x)
                        ; isHom = record
                                    { pres-≈    = λ {_} {x} {y} x≈y →
                                                  begin
                                                    ‖ g ‖ (‖ f ‖ x) ≈⟨ Hom.pres-≈ g (Hom.pres-≈ f x≈y) ⟩
                                                    ‖ g ‖ (‖ f ‖ y) ∎
                                    ; pres-·    = λ {_} {_} {x} {y} →
                                                  begin
                                                    ‖ g ‖ (‖ f ‖ (x ·[ M ] y))     ≈⟨ Hom.pres-≈ g (Hom.pres-· f) ⟩
                                                    ‖ g ‖ (‖ f ‖ x ·[ N ] ‖ f ‖ y) ≈⟨ Hom.pres-· g ⟩
                                                    ‖ g ‖ (‖ f ‖ x) ·[ O ] ‖ g ‖ (‖ f ‖ y) ∎
                                    ; pres-zero = begin
                                                    ‖ g ‖ (‖ f ‖ (zero^ M)) ≈⟨ Hom.pres-≈ g (Hom.pres-zero f) ⟩
                                                    ‖ g ‖ (zero^ N)         ≈⟨ Hom.pres-zero g ⟩
                                                    zero^ O ∎
                                    ; pres-succ = begin
                                                    ‖ g ‖ (‖ f ‖ (succ^ M)) ≈⟨ Hom.pres-≈ g (Hom.pres-succ f) ⟩
                                                    ‖ g ‖ (succ^ N)         ≈⟨ Hom.pres-succ g ⟩
                                                    succ^ O ∎
                                    ; pres-K    = begin
                                                    ‖ g ‖ (‖ f ‖ (K^ M)) ≈⟨ Hom.pres-≈ g (Hom.pres-K f) ⟩
                                                    ‖ g ‖ (K^ N)         ≈⟨ Hom.pres-K g ⟩
                                                    K^ O ∎
                                    }
                        }

infixl 20 _·_
data Tm : Ty → Set where
  _·_ : {τ₁ τ₂ : Ty} → Tm (τ₁ ⇒ τ₂) → Tm τ₁ → Tm τ₂
  K   : {τ₁ τ₂ : Ty} → Tm (τ₁ ⇒ τ₂ ⇒ τ₁)
  zero : Tm ℕ
  succ : Tm (ℕ ⇒ ℕ)

infix 19 _conv_
data _conv_ {τ : Ty} : Tm τ → Tm τ → Set where
  ≈-reflexivity  : ∀ {x} → x conv x
  ≈-symmetry     : ∀ {x y} → x conv y → y conv x
  ≈-transitivity : ∀ {x y z} → x conv y → y conv z → x conv z
  ·-cong         : ∀ {τ'} {x x'} {y y' : Tm τ'} → x conv x' → y conv y' → x · y conv x' · y'
  K-β            : ∀ {τ'} {x} {y : Tm τ'} → K · x · y conv x

Initial : CL
Initial = record
            { dom     = Tm
            ; _≈_     = _conv_
            ; i = record
                    { ≈-reflexivity  = ≈-reflexivity
                    ; ≈-symmetry     = ≈-symmetry
                    ; ≈-transitivity = ≈-transitivity
                    ; _·_            = _·_
                    ; zero           = zero
                    ; succ           = succ
                    ; K              = K
                    ; ·-cong         = ·-cong
                    ; K-β            = K-β
                    }
            }

Existence : {M : CL} → Hom Initial M
Existence {M} = record
                  { fun   = fun
                  ; isHom = record
                              { pres-≈    = pres-≈
                              ; pres-·    = CL.≈-reflexivity M
                              ; pres-zero = CL.≈-reflexivity M
                              ; pres-succ = CL.≈-reflexivity M
                              ; pres-K    = CL.≈-reflexivity M
                              }
                  }
  where
    fun : {τ : Ty} → Tm τ → dom^ M τ
    fun (x · y) = fun x ·[ M ] fun y
    fun K       = K^ M
    fun zero    = zero^ M
    fun succ    = succ^ M

    pres-≈ : ∀ {τ} {x y : Tm τ} → x ≈[ Initial ] y → fun x ≈[ M ] fun y
    pres-≈ ≈-reflexivity            = CL.≈-reflexivity M
    pres-≈ (≈-symmetry y≈x)         = CL.≈-symmetry M (pres-≈ y≈x)
    pres-≈ (≈-transitivity x≈z z≈y) = CL.≈-transitivity M (pres-≈ x≈z) (pres-≈ z≈y)
    pres-≈ (·-cong x₁≈y₁ x₂≈y₂)     = CL.·-cong M (pres-≈ x₁≈y₁) (pres-≈ x₂≈y₂)
    pres-≈ K-β                      = CL.K-β M

infix 20 ⟦⟧-syntax
⟦⟧-syntax : (M : CL) {τ : Ty} → dom^ Initial τ → dom^ M τ
⟦⟧-syntax M = ‖ Existence {M} ‖
syntax ⟦⟧-syntax M x = ⟦ x ⟧^ M

private
  module _ {M} (f : Hom Initial M) where
    open CL M using (≈-equiv)

    lemma : ∀ {τ} (x : dom^ Initial τ) → ‖ f ‖ x ≈[ M ] ⟦ x ⟧^ M
    lemma (x · y) = begin
                      ‖ f ‖ (x · y)              ≈⟨ Hom.pres-· f ⟩
                      ‖ f ‖ x ·[ M ] ‖ f ‖ y     ≈⟨ CL.·-cong M (lemma x) (lemma y) ⟩
                      ⟦ x ⟧^ M ·[ M ] ⟦ y ⟧^ M ≈⟨ reflexivity ⟩
                      ⟦ x · y ⟧^ M ∎
    lemma K       = begin
                      ‖ f ‖ K ≈⟨ Hom.pres-K f ⟩
                      K^ M    ≈⟨ reflexivity ⟩
                      ⟦ K ⟧^ M ∎
    lemma zero    = begin
                      ‖ f ‖ zero ≈⟨ Hom.pres-zero f ⟩
                      zero^ M    ≈⟨ reflexivity ⟩
                      ⟦ zero ⟧^ M ∎
    lemma succ    = begin
                      ‖ f ‖ succ ≈⟨ Hom.pres-succ f ⟩
                      succ^ M    ≈⟨ reflexivity ⟩
                      ⟦ succ ⟧^ M ∎

Uniqueness : ∀ {M} {f g : Hom Initial M} → ∀ {τ} {x : dom^ Initial τ} → ‖ f ‖ x ≈[ M ] ‖ g ‖ x
Uniqueness {M} {f} {g} {τ} {x} = let open CL M using (≈-equiv) in
                                 begin
                                   ‖ f ‖ x         ≈⟨ lemma f x ⟩
                                   ‖ Existence ‖ x ≈⟨ symmetry (lemma g x) ⟩
                                   ‖ g ‖ x ∎

Standard : CL
Standard = record
             { dom = dom
             ; _≈_ = _≡_
             ; i   = record
                       { ≈-reflexivity  = refl
                       ; ≈-symmetry     = sym
                       ; ≈-transitivity = trans
                       ; _·_            = λ f x → f x
                       ; zero           = 0
                       ; succ           = suc
                       ; K              = λ x _ → x
                       ; ·-cong         = λ { refl refl → refl }
                       ; K-β            = refl
                       }
             }
  where
    dom : Ty → Set
    dom ℕ         = Nat
    dom (τ₁ ⇒ τ₂) = dom τ₁ → dom τ₂

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Nullary

module _ where
  private
    dom : Ty → Set
    dom ℕ       = Nat
    dom (a ⇒ b) = Tm (a ⇒ b) × (dom a → dom b)

    ‖reify‖ : ∀ {τ : Ty} → dom τ → Tm τ
    ‖reify‖ {ℕ}       zer     = zero
    ‖reify‖ {ℕ}       (suc x) = succ · ‖reify‖ x
    ‖reify‖ {τ₁ ⇒ τ₂} (F , _) = F

  NonStandard : CL
  NonStandard = record
                  { dom = dom
                  ; _≈_ = _≡_
                  ; i   = record
                            { ≈-reflexivity  = refl
                            ; ≈-symmetry     = sym
                            ; ≈-transitivity = trans
                            ; _·_            = λ { (_ , f) x → f x }
                            ; zero           = 0
                            ; succ           = succ , suc
                            ; K              = K    , λ x → K · ‖reify‖ x , λ _ → x
                            ; ·-cong         = λ { refl refl → refl }
                            ; K-β            = refl
                            }
                  }

  -- we cannot define a Hom NonStandard Initial
  -- ‖reify‖ is not a Hom NonStandard Initial
  module ReifyNotHom where
    counter-example : dom^ NonStandard (ℕ ⇒ ℕ)
    counter-example = succ , λ _ → 0

    reify-not-hom : ¬ IsHom NonStandard Initial ‖reify‖
    reify-not-hom isHom = zero≢one zero≡one
      where
        zero≈one : zero conv succ · zero -- reify (appsem counter-example zero) conv reify counter-example · reify zero
        zero≈one = IsHom.pres-· isHom {x = counter-example} {y = zer}

        zero≡one : zer ≡ suc zer
        zero≡one = Hom.pres-≈ (Existence {M = Standard}) zero≈one

        zero≢one : ¬ zer ≡ suc zer
        zero≢one ()

  Gluing : CL
  Gluing = record
             { dom = λ τ → Σ (dom^ NonStandard τ) Gl
             ; _≈_ = λ { (x , _) (y , _) → x ≈[ NonStandard ] y }
             ; i   = record
                       { ≈-reflexivity  = CL.≈-reflexivity  NonStandard
                       ; ≈-symmetry     = CL.≈-symmetry     NonStandard
                       ; ≈-transitivity = CL.≈-transitivity NonStandard
                       ; _·_            = λ { (f , Glf) (x , Glx) → f ·[ NonStandard ] x , proj₁ (Glf x Glx) }
                       ; zero           = zero^ NonStandard , tt
                       ; succ           = succ^ NonStandard , λ _ _ → tt , CL.≈-reflexivity Initial
                       ; K              = K^ NonStandard , λ x Glx → (λ _ _ → Glx , CL.≈-symmetry Initial (CL.K-β Initial)) , CL.≈-reflexivity Initial
                       ; ·-cong         = cong₂ proj₂
                       ; K-β            = CL.≈-reflexivity NonStandard
                       }
             }
    where
      Gl : {τ : Ty} → dom^ NonStandard τ → Set
      Gl {ℕ}       _ = ⊤
      Gl {τ₁ ⇒ τ₂} f = ∀ (x : dom^ NonStandard τ₁) → Gl x →
                           Gl (f ·[ NonStandard ] x)
                         × ‖reify‖ (f ·[ NonStandard ] x) ≈[ Initial ] ‖reify‖ f ·[ Initial ] ‖reify‖ x

  reify : Hom Gluing Initial
  reify = record
            { fun   = λ { (x , _) → ‖reify‖ x }
            ; isHom = record
                        { pres-≈    = λ { refl → CL.≈-reflexivity Initial }
                        ; pres-·    = λ { { x = f , glf } {y = x , glx} → proj₂ (glf x glx) }
                        ; pres-zero = CL.≈-reflexivity Initial
                        ; pres-succ = CL.≈-reflexivity Initial
                        ; pres-K    = CL.≈-reflexivity Initial
                        }
            }

-- Main theorem

norm : {τ : Ty} → Tm τ → Tm τ -- = ‖ reify ‖ ∘ ⟦ · ⟧^ Gluing : dom^ Initial τ → dom^ Initial τ
norm = ‖ reify ∘ Existence ‖

norm-correct : ∀ {τ} {x : Tm τ} → norm x conv x
norm-correct = Uniqueness {f = reify ∘ Existence} {g = id}

-- Corollaries

soundness : ∀ {τ} {x y : Tm τ} → x conv y → ⟦ x ⟧^ Gluing ≈[ Gluing ] ⟦ y ⟧^ Gluing
soundness = Hom.pres-≈ (Existence {M = Gluing})

completeness : ∀ {τ} {x y : Tm τ} → ⟦ x ⟧^ Gluing ≈[ Gluing ] ⟦ y ⟧^ Gluing → x conv y
completeness {_} {x} {y} ⟦x⟧≈⟦y⟧ = let open CL Initial in
                                   begin
                                     x      ≈⟨ symmetry norm-correct ⟩
                                     norm x ≈⟨ Hom.pres-≈ reify {x = ⟦ x ⟧^ Gluing} {y = ⟦ y ⟧^ Gluing} ⟦x⟧≈⟦y⟧ ⟩
                                     norm y ≈⟨ norm-correct ⟩
                                     y ∎

private
  decide-Ty : ∀ (τ τ' : Ty) → τ ≡ τ' ⊎ ¬ τ ≡ τ'
  decide-Ty ℕ        ℕ            = inj₁ refl
  decide-Ty ℕ        (_ ⇒ _)      = inj₂ λ ()
  decide-Ty (_ ⇒ _)  ℕ            = inj₂ λ ()
  decide-Ty (τ₁ ⇒ τ₂) (τ₁' ⇒ τ₂') with decide-Ty τ₁ τ₁' | decide-Ty τ₂ τ₂'
  ... | inj₂ τ₁≢τ₁' | _           = inj₂ λ { refl → τ₁≢τ₁' refl }
  ... | inj₁ refl   | inj₁ refl   = inj₁ refl
  ... | inj₁ refl   | inj₂ τ₂≢τ₂' = inj₂ λ { refl → τ₂≢τ₂' refl }

  decide-Tm : ∀ {τ} (x y : Tm τ) → x ≡ y ⊎ ¬ x ≡ y
  decide-Tm (_·_ {τ₁} f x) (_·_ {τ₁'} f' x') with decide-Ty τ₁ τ₁'
  ... | inj₂ τ₁≢τ₁' = inj₂ λ { refl → τ₁≢τ₁' refl }
  ... | inj₁ refl with decide-Tm f f'
  ... | inj₂ f≢f'   = inj₂ λ { refl → f≢f' refl }
  ... | inj₁ refl with decide-Tm x x'
  ... | inj₂ x≢x'   = inj₂ λ { refl → x≢x' refl }
  ... | inj₁ refl      = inj₁ refl
  decide-Tm (_ · _) (K)       = inj₂ λ ()
  decide-Tm (_ · _) (zero)    = inj₂ λ ()
  decide-Tm (_ · _) (succ)    = inj₂ λ ()
  decide-Tm (K)     (_ · _)   = inj₂ λ ()
  decide-Tm (K)     (K)       = inj₁ refl
  decide-Tm (zero)  (_ · _)   = inj₂ λ ()
  decide-Tm (zero)  (zero)    = inj₁ refl
  decide-Tm (succ)  (_ · _)   = inj₂ λ ()
  decide-Tm (succ)  (succ)    = inj₁ refl

  decide-Nat : ∀ (n m : Nat) → n ≡ m ⊎ ¬ n ≡ m
  decide-Nat zer     zer     = inj₁ refl
  decide-Nat zer     (suc m) = inj₂ λ ()
  decide-Nat (suc n) zer     = inj₂ λ ()
  decide-Nat (suc n) (suc m) with decide-Nat n m
  ... | inj₂ n≢m  = inj₂ λ { refl → n≢m refl }
  ... | inj₁ refl = inj₁ refl

  decide-Gluing : ∀ {τ} (x y : dom^ Gluing τ) → x ≈[ Gluing ] y ⊎ ¬ (x ≈[ Gluing ] y)
  decide-Gluing x y = {!!}

decidability : ∀ {τ} (x y : Tm τ) → x conv y ⊎ ¬ (x conv y)
decidability x y with decide-Gluing (⟦ x ⟧^ Gluing) (⟦ y ⟧^ Gluing)
... | inj₁ ⟦x⟧≈⟦y⟧ = inj₁ (completeness ⟦x⟧≈⟦y⟧)
... | inj₂ ⟦x⟧≉⟦y⟧ = inj₂ λ x≈y → ⟦x⟧≉⟦y⟧ (soundness x≈y)

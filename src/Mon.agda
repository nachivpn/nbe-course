module Mon where

open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; module ≡-Reasoning) renaming (refl to Refl; isEquivalence to ≡-equiv)
open import Relation.Binary

module SetoidReasoning {X : Set} {R : X → X → Set} (R-equiv : IsEquivalence R) where
  open import Relation.Binary.Reasoning.Setoid (record { Carrier = X; _≈_ = R; isEquivalence = R-equiv }) public
  open IsEquivalence R-equiv public
open SetoidReasoning {{...}}

instance _ = ≡-equiv

record IsMon {M : Set} (E : M → M → Set) (_∗_ : M → M → M) (e : M) : Set where
  private
    _≈_ = E
    infix 19 _≈_

  field
    ∗-assoc      : ∀ {x y z} → (x ∗ y) ∗ z ≈ x ∗ (y ∗ z)
    e-unit-right : ∀ {x} → x ∗ e ≈ x
    e-unit-left  : ∀ {x} → e ∗ x ≈ x

record Mon : Set₁ where
  field
    M   : Set
    _≈_ : M → M → Set
    instance isEquivalence : IsEquivalence _≈_

    _∗_    : M → M → M
    ∗-cong : ∀ {x x' y y'} → x ≈ y → x' ≈ y' → x ∗ x' ≈ y ∗ y'

    e   : M

    isMon : IsMon _≈_ _∗_ e

  infix 19 _≈_
  open IsMon isMon public

dom^                  = Mon.M
infix 19 ≈-syntax
≈-syntax              = Mon._≈_
syntax ≈-syntax M x y = x ≈[ M ] y
∗-syntax              = Mon._∗_
syntax ∗-syntax M x y = x ∗[ M ] y
e^                    = Mon.e

record IsHom (M N : Mon) (f : dom^ M → dom^ N) : Set where
  field
    pres-≈ : ∀ {x y} → x ≈[ M ] y → f x ≈[ N ] f y
    pres-∗ : ∀ {x y} → f (x ∗[ M ] y) ≈[ N ] f x ∗[ N ] f y
    pres-e : f (e^ M) ≈[ N ] e^ N

record Hom (M N : Mon) : Set where
  field
    f : dom^ M → dom^ N

    isHom : IsHom M N f

  open IsHom isHom public

‖_‖ = Hom.f

id : ∀ {M} → Hom M M
id {M} = let open Mon M using (isEquivalence) in
         record
           { f     = λ x → x
           ; isHom = record
                       { pres-≈ = λ x≈y → x≈y
                       ; pres-∗ = refl
                       ; pres-e = refl
                       }
           }

_∘_ : ∀ {M N O} → Hom N O → Hom M N → Hom M O
_∘_ {M} {N} {O} g f = let open Mon O using (isEquivalence) in
                      record
                        { f     = λ x → ‖ g ‖ (‖ f ‖ x)
                        ; isHom = record
                                    { pres-≈ = λ x≈y → Hom.pres-≈ g (Hom.pres-≈ f x≈y)
                                    ; pres-∗ = λ {x} {y} →
                                               begin
                                                 ‖ g ‖ (‖ f ‖ (x ∗[ M ] y))             ≈⟨ Hom.pres-≈ g (Hom.pres-∗ f) ⟩
                                                 ‖ g ‖ (‖ f ‖ x ∗[ N ] ‖ f ‖ y)         ≈⟨ Hom.pres-∗ g ⟩
                                                 ‖ g ‖ (‖ f ‖ x) ∗[ O ] ‖ g ‖ (‖ f ‖ y) ∎
                                    ; pres-e = begin
                                                 ‖ g ‖ (‖ f ‖ (e^ M)) ≈⟨ Hom.pres-≈ g (Hom.pres-e f) ⟩
                                                 ‖ g ‖ (e^ N)         ≈⟨ Hom.pres-e g ⟩
                                                 e^ O ∎
                                    }
                        }

module _ {G : Set} where
  data Tm : Set where
    const : (c : G) → Tm
    e     : Tm
    _∗_   : (t u : Tm) → Tm

  data _conv_ : Tm → Tm → Set where
    reflexivity  : ∀ {t} → t conv t
    symmetry     : ∀ {t u} → t conv u → u conv t
    transitivity : ∀ {t u v} → t conv u → u conv v → t conv v
    ∗-assoc      : ∀ {t u v} → (t ∗ u) ∗ v conv t ∗ (u ∗ v)
    e-unit-right : ∀ {t} → t ∗ e conv t
    e-unit-left  : ∀ {t} → e ∗ t conv t
    ∗-cong       : ∀ {t t' u u'} → t conv t' → u conv u' → t ∗ u conv t' ∗ u'

  infix 19 _conv_

  Initial : Mon
  Initial = record
              { M             = Tm
              ; _≈_           = _conv_
              ; isEquivalence = record { refl = reflexivity ; sym = symmetry ; trans = transitivity }
              ; _∗_           = _∗_
              ; ∗-cong        = ∗-cong
              ; e             = e
              ; isMon         = record
                                  { ∗-assoc      = ∗-assoc
                                  ; e-unit-right = e-unit-right
                                  ; e-unit-left  = e-unit-left
                                  }
              }

  data List : Set where
    []  : List
    _∷_ : (x : G) → (xs : List) → List
  infixr 19 _∷_

  [_] = _∷ []

  _++_ : List → List → List
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ xs ++ ys

  Nf : Mon
  Nf = record
              { M             = List
              ; _≈_           = _≡_
              ; isEquivalence = ≡-equiv
              ; _∗_           = _++_
              ; ∗-cong        = λ x≡y x'≡y' → trans (cong _ x≡y) (cong _ x'≡y')
              ; e             = []
              ; isMon         = record
                                  { ∗-assoc      = λ {xs} {ys} {zs} → ++-assoc {xs} {ys} {zs}
                                  ; e-unit-right = []-right-id
                                  ; e-unit-left  = []-left-id
                                  }
              }
    where
      []-right-id : ∀ {xs} → xs ++ [] ≡ xs
      []-right-id {[]}                              = refl
      []-right-id {x ∷ xs} rewrite []-right-id {xs} = refl

      []-left-id : ∀ {xs} → [] ++ xs ≡ xs
      []-left-id = refl

      ++-assoc : ∀ {xs ys zs} → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
      ++-assoc {[]}     {ys} {zs} = refl
      ++-assoc {x ∷ xs} {ys} {zs} rewrite ++-assoc {xs} {ys} {zs} = refl

  reify : Hom Nf Initial
  reify = record
            { f     = ‖reify‖
            ; isHom = record
                        { pres-≈ =  λ {xs} {ys} xs≡ys → subst (λ ys → ‖reify‖ xs conv ‖reify‖ ys) xs≡ys refl
                        ; pres-∗ = pres-∗
                        ; pres-e = refl
                        }
            }
    where
      open Mon Initial using (isEquivalence)

      ‖reify‖ : List → Tm
      ‖reify‖ []       = e
      ‖reify‖ (x ∷ xs) = const x ∗ ‖reify‖ xs

      pres-∗ : ∀ {xs} {ys} → ‖reify‖ (xs ++ ys) conv ‖reify‖ xs ∗ ‖reify‖ ys
      pres-∗ {[]}     {ys} = sym e-unit-left
      pres-∗ {x ∷ xs} {ys} = begin
                               ‖reify‖ (x ∷ xs ++ ys)              ≈⟨ refl ⟩
                               ‖reify‖ (x ∷ (xs ++ ys))            ≈⟨ refl ⟩
                               const x ∗ ‖reify‖ (xs ++ ys)        ≈⟨ ∗-cong refl pres-∗ ⟩
                               const x ∗ (‖reify‖ xs ∗ ‖reify‖ ys) ≈⟨ sym ∗-assoc ⟩
                               (const x ∗ ‖reify‖ xs) ∗ ‖reify‖ ys ≈⟨ refl ⟩
                               ‖reify‖ (x ∷ xs) ∗ ‖reify‖ ys ∎

  module _ (M : Mon) (f : G → dom^ M) where
    open Mon M using (isEquivalence)

    private
      ‖Existence‖ : dom^ Initial → dom^ M
      ‖Existence‖ (const c) = f c
      ‖Existence‖ e         = e^ M
      ‖Existence‖ (t ∗ u)   = ‖Existence‖ t ∗[ M ] ‖Existence‖ u

      pres-≈ : ∀ {x} {y} → x conv y → ‖Existence‖ x ≈[ M ] ‖Existence‖ y
      pres-≈ reflexivity            = refl
      pres-≈ (symmetry y≈x)         = sym (pres-≈ y≈x)
      pres-≈ (transitivity x≈z z≈y) = trans (pres-≈ x≈z) (pres-≈ z≈y)
      pres-≈ ∗-assoc                = Mon.∗-assoc M
      pres-≈ e-unit-right           = Mon.e-unit-right M
      pres-≈ e-unit-left            = Mon.e-unit-left M
      pres-≈ (∗-cong x₁≈y₁ x₂≈y₂)   = Mon.∗-cong M (pres-≈ x₁≈y₁) (pres-≈ x₂≈y₂)

    Existence : Hom Initial M
    Existence = record
                  { f     = ‖Existence‖
                  ; isHom = record
                              { pres-≈ = pres-≈
                              ; pres-∗ = refl
                              ; pres-e = refl
                              }
                  }

    private
      module _ (h : Hom Initial M) (‖h‖≡f : ∀ {c} → ‖ h ‖ (const c) ≈[ M ] f c) where
        lemma : ∀ {x} → ‖ h ‖ x ≈[ M ] ‖ Existence ‖ x
        lemma {const c} = begin ‖ h ‖ (const c) ≈⟨ ‖h‖≡f ⟩ f c ≈⟨ refl ⟩ ‖Existence‖ (const c) ∎
        lemma {e}       = begin ‖ h ‖ e ≈⟨ Hom.pres-e h ⟩ e^ M ≈⟨ refl ⟩ ‖Existence‖ e ∎
        lemma {t ∗ u}   = begin
                            ‖ h ‖ (t ∗ u)                      ≈⟨ Hom.pres-∗ h ⟩
                            ‖ h ‖ t ∗[ M ] ‖ h ‖ u             ≈⟨ Mon.∗-cong M lemma lemma ⟩
                            ‖Existence‖ t ∗[ M ] ‖Existence‖ u ≈⟨ refl ⟩
                            ‖Existence‖ (t ∗ u) ∎

    module _ (h : Hom Initial M) (‖h‖≡f : ∀ {c} → ‖ h ‖ (const c) ≈[ M ] f c)
             (i : Hom Initial M) (‖i‖≡f : ∀ {c} → ‖ i ‖ (const c) ≈[ M ] f c) where
      Uniqueness : ∀ {x} → ‖ h ‖ x ≈[ M ] ‖ i ‖ x
      Uniqueness {x} = begin ‖ h ‖ x ≈⟨ lemma h ‖h‖≡f ⟩ ‖ Existence ‖ x ≈⟨ sym (lemma i ‖i‖≡f) ⟩ ‖ i ‖ x ∎

  norm : Tm → Tm
  norm = ‖ reify ∘ Existence Nf [_] ‖

  norm-correct : ∀ {x} → norm x conv x
  norm-correct = Uniqueness Initial                    const
                            (reify ∘ Existence Nf [_]) e-unit-right
                            id                         reflexivity

  Soundness : ∀ {x y} → norm x ≡ norm y → x conv y
  Soundness {x} {y} normx≡normy = let open Mon Initial using (isEquivalence) in
                                  begin
                                    x      ≈⟨ sym norm-correct ⟩
                                    norm x ≈⟨ subst (λ z → norm x conv z) normx≡normy refl ⟩
                                    norm y ≈⟨ norm-correct ⟩
                                    y ∎

  Completeness : ∀ {x y} → x conv y → norm x ≡ norm y
  Completeness x≈y = cong ‖ reify ‖ (Hom.pres-≈ (Existence Nf [_]) x≈y)


  module _ (decide-G : ∀ (c d : G) → c ≡ d ⊎ ¬ c ≡ d) where
    decide-Tm : ∀ (x y : Tm) → x ≡ y ⊎ ¬ x ≡ y
    decide-Tm (const c) (const d) with decide-G c d
    ... | inj₁ c≡d  = inj₁ (cong const c≡d)
    ... | inj₂ ¬c≡d = inj₂ λ { Refl → ¬c≡d refl }
    decide-Tm (const c) e         = inj₂ λ ()
    decide-Tm (const c) (x ∗ y)   = inj₂ λ ()
    decide-Tm e         (const c) = inj₂ λ ()
    decide-Tm e         e         = inj₁ refl
    decide-Tm e         (x ∗ y)   = inj₂ λ ()
    decide-Tm (x ∗ y)   (const c) = inj₂ λ ()
    decide-Tm (x ∗ y)   e         = inj₂ λ ()
    decide-Tm (x ∗ y)   (z ∗ a)   with decide-Tm x z | decide-Tm y a
    ... | inj₁ x≡z  | inj₁ y≡a  = inj₁ (begin x ∗ y ≈⟨ cong (_∗ y) x≡z ⟩ z ∗ y ≈⟨ cong (z ∗_) y≡a ⟩ z ∗ a ∎)
    ... | inj₁ x≡z  | inj₂ ¬y≡a = inj₂ λ { Refl → ¬y≡a refl }
    ... | inj₂ ¬x≡z | _         = inj₂ λ { Refl → ¬x≡z refl }

    decide-List : ∀ (xs ys : List) → xs ≡ ys ⊎ ¬ xs ≡ ys
    decide-List []       []       = inj₁ refl
    decide-List []       (y ∷ ys) = inj₂ λ ()
    decide-List (x ∷ xs) []       = inj₂ λ ()
    decide-List (x ∷ xs) (y ∷ ys) with decide-G x y | decide-List xs ys
    ... | inj₁ x≡y  | inj₁ xs≡ys  = inj₁ (begin (x ∷ xs ≈⟨ cong (_∷ xs) x≡y ⟩ y ∷ xs ≈⟨ cong (y ∷_) xs≡ys ⟩ y ∷ ys ∎))
    ... | inj₁ x≡y  | inj₂ ¬xs≡ys = inj₂ λ xxs≡yys → ¬xs≡ys (cong (λ { [] → []; (_ ∷ tl) → tl }) xxs≡yys)
    ... | inj₂ ¬x≡y | _           = inj₂ λ xxs≡yys → ¬x≡y   (cong (λ { [] → x;  (hd ∷ _) → hd }) xxs≡yys)

    decide-Tm/conv : ∀ x y → x conv y ⊎ ¬ x conv y
    decide-Tm/conv x y with decide-Tm (norm x) (norm y)
    ... | inj₁ normx≡normy  = inj₁ (Soundness normx≡normy)
    ... | inj₂ ¬normx≡normy = inj₂ λ x≈y → ¬normx≡normy (Completeness x≈y)

module _ where
  open import Data.Nat            renaming (ℕ to Nat; _*_ to _×_)
  open import Data.Nat.Properties

  ℕ+ = record
         { M             = Nat
         ; _≈_           = _≡_
         ; isEquivalence = ≡-equiv
         ; _∗_           = _+_
         ; ∗-cong        = λ x≡y x'≡y' → trans (cong _ x≡y) (cong _ x'≡y')
         ; e             = 0
         ; isMon         = record
                             { ∗-assoc      = λ {x} {y} {z} → +-assoc x y z
                             ; e-unit-right = +-identityʳ _
                             ; e-unit-left  = +-identityˡ _
                             }
         }

  ℕ* = record
         { M             = Nat
         ; _≈_           = _≡_
         ; isEquivalence = ≡-equiv
         ; _∗_           = _×_
         ; ∗-cong        = λ x≡y x'≡y' → trans (cong _ x≡y) (cong _ x'≡y')
         ; e             = 1
         ; isMon         = record
                             { ∗-assoc      = λ {x} {y} {z} → *-assoc x y z
                             ; e-unit-right = *-identityʳ _
                             ; e-unit-left  = *-identityˡ _
                             }
         }

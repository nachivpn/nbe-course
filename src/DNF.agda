module DNF where -- (I : Set) where

-- 8< --
open import Data.Nat
I = ℕ
infixr 20 _/\_ _\/_
-- >8 --

open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; module ≡-Reasoning) renaming (refl to Refl; isEquivalence to ≡-equiv)
open import Relation.Binary

module SetoidReasoning {X : Set} {R : X → X → Set} (R-equiv : IsEquivalence R) where
  open import Relation.Binary.Reasoning.Setoid (record { Carrier = X; _≈_ = R; isEquivalence = R-equiv }) public
  open IsEquivalence R-equiv public
open SetoidReasoning {{...}}

-- bounded distributive lattices
record IsLattice (L : Set) (E : L → L → Set) (M : L → L → L) (J : L → L → L) (⊤ : L) (⊥ : L) : Set where
  private
    infix 19 _≈_

    _≈_ = E
    _∧_ = M
    _∨_ = J

  field
    cong-∧ : ∀ {φ φ' ψ ψ'} → φ ≈ φ' → ψ ≈ ψ' → φ ∧ ψ ≈ φ' ∧ ψ'
    cong-∨ : ∀ {φ φ' ψ ψ'} → φ ≈ φ' → ψ ≈ ψ' → φ ∨ ψ ≈ φ' ∨ ψ'
    assc-∧ : ∀ {φ ψ κ}     → (φ ∧ ψ) ∧ κ ≈ φ ∧ (ψ ∧ κ)
    assc-∨ : ∀ {φ ψ κ}     → (φ ∨ ψ) ∨ κ ≈ φ ∨ (ψ ∨ κ)
    comm-∧ : ∀ {φ ψ}       → φ ∧ ψ ≈ ψ ∧ φ
    comm-∨ : ∀ {φ ψ}       → φ ∨ ψ ≈ ψ ∨ φ
    absp-∧ : ∀ {φ ψ}       → φ ∧ (φ ∨ ψ) ≈ φ
    absp-∨ : ∀ {φ ψ}       → φ ∨ (φ ∧ ψ) ≈ φ
    dist-∧ : ∀ {φ ψ κ}     → φ ∧ (ψ ∨ κ) ≈ (φ ∧ ψ) ∨ (φ ∧ κ)
    dist-∨ : ∀ {φ ψ κ}     → φ ∨ (ψ ∧ κ) ≈ (φ ∨ ψ) ∧ (φ ∨ κ)
    unit-∧ : ∀ {φ}         → ⊤ ∧ φ ≈ φ
    unit-∨ : ∀ {φ}         → ⊥ ∨ φ ≈ φ

record Lattice : Set₁ where
  infix 19 _≈_

  field
    L                : Set
    _≈_              : L → L → Set
    instance ≈-equiv : IsEquivalence _≈_

    p   : I → L
    _∧_ : L → L → L
    _∨_ : L → L → L
    ⊤   : L
    ⊥   : L

    isLattice : IsLattice L _≈_ _∧_ _∨_ ⊤ ⊥

  open IsLattice isLattice public

  left-dist-∧ = dist-∧

  right-dist-∧ : ∀ {φ ψ κ} → (φ ∨ ψ) ∧ κ ≈ (φ ∧ κ) ∨ (ψ ∧ κ)
  right-dist-∧ {φ} {ψ} {κ} = begin
                               (φ ∨ ψ) ∧ κ       ≈⟨ comm-∧ ⟩
                               κ ∧ (φ ∨ ψ)       ≈⟨ left-dist-∧ ⟩
                               (κ ∧ φ) ∨ (κ ∧ ψ) ≈⟨ cong-∨ comm-∧ comm-∧ ⟩
                               (φ ∧ κ) ∨ (ψ ∧ κ) ∎

  left-unit-∧ = unit-∧

  right-unit-∧ : ∀ {φ} → φ ∧ ⊤ ≈ φ
  right-unit-∧ {φ} = begin
                       φ ∧ ⊤ ≈⟨ comm-∧ ⟩
                       ⊤ ∧ φ ≈⟨ left-unit-∧ ⟩
                       φ ∎

  left-unit-∨ = unit-∨

  right-unit-∨ : ∀ {φ} → φ ∨ ⊥ ≈ φ
  right-unit-∨ {φ} = begin
                       φ ∨ ⊥ ≈⟨ comm-∨ ⟩
                       ⊥ ∨ φ ≈⟨ left-unit-∨ ⟩
                       φ ∎

  left-zero-∧ : ∀ {φ} → ⊥ ∧ φ ≈ ⊥
  left-zero-∧ {φ} = begin
                      ⊥ ∧ φ       ≈⟨ cong-∧ refl (sym unit-∨) ⟩
                      ⊥ ∧ (⊥ ∨ φ) ≈⟨ absp-∧ ⟩
                      ⊥ ∎

  right-zero-∧ : ∀ {φ} → φ ∧ ⊥ ≈ ⊥
  right-zero-∧ {φ} = begin
                       φ ∧ ⊥ ≈⟨ comm-∧ ⟩
                       ⊥ ∧ φ ≈⟨ left-zero-∧ ⟩
                       ⊥ ∎

‖_‖₀ = Lattice.L
p^ = Lattice.p
∧-syntax = Lattice._∧_
syntax ∧-syntax L φ ψ = φ ∧[ L ] ψ
∨-syntax = Lattice._∨_
syntax ∨-syntax L φ ψ = φ ∨[ L ] ψ
infix 19 ≈-syntax
≈-syntax = Lattice._≈_
syntax ≈-syntax L φ ψ = φ ≈[ L ] ψ
⊤^ = Lattice.⊤
⊥^ = Lattice.⊥

record Hom (L M : Lattice) : Set where
  field
    f : ‖ L ‖₀ → ‖ M ‖₀

    pres-≈ : ∀ {φ ψ} → φ ≈[ L ] ψ → f φ ≈[ M ] f ψ
    pres-p : ∀ {i}   → f (p^ L i) ≈[ M ] p^ M i
    pres-∧ : ∀ {φ ψ} → f (φ ∧[ L ] ψ) ≈[ M ] f φ ∧[ M ] f ψ
    pres-∨ : ∀ {φ ψ} → f (φ ∨[ L ] ψ) ≈[ M ] f φ ∨[ M ] f ψ
    pres-⊤ : f (⊤^ L) ≈[ M ] ⊤^ M
    pres-⊥ : f (⊥^ L) ≈[ M ] ⊥^ M

‖_‖₁ = Hom.f

id : {L : Lattice} → Hom L L
id {L} = let open Lattice L using (≈-equiv) in
         record
           { f      = λ φ → φ
           ; pres-≈ = λ φ≈ψ → φ≈ψ
           ; pres-p = refl
           ; pres-∧ = refl
           ; pres-∨ = refl
           ; pres-⊤ = refl
           ; pres-⊥ = refl
           }

_∘_ : {L M N : Lattice} → Hom M N → Hom L M → Hom L N
_∘_ {L} {M} {N} h h' = let open Lattice N using (≈-equiv) in
                       record
                         { f      = λ φ → ‖ h ‖₁ (‖ h' ‖₁ φ)
                         ; pres-≈ = λ φ≈ψ → h .Hom.pres-≈ (h' .Hom.pres-≈ φ≈ψ)
                         ; pres-p = λ {i} →
                                    begin
                                    ‖ h ‖₁ (‖ h' ‖₁ (p^ L i)) ≈⟨ h .Hom.pres-≈ (h' .Hom.pres-p) ⟩
                                    ‖ h ‖₁ (p^ M i)           ≈⟨ h .Hom.pres-p ⟩
                                    p^ N i ∎
                         ; pres-∧ = λ {φ} {ψ} →
                                    begin
                                      ‖ h ‖₁ (‖ h' ‖₁ (φ ∧[ L ] ψ))       ≈⟨ h .Hom.pres-≈ (h' .Hom.pres-∧) ⟩
                                      ‖ h ‖₁ (‖ h' ‖₁ φ ∧[ M ] ‖ h' ‖₁ ψ) ≈⟨ h .Hom.pres-∧ ⟩
                                      ‖ h ‖₁ (‖ h' ‖₁ φ) ∧[ N ] ‖ h ‖₁ (‖ h' ‖₁ ψ) ∎
                         ; pres-∨ = λ {φ} {ψ} →
                                    begin
                                      ‖ h ‖₁ (‖ h' ‖₁ (φ ∨[ L ] ψ))       ≈⟨ h .Hom.pres-≈ (h' .Hom.pres-∨) ⟩
                                      ‖ h ‖₁ (‖ h' ‖₁ φ ∨[ M ] ‖ h' ‖₁ ψ) ≈⟨ h .Hom.pres-∨ ⟩
                                      ‖ h ‖₁ (‖ h' ‖₁ φ) ∨[ N ] ‖ h ‖₁ (‖ h' ‖₁ ψ) ∎
                         ; pres-⊤ = begin
                                      ‖ h ‖₁ (‖ h' ‖₁ (⊤^ L)) ≈⟨ h .Hom.pres-≈ (h' .Hom.pres-⊤) ⟩
                                      ‖ h ‖₁ (⊤^ M)           ≈⟨ h .Hom.pres-⊤ ⟩
                                      ⊤^ N ∎
                         ; pres-⊥ = begin
                                      ‖ h ‖₁ (‖ h' ‖₁ (⊥^ L)) ≈⟨ h .Hom.pres-≈ (h' .Hom.pres-⊥) ⟩
                                      ‖ h ‖₁ (⊥^ M)           ≈⟨ h .Hom.pres-⊥ ⟩
                                      ⊥^ N ∎
                         }

data Term : Set where
  p    : (i   : I)    → Term
  _/\_ : (φ ψ : Term) → Term
  _\/_ : (φ ψ : Term) → Term
  true : Term
  fals : Term

infix 19 _conv_
data _conv_ : Term → Term → Set where
  conv-refl : ∀ {φ}         → φ conv φ
  conv-symm : ∀ {φ ψ}       → φ conv ψ → ψ conv φ
  conv-tran : ∀ {φ ψ κ}     → φ conv ψ → ψ conv κ → φ conv κ
  cong-∧    : ∀ {φ φ' ψ ψ'} → φ conv φ' → ψ conv ψ' → φ /\ ψ conv φ' /\ ψ'
  cong-∨    : ∀ {φ φ' ψ ψ'} → φ conv φ' → ψ conv ψ' → φ \/ ψ conv φ' \/ ψ'
  assc-∧    : ∀ {φ ψ κ}     → (φ /\ ψ) /\ κ conv φ /\ (ψ /\ κ)
  assc-∨    : ∀ {φ ψ κ}     → (φ \/ ψ) \/ κ conv φ \/ (ψ \/ κ)
  comm-∧    : ∀ {φ ψ}       → φ /\ ψ conv ψ /\ φ
  comm-∨    : ∀ {φ ψ}       → φ \/ ψ conv ψ \/ φ
  absp-∧    : ∀ {φ ψ}       → φ /\ (φ \/ ψ) conv φ
  absp-∨    : ∀ {φ ψ}       → φ \/ (φ /\ ψ) conv φ
  dist-∧    : ∀ {φ ψ κ}     → φ /\ (ψ \/ κ) conv (φ /\ ψ) \/ (φ /\ κ)
  dist-∨    : ∀ {φ ψ κ}     → φ \/ (ψ /\ κ) conv (φ \/ ψ) /\ (φ \/ κ)
  unit-∧    : ∀ {φ}         → true /\ φ conv φ
  unit-∨    : ∀ {φ}         → fals \/ φ conv φ

Initial : Lattice
Initial = record
            { L         = Term
            ; _≈_       = _conv_
            ; ≈-equiv   = record { refl = conv-refl ; sym = conv-symm ; trans = conv-tran }
            ; p         = p
            ; _∧_       = _/\_
            ; _∨_       = _\/_
            ; ⊤         = true
            ; ⊥         = fals
            ; isLattice = record
                            { cong-∧ = cong-∧
                            ; cong-∨ = cong-∨
                            ; assc-∧ = assc-∧
                            ; assc-∨ = assc-∨
                            ; comm-∧ = comm-∧
                            ; comm-∨ = comm-∨
                            ; absp-∧ = absp-∧
                            ; absp-∨ = absp-∨
                            ; dist-∧ = dist-∧
                            ; dist-∨ = dist-∨
                            ; unit-∧ = unit-∧
                            ; unit-∨ = unit-∨
                            }
            }

open import Data.List
open import Data.List.Properties

private
  open Lattice Initial using (≈-equiv)

  reify-clause : List I → Term
  reify-clause []               = true
  reify-clause (i ∷ [])         = p i
  reify-clause (i ∷ is@(_ ∷ _)) = p i /\ reify-clause is

  reify-clause-clause : ∀ (i : I) (is : List I) → reify-clause (i ∷ is) conv p i /\ reify-clause is
  reify-clause-clause i []       = sym (Lattice.right-unit-∧ Initial)
  reify-clause-clause i (j ∷ js) = refl

  ‖reify‖₁ : List (List I) → Term
  ‖reify‖₁ []               = fals
  ‖reify‖₁ (c ∷ [])         = reify-clause c
  ‖reify‖₁ (c ∷ cs@(_ ∷ _)) = reify-clause c \/ ‖reify‖₁ cs

  ‖reify‖₁-clause : ∀ (c : List I) (cs : List (List I)) → ‖reify‖₁ (c ∷ cs) conv reify-clause c \/ ‖reify‖₁ cs
  ‖reify‖₁-clause c []       = sym (Lattice.right-unit-∨ Initial)
  ‖reify‖₁-clause c (d ∷ ds) = refl

  join = _++_

  pres-join : ∀ (cs ds : List (List I)) → ‖reify‖₁ (join cs ds) conv ‖reify‖₁ cs \/ ‖reify‖₁ ds
  pres-join []       ds = begin
                            ‖reify‖₁ ds ≈⟨ sym unit-∨ ⟩
                            fals \/ ‖reify‖₁ ds ∎
  pres-join (c ∷ cs) ds = begin
                            ‖reify‖₁ (join (c ∷ cs) ds)                    ≈⟨ refl ⟩
                            ‖reify‖₁ (c ∷ join cs ds)                      ≈⟨ ‖reify‖₁-clause c (join cs ds) ⟩
                            reify-clause c \/ ‖reify‖₁ (join cs ds)        ≈⟨ cong-∨ refl (pres-join cs ds) ⟩
                            reify-clause c \/ (‖reify‖₁ cs \/ ‖reify‖₁ ds) ≈⟨ sym assc-∨ ⟩
                            (reify-clause c \/ ‖reify‖₁ cs) \/ ‖reify‖₁ ds ≈⟨ cong-∨ (sym (‖reify‖₁-clause c cs)) refl ⟩
                            ‖reify‖₁ (c ∷ cs) \/ ‖reify‖₁ ds ∎

  meet-atom : I → List (List I) → List (List I)
  meet-atom i []       = []
  meet-atom i (d ∷ ds) = (i ∷ d) ∷ meet-atom i ds

  meet-clause : List I → List (List I) → List (List I)
  meet-clause []       ds = ds
  meet-clause (i ∷ is) ds = meet-atom i (meet-clause is ds)

  meet : List (List I) → List (List I) → List (List I)
  meet []       ds = []
  meet (c ∷ cs) ds = join (meet-clause c ds) (meet cs ds)

  pres-meet-atom : ∀ {i ds} → ‖reify‖₁ (meet-atom i ds) conv p i /\ ‖reify‖₁ ds
  pres-meet-atom {i} {[]}     = begin
                                  fals ≈⟨ sym (Lattice.right-zero-∧ Initial) ⟩
                                  p i /\ fals ∎
  pres-meet-atom {i} {d ∷ ds} = begin
                                  ‖reify‖₁ (meet-atom i (d ∷ ds))                      ≈⟨ refl ⟩
                                  ‖reify‖₁ ((i ∷ d) ∷ meet-atom i ds)                  ≈⟨ ‖reify‖₁-clause (i ∷ d) (meet-atom i ds) ⟩
                                  reify-clause (i ∷ d) \/ ‖reify‖₁ (meet-atom i ds)    ≈⟨ cong-∨ (reify-clause-clause i d) refl ⟩
                                  (p i /\ reify-clause d) \/ ‖reify‖₁ (meet-atom i ds) ≈⟨ cong-∨ refl (pres-meet-atom {ds = ds}) ⟩
                                  (p i /\ reify-clause d) \/ (p i /\ ‖reify‖₁ ds)      ≈⟨ sym (Lattice.left-dist-∧ Initial) ⟩
                                  p i /\ (reify-clause d \/ ‖reify‖₁ ds)               ≈⟨ cong-∧ refl (sym (‖reify‖₁-clause d ds)) ⟩
                                  p i /\ ‖reify‖₁ (d ∷ ds) ∎

  pres-meet-clause : ∀ {c : List I} {ds : List (List I)} → ‖reify‖₁ (meet-clause c ds) conv reify-clause c /\ ‖reify‖₁ ds
  pres-meet-clause {[]}     {ds} = begin
                                    ‖reify‖₁ (meet-clause [] ds) ≈⟨ refl ⟩
                                    ‖reify‖₁ ds                  ≈⟨ sym unit-∧ ⟩
                                    true /\ ‖reify‖₁ ds          ≈⟨ refl ⟩
                                    reify-clause [] /\ ‖reify‖₁ ds ∎
  pres-meet-clause {i ∷ is} {ds} = begin
                                     ‖reify‖₁ (meet-clause (i ∷ is) ds)         ≈⟨ refl ⟩
                                     ‖reify‖₁ (meet-atom i (meet-clause is ds)) ≈⟨ pres-meet-atom {ds = meet-clause is ds} ⟩
                                     p i /\ (‖reify‖₁ (meet-clause is ds))      ≈⟨ cong-∧ refl pres-meet-clause ⟩
                                     p i /\ (reify-clause is /\ ‖reify‖₁ ds)    ≈⟨ sym assc-∧ ⟩
                                     (p i /\ reify-clause is) /\ ‖reify‖₁ ds    ≈⟨ cong-∧ (sym (reify-clause-clause i is)) refl ⟩
                                     reify-clause (i ∷ is) /\ ‖reify‖₁ ds ∎

  pres-meet : ∀ (cs ds : List (List I)) → ‖reify‖₁ (meet cs ds) conv ‖reify‖₁ cs /\ ‖reify‖₁ ds
  pres-meet []       ds = begin
                            ‖reify‖₁ (meet [] ds) ≈⟨ refl ⟩
                            ‖reify‖₁ []           ≈⟨ refl ⟩
                            fals                  ≈⟨ sym (Lattice.left-zero-∧ Initial) ⟩
                            fals /\ ‖reify‖₁ ds   ≈⟨ refl ⟩
                            ‖reify‖₁ [] /\ ‖reify‖₁ ds ∎
  pres-meet (c ∷ cs) ds = begin
                            ‖reify‖₁ (meet (c ∷ cs) ds)                                     ≈⟨ refl ⟩
                            ‖reify‖₁ (join (meet-clause c ds) (meet cs ds))                 ≈⟨ pres-join (meet-clause c ds) (meet cs ds) ⟩
                            ‖reify‖₁ (meet-clause c ds) \/ ‖reify‖₁ (meet cs ds)            ≈⟨ cong-∨ (pres-meet-clause {ds = ds}) (pres-meet cs ds) ⟩
                            (reify-clause c /\ ‖reify‖₁ ds) \/ (‖reify‖₁ cs /\ ‖reify‖₁ ds) ≈⟨ sym (Lattice.right-dist-∧ Initial) ⟩
                            (reify-clause c \/ ‖reify‖₁ cs) /\ ‖reify‖₁ ds                  ≈⟨ cong-∧ (sym (‖reify‖₁-clause c cs)) refl ⟩
                            ‖reify‖₁ (c ∷ cs) /\ ‖reify‖₁ ds ∎

DNF : Lattice
DNF = record
        { L         = List (List I)
        ; _≈_       = λ cs ds → ‖reify‖₁ cs conv ‖reify‖₁ ds
        ; ≈-equiv   = record { refl = conv-refl ; sym = conv-symm ; trans = conv-tran }
        ; p         = λ i → [ [ i ] ]
        ; _∧_       = meet
        ; _∨_       = join
        ; ⊤         = [ [] ]
        ; ⊥         = []
        ; isLattice = record
                        { cong-∧ = λ {φ} {φ'} {ψ} {ψ'} φ≈φ' ψ≈ψ' →
                                   begin
                                     ‖reify‖₁ (meet φ ψ)        ≈⟨ pres-meet φ ψ ⟩
                                     ‖reify‖₁ φ  /\ ‖reify‖₁ ψ  ≈⟨ cong-∧ φ≈φ' ψ≈ψ' ⟩
                                     ‖reify‖₁ φ' /\ ‖reify‖₁ ψ' ≈⟨ sym (pres-meet φ' ψ') ⟩
                                     ‖reify‖₁ (meet φ' ψ') ∎
                        ; cong-∨ = λ {φ} {φ'} {ψ} {ψ'} φ≈φ' ψ≈ψ' →
                                   begin
                                     ‖reify‖₁ (join φ ψ)        ≈⟨ pres-join φ ψ ⟩
                                     ‖reify‖₁ φ  \/ ‖reify‖₁ ψ  ≈⟨ cong-∨ φ≈φ' ψ≈ψ' ⟩
                                     ‖reify‖₁ φ' \/ ‖reify‖₁ ψ' ≈⟨ sym (pres-join φ' ψ') ⟩
                                     ‖reify‖₁ (join φ' ψ') ∎
                        ; assc-∧ = λ {φ} {ψ} {κ} →
                                   begin
                                     ‖reify‖₁ (meet (meet φ ψ) κ)             ≈⟨ pres-meet (meet φ ψ) κ ⟩
                                     ‖reify‖₁ (meet φ ψ) /\ ‖reify‖₁ κ        ≈⟨ cong-∧ (pres-meet φ ψ) refl ⟩
                                     (‖reify‖₁ φ /\ ‖reify‖₁ ψ) /\ ‖reify‖₁ κ ≈⟨ assc-∧ ⟩
                                     ‖reify‖₁ φ /\ (‖reify‖₁ ψ /\ ‖reify‖₁ κ) ≈⟨ cong-∧ refl (sym (pres-meet ψ κ)) ⟩
                                     ‖reify‖₁ φ /\ (‖reify‖₁ (meet ψ κ))      ≈⟨ sym (pres-meet φ _) ⟩
                                     ‖reify‖₁ (meet φ (meet ψ κ)) ∎
                        ; assc-∨ = λ {φ} {ψ} {κ} →
                                   begin
                                     ‖reify‖₁ (join (join φ ψ) κ)             ≈⟨ pres-join (join φ ψ) κ ⟩
                                     ‖reify‖₁ (join φ ψ) \/ ‖reify‖₁ κ        ≈⟨ cong-∨ (pres-join φ ψ) refl ⟩
                                     (‖reify‖₁ φ \/ ‖reify‖₁ ψ) \/ ‖reify‖₁ κ ≈⟨ assc-∨ ⟩
                                     ‖reify‖₁ φ \/ (‖reify‖₁ ψ \/ ‖reify‖₁ κ) ≈⟨ cong-∨ refl (sym (pres-join ψ κ)) ⟩
                                     ‖reify‖₁ φ \/ (‖reify‖₁ (join ψ κ))      ≈⟨ sym (pres-join φ _) ⟩
                                     ‖reify‖₁ (join φ (join ψ κ)) ∎
                        ; comm-∧ = λ {φ} {ψ} →
                                   begin
                                     ‖reify‖₁ (meet φ ψ)      ≈⟨ pres-meet φ ψ ⟩
                                     ‖reify‖₁ φ /\ ‖reify‖₁ ψ ≈⟨ comm-∧ ⟩
                                     ‖reify‖₁ ψ /\ ‖reify‖₁ φ ≈⟨ sym (pres-meet ψ φ) ⟩
                                     ‖reify‖₁ (meet ψ φ) ∎
                        ; comm-∨ = λ {φ} {ψ} →
                                   begin
                                     ‖reify‖₁ (join φ ψ)      ≈⟨ pres-join φ ψ ⟩
                                     ‖reify‖₁ φ \/ ‖reify‖₁ ψ ≈⟨ comm-∨ ⟩
                                     ‖reify‖₁ ψ \/ ‖reify‖₁ φ ≈⟨ sym (pres-join ψ φ) ⟩
                                     ‖reify‖₁ (join ψ φ) ∎
                        ; absp-∧ = λ {φ} {ψ} →
                                   begin
                                     ‖reify‖₁ (meet φ (join φ ψ))             ≈⟨ pres-meet φ _ ⟩
                                     ‖reify‖₁ φ /\ ‖reify‖₁ (join φ ψ)        ≈⟨ cong-∧ refl (pres-join φ ψ) ⟩
                                     ‖reify‖₁ φ /\ (‖reify‖₁ φ \/ ‖reify‖₁ ψ) ≈⟨ absp-∧ ⟩
                                     ‖reify‖₁ φ ∎
                        ; absp-∨ = λ {φ} {ψ} →
                                   begin
                                     ‖reify‖₁ (join φ (meet φ ψ))             ≈⟨ pres-join φ _ ⟩
                                     ‖reify‖₁ φ \/ ‖reify‖₁ (meet φ ψ)        ≈⟨ cong-∨ refl (pres-meet φ ψ) ⟩
                                     ‖reify‖₁ φ \/ (‖reify‖₁ φ /\ ‖reify‖₁ ψ) ≈⟨ absp-∨ ⟩
                                     ‖reify‖₁ φ ∎
                        ; dist-∧ = λ {φ} {ψ} {κ} →
                                   begin
                                     ‖reify‖₁ (meet φ (join ψ κ))                             ≈⟨ pres-meet φ _ ⟩
                                     ‖reify‖₁ φ /\ ‖reify‖₁ (join ψ κ)                        ≈⟨ cong-∧ refl (pres-join ψ κ) ⟩
                                     ‖reify‖₁ φ /\ (‖reify‖₁ ψ \/ ‖reify‖₁ κ)                 ≈⟨ dist-∧ ⟩
                                     (‖reify‖₁ φ /\ ‖reify‖₁ ψ) \/ (‖reify‖₁ φ /\ ‖reify‖₁ κ) ≈⟨ cong-∨ (sym (pres-meet φ ψ)) (sym (pres-meet φ κ)) ⟩
                                     ‖reify‖₁ (meet φ ψ) \/ ‖reify‖₁ (meet φ κ)               ≈⟨ sym (pres-join (meet φ ψ) (meet φ κ)) ⟩
                                     ‖reify‖₁ (join (meet φ ψ) (meet φ κ)) ∎
                        ; dist-∨ = λ {φ} {ψ} {κ} →
                                   begin
                                     ‖reify‖₁ (join φ (meet ψ κ))                             ≈⟨ pres-join φ _ ⟩
                                     ‖reify‖₁ φ \/ ‖reify‖₁ (meet ψ κ)                        ≈⟨ cong-∨ refl (pres-meet ψ κ) ⟩
                                     ‖reify‖₁ φ \/ (‖reify‖₁ ψ /\ ‖reify‖₁ κ)                 ≈⟨ dist-∨ ⟩
                                     (‖reify‖₁ φ \/ ‖reify‖₁ ψ) /\ (‖reify‖₁ φ \/ ‖reify‖₁ κ) ≈⟨ cong-∧ (sym (pres-join φ ψ)) (sym (pres-join φ κ)) ⟩
                                     ‖reify‖₁ (join φ ψ) /\ ‖reify‖₁ (join φ κ)               ≈⟨ sym (pres-meet (join φ ψ) (join φ κ)) ⟩
                                     ‖reify‖₁ (meet (join φ ψ) (join φ κ)) ∎
                        ; unit-∧ = λ {φ} →
                                   begin
                                     ‖reify‖₁ (meet [ [] ] φ)                       ≈⟨ refl ⟩
                                     ‖reify‖₁ (join (meet-clause [] φ) (meet [] φ)) ≈⟨ refl ⟩
                                     ‖reify‖₁ (join φ [])                           ≈⟨ subst (λ ψ → ‖reify‖₁ (join φ []) conv ‖reify‖₁ ψ) (++-identityʳ φ) refl ⟩
                                     ‖reify‖₁ φ ∎
                        ; unit-∨ = λ {φ} →
                                   begin
                                     ‖reify‖₁ (join [] φ) ≈⟨ refl ⟩
                                     ‖reify‖₁ φ ∎
                        }
        }

reify : Hom DNF Initial
reify = record
          { f      = ‖reify‖₁
          ; pres-≈ = λ φ≈ψ → φ≈ψ
          ; pres-p = λ {i} →
                     begin
                       ‖reify‖₁ [ [ i ] ] ≈⟨ refl ⟩
                       reify-clause [ i ] ≈⟨ refl ⟩
                       p i ∎
          ; pres-∧ = λ {φ} {ψ} → pres-meet φ ψ
          ; pres-∨ = λ {φ} {ψ} → pres-join φ ψ
          ; pres-⊤ = begin
                       ‖reify‖₁ [ [] ] ≈⟨ refl ⟩
                       reify-clause [] ≈⟨ refl ⟩
                       true ∎
          ; pres-⊥ = begin
                       ‖reify‖₁ [] ≈⟨ refl ⟩
                       fals ∎
          }

module _ (L : Lattice) where
  open Lattice L using (≈-equiv)

  private
    F : ‖ Initial ‖₀ → ‖ L ‖₀
    F (p i)    = p^ L i
    F (φ /\ ψ) = F φ ∧[ L ] F ψ
    F (φ \/ ψ) = F φ ∨[ L ] F ψ
    F true     = ⊤^ L
    F fals     = ⊥^ L

  Existence : Hom Initial L
  Existence .Hom.f                          = F
  Existence .Hom.pres-≈ conv-refl           = refl
  Existence .Hom.pres-≈ (conv-symm φ≈ψ)     = sym (Existence .Hom.pres-≈ φ≈ψ)
  Existence .Hom.pres-≈ (conv-tran φ≈ψ ψ≈κ) = trans (Existence .Hom.pres-≈ φ≈ψ) (Existence .Hom.pres-≈ ψ≈κ)
  Existence .Hom.pres-≈ (cong-∧ φ≈φ' ψ≈ψ')  = L .Lattice.cong-∧ (Existence .Hom.pres-≈ φ≈φ') (Existence .Hom.pres-≈ ψ≈ψ')
  Existence .Hom.pres-≈ (cong-∨ φ≈φ' ψ≈ψ')  = L .Lattice.cong-∨ (Existence .Hom.pres-≈ φ≈φ') (Existence .Hom.pres-≈ ψ≈ψ')
  Existence .Hom.pres-≈ assc-∧              = L .Lattice.assc-∧
  Existence .Hom.pres-≈ assc-∨              = L .Lattice.assc-∨
  Existence .Hom.pres-≈ comm-∧              = L .Lattice.comm-∧
  Existence .Hom.pres-≈ comm-∨              = L .Lattice.comm-∨
  Existence .Hom.pres-≈ absp-∧              = L .Lattice.absp-∧
  Existence .Hom.pres-≈ absp-∨              = L .Lattice.absp-∨
  Existence .Hom.pres-≈ dist-∧              = L .Lattice.dist-∧
  Existence .Hom.pres-≈ dist-∨              = L .Lattice.dist-∨
  Existence .Hom.pres-≈ unit-∧              = L .Lattice.unit-∧
  Existence .Hom.pres-≈ unit-∨              = L .Lattice.unit-∨
  Existence .Hom.pres-p                     = refl
  Existence .Hom.pres-∧                     = refl
  Existence .Hom.pres-∨                     = refl
  Existence .Hom.pres-⊤                     = refl
  Existence .Hom.pres-⊥                     = refl

  private
    module _ (h : Hom Initial L) where
      h≈Initial : (φ : ‖ Initial ‖₀) → ‖ h ‖₁ φ ≈[ L ] ‖ Existence ‖₁ φ
      h≈Initial (p i)    = h .Hom.pres-p
      h≈Initial (φ /\ ψ) = begin
                             ‖ h ‖₁ (φ /\ ψ)                          ≈⟨ h .Hom.pres-∧ ⟩
                             ‖ h ‖₁ φ ∧[ L ] ‖ h ‖₁ ψ                 ≈⟨ L .Lattice.cong-∧ (h≈Initial φ) (h≈Initial ψ) ⟩
                             ‖ Existence ‖₁ φ ∧[ L ] ‖ Existence ‖₁ ψ ≈⟨ refl ⟩
                             ‖ Existence ‖₁ (φ /\ ψ) ∎
      h≈Initial (φ \/ ψ) = begin
                             ‖ h ‖₁ (φ \/ ψ)                          ≈⟨ h .Hom.pres-∨ ⟩
                             ‖ h ‖₁ φ ∨[ L ] ‖ h ‖₁ ψ                 ≈⟨ L .Lattice.cong-∨ (h≈Initial φ) (h≈Initial ψ) ⟩
                             ‖ Existence ‖₁ φ ∨[ L ] ‖ Existence ‖₁ ψ ≈⟨ refl ⟩
                             ‖ Existence ‖₁ (φ \/ ψ) ∎
      h≈Initial true     = begin
                             ‖ h ‖₁ true ≈⟨ h .Hom.pres-⊤ ⟩
                             ⊤^ L        ≈⟨ refl ⟩
                             ‖ Existence ‖₁ true ∎
      h≈Initial fals     = begin
                             ‖ h ‖₁ fals ≈⟨ h .Hom.pres-⊥ ⟩
                             ⊥^ L        ≈⟨ refl ⟩
                             ‖ Existence ‖₁ fals ∎

  module _ (h  : Hom Initial L) (h' : Hom Initial L) where
    Uniqueness : {φ : ‖ Initial ‖₀} → ‖ h ‖₁ φ ≈[ L ] ‖ h' ‖₁ φ
    Uniqueness {φ} = begin
                       ‖ h ‖₁ φ         ≈⟨ h≈Initial h φ ⟩
                       ‖ Existence ‖₁ φ ≈⟨ sym (h≈Initial h' φ) ⟩
                       ‖ h' ‖₁ φ ∎

norm : Term → Term
norm = ‖ reify ∘ Existence DNF ‖₁

norm-correct : ∀ {φ} → norm φ conv φ
norm-correct {φ} = Uniqueness Initial (reify ∘ Existence DNF) id

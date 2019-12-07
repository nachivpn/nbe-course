----------------------
-- Weak normalization
----------------------

module WeakNorm where

open import CLT

open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂ ; subst)
  renaming (refl to ≡-refl ; trans to ≡-trans ; sym to ≡-sym)

private
  variable
    a b c : Ty

open Norm
open Soundness
open Completeness
open Utilities

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

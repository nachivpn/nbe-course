-----------------------------------------------
-- Proving consistency using logical relations
-----------------------------------------------

module ConsistencyLR where

open import CLT

private
  variable
    a b c : Ty

open Norm
open Soundness
open Completeness
open Utilities

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

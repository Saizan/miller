module RenOrn where

open import Data.Product.Extras
open import Relation.Binary.PropositionalEquality

open import Injection
open import Lists

open import Syntax

-- RTm i t is the inductive version of the type Σ (Tm Sg G D T) λ s → ren i s ≡ t
-- In the language of "Ornamental Algebras, Algebraic Ornaments" RTm i t
-- would be the latter and we'd get both the type and the
-- remember/forget conversions for free by expressing ren i as a fold.
mutual
  data RTm {Sg : Ctx}{G : MCtx}{D : Ctx}{K : Ctx} (i : Inj D K) : {T : Ty} → Tm Sg G K T → Set where
    con : {Ss : Fwd Ty}{B : Base} →
          (c : Sg ∋ (Ss ->> B)) → ∀ {tms} → (RTms i {Ss} tms) → RTm i {(! B)} (con c tms)
    fun : {Ss : Bwd Ty}{B : Base} →
              (u : G ∋ (B <<- Ss)) → (j : Inj Ss D) → ∀ {k} → (i ∘i j) ≡ k → RTm i {(! B)} (fun u k)
    var : forall {Ss B} → (v : D ∋ (Ss ->> B)) → ∀ {x} → (i $ v) ≡ x → ∀ {tms} → RTms i {Ss} tms → RTm i {(! B)} (var x tms)
    lam : {S : Ty}{Ss : Fwd Ty}{B : Base} → ∀ {b} →
          RTm (cons i) {(Ss ->> B)} b → RTm i {(S :> Ss ->> B)} (lam b)

  data RTms {Sg : Ctx}{G : MCtx}{D K : Ctx}(i : Inj D K) : {Ss : Fwd Ty} → Tms Sg G K Ss → Set where
    [] : RTms i { !> } []
    _∷_ : {S : Ty}{Ss : Fwd Ty} → ∀ {x xs} →
           RTm i {S} x → RTms i {Ss} xs → RTms i {(S :> Ss)} (x ∷ xs)

mutual
  forget : ∀ {Sg G D D0}{T : Ty} → {i : Inj D D0} → {t : Tm Sg G D0 T} → (x : RTm i t) → Σ (Tm Sg G D T) \ s → ren i s ≡ t
  forget (con c x) = mapΣ (con c) (cong (con c)) (forgets x)
  forget (fun u j eq) = fun u j , cong (fun u) eq
  forget {i = i} (var v refl x₂) = mapΣ (var v) (cong (var (i $ v))) (forgets x₂)
  forget (lam x) = mapΣ lam (cong lam) (forget x) 

  forgets : ∀ {Sg G D D0}{Ts} → {i : Inj D D0} → {t : Tms Sg G D0 Ts} → (x : RTms i t) → Σ (Tms Sg G D Ts) \ s → rens i s ≡ t
  forgets [] = [] , refl
  forgets (t ∷ ts) = mapΣ₂ _∷_ (cong₂ _∷_) (forget t) (forgets ts)

mutual
  remember : ∀ {Sg G D D0}{T : Ty} → (i : Inj D D0) → (s : Tm Sg G D T) → Σ (RTm i (ren i s)) \ rt -> proj₁ (forget rt) ≡ s
  remember i (con c ts) = mapΣ (con c) (cong (con c)) (remembers i ts)
  remember i (fun u j) = fun u j refl , refl
  remember i (var x ts) = mapΣ (var x refl) (cong (var x)) (remembers i ts)
  remember i (lam s) = mapΣ lam (cong lam) (remember (cons i) s)

  remembers : ∀ {Sg G D D0}{T} → (i : Inj D D0) → (s : Tms Sg G D T) → Σ (RTms i (rens i s)) \ rt -> proj₁ (forgets rt) ≡ s
  remembers i [] = [] , refl
  remembers i (t ∷ ts) = mapΣ₂ _∷_ (cong₂ _∷_) (remember i t) (remembers i ts)


-- One advantage of this representation is the good interaction with
-- pattern matching as shown here in unique, in fact since they are
-- indexed by t once we pattern match on x Agda can tell that y must
-- have the same constructor and excludes the other cases for us.
mutual
  unique : ∀ {Sg G D D0}{T : Ty} → {i : Inj D D0} → {t : Tm Sg G D0 T} → (x y : RTm i t) → x ≡ y
  unique (con c x) (con .c x₁) = cong (con c) (uniques x x₁)
  unique {i = i} (fun u j eq1)(fun .u j₁ eq2) with  ∘i-inj i j j₁ (trans eq1 (sym eq2)) | eq1 | eq2
  unique {i = i} (fun u .j₁ eq1) (fun .u j₁ eq2) | refl | refl | refl = refl
  unique {i = i} (var v x₁ x₂) (var v₁ x₃ x₄) with injective i v v₁ (trans x₁ (sym x₃)) 
  unique (var .v₁ refl x₂) (var v₁ e x₄) | refl with e 
  ... | refl = cong (var v₁ refl) (uniques x₂ x₄)
  unique (lam x) (lam y) = cong lam (unique x y)
  
  uniques : ∀ {Sg G D D0}{Ss : Fwd Ty} → {i : Inj D D0} → {t : Tms Sg G D0 Ss} → (x y : RTms i t) → x ≡ y
  uniques [] [] = refl
  uniques (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (unique x y) (uniques xs ys)

ren-inj : ∀ {Sg G D D0}{T : Ty} → (i : Inj D D0) → (s t : Tm Sg G D T) -> ren i s ≡ ren i t -> s ≡ t
ren-inj i s t eq with remember i s | remember i t
... | (rs , fogrs≡s) | (rt , fogrt≡t) rewrite eq = trans (sym fogrs≡s) (trans (cong (λ r → proj₁ (forget r)) (unique rs rt)) fogrt≡t)


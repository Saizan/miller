module Syntax.RenOrn where

open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Bool

open import Support.Product

open import Injection

open import Syntax.Type

-- RTm i t is the inductive version of Σ (Tm Sg G D T) λ s → ren i s ≡ t
-- In the language of "Ornamental Algebras, Algebraic Ornaments" RTm i t
-- would be the latter and we'd get both RTm and the remember/forget 
-- conversions for free by expressing ren i as a fold.
mutual
  data RTm {b : Bool} {Sg : Ctx}{G : MCtx}{D : Ctx}{K : Ctx} (i : Inj D K) : {T : Ty} → Tm< b > Sg G K T → Set where
    con : {Ss : Fwd Ty}{B : Base} →
          (c : Sg ∋ (Ss ->> B)) → ∀ {tms} → (RTms i {Ss} tms) → RTm i {(! B)} (con c tms)
    mvar : {Ss : Bwd Ty}{B : Base} →
              (u : G ∋ (B <<- Ss)) → ∀ {k} → RArgs b i k → RTm i {(! B)} (mvar u k)
    var : forall {Ss B} → (v : D ∋ (Ss ->> B)) → ∀ {x} → (i $ v) ≡ x → ∀ {tms} → RTms i {Ss} tms → RTm i {(! B)} (var x tms)
    lam : {S : Ty}{Ss : Fwd Ty}{B : Base} → ∀ {b} →
          RTm (cons i) {(Ss ->> B)} b → RTm i {(S :> Ss ->> B)} (lam b)

  data RTms {b : Bool}{Sg : Ctx}{G : MCtx}{D K : Ctx}(i : Inj D K) : {Ss : Fwd Ty} → Tms< b > Sg G K Ss → Set where
    [] : RTms i { !> } []
    _∷_ : {S : Ty}{Ss : Fwd Ty} → ∀ {x xs} →
           RTm i {S} x → RTms i {Ss} xs → RTms i {(S :> Ss)} (x ∷ xs)

  RArgs : (b : Bool){Sg : Ctx}{G : MCtx}{D K : Ctx}(i : Inj D K) -> {Ss : Fwd Ty} → Args b Sg G K Ss → Set
  RArgs true  i k  = ∃ (λ j → i ∘i j ≡ k)
  RArgs false i xs = RTms i xs

_⁻¹_ : ∀ {b}{Sg : Ctx}{G : MCtx}{D : Ctx}{K : Ctx} (i : Inj D K) {T} → Term< b > Sg G K T → Set
_⁻¹_ i {inj₁ _} t  = RTm i t
_⁻¹_ i {inj₂ _} ts = RTms i ts

mutual
  forget : ∀ {b Sg G D D0}{T : Ty} → {i : Inj D D0} → {t : Tm< b > Sg G D0 T} → (x : RTm i t) → Σ (Tm< b > Sg G D T) \ s → ren i s ≡ t
  forget         (con c x)         = mapΣ (con c) (cong (con c)) (forgets x)
  forget {true}  (mvar u (j , eq)) = mvar u j , cong (mvar u) eq
  forget {false} (mvar u ts)       = mapΣ (mvar u) (cong (mvar u)) (forgets ts)
  forget {i = i} (var v refl x₂)   = mapΣ (var v) (cong (var (i $ v))) (forgets x₂)
  forget         (lam x)           = mapΣ lam (cong lam) (forget x) 

  forgets : ∀ {b Sg G D D0}{Ts} → {i : Inj D D0} → {t : Tms< b > Sg G D0 Ts} → (x : RTms i t) → Σ (Tms< b > Sg G D Ts) \ s → rens i s ≡ t
  forgets []       = [] , refl
  forgets (t ∷ ts) = mapΣ₂ _∷_ (cong₂ _∷_) (forget t) (forgets ts)

mutual
  remember : ∀ {b Sg G D D0}{T : Ty} → (i : Inj D D0) → (s : Tm< b > Sg G D T) → Σ (RTm i (ren i s)) \ rt -> proj₁ (forget rt) ≡ s
  remember         i (con c ts)  = mapΣ (con c) (cong (con c)) (remembers i ts)
  remember {true}  i (mvar u j)  = mvar u (j , refl) , refl
  remember {false} i (mvar u ts) = mapΣ (mvar u) (cong (mvar u)) (remembers i ts)
  remember         i (var x ts)  = mapΣ (var x refl) (cong (var x)) (remembers i ts)
  remember         i (lam s)     = mapΣ lam (cong lam) (remember (cons i) s)

  remembers : ∀ {b Sg G D D0}{T} → (i : Inj D D0) → (s : Tms< b > Sg G D T) → Σ (RTms i (rens i s)) \ rt -> proj₁ (forgets rt) ≡ s
  remembers i []       = [] , refl
  remembers i (t ∷ ts) = mapΣ₂ _∷_ (cong₂ _∷_) (remember i t) (remembers i ts)


-- One advantage of this representation is the good interaction with
-- pattern matching as shown here in unique: since x and y share the
-- index t we don't have to consider the patterns where they are
-- matched against different constructors.
mutual
  unique : ∀ {b Sg G D D0}{T : Ty} → {i : Inj D D0} → {t : Tm< b > Sg G D0 T} → (x y : RTm i t) → x ≡ y
  unique         (con c xs)       (con .c ys)  = cong (con c) (uniques xs ys)
  unique         (lam x)          (lam y)      = cong lam (unique x y)
  unique {false} (mvar u xs)      (mvar .u ys) = cong (mvar u) (uniques xs ys)
  unique {i = i} (var v i$v≡x xs) (var  w i$w≡x ys) with injective i v w (trans i$v≡x (sym i$w≡x))
  unique         (var v i$v≡x xs) (var .v i$w≡x ys)    | refl 
    = cong₂ (λ a b → var v a b) (proof-irrelevance i$v≡x i$w≡x) (uniques xs ys)
  unique {true} {i = i} (mvar u (j , i∘j≡k)) (mvar .u (j₁ , i∘j₁≡k)) with ∘i-inj i j j₁ (trans i∘j≡k (sym i∘j₁≡k))
  unique {true} {i = i} (mvar u (j , i∘j≡k)) (mvar .u (.j , i∘j₁≡k))    | refl 
    = cong (λ e → mvar u (j , e)) (proof-irrelevance i∘j≡k i∘j₁≡k)

  uniques : ∀ {b Sg G D D0}{Ss : Fwd Ty} → {i : Inj D D0} → {t : Tms< b > Sg G D0 Ss} → (x y : RTms i t) → x ≡ y
  uniques []       []       = refl
  uniques (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (unique x y) (uniques xs ys)

ren-inj : ∀ {b Sg G D D0}{T : Ty} → (i : Inj D D0) → (s t : Tm< b > Sg G D T) -> ren i s ≡ ren i t -> s ≡ t
ren-inj i s t eq 
 with remember i s   | remember i t
... | (rs , fogrs≡s) | (rt , fogrt≡t) rewrite eq = trans (sym fogrs≡s) (trans (cong (λ r → proj₁ (forget r)) (unique rs rt)) fogrt≡t)

module Inversion where

open import Data.Product renaming (map to mapΣ)
open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Maybe
open import Category.Monad
import Level
open RawMonad (monad {Level.zero})

open import Injection
open import Lists

open import Syntax
open import Purging

mutual
  data RTm (Sg : Ctx)(G : MCtx)(D : Ctx)(K : Ctx) (i : Inj D K) : (T : Ty) → Tm Sg G K T → Set where
    con : {Ss : Fwd Ty}{B : Base} →
          (c : Sg ∋ (Ss ->> B)) → ∀ {tms} → (RTms Sg G D K i Ss tms) → RTm Sg G D K i (! B) (con c tms)
    fun : {Ss : Bwd Ty}{B : Base} →
              (u : G ∋ (B <<- Ss)) → (j : Inj Ss D) → ∀ {k} → (i ∘i j) ≡ k → RTm Sg G D K i (! B) (fun u k)
    var : forall {Ss B} → (v : D ∋ (Ss ->> B)) → ∀ {x} → (i $ v) ≡ x → ∀ {tms} → RTms Sg G D K i Ss tms → RTm Sg G D K i (! B) (var x tms)
    lam : {S : Ty}{Ss : Fwd Ty}{B : Base} → ∀ {b} →
          RTm Sg G (D <: S) (K <: S) (cons i) (Ss ->> B) b → RTm Sg G D K i (S :> Ss ->> B) (lam b)

  data RTms (Sg : Ctx)(G : MCtx)(D K : Ctx)(i : Inj D K) : (Ss : Fwd Ty) → Tms Sg G K Ss → Set where
    [] : RTms Sg G D K i !> []
    _∷_ : {S : Ty}{Ss : Fwd Ty} → ∀ {x xs} →
           RTm Sg G D K i S x → RTms Sg G D K i Ss xs → RTms Sg G D K i (S :> Ss) (x ∷ xs)

mutual
  unique : ∀ {Sg G D D0}{T : Ty} → {i : Inj D D0} → {t : Tm Sg G D0 T} → (x y : RTm Sg G D D0 i T t) → x ≡ y
  unique (con c x) (con .c x₁) = cong (con c) (uniques x x₁)
  unique {i = i} (fun u j eq1)(fun .u j₁ eq2) with  ∘i-inj i j j₁ (trans eq1 (sym eq2)) | eq1 | eq2
  unique {i = i} (fun u .j₁ eq1) (fun .u j₁ eq2) | refl | refl | refl = refl
  unique {i = i} (var v x₁ x₂) (var v₁ x₃ x₄) with injective i v v₁ (trans x₁ (sym x₃)) 
  unique (var .v₁ refl x₂) (var v₁ e x₄) | refl with e 
  ... | refl = cong (var v₁ refl) (uniques x₂ x₄)
  unique (lam x) (lam y) = cong lam (unique x y)
  
  uniques : ∀ {Sg G D D0}{Ss : Fwd Ty} → {i : Inj D D0} → {t : Tms Sg G D0 Ss} → (x y : RTms Sg G D D0 i Ss t) → x ≡ y
  uniques [] [] = refl
  uniques (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (unique x y) (uniques xs ys)

mutual
  remember : ∀ {Sg G D D0}{T : Ty} → (i : Inj D D0) → (s : Tm Sg G D T) →
             RTm Sg G D D0 i T (ren i s)
  remember i (con c ts) = con c (remembers i ts)
  remember i (fun u j) = fun u j refl
  remember i (var x ts) = var x refl (remembers i ts)
  remember i (lam s) = lam (remember (cons i) s)

  remembers : ∀ {Sg G D D0}{T} → (i : Inj D D0) → (s : Tms Sg G D T) →
             RTms Sg G D D0 i T (rens i s)
  remembers i [] = []
  remembers i (t ∷ s) = (remember i t) ∷ (remembers i s)

mutual
  forget : ∀ {Sg G D D0}{T : Ty} → {i : Inj D D0} → {t : Tm Sg G D0 T} → (x : RTm Sg G D D0 i T t) → Σ (Tm Sg G D T) \ s → ren i s ≡ t
  forget (con c x) = mapΣ (con c) (cong (con c)) (forgets x)
  forget (fun u j eq) = fun u j , cong (fun u) eq
  forget {i = i} (var v refl x₂) = mapΣ (var v) (cong (var (i $ v))) (forgets x₂)
  forget (lam x) = mapΣ lam (cong lam) (forget x) 
  
  forgets : ∀ {Sg G D D0}{Ts} → {i : Inj D D0} → {t : Tms Sg G D0 Ts} → (x : RTms Sg G D D0 i Ts t) → Σ (Tms Sg G D Ts) \ s → rens i s ≡ t
  forgets [] = [] , refl
  forgets (x₁ ∷ x₂) = ((proj₁ (forget x₁)) ∷ (proj₁ (forgets x₂))) , (cong₂ _∷_ (proj₂ (forget x₁)) (proj₂ (forgets x₂)))

mutual
  invertTm' : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tm Sg G D T) → (ρ : MetaRen G G1) → MRProp ρ i t
    → Dec (RTm Sg G1 Ss D i T (sub (toSub ρ) t))
  invertTm' i (con x x₁) r m with invertTm's i x₁ r m
  invertTm' i (con x x₁) r m | yes p = yes (con x p)
  invertTm' i (con x x₁) r m | no ¬p = no (λ {(con .x ys) → ¬p ys})
  invertTm' i (fun u j) r m = yes (fun (proj₁ (proj₂ (r _ u))) (proj₁ m) (proj₂ m))
  invertTm' i (var x x₁) r m with invert (i) x | invertTm's i x₁ r m 
  invertTm' i (var x x₁) r m | yes (y , eq) | yes p₁ = yes (var y eq p₁)
  invertTm' i (var x x₁) r m | yes p | no ¬p = no λ {(var y eq xs) → ¬p xs}
  invertTm' i (var x x₁) r m | no ¬p | q = no λ {(var y eq xs) → ¬p (y , eq)}
  invertTm' i (lam t) r m with invertTm' (cons i) t r m
  invertTm' i (lam t) r m | yes p = yes (lam p)
  invertTm' i (lam t) r m | no ¬p = no (λ {(lam q) → ¬p q})

  invertTm's : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tms Sg G D T) → (ρ : MetaRen G G1) → MRProps ρ i t 
            → Dec (RTms Sg G1 Ss D i T (subs (toSub ρ) t))
  invertTm's i [] r m = yes []
  invertTm's i (x ∷ t) r m with invertTm' i x r (proj₁ m) | invertTm's i t r (proj₂ m)
  invertTm's i (x ∷ t) r m | yes p | yes p₁ = yes (p ∷ p₁)
  invertTm's i (x ∷ t) r m | yes p | no ¬p = no λ {(y ∷ ys) → ¬p ys}
  invertTm's i (x ∷ t) r m | no ¬p | z = no λ {(y ∷ ys) → ¬p y}

invertTm : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tm Sg G D T) → (ρ : MetaRen G G1) → MRProp ρ i t
             → Dec (∃ \ s → ren i s ≡ (sub (toSub ρ) t))
invertTm i t ρ m = Dec.map′ forget (λ p → subst (RTm _ _ _ _ _ _ ) (proj₂ p) (remember i (proj₁ p))) (invertTm' i t ρ m)
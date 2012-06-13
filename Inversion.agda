module Inversion where

open import Data.Product renaming (map to mapΣ)
open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Sum renaming (inj₁ to yes; inj₂ to no)
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
  forget : ∀ {Sg G D D0}{T : Ty} → {i : Inj D D0} → {t : Tm Sg G D0 T} → (x : RTm Sg G D D0 i T t) → Σ (Tm Sg G D T) \ s → ren i s ≡ t
  forget (con c x) = mapΣ (con c) (cong (con c)) (forgets x)
  forget (fun u j eq) = fun u j , cong (fun u) eq
  forget {i = i} (var v refl x₂) = mapΣ (var v) (cong (var (i $ v))) (forgets x₂)
  forget (lam x) = mapΣ lam (cong lam) (forget x) 
  
  forgets : ∀ {Sg G D D0}{Ts} → {i : Inj D D0} → {t : Tms Sg G D0 Ts} → (x : RTms Sg G D D0 i Ts t) → Σ (Tms Sg G D Ts) \ s → rens i s ≡ t
  forgets [] = [] , refl
  forgets (x₁ ∷ x₂) = ((proj₁ (forget x₁)) ∷ (proj₁ (forgets x₂))) , (cong₂ _∷_ (proj₂ (forget x₁)) (proj₂ (forgets x₂)))

mutual
  remember : ∀ {Sg G D D0}{T : Ty} → (i : Inj D D0) → (s : Tm Sg G D T) →
             Σ (RTm Sg G D D0 i T (ren i s)) \ rt -> proj₁ (forget rt) ≡ s
  remember i (con c ts) = mapΣ (con c) (cong (con c)) (remembers i ts)
  remember i (fun u j) = fun u j refl , refl
  remember i (var x ts) = mapΣ (var x refl) (cong (var x)) (remembers i ts)
  remember i (lam s) = mapΣ lam (cong lam) (remember (cons i) s)

  remembers : ∀ {Sg G D D0}{T} → (i : Inj D D0) → (s : Tms Sg G D T) → Σ (RTms Sg G D D0 i T (rens i s)) \ rt -> proj₁ (forgets rt) ≡ s
  remembers i [] = [] , refl
  remembers i (t ∷ ts) = proj₁ rect ∷ proj₁ rects , cong₂ _∷_ (proj₂ rect) (proj₂ rects) where
    rect = remember i t
    rects = remembers i ts


ren-inj : ∀ {Sg G D D0}{T : Ty} → (i : Inj D D0) → (s t : Tm Sg G D T) -> ren i s ≡ ren i t -> s ≡ t
ren-inj i s t eq with remember i s | remember i t
... | (rs , fogrs≡s) | (rt , fogrt≡t) rewrite eq = trans (sym fogrs≡s) (trans (cong (λ r → proj₁ (forget r)) (unique rs rt)) fogrt≡t)
open import OneHoleContext

notInv : ∀ {Sg G D D' T} (i : Inj D D') (t : Term Sg G D' T) → Set
notInv i t = ∃ \ D1 -> ∃ \ Ss -> ∃ \ B -> Σ (D1 ∋ Ss ->> B) \ x -> ∃ \ ts -> Σ (Context _ _ _ (D1 , inj₁ _) ) \ C → 
       ∫ C (var x ts) ≡ t × x ∉ (∫Inj C i)

map-occ : ∀ {Sg G DI D T D' T' }{i : Inj D' DI}{t : Term Sg G D T} (d : DTm Sg G (DI , T') (D , T) ) → notInv (∫oInj d i) t → notInv i (∫once d t)
map-occ d (D1 , Ss , B , x , ys , C , eq , x∉i) = D1 , Ss , B , x , ys , d ∷ C , cong (∫once d) eq , x∉i

mutual
  invertTm' : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tm Sg G D T) → (ρ : MetaRen G G1) → ρ / t ∈ i
    → (RTm Sg G1 Ss D i T (sub (toSub ρ) t)) ⊎ (notInv i t)
  invertTm' i (con c ts) r m with invertTm's i ts r m
  invertTm' i (con c ts) r m | yes p = yes (con c p)
  invertTm' i (con c ts) r m | no e = no (map-occ (con c) e)
  invertTm' i (fun u j) r m = yes (fun (body (r _ u)) (proj₁ m) (proj₂ m))
  invertTm' i (var x ts) r m with invert (i) x | invertTm's i ts r m 
  invertTm' i (var x ts) r m | yes (y , eq) | yes p₁ = yes (var y eq p₁)
  invertTm' i (var x ts) r m | yes p | no ¬p = no (map-occ (var x) ¬p)
  invertTm' i (var x ts) r m | no ¬p | q = no (_ , _ , _ , x , ts , [] , refl , ∉Im-∉ i x (λ b x₁ → ¬p (b , sym x₁)))
  invertTm' i (lam t) r m with invertTm' (cons i) t r m
  invertTm' i (lam t) r m | yes p = yes (lam p)
  invertTm' i (lam t) r m | no q = no (map-occ lam q)

  invertTm's : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tms Sg G D T) → (ρ : MetaRen G G1) → ρ /s t ∈ i 
            → (RTms Sg G1 Ss D i T (subs (toSub ρ) t)) ⊎ (notInv i t)
  invertTm's i [] r m = yes []
  invertTm's i (x ∷ t) r m with invertTm' i x r (proj₁ m) | invertTm's i t r (proj₂ m)
  invertTm's i (x ∷ t) r m | yes p | yes p₁ = yes (p ∷ p₁)
  invertTm's i (x ∷ t) r m | yes p | no ¬p = no (map-occ (tail x) ¬p)
  invertTm's i (x ∷ t) r m | no ¬p | z = no (map-occ (head t) ¬p)

invertTm : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tm Sg G D T) → (ρ : MetaRen G G1) → ρ / t ∈ i → (∃ \ s → ren i s ≡ sub (toSub ρ) t) ⊎ (notInv i t)
invertTm i t ρ m = Data.Sum.map forget (\ x -> x) (invertTm' i t ρ m)


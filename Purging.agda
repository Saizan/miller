module Purging where

open import Data.Product renaming (map to mapΣ)
open import Data.Nat hiding (_≤_) renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.Maybe
open import Category.Monad
import Level
open RawMonad (monad {Level.zero})

open import Injection
open import Lists

open import Syntax
open import Equality

record VarClosure (D : MCtx) (S : MTy) : Set where
  constructor _/_
  field
    {Ψ} : Ctx
    ρ-env : Inj Ψ (ctx S)
    body : D ∋ (type S <<- Ψ)

open VarClosure public using (body; ρ-env)

MetaRen : MCtx → MCtx → Set
MetaRen G D = ∀ S → G ∋ S → VarClosure D S

toSub : ∀ {Sg G D} → MetaRen G D → Sub Sg G D
toSub r = λ S x → fun (body (r S x)) (ρ-env (r S x))

idmr : ∀ {G} -> MetaRen G G
idmr = \ S x -> id-i / x

_∘mr_ : ∀ {G1 G2 G3} → MetaRen G2 G3 → MetaRen G1 G2 → MetaRen G1 G3
f ∘mr g = λ S x → let gr = g S x; fr = f _ (body gr) in
                  (ρ-env gr ∘i ρ-env fr) / body fr 

singleton : ∀ {G S} → (u : G ∋ S) → ∀ {Ψ} → Inj Ψ (ctx S) → MetaRen G ((G - u) <: (type S <<- Ψ))
singleton u  j T  v with thick u v
singleton u  j T  v | inj₁ x = id-i / suc (proj₁ x)
singleton .v j ._ v | inj₂ refl = j / zero 

mutual
  _/_∈_ : ∀ {Sg : Ctx} {G1 G2 : MCtx} → MetaRen G1 G2 → ∀ {D1 D2 : Ctx} → ∀ {T} → Tm Sg G1 D2 T →  Inj D1 D2 → Set
  r / con c ts ∈ i = r /s ts ∈ i
  r / fun u j ∈ i = ∃ (λ k → i ∘i k ≡ j ∘i ρ-env (r _ u))
  r / var x ts ∈ i = r /s ts ∈ i
  r / lam t ∈ i = r / t ∈ cons i

  _/s_∈_ : ∀ {Sg : Ctx} {G1 G2 : MCtx} → MetaRen G1 G2 → ∀ {D1 D2 : Ctx} → ∀ {Ts} → Tms Sg G1 D2 Ts → Inj D1 D2 → Set
  r /s [] ∈ i = ⊤
  r /s (x ∷ ts) ∈ i = r / x ∈ i × r /s ts ∈ i

-- downward closed
mutual
  DClosedMRP : ∀ {Sg G1 G2 G3} (f : MetaRen G2 G3)(g : MetaRen G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tm Sg G1 D2 T) → g / t ∈ i → (f ∘mr g) / t ∈ i
  DClosedMRP f g i (con c ts) m = DClosedMRPs f g i ts m
  DClosedMRP f g i (fun u j) (h , i∘h≡j∘gu) = h ∘i fj , 
       (begin i ∘i (h ∘i fj)             ≡⟨ assoc-∘i ⟩ 
              (i ∘i h) ∘i fj             ≡⟨ cong (λ k → k ∘i fj) i∘h≡j∘gu ⟩ 
              (j ∘i ρ-env (g _ u)) ∘i fj ≡⟨ sym assoc-∘i ⟩ 
              j ∘i (ρ-env (g _ u) ∘i fj) ∎)
    where
      fr = f _ (body (g _ u))
      fj = ρ-env fr
  DClosedMRP f g i (var x ts) m = DClosedMRPs f g i ts m
  DClosedMRP f g i (lam t) m = DClosedMRP f g (cons i) t m
  
  DClosedMRPs : ∀ {Sg G1 G2 G3} → (f : MetaRen G2 G3)(g : MetaRen G1 G2) → ∀ {D1 D2 : Ctx} → (i : Inj D1 D2) ->
               ∀ {T} → (t : Tms Sg G1 D2 T) → g /s t ∈ i → (f ∘mr g) /s t ∈ i
  DClosedMRPs f g i [] m = _
  DClosedMRPs f g i (t ∷ ts) m = (DClosedMRP f g i t (proj₁ m)) , (DClosedMRPs f g i ts (proj₂ m))

  step-MRP : ∀ {Sg G1 G2 G3} (f : MetaRen G2 G3)(g : MetaRen G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tm Sg G1 D2 T) → f / sub (toSub g) t ∈ i → (f ∘mr g) / t ∈ i
  step-MRP f g i (con c ts) m = step-MRPs f g i ts m
  step-MRP f g i (fun u j) (k , p) = k , 
    (begin i ∘i k                                             ≡⟨ p ⟩ 
           (j ∘i ρ-env (g _ u)) ∘i ρ-env (f _ (body (g _ u))) ≡⟨ sym assoc-∘i ⟩ 
           j ∘i (ρ-env (g _ u) ∘i ρ-env (f _ (body (g _ u)))) ∎)
  step-MRP f g i (var x ts) m = step-MRPs f g i ts m
  step-MRP f g i (lam t) m = step-MRP f g (cons i) t m
  
  step-MRPs : ∀ {Sg G1 G2 G3} (f : MetaRen G2 G3)(g : MetaRen G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tms Sg G1 D2 T) → f /s subs (toSub g) t ∈ i  → (f ∘mr g) /s t ∈ i
  step-MRPs f g i [] ms = _
  step-MRPs f g i (t ∷ ts) ms = step-MRP f g i t (proj₁ ms) , step-MRPs f g i ts (proj₂ ms)

{-# NO_TERMINATION_CHECK #-}
mutual
  
  purge : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tm Sg G D2 T) → ∃ \ G1 → Σ (MetaRen G G1) \ ρ → ρ / t ∈ i
  purge i (con c ts) = purges i ts
  purge i (fun u j) = _ , (singleton u (proj₁ (proj₂ r)) , aux) where
    r = purje i j
    aux : ∃ (λ k → i ∘i k ≡ j ∘i ρ-env (singleton u (proj₁ (proj₂ r)) _ u))
    aux rewrite thick-refl u = (proj₁ (proj₂ (proj₂ r))) , proj₁ (proj₂ (proj₂ (proj₂ r)))
  purge i (var x ts) = purges i ts
  purge i (lam t) = purge (cons i) t

  purges : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tms Sg G D2 T) → ∃ \ G1 → Σ (MetaRen G G1) \ ρ → ρ /s t ∈ i
  purges {Sg}{G} i [] = G , idmr , tt
  purges i (t ∷ t₁) with purge i t
  ... | (G1 , ρ , p) with purges i (subs (toSub ρ) t₁)
  ... | (G2 , ρ2 , p2) = G2 , ρ2 ∘mr ρ , DClosedMRP ρ2 ρ i t p , step-MRPs ρ2 ρ i t₁ p2

mutual
  uni-pullbackT : ∀ {D1 D2 Du : Ctx} → (i : Inj D1 D2)(j : Inj Du D2) -> ∀ {Dr} -> (h : Inj Dr Du) (k : Inj Dr D1)
                 -> (∀ a (y : Du ∋ a)(x : D1 ∋ a) -> i $ x ≡ j $ y -> (∃ \ z -> k $ z ≡ x × h $ z ≡ y)) ->
                 ∀ {Sg G T} (t : Tm Sg G _ T) s -> eqT (ren i t) (ren j s) -> ∃ \ q -> ren h q ≡ s 
  uni-pullbackT i j h k uni (con c ts) (con .c ts₁) (con refl eqts) = (con c (proj₁ recs)) , (cong (con c) (proj₂ recs))
    where    recs = uni-pullbackTs i j h k uni ts ts₁ eqts
  uni-pullbackT i j h k uni (con c ts) (fun u j₁) ()
  uni-pullbackT i j h k uni (con c ts) (var x ts₁) ()
  uni-pullbackT i j h k uni (fun u j₁) (con c ts) ()
  uni-pullbackT i j h k uni (fun u j₁) (fun .u j₂) (fun refl eq) = fun u (proj₁ rec) , cong (fun u) (sym (proj₂ prec)) 
                                                                                          
    where rec = uni-pullback i j h k uni j₂ j₁ eq
          prec = proj₂ rec
  uni-pullbackT i j h k uni (fun u j₁) (var x ts) ()
  uni-pullbackT i j h k uni (var x ts) (con c ts₁) ()
  uni-pullbackT i j h k uni (var x ts) (fun u j₁) ()
  uni-pullbackT i j h k uni (var x ts) (var x₁ ts₁) (var ix≡jx₁ eq) = 
                (var (proj₁ rec) (proj₁ recs)) , ((cong₂ var (proj₂ (proj₂ rec)) (proj₂ recs)))
             where rec = (uni _ x₁ x ix≡jx₁)
                   recs = uni-pullbackTs i j h k uni ts ts₁ eq
  uni-pullbackT i j h k uni (lam t) (lam s) (lam eq) = lam (proj₁ rec) , cong lam prec where
           rec = uni-pullbackT (cons i) (cons j) (cons h) (cons k) (cons-pullback i j h k uni) t s eq
           prec = proj₂ rec
 
  uni-pullbackTs : ∀ {D1 D2 Du : Ctx} → (i : Inj D1 D2)(j : Inj Du D2) -> ∀ {Dr} -> (h : Inj Dr Du) (k : Inj Dr D1)
                 -> (∀ a (y : Du ∋ a)(x : D1 ∋ a) -> i $ x ≡ j $ y -> (∃ \ z -> k $ z ≡ x × h $ z ≡ y)) ->
                 ∀ {Sg G T} (t : Tms Sg G _ T) s -> eqT (rens i t) (rens j s) -> ∃ \ q -> rens h q ≡ s
  uni-pullbackTs i j h k uni [] [] eq = [] , refl
  uni-pullbackTs i j h k uni (t ∷ ts) (s ∷ ss) (eqt ∷ eqts) = (proj₁ rect ∷ proj₁ rects) , cong₂ _∷_ (proj₂ rect) (proj₂ rects) where
                 rect = uni-pullbackT i j h k uni t s eqt
                 rects = uni-pullbackTs i j h k uni ts ss eqts
 
mutual
  purge-gen : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tm Sg G D2 T) → 
              ∀ {G2} -> (s : Sub Sg G G2) -> (z : Tm Sg G2 D1 T) -> eqT (ren i z) (sub s t) -> s ≤ toSub (proj₁ (proj₂ (purge i t)))
  purge-gen i (con c ts) s (con c₁ ts₁) (con _ eq) = purge-gens i ts s ts₁ eq
  purge-gen i (con c ts) s (fun u j) ()
  purge-gen i (con c ts) s (var x ts₁) ()
  purge-gen {Sg} {G} i (fun {Ss = Ss} {B} u j) {G2} s z eq with (purje i j) 
  ... | (P , k , h , pull , uni) = r , proof where
            uniT = uni-pullbackT _ _ k h uni z (s (B <<- Ss) u) eq
            r : (S₁ : MTy) → B <<- P ∷ G - u ∋ S₁ → Tm Sg G2 (ctx S₁) ([] ->> type S₁)
            r .(B <<- P) zero = proj₁ uniT
            r S₁ (suc v) = s S₁ (thin u S₁ v)
            proof : (S₁ : MTy) (u₁ : G ∋ S₁) → s S₁ u₁ ≡ ren (ρ-env (singleton u k S₁ u₁))
                                                         (r _ (body (singleton u k S₁ u₁)))
            proof S₁ u₁ with thick u u₁ 
            proof S₁ .(thin u S₁ v) | inj₁ (v , refl) = sym (ren-id _)
            proof ._ ._ | inj₂ refl = sym ((proj₂ uniT))
  purge-gen i (var x ts) s (con c ts₁) ()
  purge-gen i (var x ts) s (fun u j) ()
  purge-gen i (var x ts) s (var x₁ ts₁) (var eqv eq) = purge-gens i ts s ts₁ eq
  purge-gen i (lam t) s (lam z) (lam eq) = purge-gen (cons i) t s z eq

  purge-gens : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tms Sg G D2 T) → 
              ∀ {G2} -> (s : Sub Sg G G2) -> (z : Tms Sg G2 D1 T) -> eqT (rens i z) (subs s t) -> s ≤ toSub (proj₁ (proj₂ (purges i t)))
  purge-gens i [] s [] eq = s , (λ S u → sym (ren-id _))
  purge-gens i (t ∷ ts) s (z ∷ zs) (eqt ∷ eqts) with purge-gen i t s z eqt 
  ... | (r , s≡r∘ρ) with purge-gens i (subs (toSub (proj₁ (proj₂ (purge i t)))) ts) r zs (≡-T (trans (T-≡ eqts) 
                         (trans (subs-ext s≡r∘ρ ts) (sym (subs-∘ ts)))))
  ... | (r1 , r≡r1∘ρ1) = r1 , (λ S u → trans (s≡r∘ρ S u) (trans (sub-ext r≡r1∘ρ1 (toSub ρ S u)) (sym (sub-∘ {f = r1} {g = toSub ρ1} (toSub ρ S u)))))
    where
      ρ = (proj₁ (proj₂ (purge i t)))
      ρ1 = proj₁ (proj₂ (purges i (subs (toSub ρ) ts)))
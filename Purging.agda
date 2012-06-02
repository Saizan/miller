module Purging where

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

MetaRen : MCtx → MCtx → Set
MetaRen G D = ∀ S → G ∋ S → ∃ \ Ψ → D ∋ (type S <<- Ψ) × Inj Ψ (ctx S)

toSub : ∀ {Sg G D} → MetaRen G D → Sub Sg G D
toSub r = λ S x → fun (proj₁ (proj₂ (r S x))) (proj₂ (proj₂ (r S x)))

_∘mr_ : ∀ {G1 G2 G3} → MetaRen G2 G3 → MetaRen G1 G2 → MetaRen G1 G3
f ∘mr g = λ S x → let gr = g S x; Ψ = proj₁ gr; v = proj₁ (proj₂ gr); j = proj₂ (proj₂ gr) 
                      fr = f _ v; fΨ = proj₁ fr; fv = proj₁ (proj₂ fr); fj = proj₂ (proj₂ fr)  in
                  fΨ , (fv , j ∘i fj)

singleton : ∀ {G S} → (u : G ∋ S) → ∀ {Ψ} → Inj Ψ (ctx S) → MetaRen G ((G - u) <: (type S <<- Ψ))
singleton u j T v with thick u v
singleton {G} {type <<- ctx} u j T v | inj₁ x = _ , ((suc (proj₁ x)) , (quo (λ _ x₁ → x₁) {λ _ e → e}))
singleton {G} {type <<- ctx} .v j .(type <<- ctx) v | inj₂ refl = _ , (zero , j) 

mutual
  MRProp : ∀ {Sg : Ctx} {G1 G2 : MCtx} → MetaRen G1 G2 → ∀ {D1 D2 : Ctx} → Inj D1 D2 → ∀ {T} → Tm Sg G1 D2 T → Set
  MRProp r i (con x x₁) = MRProps r i x₁
  MRProp r i (fun u j) = Σ (Inj (proj₁ (r _ u)) _) (λ k → i ∘i k ≡ j ∘i proj₂ (proj₂ (r _ u)))
  MRProp r i (var x x₁) = MRProps r i x₁
  MRProp r i (lam t) = MRProp r (cons i) t

  MRProps : ∀ {Sg : Ctx} {G1 G2 : MCtx} → MetaRen G1 G2 → ∀ {D1 D2 : Ctx} → Inj D1 D2 → ∀ {Ts} → Tms Sg G1 D2 Ts → Set
  MRProps r i [] = ⊤
  MRProps r i (x ∷ ts) = MRProp r i x × MRProps r i ts

-- downward closed
mutual
  DClosedMRP : ∀ {Sg G1 G2 G3} (f : MetaRen G2 G3)(g : MetaRen G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tm Sg G1 D2 T) → MRProp g i t → MRProp (_∘mr_ f g) i t
  DClosedMRP f g i (con c ts) m = DClosedMRPs f g i ts m
  DClosedMRP f g i (fun u j) (h , i∘h≡j∘gu) = h ∘i fj , trans assoc-∘i (trans (cong (λ k → k ∘i fj) i∘h≡j∘gu) (sym assoc-∘i)) where
    fr = f _ (proj₁ (proj₂ (g _ u)))
    fj = proj₂ (proj₂ fr)
  DClosedMRP f g i (var x ts) m = DClosedMRPs f g i ts m
  DClosedMRP f g i (lam t) m = DClosedMRP f g (cons i) t m
  
  DClosedMRPs : ∀ {Sg G1 G2 G3} → (f : MetaRen G2 G3)(g : MetaRen G1 G2) → ∀ {D1 D2 : Ctx} → (i : Inj D1 D2) ->
               ∀ {T} → (t : Tms Sg G1 D2 T) → MRProps g i t → MRProps (_∘mr_ f g) i t
  DClosedMRPs f g i [] m = _
  DClosedMRPs f g i (t ∷ ts) m = (DClosedMRP f g i t (proj₁ m)) , (DClosedMRPs f g i ts (proj₂ m))

  step-MRP : ∀ {Sg G1 G2 G3} (f : MetaRen G2 G3)(g : MetaRen G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tm Sg G1 D2 T) → MRProp f i (sub (toSub g) t) → MRProp (f ∘mr g) i t
  step-MRP f g i (con c ts) m = step-MRPs f g i ts m
  step-MRP f g i (fun u j) (k , p) = k , trans p (sym assoc-∘i)
  step-MRP f g i (var x ts) m = step-MRPs f g i ts m
  step-MRP f g i (lam t) m = step-MRP f g (cons i) t m
  
  step-MRPs : ∀ {Sg G1 G2 G3} (f : MetaRen G2 G3)(g : MetaRen G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tms Sg G1 D2 T) → MRProps f i (subs (toSub g) t) → MRProps (f ∘mr g) i t
  step-MRPs f g i [] ms = _
  step-MRPs f g i (t ∷ ts) ms = (step-MRP f g i t (proj₁ ms)) , (step-MRPs f g i ts (proj₂ ms))

{-# NO_TERMINATION_CHECK #-}
mutual
  
  purge : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tm Sg G D2 T) → (∃ \ G1 → Σ (MetaRen G G1) \ ρ → MRProp ρ i t)
  purge i (con c ts) = purges i ts
  purge i (fun u j) = _ , (singleton u (proj₁ (proj₂ r)) , aux) where
    r = purje i j
    aux : Σ (Inj (proj₁ (singleton u (proj₁ (proj₂ r)) _  u)) _)
           (λ k →
                i ∘i k ≡
                     j ∘i
                  proj₂
                    (proj₂
              (singleton u (proj₁ (proj₂ r)) _ u)))
    aux rewrite thick-refl u = proj₂ (proj₂ r)
  purge i (var x ts) = purges i ts
  purge i (lam t) = purge (cons i) t

  purges : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tms Sg G D2 T) → (∃ \ G1 → Σ (MetaRen G G1) \ ρ → MRProps ρ i t)
  purges {Sg}{G} i [] = G , (λ S x → _ , (x , (quo (λ x₁ x₂ → x₂) {\ _ eq → eq}))) , tt
  purges i (t ∷ t₁) with purge i t
  ... | (G1 , ρ , p) with purges i (subs (toSub ρ) t₁)
  ... | (G2 , ρ2 , p2) = G2 , ((ρ2 ∘mr ρ) , ((DClosedMRP ρ2 ρ i t p) , step-MRPs ρ2 ρ i t₁ p2))

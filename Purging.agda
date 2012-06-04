module Purging where

open import Data.Product renaming (map to mapΣ)
open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
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
    aux rewrite thick-refl u = proj₂ (proj₂ r)
  purge i (var x ts) = purges i ts
  purge i (lam t) = purge (cons i) t

  purges : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tms Sg G D2 T) → ∃ \ G1 → Σ (MetaRen G G1) \ ρ → ρ /s t ∈ i
  purges {Sg}{G} i [] = G , (λ S x → id-i / x) , tt
  purges i (t ∷ t₁) with purge i t
  ... | (G1 , ρ , p) with purges i (subs (toSub ρ) t₁)
  ... | (G2 , ρ2 , p2) = G2 , ρ2 ∘mr ρ , DClosedMRP ρ2 ρ i t p , step-MRPs ρ2 ρ i t₁ p2

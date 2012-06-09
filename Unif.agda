module Unif where

open import Data.Product renaming (map to mapΣ)
open import Data.Nat hiding (_≤_) renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.Sum renaming (inj₁ to yes; inj₂ to no)
open import Data.Maybe
open import Category.Monad
import Level
open RawMonad (monad {Level.zero})

open import Injection
open import Lists

open import Syntax
open import OneHoleContext
open import OccursCheck
open import Purging
open import Inversion

Property : ∀ Sg G -> Set₁
Property Sg G = (∀ {G2} -> Sub Sg G G2 -> Set)

Unifies : ∀ {Sg G1 D S} (x y : Term Sg G1 D S) -> Property Sg G1
Unifies x y σ = subT σ x ≡ subT σ y

∃σ_ : ∀ {Sg G1} -> Property Sg G1 -> Set
∃σ P = ∃ \ G2 -> ∃ \ σ -> P {G2} σ

_≤_ : ∀ {Sg D C1 C2} -> Sub Sg D C1 -> Sub Sg D C2 -> Set
f ≤ g = ∃ \ r -> ∀ S u -> f S u ≡ (r ∘s g) S u

Max : ∀ {Sg G1} -> Property Sg G1 -> Property Sg G1
Max P σ = P σ × (∀ {G'} ρ -> P {G'} ρ -> ρ ≤ σ)
  
flexSame : ∀ {Sg G D S} → (u : G ∋ S) → (i j : Inj (ctx S) D) → ∃σ Max (Unifies {Sg} (Tm.fun u i) (fun u j))
flexSame {Sg} {G} {D} {S} u i j = _ , σ , aux , maxprop where
    r = intersect i j
    k = proj₁ (proj₂ r)
    σ = (toSub (singleton u k))
    aux : ren i (σ _ u) ≡ ren j (σ _ u)
    aux rewrite thick-refl u = cong (fun zero) (proj₁ (proj₂ (proj₂ r)))
    maxprop : {G' : List MTy}
      (ρ : (S : MTy) → G ∋ S → Tm Sg G' (ctx S) (! type S)) →
      ren i (ρ _ u) ≡ ren j (ρ _ u) → ρ ≤ σ
    maxprop {G'} ρ eq = dif , proof where
      dif : (S₁ : MTy) →
        type S <<- proj₁ (intersect i j) ∷ G - u ∋ S₁ →
        Tm Sg G' (ctx S₁) ([] ->> type S₁)
      dif ._ zero = {! (ρ S u) !}
      dif S₁ (suc v) = ρ _ (thin u _ v)
      proof : (S₁ : MTy) (u₁ : G ∋ S₁) → ρ S₁ u₁ ≡ (dif ∘s σ) S₁ u₁
      proof S₁ u₁ with thick u u₁ 
      proof S₁ u₁ | inj₁ (v , eq') rewrite eq' = {!!}
      proof .S .u | inj₂ refl = {!!}

Spec : ∀ {Sg G1 D S} (x y : Term Sg G1 D S) -> Set
Spec x y = ∃σ Max (Unifies x y) ⊎ ¬ ∃σ Unifies x y


flexRigid : ∀ {Sg G D S} →
               (u : G ∋ S) →
               (i : Inj (ctx S) D) →
               (s : Tm Sg (G - u) D (! type S)) → (∃ \ G1 → Σ (MetaRen (G - u) G1) \ ρ → ρ / s ∈ i) ->
               Spec (fun u i) (sub (\ S v -> mvar (thin u S v)) s)
flexRigid {S = S} u i s (G1 , ρ , m) with invertTm i s ρ m 
flexRigid {S = S} u i .(∫ C (var x ys)) (G1 , ρ , m) | inj₂ (D1 , Ss , B , x , ys , C , refl , x∉i) = no (aux x∉i) where
  aux : x ∉ ∫Inj C i -> ∃σ (Unifies (fun u i) (sub (λ S v → mvar (thin u S v)) (∫ C (var x ys)))) → ⊥
  aux x∉i (_ , σ , eq) with ren-∫ x (subC _ C) (σ _ u) i (subs _ ys) (trans eq (trans (sub-∘ (∫ C (var x ys))) (∫-sub _ C (var x ys))))
                       | ∫Ctx C (ctx S) | ∫Inj C i | ∫Inj-subC {s = (λ z t → ren id-i (σ z (thin u z t)))} C i
  ... | (b , x≡i$b) | ._ | ._ | refl = ∉-∉Im (∫Inj (subC (λ z t → ren id-i (σ z (thin u z t))) C) i) x x∉i b x≡i$b

flexRigid {Sg} {G} u i s (G1 , ρ , m) | inj₁ (t , eq) = yes (G1 , σ , 
   (begin
     ren i (σ _ u)                              ≡⟨ cong (ren i) σx≡t' ⟩ 
     ren i t                                    ≡⟨ eq ⟩ 
     sub (toSub ρ) s                            ≡⟨ sub-ext σthiny≡toSubρy s ⟩ 
     sub (λ S v → sub σ (mvar (thin u S v))) s  ≡⟨ sym (sub-∘ s) ⟩ 
     sub σ (sub (λ S v → mvar (thin u S v)) s)  ∎) , {!!} )
    where
      σ : (S : MTy) → G ∋ S → Tm Sg G1 (ctx S) (! (type S))
      σ S v with thick u v
      σ S v | inj₁ (w , eq) = toSub ρ _ w
      σ ._ .u | inj₂ refl = t
      σx≡t' : σ _ u ≡ t
      σx≡t' rewrite thick-refl u = refl
      σthiny≡toSubρy : (S : MTy) (x₁ : G - u ∋ S) → toSub ρ _ x₁ ≡ sub σ (mvar (thin u S x₁))
      σthiny≡toSubρy S y rewrite thick-thin u y | left-id (ρ-env (ρ S y)) = refl

flexAny : ∀ {Sg G D S} → (u : G ∋ S) → (i : Inj (ctx S) D) → (t : Tm Sg G D (! (type S))) 
          → Spec (fun u i) t
flexAny u i t with check u t 
flexAny u i .(sub (λ S v → mvar (thin u S v)) s) | inj₁ (s , refl) = flexRigid u i s (purge i s)
flexAny u i .(fun u j) | inj₂ (G1 , j , [] , refl) = yes (flexSame u i j)
flexAny u i .(∫once x (∫ ps (fun u j))) | inj₂ (G1 , j , x ∷ ps , refl) = no λ {(D1 , s , eq) → 
        not-nil (subC s ps) (No-Cycle (subC s (x ∷ ps)) (s _ u) i j (trans eq (∫-sub s (x ∷ ps) (fun u j))))}


unify-comm : ∀ {Sg G D T} → (x y : Term Sg G D T) → ∃σ Unifies x y → ∃σ Unifies y x
unify-comm _ _ (G , σ , eq) = (G , σ , sym eq)

spec-comm : ∀ {Sg G D T} → (x y : Term Sg G D T) → Spec x y → Spec y x
spec-comm _ _ = Data.Sum.map (λ { (G , σ , eq , max) → G , σ , sym eq , (λ {_} ρ x → max ρ (sym x))}) (λ x x₁ → x (unify-comm _ _ x₁))
 
{-# NO_TERMINATION_CHECK #-}
mutual
  unify : ∀ {Sg G D T} → (x y : Tm Sg G D T) → Spec x y
  unify (con x xs) (con y ys) with eq-∋ (_ , x) (_ , y) 
  ... | no _ = no {!!}
  unify (con x xs) (con .x ys) | yes refl with unifyTms xs ys
  ... | no p = no (λ { (_ , σ , eq) → p (_ , (σ , {!!}))})
  ... | yes (_ , σ , eq , max) = yes (_ , σ , cong (con x) eq , {!!})
  unify (fun x xs) t = flexAny x xs t
  unify s (fun y ys) = spec-comm (fun y ys) s (flexAny y ys s)
  unify (var x xs) (var y ys) with eq-∋ (_ , x) (_ , y) 
  ... | no _ = no {!!}
  unify (var x xs) (var .x ys) | yes refl with unifyTms xs ys
  ... | no p = no {!!}
  ... | yes (_ , σ , eq , max) = yes (_ , σ , cong (var x) eq , {!!})
  unify (lam x) (lam y) with unify x y
  ... | no p = no {!!}
  ... | yes (_ , σ , eq , max) = yes (_ , σ , cong lam eq , {!max!})
  unify _ _ = no {!!}


  unifyTms : ∀ {Sg G D Ts} → (x y : Tms Sg G D Ts) → Spec x y
  unifyTms [] [] = yes (_ , ((λ S x → mvar x) , refl , (λ ρ x → ρ , {!!})))
  unifyTms (s ∷ xs) (t ∷ ys) with unify s t 
  ... | no p = no {!p!} -- easy
  ... | yes (_ , σ , eq , max) with unifyTms (subs σ xs) (subs σ ys) 
  ... | no p = no {!p!} -- needs most-generality of σ
  ... | yes (_ , σ1 , eq1 , max1) = yes (_ , (σ1 ∘s σ) , 
    cong₂ _∷_ (begin sub (λ z t₁ → sub σ1 (σ z t₁)) s ≡⟨ sym (sub-∘ s) ⟩ 
                     sub σ1 (sub σ s)                 ≡⟨ cong (sub σ1) eq ⟩ 
                     sub σ1 (sub σ t)                 ≡⟨ sub-∘ t ⟩ 
                     sub (λ z t₁ → sub σ1 (σ z t₁)) t ∎) 
              (begin subs (λ z t₁ → sub σ1 (σ z t₁)) xs ≡⟨ sym (subs-∘ xs) ⟩ 
                     subs σ1 (subs σ xs)                ≡⟨ eq1 ⟩ 
                     subs σ1 (subs σ ys)                ≡⟨ subs-∘ ys ⟩ 
                     subs (λ z t₁ → sub σ1 (σ z t₁)) ys ∎)
    , {!!})
{-

-- sketch of how to ensure termination

Bwd-len : ∀ {A : Set} → Bwd A → Nat
Bwd-len !> = zero
Bwd-len (x :> xs) = suc (Bwd-len xs)

Ctx-len : MCtx → Nat
Ctx-len <! = zero
Ctx-len (x <: (_ <<- f)) = suc (Bwd-len f + (Ctx-len x))

data Subs (Sg : Ctx) : MCtx → Nat → Set where
  nil : ∀ {G} → Subs Sg G (Ctx-len G)
  _◇_ : ∀ {n G D} → Sub Sg G D → (ss : Subs Sg D n) → Subs Sg G (suc n)

mutual
  unify : ∀ {Sg G D T} → (x y : Tm Sg G D T) → ∀ {n} → Subs Sg G n → Maybe (Subs Sg G n)
  unify (con x xs) (con y ys) a with eq-∋ (_ , x) (_ , y)
  unify (con x xs) (con .x ys) a | yes refl = unifyTms xs ys a
  unify (con x xs) (con y ys) a | no y₁ = nothing
  unify (fun x xs) (fun y ys) nil = {!!}
  unify (fun x xs) t nil = {!!}
  unify s (fun y ys) nil = {!!}
  unify (var x xs) (var y ys) a with eq-∋ (_ , x) (_ , y) 
  unify (var x xs) (var .x ys) a | yes refl = unifyTms xs ys a
  unify (var x xs) (var y ys) a | no y₁ = nothing
  unify (lam x) (lam y) a = unify x y a
  unify s t (s₁ ◇ a) = _◇_ s₁ <$> unify (sub s₁ s) (sub s₁ t) a
  unify _ _ _ = nothing

  unifyTms : ∀ {Sg G D Ts} → (x y : Tms Sg G D Ts) → ∀ {n} → Subs Sg G n → Maybe (Subs Sg G n)
  unifyTms [] [] a = yes a
  unifyTms (x ∷ xs) (y ∷ ys) a = unify x y a >>= unifyTms xs ys
-}

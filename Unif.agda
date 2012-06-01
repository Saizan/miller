module Unif where

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
open import OccursCheck
open import Purging
open import Inversion

flexSame : ∀ {Sg G D S} → (u : G ∋ S) → (i j : Inj (ctx S) D) → ∃ \ G1 → Σ (Sub Sg G G1) \ s → ren {Sg} i (s _ u) ≡ ren j (s _ u)
flexSame u i j = _ , σ , aux where
    r = intersect i j
    k = proj₁ (proj₂ r)
    σ = (toSub (singleton u k))
    aux : ren i (σ _ u) ≡ sub σ (fun u j)
    aux rewrite thick-refl u = cong (fun zero) (proj₂ (proj₂ r))

flexRigid : ∀ {Sg G D S} →
               (u : G ∋ S) →
               (i : Inj (ctx S) D) →
               (s : Tm Sg (G - u) D (! type S)) → (∃ \ G1 → Σ (MetaRen (G - u) G1) \ ρ → MRProp ρ i s) ->
               Maybe (∃ λ G1 → Σ (Sub Sg G G1) λ s₁ → ren i (s₁ S u) ≡ sub s₁ (sub (λ S₁ v → mvar (thin u S₁ v)) s))
flexRigid u i s (G1 , ρ , m) with invertTm i s ρ m 
flexRigid u i s (G1 , ρ , m) | no ¬p = nothing
flexRigid {Sg} {G} u i s (G1 , ρ , m) | yes (t , eq) = just (G1 , (σ , 
     trans (trans (cong (ren i) σx≡t') (trans eq (sub-ext σthiny≡toSubρy s))) (sym (sub-∘ s))))
    where
      σ : (S : MTy) → G ∋ S → Tm Sg G1 (ctx S) (! (type S))
      σ S v with thick u v
      σ S v | inj₁ (w , eq) = toSub ρ _ w
      σ ._ .u | inj₂ refl = t
      σx≡t' : σ _ u ≡ t
      σx≡t' rewrite thick-refl u = refl
      σthiny≡toSubρy : (S : MTy) (x₁ : G - u ∋ S) → toSub ρ _ x₁ ≡ sub σ (mvar (thin u S x₁))
      σthiny≡toSubρy S y rewrite thick-thin u y | left-id (proj₂ (proj₂ (ρ S y))) = refl

flexAny : ∀ {Sg G D S} → (u : G ∋ S) → (i : Inj (ctx S) D) → (t : Tm Sg G D (! (type S))) 
          → Maybe (∃ \ G1 → Σ (Sub Sg G G1) \ s → sub s (fun u i) ≡ sub s t)
flexAny u i t with check u t 
flexAny u i .(sub (λ S v → mvar (thin u S v)) s) | inj₁ (s , refl) = flexRigid u i s (purge i s)
flexAny u i .(fun u j) | inj₂ (G1 , j , [] , refl) = just (flexSame u i j)
flexAny u i .(∫once x (∫ ps (fun u j))) | inj₂ (G1 , j , x ∷ ps , refl) = nothing

Unify : ∀ {Sg G D T} → (x y : Tm Sg G D T) → Set
Unify {Sg} {G} {D} {T} x y = (∃ \ G1 → Σ (Sub Sg G G1) \ s → sub s x ≡ sub s y)

unify-comm : ∀ {Sg G D T} → (x y : Tm Sg G D T) → Unify x y → Unify y x
unify-comm _ _ (G , σ , eq) = G , σ , sym eq
 
{-# NO_TERMINATION_CHECK #-}
mutual
  unify : ∀ {Sg G D T} → (x y : Tm Sg G D T) → Maybe (∃ \ G1 → Σ (Sub Sg G G1) \ s → sub s x ≡ sub s y)
  unify (con x xs) (con y ys) with eq-∋ (_ , x) (_ , y) 
  ... | no _ = nothing
  unify (con x xs) (con .x ys) | yes refl with unifyTms xs ys
  ... | nothing = nothing
  ... | just (_ , σ , eq) = just (_ , σ , cong (con x) eq)
  unify (fun x xs) t = flexAny x xs t
  unify s (fun y ys) = unify-comm (fun y ys) s <$> flexAny y ys s
  unify (var x xs) (var y ys) with eq-∋ (_ , x) (_ , y) 
  ... | no _ = nothing
  unify (var x xs) (var .x ys) | yes refl with unifyTms xs ys
  ... | nothing = nothing
  ... | just (_ , σ , eq) = just (_ , σ , cong (var x) eq)
  unify (lam x) (lam y) with unify x y
  ... | nothing = nothing
  ... | just (_ , σ , eq) = just (_ , σ , cong lam eq)
  unify _ _ = nothing


  unifyTms : ∀ {Sg G D Ts} → (x y : Tms Sg G D Ts) → Maybe (∃ \ G1 → Σ (Sub Sg G G1) \ s → subs s x ≡ subs s y)
  unifyTms [] [] = just (_ , ((λ S x → fun x (quo (λ _ x₁ → x₁) {λ _ e → e})) , refl))
  unifyTms (s ∷ xs) (t ∷ ys) with unify s t 
  ... | nothing = nothing
  ... | just (_ , σ , eq) with unifyTms (subs σ xs) (subs σ ys) 
  ... | nothing = nothing
  ... | just (_ , σ1 , eq1) = just (_ , ((λ S x → sub σ1 (σ S x)) , 
    cong₂ _∷_ (trans (trans (sym (sub-∘ s)) (cong (sub σ1) eq)) (sub-∘ t)) (trans (trans (sym (subs-∘ xs)) eq1) (subs-∘ ys))))

{-

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
  unifyTms [] [] a = just a
  unifyTms (x ∷ xs) (y ∷ ys) a = unify x y a >>= unifyTms xs ys
-}

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

{-# NO_TERMINATION_CHECK #-}
mutual
  unify : ∀ {Sg G D T} → (x y : Tm Sg G D T) → Maybe (∃ \ G1 -> Σ (Sub Sg G G1) \ s -> sub s x ≡ sub s y)
  unify (con x xs) (con y ys) with eq-∋ (_ , x) (_ , y) 
  ... | no _ = nothing
  unify (con x xs) (con .x ys) | yes refl with unifyTms xs ys
  ... | nothing = nothing
  ... | just (_ , σ , eq) = just (_ , σ , cong (con x) eq)

  unify (fun x xs) t with check x t 
  unify (fun x xs) t | inj₁ x₁  = {!!} -- needs forget-MRTm
  unify (fun x xs) .(fun x j) | inj₂ (_ , j , [] , refl) = just (_ , (toSub (singleton x k)) , aux) where
    r = intersect xs j
    k = proj₁ (proj₂ r)
    aux : ren xs (toSub (singleton x k) _ x) ≡ sub (toSub (singleton x k)) (fun x j)
    aux rewrite thick-refl x = cong (fun zero) (proj₂ (proj₂ r))
  unify (fun x xs) .(∫once x₁ (∫ ps (fun x j))) | inj₂ (proj₁ , j , x₁ ∷ ps , refl) = nothing
  unify s (fun y ys) = {!!} -- mirror
  unify (var x xs) (var y ys) = {!!} -- like con
  unify (lam x) (lam y) with unify x y
  ... | nothing = nothing
  ... | just (_ , σ , eq) = just (_ , σ , cong lam eq)
  unify _ _ = nothing


  
  unifyTms : ∀ {Sg G D Ts} → (x y : Tms Sg G D Ts) → Maybe (∃ \ G1 -> Σ (Sub Sg G G1) \ s -> subs s x ≡ subs s y)
  unifyTms [] [] = just (_ , ((λ S x → fun x (quo (λ _ x₁ → x₁) {λ _ e → e})) , refl))
  unifyTms (s ∷ xs) (t ∷ ys) with unify s t 
  ... | nothing = nothing
  ... | just (_ , σ , eq) with unifyTms (subs σ xs) (subs σ ys) 
  ... | nothing = nothing
  ... | just (_ , σ1 , eq1) = just (_ , ((λ S x → sub σ1 (σ S x)) , 
    cong₂ _∷_ (trans (trans (sym (sub-∘ s)) (cong (sub σ1) eq)) (sub-∘ t)) (trans (trans (sym (subs-∘ xs)) eq1) (subs-∘ ys)))) -- XXX sub assoc
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

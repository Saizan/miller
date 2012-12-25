module Height where

open import Data.Sum
open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Injection
open import Data.List.Extras

open import Syntax

Height = ℕ

mutual
  height : ∀ {Sg G D T} -> Tm Sg G D T -> Height
  height (con c ts) = (suc (heights ts))
  height (mvar u j) = 0
  height (var x ts) = suc (heights ts)
  height (lam t) = suc (height t)

  heights : ∀ {Sg G D T} -> Tms Sg G D T -> Height
  heights [] = 0
  heights (t ∷ ts) = suc ((height t) ⊔ (heights ts))

heightT : ∀ {Sg G D T} -> Term Sg G D T -> Height
heightT {T = inj₁ _} = height
heightT {T = inj₂ _} = heights

renT-height : ∀ {T Sg G D D1} -> (i : Inj D D1) -> (t : Term Sg G D T) -> heightT t ≡ heightT (renT i t)
renT-height {inj₁ ._} i (con c ts) = cong suc (renT-height i ts)
renT-height {inj₁ ._} i (mvar u j) = refl
renT-height {inj₁ ._} i (var x ts) = cong suc (renT-height i ts)
renT-height {inj₁ ._} i (lam t) = cong suc (renT-height _ t)
renT-height {inj₂ .[]} i [] = refl
renT-height {inj₂ ._} i (t ∷ t₁) = cong₂ (\ x y -> suc (x ⊔ y)) (renT-height i t) (renT-height i t₁)



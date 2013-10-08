module Support.Nat where

import Level
open import Relation.Binary

import Data.Nat as N
open N public hiding (_≤′_; module _≤′_; _<′_; _≥′_; _>′_)
open import Data.Nat.Properties

open import Support.Equality
-- _≤′_ _<′_ _≥′_
infix 4  _>′_

data _>′_ : (m : ℕ) → ℕ → Set where
  >′-refl : ∀ {m n} (m≡n : m ≡ n)   → suc m >′ n
  >′-step : ∀ {m n} (m≤′n : m >′ n) → suc m >′ n
{-
_<′_ : Rel ℕ Level.zero
m <′ n = suc m ≤′ n

_≥′_ : Rel ℕ Level.zero
m ≥′ n = n ≤′ m

_>′_ : Rel ℕ Level.zero
m >′ n = n <′ m
-}
N>′⇒>′ : ∀ {m n} -> m N.>′ n -> m >′ n
N>′⇒>′ ≤′-refl      = >′-refl refl
N>′⇒>′ (≤′-step le) = >′-step (N>′⇒>′ le)

cast : ∀ {m n o} -> m ≡ n -> n > o -> m >′ o
cast refl le = N>′⇒>′ (≤⇒≤′ le)


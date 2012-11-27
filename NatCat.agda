module NatCat {A : Set} where
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to map⊎)
open import Function
open import Data.List
open import Vars

split# : ∀ m {n}{T : A} -> _∋_ (m ++ n) T -> _∋_ m T ⊎ _∋_ n T
split# []      i       = inj₂ i
split# (_ ∷ n) zero    = inj₁ zero
split# (_ ∷ n) (suc i) = map⊎ suc id (split# n i)

split : ∀ {m} {n}{T} -> _∋_ (m ++ n) T -> _∋_ m T ⊎ _∋_ n T
split = split# _

glue# : ∀ m {n} {T : A} -> _∋_ m T ⊎ _∋_ n T -> _∋_ (m ++ n) T
glue# []      (inj₁ ())
glue# []      (inj₂ y)       = y
glue# (_ ∷ n) (inj₁ zero)    = zero
glue# (_ ∷ n) (inj₁ (suc i)) = suc (glue# n (inj₁ i))
glue# (_ ∷ n) (inj₂ y)       = suc (glue# n (inj₂ y))

glue : ∀ {m n T} -> _∋_ m T ⊎ _∋_ n T -> _∋_ (m ++ n) T
glue = glue# _

glue∘split≡id : ∀ {m n T} (i : _∋_ (m ++ n) T) -> glue {m} {n} (split i) ≡ i
glue∘split≡id {[]}     i       = refl
glue∘split≡id {_ ∷ n}  zero    = refl
glue∘split≡id {_ ∷ n}  (suc i) with split {n} i | glue∘split≡id {n} i
glue∘split≡id {_ ∷ n}  (suc i)    | inj₁ x      | glueinj₁x≡i rewrite glueinj₁x≡i = refl
glue∘split≡id {_ ∷ n'} (suc i)    | inj₂ y      | glueinj₂y≡i rewrite glueinj₂y≡i = refl 

split∘glue≡id : ∀ {m n T} (i : _∋_ m T ⊎ _∋_ n T) -> split {m} {n} (glue i) ≡ i
split∘glue≡id {[]}        (inj₁ ())
split∘glue≡id {[]}        (inj₂ y)       = refl
split∘glue≡id {_ ∷ n}     (inj₁ zero)    = refl
split∘glue≡id {_ ∷ m} {n} (inj₁ (suc i)) rewrite split∘glue≡id {m} {n} (inj₁ i) = refl
split∘glue≡id {_ ∷ m} {n} (inj₂ y)       rewrite split∘glue≡id {m} {n} (inj₂ y) = refl

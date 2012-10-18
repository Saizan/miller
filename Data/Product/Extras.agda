module Data.Product.Extras where

open import Data.Product public renaming (map to mapΣ)

mapΣ₂ : ∀ {a b c p q r}
        {A : Set a} {B : Set b} {C : Set c} {P : A → Set p} {Q : B → Set q} {R : C -> Set r} →
        (f : A -> B -> C) → (∀ {x y} → P x → Q y -> R (f x y)) →
        Σ A P → Σ B Q -> Σ C R
mapΣ₂ f g (x₀ , y₀) (x , y) = (f x₀ x , g y₀ y)

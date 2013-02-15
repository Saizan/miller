module Injection.Sum where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Sum

open import Injection
open import Vars.SumIso


inj₁-inj : ∀ {A B : Set} {x : A}{y} -> inj₁ {A = A} {B} x ≡ inj₁ y -> x ≡ y
inj₁-inj refl = refl

inj₂-inj : ∀ {A B : Set} {x}{y} -> inj₂ {A = A} {B} x ≡ inj₂ y -> x ≡ y
inj₂-inj refl = refl

left# : ∀ {A : Set} xs {ys : List A} -> Inj xs (xs ++ ys)
left# xs {ys} = quo (λ x i → glue# xs (inj₁ i)) {λ x {i} {j} eq → 
      inj₁-inj (trans (sym (split∘glue≡id (inj₁ i))) (trans (cong (split# xs) eq) (split∘glue≡id (inj₁ j))))}

right# : ∀ {A : Set} xs {ys : List A} -> Inj ys (xs ++ ys)
right# xs {ys} = quo (λ x i → glue# xs (inj₂ i)) {λ x {i} {j} eq → 
      inj₂-inj (trans (sym (split∘glue≡id (inj₂ i))) (trans (cong (split# xs) eq) (split∘glue≡id (inj₂ j))))}

left : ∀ {A : Set} {xs ys : List A} -> Inj xs (xs ++ ys)
left = left# _

right : ∀ {A : Set} {xs ys : List A} -> Inj ys (xs ++ ys)
right {xs = xs} = right# xs

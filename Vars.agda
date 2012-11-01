module Vars where

open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.Product
open import Data.Unit
open import Data.Maybe
open import Relation.Nullary
open import Function hiding (_$_)
open import Data.Empty
open import Relation.Nullary.Decidable
open import Data.Sum

infix 4 _∋_

-- Proofs of membership in finite (multi-)sets (as lists)
-- a.k.a. typed de Bruijn indices 
-- i.e. our variable names.
data _∋_ {A : Set} : List A → A → Set where
  zero : ∀ {G T} → T ∷ G ∋ T
  suc : ∀ {G T S} → G ∋ T → S ∷ G ∋ T

_∈_ : {A : Set} → A → List A → Set
_∈_ x xs = xs ∋ x

∋-case : ∀ {A : Set}{xs : List A}{x} {P : ∀ a -> x ∷ xs ∋ a -> Set} -> P x zero -> (∀ a y -> P a (suc y)) -> ∀ a y -> P a y
∋-case z s a zero    = z
∋-case z s a (suc v) = s a v

-- Given G = [T1 , .. , S , .. , Tn], (u : G ∋ S) we have this isomorphism:
--
--   G ∋ T
-- ≡ [T1 , .. , S , .. , Tn] ∋ T
-- ≅ T1 ≡ T ⊎ .. ⊎ S ≡ T ⊎ .. ⊎ Tn ≡ T
-- ≅ (T1 ≡ T ⊎ .. ⊎ Tn ≡ T) ⊎ S ≡ T  
-- ≅ (G - u) ∋ T ⊎ S ≡ T
--
-- thin and thick below are the witnesses

_-_ : ∀{A} {T} → (G : List A) → G ∋ T → List A
_-_ {_} {T} .(T ∷ G) (zero {G}) = G
._ - suc {G} {_} {S} x = S ∷ (G - x) 

infix 35 _-_

thin : ∀ {A} {G : List A}{S} → (x : G ∋ S) → ∀ T → (G - x) ∋ T → G ∋ T
thin zero    _ y    = suc y
thin (suc x) _ zero = zero
thin (suc x) _ (suc y) = suc (thin x _ y)

suc-inj1 : ∀ {A : Set}{xs : List A}{x z} {i : xs ∋ x}{j : xs ∋ x} → suc {S = z} i ≡ suc j → i ≡ j
suc-inj1 refl = refl

x∉thinx : ∀ {A} {G : List A}{S} → (x : G ∋ S) → (y : (G - x) ∋ S) -> x ≡ thin x S y -> ⊥
x∉thinx zero    y    () 
x∉thinx (suc x) zero ()
x∉thinx (suc x) (suc y) eq = x∉thinx x y (suc-inj1 eq)

thick : ∀ {A}{G : List A}{S T} → (x : G ∋ S) → (y : G ∋ T) → (∃ \ z → thin x T z ≡ y) ⊎ ((S , x) ≡ (T , y))
thick zero    zero    = inj₂ refl
thick zero    (suc y) = inj₁ (y , refl)
thick (suc x) zero    = inj₁ (zero , refl)
thick (suc x) (suc y) with thick x y
thick (suc x)  (suc y)   | inj₁ (z , eq) = inj₁ (suc z , cong suc eq)
thick (suc .y) (suc y)   | inj₂ refl     = inj₂ refl

thick-refl : ∀ {A}{G : List A}{S} → (x : G ∋ S) → thick x x ≡ inj₂ refl
thick-refl zero = refl
thick-refl (suc x) rewrite thick-refl x = refl

thick-thin : ∀ {A}{G : List A}{S T} (x : G ∋ S) → (y : (G - x) ∋ T) → thick x (thin x T y) ≡ inj₁ (y , refl)
thick-thin zero    y    = refl
thick-thin (suc x) zero = refl
thick-thin (suc x) (suc y) rewrite thick-thin x y = refl

thin-inj : ∀ {A : Set}{xs : List A}{x y : A} -> (v : xs ∋ x) -> {i j : (xs - v) ∋ y} -> thin v y i ≡ thin v y j -> i ≡ j
thin-inj v {i} {j} eq with cong (\ x -> maybe′ (\ x -> Maybe.just (proj₁ x)) nothing (isInj₁ (thick v x))) eq 
... | p rewrite thick-thin v i | thick-thin v j with p 
thin-inj v {i} {.i} eq | p | refl = refl

suc-inj : ∀ {A : Set}{xs : List A}{x y z} {i : xs ∋ x}{j : xs ∋ y} → (x , suc {S = z} i) ≡ (y , suc j) → (x , i) ≡ (y , j)
suc-inj refl = refl

eq-∋ : ∀ {A : Set}{xs : List A} → (i j : ∃ (_∋_ xs)) → Dec (i ≡ j)
eq-∋ (.y , zero) (y , zero)  = yes refl
eq-∋ (x , zero)  (y , suc j) = no (λ ())
eq-∋ (x , suc i) (y , zero)  = no (λ ())
eq-∋ (x , suc i) (y , suc j) with eq-∋ (x , i) (y , j)
eq-∋ (.y , suc .j) (y , suc j)  | yes refl = yes refl
eq-∋ (x , suc i)   (y , suc j)  | no  ¬p   = no (¬p ∘ suc-inj)

cong-proj₁ : ∀ {A : Set}{xs : List A}{x : A} {i j : xs ∋ x} -> i ≡ j -> _≡_ {A = ∃ (_∋_ xs)} (x , i) (x , j)
cong-proj₁ refl = refl

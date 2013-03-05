module Vars where

open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Function using (_∘_)
open import Data.Empty
open import Data.Sum

open import Support.Equality
open ≡-Reasoning

open import Relation.Nullary public
open import Data.List public hiding ([_])

infix 4 _∋_

-- Proofs of membership in lists
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

_≅∋_ : ∀ {A : Set}{G S} {T : A} -> G ∋ S -> G ∋ T -> Set
_≅∋_ {A} {G} {S} {T} u v = S ≡ T × u ≅ v

-- Given G = [T1 , .. , S , .. , Tn], (u : G ∋ S) we have this isomorphism:
--
--   G ∋ T
-- ≡ [T1 , .. , S , .. , Tn] ∋ T
-- ≅ T1 ≡ T ⊎ .. ⊎ S ≡ T ⊎ .. ⊎ Tn ≡ T
-- ≅ (T1 ≡ T ⊎ .. ⊎ Tn ≡ T) ⊎ S ≡ T  
-- ≅ (G - u) ∋ T ⊎ S ≡ T
--
-- thin and thick below are the witnesses

_-_ : ∀ {A T} → (G : List A) → G ∋ T → List A
(T ∷ G) - zero  = G
(S ∷ G) - suc x = S ∷ (G - x) 

infix 35 _-_

length-del : ∀ {A}{S : A}{X} -> (u : X ∋ S) -> length X ≡ suc (length (X - u))
length-del zero = refl
length-del (suc u) = cong suc (length-del u)

thin : ∀ {A} {G : List A}{S} → (x : G ∋ S) → ∀ T → (G - x) ∋ T → G ∋ T
thin zero    _ y    = suc y
thin (suc x) _ zero = zero
thin (suc x) _ (suc y) = suc (thin x _ y)

suc-inj1 : ∀ {A : Set}{xs : List A}{x z} {i : xs ∋ x}{j : xs ∋ x} → _∋_.suc {S = z} i ≡ suc j → i ≡ j
suc-inj1 refl = refl

x∉thinx : ∀ {A} {G : List A}{S} → (x : G ∋ S) → (y : (G - x) ∋ S) -> x ≡ thin x S y -> ⊥
x∉thinx zero    y    () 
x∉thinx (suc x) zero ()
x∉thinx (suc x) (suc y) eq = x∉thinx x y (suc-inj1 eq)

thick : ∀ {A}{G : List A}{S T} → (x : G ∋ S) → (y : G ∋ T) → (∃ \ z → thin x T z ≡ y) ⊎ x ≅∋ y
thick zero    zero    = inj₂ refl`
thick zero    (suc y) = inj₁ (y , refl)
thick (suc x) zero    = inj₁ (zero , refl)
thick (suc x) (suc y) with thick x y
thick (suc x)  (suc y)   | inj₁ (z , eq) = inj₁ (suc z , cong suc eq)
thick (suc .y) (suc y)   | inj₂ refl`    = inj₂ refl`

thick-refl : ∀ {A}{G : List A}{S} → (x : G ∋ S) → thick x x ≡ inj₂ refl`
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

_≅∋?_ : ∀ {A : Set} {G : List A} {S} (u : G ∋ S) {T} (v : G ∋ T) -> Dec (u ≅∋ v)
u ≅∋? v         with thick u v
...                | inj₂ eq         = yes eq
_≅∋?_ {S = S} u ._ | inj₁ (w , refl) = no (aux w) where
  aux : ∀ {T} (w : _ ∋ T) -> Σ (S ≡ T) (λ x → u ≅ thin u T w) → ⊥
  aux w (refl , eq) = x∉thinx u w (≅-to-≡ eq)
 

any? : ∀ {A : Set}{G : List A}{P : ∀ {S} -> G ∋ S -> Set} -> (∀ {S} v -> Dec (P {S} v)) -> Dec (∃ \ S -> ∃ (P {S}))
any? {_} {[]}    dec = no (\ {(_ , () , _)})
any? {_} {S ∷ G} dec 
 with dec zero | any? (\ v -> dec (suc v))
... | yes p    | _               = yes (_ , zero , p)
... | no ¬p    | yes (T , v , p) = yes (T , suc v , p)
... | no ¬p    | no ¬q           = no  λ {(._ , zero , p) → ¬p p; 
                                          (_ , suc v , p) → ¬q (_ , v , p)}

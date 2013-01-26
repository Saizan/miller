module Presheaves (T : Set) where
open import Data.List
open import Vars
open import Vars.SumIso
open import Data.Product

_op : Set → Set
X op = X

Π : List T -> (T -> Set) -> Set
Π σs P = ∀ {σ} -> σs ∋ σ -> P σ

Hom : List T → List T → Set -- free cocomplete category on T
Hom xs ys = ∀ {x} → (σ : xs ∋ x) → ys ∋ x

Presheaf : Set₁
Presheaf = List T → Set -- functor

Univ : Set₁
Univ = T → Presheaf  

y : List T op → Presheaf
y τ = λ σs → Hom τ σs

_^_ : Presheaf → Presheaf → Presheaf
X ^ Y = λ σs → (τs : _) → Hom σs τs → Y τs → X τs

_⊙_ : Presheaf → Univ → Presheaf
P ⊙ Y = λ τs → ∃ (λ σs → (P σs) × (Π σs \ σ → Y σ τs))
            -- ^ coend

_∙_ : Univ → Univ → Univ
X ∙ Y = \ τ → X τ ⊙ Y 

V : Univ
V τ = y (τ ∷ [])

_⇒_ : Univ → Univ → Set
X ⇒ Y = ∀ τ σs → X τ σs → Y τ σs -- natural in σs

open import Data.Sum
module Mon (A : Univ) (unit : V ⇒ A) (mul : (A ∙ A) ⇒ A) where
  
  ι : ∀ {γs γ} → γs ∋ γ → A γ γs
  ι {γs} {γ} v = unit γ γs (λ { {.γ} zero → v; (suc ())})

  ς : ∀ {σs τ} → ∀ γs → ((A τ ^ y σs) γs) × (Π σs \ σ → A σ γs) → A τ γs 
  ς {σs} {τ} γs (t , ts) = mul τ γs ((σs ++ γs) , ((t (σs ++ γs) (λ v → glue# σs (inj₂ v)) (λ v → glue# σs (inj₁ v))) 
                                                , (λ x → [ ts , ι ]′ (split# σs x))))

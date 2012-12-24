module MetaRens where

open import Data.Product renaming (map to mapΣ)
open import Data.Nat hiding (_≤_) renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality hiding ([_])
import Relation.Binary.HeterogeneousEquality as Het
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; _≇_ ; refl; ≅-to-≡)
open ≡-Reasoning
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.List.All

open import Injection
open import Limits.Injection
open import Lists
open import Vars2 

open import Syntax
open import Equality


record VarClosure (D : MCtx) (S : MTy) : Set where
  constructor _/_
  field
    {Ψ} : Ctx
    ρ-env : Inj Ψ (ctx S)
    body : D ∋ (type S <<- Ψ)

open VarClosure public 

map-Vc : ∀ {τ D S0 S} → Inj S0 S → VarClosure D (τ <<- S0) → VarClosure D (τ <<- S)
map-Vc j (i / u) = ((j ∘i i) / u)

record _≈vc_ {D S}(x y : VarClosure D S) : Set where
   constructor vc
   field
     Ψeq : Ψ x ≡ Ψ y
     ρeq : ρ-env x ≅ ρ-env y
     beq : body x ≅ body y

to-vc : ∀ {D S}{x y : VarClosure D S} → x ≡ y → x ≈vc y
to-vc refl = vc refl refl refl

promote : ∀ {D S}{x y : VarClosure D S} → x ≈vc y → x ≡ y
promote (vc refl refl refl) = refl

map-Vc-inj : ∀ {τ D S0 S} → (i : Inj S0 S) → {x y : VarClosure D (τ <<- S0)} → map-Vc i x ≈vc map-Vc i y -> x ≡ y
map-Vc-inj i {ix / x} {jy / .x} (vc refl eq refl) = cong₂ _/_ (∘i-inj i _ _ (≅-to-≡ eq)) refl

left-map[id] : ∀ {D S} -> {x : VarClosure D S} -> map-Vc id-i x ≡ x
left-map[id] = cong₂ _/_ (left-id _) refl

MetaRen : MCtx → MCtx → Set
MetaRen G D = ∀ S → G ∋ S → VarClosure D S

toSub : ∀ {Sg G D} → MetaRen G D → Sub Sg G D
toSub r = λ S x → fun (body (r S x)) (ρ-env (r S x))

idmr : ∀ {G} → MetaRen G G
idmr = \ S x → id-i / x

_∘mr_ : ∀ {G1 G2 G3} → MetaRen G2 G3 → MetaRen G1 G2 → MetaRen G1 G3
f ∘mr g = λ S x → let gr = g S x in map-Vc (ρ-env gr) (f _ (body gr))

-- Kleisli star
_⋆_ : ∀ {G D} → MetaRen G D → ∀ {S} → VarClosure G S → VarClosure D S
f ⋆ (i / u) = map-Vc i (f _ u)

bind : ∀ {G D} → MetaRen G D → ∀ {S} → VarClosure G S → VarClosure D S
bind = _⋆_

singleton : ∀ {G S} → (u : G ∋ S) → ∀ {Ψ} → Inj Ψ (ctx S) → MetaRen G ((G - u) <: (type S <<- Ψ))
singleton  u j  T v with thick u v
singleton  u j  T v | inj₁ x             = id-i / suc (proj₁ x)
singleton .v j ._ v | inj₂ (refl , refl) = j / zero 

singleton-refl : ∀ {G S} (u : G ∋ S) {Ψ} (i : Inj Ψ (ctx S)) → singleton u i _ u ≡ i / zero
singleton-refl u i rewrite thick-refl u = refl

singleton-thin : ∀ {G S} (u : G ∋ S) {Ψ} (i : Inj Ψ (ctx S)) → ∀ {T} (v : (G - u) ∋ T) → singleton u i _ (thin u T v) ≡ id-i / (suc v)
singleton-thin u i v rewrite thick-thin u v = refl

wk : ∀ {D S x} → VarClosure D S → VarClosure (x ∷ D) S
wk (i / u) = i / (suc u)

wk-inj : ∀ {G S x} {u v : VarClosure G S} -> wk {G} {S} {x} u ≡ wk v -> u ≡ v
wk-inj refl = refl

_≡mr_ : ∀ {G D} (f g : MetaRen G D) -> Set
f ≡mr g = ∀ S x -> f S x ≡ g S x

∘mr-resp-≡  : ∀ {A B C} {f h : MetaRen B C} {g i : MetaRen A B} → f ≡mr h → g ≡mr i → (f ∘mr g) ≡mr (h ∘mr i)
∘mr-resp-≡ f≡h g≡i S x rewrite g≡i S x = cong (map-Vc _) (f≡h _ _)

singleton-inv : ∀ {G S}(u : G ∋ S) {Ψ} (i : Inj Ψ (ctx S)) -> let f = singleton u i in 
                 ∀ S (x : _ ∋ S) -> ∃ \ Ψ -> ∃ \ y -> ∃ \ j -> f (type S <<- Ψ) y ≡ j / x
singleton-inv u i ._ zero    = _ , u          , i    , singleton-refl u i
singleton-inv u i  S (suc x) = _ , thin u S x , id-i , singleton-thin u i x

import Category

module MRop = Category MCtx (λ X Y → MetaRen Y X) (λ f g → g ∘mr f) idmr (λ f g → ∀ S x → f S x ≡ g S x) 
module MRopProps = MRop.Props (λ S x → cong₂ _/_ (sym assoc-∘i) refl) (λ S x → left-map[id]) (λ S x → cong₂ _/_ (right-id _) refl) 
             (λ {A} {B} → record { refl = λ S x₁ → refl; sym = λ x S x₁ → sym (x _ _); trans = λ x x₁ S x₂ → trans (x S x₂) (x₁ S x₂) }) 
             (λ eq₁ eq₂ S x → ∘mr-resp-≡ eq₂ eq₁ S x)

id-epic : ∀ {G} -> MRop.Monic (idmr {G})
id-epic eq S x = map-Vc-inj id-i (to-vc (eq S x))

singleton-epic : ∀ {G S}(u : G ∋ S) {Ψ} (i : Inj Ψ (ctx S)) -> let f = singleton u i in 
                 MRop.Monic f
singleton-epic u i eq S x with singleton-inv u i S x 
... | _ , y , j , eq' with eq _ y 
... | eq'' rewrite eq' = map-Vc-inj j (to-vc eq'')

eval : ∀ {p} {A : Set} {P : A → Set p} {xs : List A} →
         All P xs → (∀ (x : A) → xs ∋ x → P x)
eval (px ∷ f) x zero = px
eval (px ∷ f) x (suc u) = eval f x u
eval [] _ ()

reify : ∀ {p} {A : Set} {P : A → Set p} {xs} →
           (f : ∀ x → xs ∋ x → P x) → Σ (All P xs) \ a -> (∀ x i -> eval a x i ≡ f x i)
reify {p} {A} {P} {[]}     f = [] , \ _ ()
reify {p} {A} {P} {x ∷ xs} f = (f x zero ∷ proj₁ rec) , (\ { ._ zero -> refl ; _ (suc i) -> proj₂ rec _ i})
  where rec = reify (λ x u → f x (suc u)) 

_hasBody_ : ∀ {G}{T}(cl : VarClosure G T) {S}(x : G ∋ S) -> Set
_hasBody_ {G} {T} cl {S} x = ∃ \ (j : Inj (ctx S) (ctx T)) -> type T ≡ type S × cl ≅ (j / x)

dec-HasBody : ∀ {G}{T}(cl : VarClosure G T) {S}(x : G ∋ S) -> Dec (cl hasBody x) 
dec-HasBody (j / y) x with y ≡∋? x 
dec-HasBody {G} {.type₁ <<- ctx₁} (j / .x) {type₁ <<- ctx} x | yes (refl , refl) = yes (j , refl , refl)
dec-HasBody {G} {type <<- ctx₁} (j / y) {type₁ <<- ctx} x | no ¬p = no (aux ¬p)
  where aux : ∀ {type}{y : _ ∋ (type <<- _)} -> (¬ (y ≡∋ x)) -> Σ (Inj ctx ctx₁) (λ j₁ → Σ (type ≡ type₁) (λ x₁ → j / y ≅ j₁ / x)) → ⊥ 
        aux ¬p₁ (proj₁ , refl , eq) = ¬p₁ ((cong (_<<-_ _) (_≈vc_.Ψeq (to-vc (≅-to-≡ eq)))) , (_≈vc_.beq (to-vc (≅-to-≡ eq))))

Image : ∀ {G G1} (f : MetaRen G G1) {S} (x : G1 ∋ S) -> Set
Image f x = ∃ \ Ψ -> ∃ \ y -> ∃ \ j -> f (_ <<- Ψ) y ≡ j / x

thin1 : ∀ {S G T} -> VarClosure (S ∷ G) T -> VarClosure (S ∷ S ∷ G) T
thin1 (i / zero) = i / zero
thin1 (i / suc v) = i / (suc (suc v))

epic-inv : ∀ {G G1}(f : MetaRen G G1) -> MRop.Monic f -> ∀ S (x : _ ∋ S) -> Image f x
epic-inv f f-epic S x with any? (\ v -> dec-HasBody (f _ v) x) 
epic-inv f f-epic (._ <<- _) x | yes (T , v , j , refl , eq) = _ , v , j , ≅-to-≡ eq
epic-inv {G} {G1} f f-epic S x | no ¬p = ⊥-elim absurd where
  g1 = \ S v -> wk (singleton x id-i S v)
  g2 = \ S v -> thin1 (singleton x id-i S v)

  g1∘f≡g2∘f : (g1 ∘mr f) ≡mr (g2 ∘mr f)
  g1∘f≡g2∘f S v       with f _ v    | inspect (f _) v | thick x (body (f _ v))
  g1∘f≡g2∘f S₁ v         | jfv / fv | _               | inj₁ x₁            = refl
  g1∘f≡g2∘f (._ <<- _) v | jfv / .x | [ eq ]          | inj₂ (refl , refl) 
         = ⊥-elim (¬p (_ , v , jfv , refl , Het.≡-to-≅ eq))

  absurd : ⊥
  absurd with trans (f-epic {S ∷ S ∷ (G1 - x)} {g1} {g2} g1∘f≡g2∘f _ x) (cong thin1 (singleton-refl x id-i))
  ...       | ()

module Subop {Sg} = Category MCtx (λ X Y → Sub Sg Y X) (λ f g → g ∘s f) id-s _≡s_
module SubopProps {Sg : Ctx} where
  module X = Subop {Sg}
  module D = X.Props (\ {A} {B} {C} {D} {f} {g} {h} -> λ S u → sub-∘ (h S u)) 
                     (λ {A} {B} {f} S u → ren-id (f S u)) 
                     (λ {A} {B} {f} S u → sub-id (f S u)) 
                     (λ {A} {B} →
                          record {
                          refl = λ S x₁ → refl;
                          sym = λ x S x₁ → sym (x _ _);
                          trans = λ x x₁ S x₂ → trans (x S x₂) (x₁ S x₂) }) 
                     (λ {A} {B} {C} {f} {h} {g} {i} eq1 eq2 S u →
                          trans (cong (sub g) (eq1 S u)) (sub-ext eq2 (h S u)))
  open D public


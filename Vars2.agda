module Vars2 where

open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; _≇_ ; refl; ≅-to-≡)
open ≡-Reasoning
open import Data.Product
open import Data.Unit
open import Data.Maybe
open import Relation.Nullary
--open import Function hiding (_$_)
open import Data.Empty
open import Relation.Nullary.Decidable
open import Data.Sum

open import Vars

abstract
  _-[_,_] : ∀ {A} (G : List A) -> ∀ {S T} -> G ∋ S -> G ∋ T -> List A
  G -[ u , v ] with thick u v 
  ... | inj₂ _ = G - u
  ... | inj₁ (v' , _) = (G - u) - v'

data One⊎Other {A}{G : List A}{S S1} (x : G ∋ S)(z : G ∋ S1) : ∀ {T} -> G ∋ T -> Set where
  one : ∀ {y} -> (eq : x ≡ y) -> One⊎Other x z y
  other : ∀ {y} -> (neq : (eq : S1 ≡ S) -> ¬ x ≡ subst (_∋_ G) eq y) (eq : z ≡ y) -> One⊎Other x z y

abstract
  thin[_,_] : ∀ {A}{G : List A}{S S1 T} → (x : G ∋ S)(z : G ∋ S1) → (y : (G -[ x , z ]) ∋ T) -> G ∋ T
  thin[ x , z ] y with thick x z
  thin[ x , z ] y    | inj₁ (z' , _) = thin x _ (thin z' _ y)
  thin[ x , z ] y    | inj₂ _        = thin x _ y
  
  thin[_,_]-inj : ∀ {A}{G : List A}{S S1 T} → (x : G ∋ S)(z : G ∋ S1) → {y y' : (G -[ x , z ]) ∋ T} 
                  -> thin[ x , z ] y ≡ thin[ x , z ] y' -> y ≡ y'
  thin[ x , z ]-inj eq  with thick x z 
  ... | inj₁ (z' , _) = thin-inj z' (thin-inj x eq)
  ... | inj₂ _        = thin-inj x eq
  
  thin[_,_]-disjoint : ∀ {A}{G : List A}{S S1 T} → (x : G ∋ S)(z : G ∋ S1) → {y : (G -[ x , z ]) ∋ T} 
                       -> One⊎Other x z (thin[ x , z ] y) -> ⊥
  thin[ x ,  z ]-disjoint eq           with thick x z 
  thin[ x , ._ ]-disjoint (one eq)       | inj₁ (z' , refl)   = x∉thinx x _ eq
  thin[ x , ._ ]-disjoint (other _ eq)   | inj₁ (z' , refl)   = x∉thinx z' _ (thin-inj x eq)
  thin[ x , .x ]-disjoint (one eq)       | inj₂ (refl , refl) = x∉thinx x _ eq
  thin[ x , .x ]-disjoint (other neq eq) | inj₂ (refl , refl) = x∉thinx x _ eq

data Thick {A}{G : List A}{S S1} (x : G ∋ S)(z : G ∋ S1) {T : _} (y : G ∋ T) : Set where
  one⊎other : (eq : One⊎Other x z y) -> Thick x z y
  neither : (w : G -[ x , z ] ∋ T) -> (eq : thin[ x , z ] w ≡ y) -> Thick x z y

abstract
  thick[_,_] : ∀ {A}{G : List A}{S S1 T} → (x : G ∋ S)(z : G ∋ S1) → (y : G ∋ T) → Thick x z y
  thick[ x ,  z ]  y with thick x z          | thick x y          | neither {x = x} {z = z} {y = y} 
  thick[ x , .x ] ._    | inj₂ (refl , refl) | inj₁ (y' , refl)   | ne = ne y' refl 
  thick[ x , .x ] .x    | inj₂ (refl , refl) | inj₂ (refl , refl) | ne = one⊎other (one refl)
  thick[ x ,  z ] .x    | inj₁ (z' , eq)     | inj₂ (refl , refl) | ne = one⊎other (one refl)
  thick[ x ,  z ]  y    | inj₁ (z' , eq)     | inj₁ (y' , eq')    | ne with thick z' y' 
  thick[ x , ._ ] ._    | inj₁ (z' , refl)   | inj₁ (._ , refl)   | ne    | inj₁ (y'' , refl)  = ne y'' refl 
  thick[ x ,  z ] ._    | inj₁ (z' , eq)     | inj₁ (._ , refl)   | ne    | inj₂ (refl , refl) = one⊎other (other neq (sym eq))
    where 
      neq : ∀ {S v} (eq₁ : S ≡ _) → x ≡ subst (_∋_ _) eq₁ (thin x _ v) → ⊥
      neq refl eq = x∉thinx x _ eq

  thick[_,_]-refl : ∀ {A}{G : List A}{S S1} → (x : G ∋ S)(z : G ∋ S1) → thick[ x , z ] x ≡ one⊎other (one refl)
  thick[ x , z ]-refl with thick[ x , z ] x 
  thick[ x , z ]-refl    | one⊎other (one refl)     = refl
  thick[ x , z ]-refl    | one⊎other (other neq eq) = ⊥-elim (neq refl refl)
  thick[ x , z ]-refl    | neither w eq             = ⊥-elim (thin[ x , z ]-disjoint (one (sym eq)))



  thick[_,_]-thin : ∀ {A} {G : List A}{S S1 T} → (x : G ∋ S)(z : G ∋ S1)(y : G -[ x , z ] ∋ T) → thick[ x , z ] (thin[ x , z ] y) ≡ neither y refl
  thick[ x , z ]-thin y with thick[ x , z ] (thin[ x , z ] y)
  ...                      | one⊎other eq  = ⊥-elim (thin[ x , z ]-disjoint eq)
  ...                      | neither y' eq with thin[ x , z ]-inj eq | eq
  thick[ x , z ]-thin y    | neither .y eq    | refl                 | refl = refl

thick[_,_]-refl₂ : ∀ {A}{G : List A}{S S1} → (x : G ∋ S)(z : G ∋ S1) → ∃ \ eq -> thick[ x , z ] z ≡ one⊎other eq
thick[ x ,  z ]-refl₂ with thick[ x , z ] z 
thick[ x ,  z ]-refl₂    | one⊎other eq = _ , refl
thick[ x ,  z ]-refl₂    | neither w eq with thick x z
thick[ x , ._ ]-refl₂    | neither w eq | inj₁ (z' , refl) = ⊥-elim (thin[ x , _ ]-disjoint (other neq (sym eq)))
    where 
      neq : ∀ {S} {z : _ ∋ S}{v : _ ∋ S} (eq₁ : S ≡ _) → x ≡ subst (_∋_ _) eq₁ (thin[ x , z ] v) → ⊥
      neq refl eq = thin[ x , _ ]-disjoint (one eq)

thick[ .z , z ]-refl₂ | neither w eq | inj₂ (refl , refl) = ⊥-elim (thin[ z , z ]-disjoint (one (sym eq))) -- 


thick[_,_]-refl₂₂ : ∀ {A}{G : List A}{S S1} → (x : G ∋ S)(z : G ∋ S1) 
                    → ((eq : S1 ≡ S) -> ¬ x ≡ subst (_∋_ G) eq z)
                    → ∃ \ neq -> thick[ x , z ] z ≡ one⊎other (other neq refl)
thick[ x , z ]-refl₂₂ neq with thick[ x , z ] z            | thick[ x , z ]-refl₂
thick[ x , z ]-refl₂₂ neq  | .(one⊎other (one eq))         | one eq , refl         = ⊥-elim (neq refl eq)
thick[ x , z ]-refl₂₂ neq₁ | .(one⊎other (other neq refl)) | other neq refl , refl = _ , refl

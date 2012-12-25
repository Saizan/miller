module Colimits.FinSet {Ty : Set} where

open import Data.Product renaming (map to mapΣ)
open import Data.Nat hiding (_≤_) renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; _≇_ ; refl; ≅-to-≡)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.List.Extras
open import Syntax
open import Vars

Fun : List Ty → List Ty → Set
Fun G D = ∀ S → G ∋ S → D ∋ S

idf : ∀ {G} -> Fun G G
idf = \ S x ->  x

_∘f_ : ∀ {G1 G2 G3} → Fun G2 G3 → Fun G1 G2 → Fun G1 G3
f ∘f g = λ S x → f S (g S x)

import Category

module Fop = Category (List Ty) (λ X Y → Fun Y X) (λ f g → g ∘f f) idf (λ f g → ∀ S x → f S x ≡ g S x) 

open import Data.List.All

eval : ∀ {p} {A : Set} {P : A → Set p} {xs : List A} →
         All P xs → (∀ (x : A) → xs ∋ x → P x)
eval (px ∷ f) x zero = px
eval (px ∷ f) x (suc u) = eval f x u
eval [] _ ()

reify : ∀ {p} {A : Set} {P : A → Set p} {xs} → (∀ x → xs ∋ x → P x) → All P xs
reify {p} {A} {P} {[]} f = []
reify {p} {A} {P} {x ∷ xs} f = (f x zero) ∷ (reify (λ x u → f x (suc u))) 

abstract
  _-[_,_] : ∀ {A} (G : List A) -> ∀ {S T} -> G ∋ S -> G ∋ T -> List A
  G -[ u , v ] with thick u v 
  ... | inj₂ _ = G - u
  ... | inj₁ (v' , _) = (G - u) - v'

abstract
  thin[_,_] : ∀ {A}{G : List A}{S S1 T} → (x : G ∋ S)(z : G ∋ S1) → (y : (G -[ x , z ]) ∋ T) -> G ∋ T
  thin[ x , z ] y with thick x z
  thin[_,_] x z y    | inj₁ (z' , _) = thin x _ (thin z' _ y)
  thin[_,_] x z y    | inj₂ _        = thin x _ y
  
  thin[_,_]-inj : ∀ {A}{G : List A}{S S1 T} → (x : G ∋ S)(z : G ∋ S1) → {y y' : (G -[ x , z ]) ∋ T} 
                  -> thin[ x , z ] y ≡ thin[ x , z ] y' -> y ≡ y'
  thin[ x , z ]-inj eq  with thick x z 
  ... | inj₁ (z' , _) = thin-inj z' (thin-inj x eq)
  ... | inj₂ _        = thin-inj x eq
  
  thin[_,_]-disjoint : ∀ {A}{G : List A}{S} → (x : G ∋ S)(z : G ∋ S) → {y : (G -[ x , z ]) ∋ S} 
                       -> (x ≡ thin[ x , z ] y ⊎ z ≡ thin[ x , z ] y) -> ⊥
  thin[ x , z ]-disjoint eq with thick x z 
  thin[_,_]-disjoint {A} {G} {S} x .(thin x S z') (inj₁ eq) | inj₁ (z' , refl) = x∉thinx x _ eq
  thin[_,_]-disjoint {A} {G} {S} x .(thin x S z') (inj₂ eq) | inj₁ (z' , refl) = x∉thinx z' _ (thin-inj x eq)
  thin[_,_]-disjoint .z z eq | inj₂ (refl , refl) = x∉thinx z _ ([ (λ x → x) , (λ x → x) ]′ eq)

data Thick {A}{G : List A}{S} (x : G ∋ S)(z : G ∋ S) : {T : _} -> (y : G ∋ T) -> Set where
  one⊎other : ∀ {y} -> (eq : x ≡ y ⊎ (x ≢ y × z ≡ y)) -> Thick x z y
  neither : ∀ {T y} -> (w : G -[ x , z ] ∋ T) -> (eq : thin[ x , z ] w ≡ y) -> Thick x z y

abstract
  thick[_,_] : ∀ {A}{G : List A}{S T} → (x : G ∋ S)(z : G ∋ S) → (y : G ∋ T) → Thick x z y
  thick[ x , z ] y with thick x z          | thick x y          | neither {x = x} {z = z} {y = y} 
  thick[_,_] x .x ._  | inj₂ (refl , refl) | inj₁ (y' , refl)   | ne = ne y' refl 
  thick[_,_] x .x .x  | inj₂ (refl , refl) | inj₂ (refl , refl) | ne = one⊎other (inj₁ refl)
  thick[_,_] x  z .x  | inj₁ (z' , eq)     | inj₂ (refl , refl) | ne = one⊎other (inj₁ refl)
  thick[_,_] x  z  y  | inj₁ (z' , eq)     | inj₁ (y' , eq')    | ne with thick z' y' 
  thick[_,_] x ._ ._  | inj₁ (z' , refl)   | inj₁ (._ , refl)   | ne    | inj₁ (y'' , refl)  = ne y'' refl 
  thick[_,_] x  z ._  | inj₁ (z' , eq)     | inj₁ (._ , refl)   | ne    | inj₂ (refl , refl) = one⊎other (inj₂ (x∉thinx x z' , sym eq))

  thick[_,_]-refl : ∀ {A}{G : List A}{S} → (x : G ∋ S)(z : G ∋ S) → thick[ x , z ] x ≡ one⊎other (inj₁ refl)
  thick[ x , z ]-refl with thick[ x , z ] x 
  thick[ x , z ]-refl    | one⊎other (inj₁ refl) = refl
  thick[ x , z ]-refl    | one⊎other (inj₂ y)    = ⊥-elim (proj₁ y refl)
  thick[ x , z ]-refl    | neither w eq          = ⊥-elim (thin[ x , z ]-disjoint (inj₁ (sym eq)))

  thick[_,_]-thin : ∀ {A} {G : List A}{S T} → (x : G ∋ S)(z : G ∋ S)(y : G -[ x , z ] ∋ T) → thick[ x , z ] (thin[ x , z ] y) ≡ neither y refl
  thick[ x , z ]-thin y with thick[ x , z ] (thin[ x , z ] y)
  ...                      | one⊎other eq  = ⊥-elim (thin[ x , z ]-disjoint (Data.Sum.map (λ x₁ → x₁) proj₂ eq))
  ...                      | neither y' eq with thin[ x , z ]-inj eq | eq
  thick[_,_]-thin x z y    | neither .y eq    | refl                 | refl = refl

postulate
 coproduct : ∀ {A B} -> (f : Fun [] A)(g : Fun [] B) -> Fop.Pullback f g

equalizer : ∀ {Z X} -> (f : All (_∋_ X) Z)(g : All (_∋_ X) Z) -> Fop.Equalizer (eval f) (eval g)
equalizer {[]} f g = Fop.Equ _ , idf , record {
                                         commutes = λ _ → λ ();
                                         universal = λ m commutes S x → m S x;
                                         universal-unique = λ u e∘u≡m S x → e∘u≡m S x;
                                         e∘universal≡m = λ S x → refl }
equalizer {τ ∷ Z} {X} (u ∷ f) (v ∷ g) 
  = Category.Equ E' , e' , 
    record {
      commutes = ∋-case commz comms;
      universal = universal';
      universal-unique = universal-unique';
      e∘universal≡m = e∘universal≡m' }
 where
   open Fop.Equalizer (equalizer f g)
   eu = e _ u
   ev = e _ v

   E' : List Ty
   E' = τ ∷ (E -[ e _ u , e _ v ])

   e'' : ∀ S {ez : E ∋ S} -> Thick eu ev ez -> E' ∋ S
   e'' S  (neither w _) = suc w
   e'' .τ (one⊎other _) = zero
   e' : Fun X E'
   e' S z = e'' S (thick[ eu , ev ] (e _ z))

   e'u≡zero : e' _ u ≡ zero
   e'u≡zero rewrite thick[ eu , ev ]-refl = refl

   commz : e' τ u ≡ e' τ v
   commz with thick[ eu , ev ] eu | thick[ eu , ev ] ev
   commz    | one⊎other _         | one⊎other _  = refl
   commz    | neither w eq        | _            = ⊥-elim (thin[ eu , ev ]-disjoint (inj₁ (sym eq)))
   commz    | _                   | neither w eq = ⊥-elim (thin[ eu , ev ]-disjoint (inj₂ (sym eq)))

   comms : (a : Ty) (y : Z ∋ a) → e' a (eval (u ∷ f) a (suc y)) ≡ e' a (eval (v ∷ g) a (suc y))
   comms a y rewrite commutes a y = refl

   universal' : {Q : List Ty} (m : (S : Ty) → X ∋ S → Q ∋ S) →
      ((S : Ty) (x : τ ∷ Z ∋ S) → m S (eval (u ∷ f) S x) ≡ m S (eval (v ∷ g) S x)) →
      (S : Ty) → E' ∋ S → Q ∋ S
   universal' m m-comm .τ zero = m _ u
   universal' m m-comm S (suc z) = universal m (λ S₁ x → m-comm S₁ (suc x)) S (thin[ eu , ev ] z)

   e∘universal≡m' : {Q : List Ty} {m : (S : Ty) → X ∋ S → Q ∋ S}
                    {m-comm : (S : Ty) (x : τ ∷ Z ∋ S) → m S (eval (u ∷ f) S x) ≡ m S (eval (v ∷ g) S x)}
                    (S : Ty) (x : X ∋ S) → universal' m m-comm S (e' S x) ≡ m S x
   e∘universal≡m' {Q} {m} {m-comm}  S x with thick[ eu , ev ] (e S x) 
   e∘universal≡m' {Q} {m} {m-comm}  S x    | neither w eq rewrite eq = e∘universal≡m S x
   e∘universal≡m' {Q} {m} {m-comm} .τ x    | one⊎other eq = trans p (e∘universal≡m _ x)
     where
       p : m τ u ≡ universal m (λ S₁ x₁ → m-comm S₁ (suc x₁)) τ (e τ x)
       p with eq 
       ... | inj₁ eq rewrite sym eq = sym (e∘universal≡m _ u) 
       ... | inj₂ (_ , eq) rewrite sym eq = trans (m-comm _ zero) (sym (e∘universal≡m _ v))


   universal-unique' : {Q : List Ty} {m : (S : Ty) → X ∋ S → Q ∋ S}
      {commutes₁ : (S : Ty) (x : τ ∷ Z ∋ S) → m S (eval (u ∷ f) S x) ≡ m S (eval (v ∷ g) S x)}
      (u₁ : (S : Ty) → E' ∋ S → Q ∋ S) →
      ((S : Ty) (x : X ∋ S) → u₁ S (e' S x) ≡ m S x) →
      (S : Ty) (x : E' ∋ S) → u₁ S x ≡ universal' m commutes₁ S x
   universal-unique' uni uni∘e'≡m .τ zero = trans (cong (uni _) (sym e'u≡zero)) (uni∘e'≡m _ u)
   universal-unique' {Q} {m} {m-comm} uni uni∘e'≡m S (suc z) 
     = trans uni[sucz]≡uni'[thin[eu,ev][z]] (universal-unique {Q} {m} {λ S₁ x₂ → m-comm S₁ (suc x₂)} uni' uni'∘e≡m S (thin[ eu , ev ] z))
    where
      uni' : (S₁ : Ty) → E ∋ S₁ → Q ∋ S₁
      uni' S x with thick[ eu , ev ] x
      uni' .τ x | one⊎other eq = uni τ zero
      uni' S₁ x | neither w eq = uni S₁ (suc w)
      
      uni'∘e≡m : ((S : Ty) (x : X ∋ S) → uni' S (e S x) ≡ m S x)
      uni'∘e≡m S x with thick[ eu , ev ] (e _ x) | uni∘e'≡m S x  
      uni'∘e≡m .τ x   | one⊎other eq             | qq = qq
      uni'∘e≡m S₁ x   | neither w eq             | qq = qq

      uni[sucz]≡uni'[thin[eu,ev][z]] : uni S (suc z) ≡ uni' S (thin[ e τ u , e τ v ] z)
      uni[sucz]≡uni'[thin[eu,ev][z]] rewrite thick[ eu , ev ]-thin z = refl

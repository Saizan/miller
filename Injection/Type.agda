module Injection.Type where

open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Data.Sum

open import Vars

-- Inj X Y is a first-order representation for injective maps (∀ S → X ∋ S -> Y ∋ S). 
-- It's a little clunkier to work with but its propositional equality
-- is extensional which saves the trouble of proving that
-- the properties we'll care about respect the pointwise equality.
--
-- The isomorphism with the functional representation is witnessed by quo and _$_ below,
-- among some convenience lemmas.
mutual
  data Inj {A : Set}: (List A) → List A → Set where
    []  : ∀ {xs} → Inj [] xs
    _∷_[_] : ∀ {xs} {y} {ys : List A} (i : y ∈ xs) (is : Inj ys xs) (pf : (i ∉ is)) → Inj (y ∷ ys) xs

  _∉_ : ∀ {A : Set}{y : A} {xs ys} → y ∈ xs → Inj ys xs → Set
  pf ∉ [] = ⊤ 
  pf ∉ (i ∷ pfs [ pf₁ ]) = False (eq-∋ (_ , pf) (_ , i)) × pf ∉ pfs

proof-irr-False : ∀ {P : Set}{d : Dec P} -> (p q : False d) -> p ≡ q
proof-irr-False {d = yes _} () _
proof-irr-False {d = no  _} _ _ = refl

proof-irr-∉ : ∀ {A : Set} {xs ys} {y : A} {i : y ∈ xs} (f : Inj ys xs) → (p q : i ∉ f) → p ≡ q
proof-irr-∉ []             p        q        = refl
proof-irr-∉ (v ∷ f [ pf ]) (Fp , p) (Fq , q) = cong₂ _,_ (proof-irr-False Fp Fq) (proof-irr-∉ f p q)

cong-∷[] : ∀ {A : Set}{xs ys} {y : A}
           {i j : y ∈ xs}      → i  ≡ j  → 
           {is js : Inj ys xs} → is ≡ js → 
           ∀ {pf1 pf2} → i ∷ is [ pf1 ] ≡ j ∷ js [ pf2 ]
cong-∷[] {i = i} refl {is} refl {pf1} {pf2}  = cong (λ pf → i ∷ is [ pf ]) (proof-irr-∉ is pf1 pf2)

mkFalse : ∀ {P : Set} → (P → ⊥) → ∀ {d : Dec P} → False d
mkFalse ¬p {yes p} = ¬p p
mkFalse ¬p {no ¬p₁} = tt 

fromFalse : ∀ {P : Set} {d : Dec P} → False d → P → ⊥
fromFalse {P} {yes p} ()
fromFalse {P} {no ¬p} _ = ¬p

quo' : ∀ {A : Set} {xs ys} → (f : ∀ (x : A) → x ∈ xs → x ∈ ys){inj : ∀ x → {i j : x ∈ xs} → f x i ≡ f x j → i ≡ j} → 
    Σ (Inj xs ys) \ is → (∀ x (i : x ∈ ys) → (∀ y j → False (eq-∋ (_ , i) (_ , f y j))) → (i ∉ is))
quo' {_} {[]} f {inj} = [] , (λ x i x₁ → _)
quo' {_} {x ∷ xs} f {inj} = is , proof where
   rec = (quo' {_} {xs} (λ x₁ x₂ → f x₁ (suc x₂)) {(λ x₁ x₂ → suc-inj1 (inj x₁ x₂))})
   abstract
    pf : f x zero ∉ proj₁ (quo' (λ x₁ x₂ → f x₁ (suc x₂)) {(λ x₁ x₂ → suc-inj1 (inj x₁ x₂))})
    pf = proj₂ rec x (f x zero) (λ y j → mkFalse (lemmma y j))  
      where lemmma : ∀ y j → (x , f x zero) ≡ (y , f y (suc j)) → ⊥
            lemmma y j eq with cong proj₁ eq
            lemmma .x j eq | refl with f x zero | inj x {zero} {suc j}  
            lemmma ._ j refl | refl | .(f x (suc j)) | q with q refl 
            ... | ()
   is = f x zero ∷ proj₁ rec [ pf ]
  
   proof : ∀ x i → (∀ y j → False (eq-∋ (_ , i) (_ , f y j))) → i ∉ is
   proof z i e = e x zero , proj₂ rec z i (λ y j → e y (suc j))

quo : ∀ {A : Set} {xs ys} → (f : ∀ (x : A) → x ∈ xs → x ∈ ys){inj : ∀ x → {i j : x ∈ xs} → f x i ≡ f x j → i ≡ j} → (Inj xs ys)
quo f {inj} = proj₁ (quo' f {inj})

quo-ext : ∀ {A : Set} {xs ys} → {f : ∀ (x : A) → x ∈ xs → x ∈ ys}{injf : ∀ x → {i j : x ∈ xs} → f x i ≡ f x j → i ≡ j} →
            {g : ∀ (x : A) → x ∈ xs → x ∈ ys}{injg : ∀ x → {i j : x ∈ xs} → g x i ≡ g x j → i ≡ j} →
            (∀ x v → f x v ≡ g x v) → quo f {injf} ≡ quo g {injg}
quo-ext {A} {[]}                                 eq = refl
quo-ext {A} {x ∷ xs} {injf = injf} {injg = injg} eq = cong-∷[] (eq _ zero) (quo-ext {injf = λ x₁ x₂ → suc-inj1 (injf x₁ x₂)} 
                                                                                    {injg = λ x₁ x₂ → suc-inj1 (injg x₁ x₂)} (λ x₁ v → eq x₁ (suc v)))

_$_ : ∀ {A : Set} {xs ys : List A} → Inj xs ys → ∀ {x} → x ∈ xs → x ∈ ys
(i ∷ is [ pf ]) $ zero = i
(i ∷ is [ pf ]) $ suc x₂ = is $ x₂
[] $ () 

_∉Im_ : ∀ {A : Set} {xs ys : List A} → ∀ {x} (i : x ∈ ys) → (f : Inj xs ys) → Set
i ∉Im f = ∀ b → ¬ i ≡ f $ b
  
∉-∉Im : ∀ {A : Set} {xs ys : List A} → (f : Inj xs ys) → ∀ {x} (i : x ∈ ys) → i ∉ f → i ∉Im f
∉-∉Im (i₁ ∷ f [ pf ]) .i₁ i∉f zero refl = fromFalse (proj₁ i∉f) refl
∉-∉Im (i₁ ∷ f [ pf ]) i i∉f (suc b) eq = ∉-∉Im f i (proj₂ i∉f) b eq
∉-∉Im [] _ _ () _

∉Im-∉ : ∀ {A : Set} {xs ys : List A} → (f : Inj xs ys) → ∀ {x} (i : x ∈ ys) → i ∉Im f → i ∉ f
∉Im-∉ [] _ _ = _
∉Im-∉ {_}{x ∷ _} {ys} (i ∷ f [ pf ]) {t} i₁ ¬p = mkFalse (aux i pf ¬p) , ∉Im-∉ f i₁ (λ b x → ¬p (suc b) x)
    where aux : ∀ {x} (i : ys ∋ x) pf → i₁ ∉Im (i ∷ f [ pf ]) → (t , i₁) ≡ (x , i) → ⊥
          aux .i₁ pf₁ ¬Im refl = ¬Im zero refl

injective : ∀ {A : Set} {xs ys : List A} → (f : Inj xs ys) → ∀ {x} → (a b : x ∈ xs) → f $ a ≡ f $ b → a ≡ b
injective f zero zero eq = refl
injective (i ∷ f [ pf ]) zero (suc b) eq = ⊥-elim (∉-∉Im f i pf b eq)
injective (i ∷ f [ pf ]) (suc a₁) zero eq = ⊥-elim (∉-∉Im f i pf a₁ (sym eq))
injective (i ∷ f [ pf ]) (suc a₁) (suc b) eq = cong suc (injective f a₁ b eq)

iso1 : ∀ {A : Set} {xs ys : List A} → (f : Inj xs ys) → (inj : _) → quo (\ x v → f $ v) {inj} ≡ f
iso1 [] _ = refl
iso1 (i ∷ f [ pf ]) inj = cong-∷[] refl (iso1 f (λ x₁ x₂ → suc-inj1 (inj x₁ x₂)))

iso2 : ∀ {A : Set} {xs ys : List A} → (f : ∀ (x : A) → x ∈ xs → x ∈ ys)(inj : ∀ x → {i j : x ∈ xs} → f x i ≡ f x j → i ≡ j)
         → ∀ {x} (v : x ∈ xs) → quo f {inj} $ v ≡ f x v
iso2 f inj zero = refl
iso2 f inj (suc v) = iso2 (λ x₁ x₂ → f x₁ (suc x₂)) (λ x₁ x₂ → suc-inj1 (inj x₁ x₂)) v

iso1- : ∀ {A : Set} {xs ys : List A} → (f : Inj xs ys) → quo (\ x v → f $ v) {\ x -> injective f _ _} ≡ f

iso1- f = iso1 f _

ext-$ : ∀ {A : Set} {xs ys : List A} → (f g : Inj xs ys) → (∀ x (v : xs ∋ x) -> f $ v ≡ g $ v) -> f ≡ g
ext-$ f g eq = trans (sym (iso1- f)) (trans (quo-ext {injf = λ x → injective f _ _} {injg = λ x → injective g _ _} eq) (iso1- g))

∉Im$-∉ : ∀ {A : Set} {xs ys : List A} (f : ∀ x (v : x ∈ xs) → x ∈ ys){inj} 
     → ∀ {x} (i : x ∈ ys) → (∀ (b : x ∈ xs) → i ≡ f x b → ⊥) → i ∉ (quo f {inj}) 
∉Im$-∉ f {inj} i eq = ∉Im-∉ (quo f {inj}) i (λ b x → eq b (begin i ≡⟨ x ⟩ quo f $ b ≡⟨ iso2 f inj b ⟩ f _ b ∎))

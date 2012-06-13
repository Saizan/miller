module Injection where

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

data _∋_ {A : Set} : List A → A → Set where
  zero : ∀ {G T} → T ∷ G ∋ T
  suc : ∀ {G T S} → G ∋ T → S ∷ G ∋ T

zero≢suc : ∀ {A : Set}{x : A}{xs : List A}{i : xs ∋ x} -> _∋_.zero ≡ suc i -> ⊥
zero≢suc ()

∋-case : ∀ {A : Set}{xs : List A}{x} {P : ∀ a -> x ∷ xs ∋ a -> Set} -> P x zero -> (∀ a y -> P a (suc y)) -> ∀ a y -> P a y
∋-case z s a zero = z
∋-case z s a (suc v) = s a v
 
_-_ : ∀{A} {T} → (G : List A) → G ∋ T → List A
_-_ {_} {T} .(T ∷ G) (zero {G}) = G
._ - suc {G} {_} {S} x = S ∷ (G - x) 

infix 35 _-_

thin : ∀ {A} {G : List A}{S} → (x : G ∋ S) → ∀ T → (G - x) ∋ T → G ∋ T
thin zero _ y = suc y
thin (suc x) _ zero = zero
thin (suc x) _ (suc y) = suc (thin x _ y)

thick : ∀ {A}{G : List A}{S T} → (x : G ∋ S) → (y : G ∋ T) → (∃ \ z → thin x T z ≡ y) ⊎ ((S , x) ≡ (T , y))
thick zero zero = inj₂ refl
thick zero (suc y) = inj₁ (y , refl)
thick (suc x) zero = inj₁ (zero , refl)
thick (suc x) (suc y) with thick x y
thick (suc x) (suc y) | inj₁ (z , eq) = inj₁ (suc z , cong suc eq)
thick (suc .y) (suc y) | inj₂ refl = inj₂ refl

thick-refl : ∀ {A}{G : List A}{S} → (x : G ∋ S) → thick x x ≡ inj₂ refl
thick-refl zero = refl
thick-refl (suc x) rewrite thick-refl x = refl

thick-thin : ∀ {A}{G : List A}{S T} (x : G ∋ S) → (y : (G - x) ∋ T) → thick x (thin x T y) ≡ inj₁ (y , refl)
thick-thin zero y = refl
thick-thin (suc x) zero = refl
thick-thin (suc x) (suc y) rewrite thick-thin x y = refl

_∈_ : {A : Set} → A → List A → Set
_∈_ x xs = xs ∋ x

suc-inj : ∀ {A : Set}{xs : List A}{x y z} {i : xs ∋ x}{j : xs ∋ y} → (x , suc {S = z} i) ≡ (y , suc j) → (x , i) ≡ (y , j)
suc-inj refl = refl

suc-inj1 : ∀ {A : Set}{xs : List A}{x z} {i : xs ∋ x}{j : xs ∋ x} → suc {S = z} i ≡ suc j → i ≡ j
suc-inj1 refl = refl

eq-∋ : ∀ {A : Set}{xs : List A} → (i j : ∃ (_∋_ xs)) → Dec (i ≡ j)
eq-∋ (.y , zero) (y , zero) = yes refl
eq-∋ (x , zero)  (y , suc j) = no (λ ())
eq-∋ (x , suc i) (y , zero) = no (λ ())
eq-∋ (x , suc i) (y , suc j) with eq-∋ (x , i) (y , j)
eq-∋ (.y , suc .j) (y , suc j) | yes refl = yes refl
eq-∋ (x , suc i) (y , suc j) | no ¬p = no (¬p ∘ suc-inj)

cong-proj₁ : ∀ {A : Set}{xs : List A}{x : A} {i j : xs ∋ x} -> i ≡ j -> _≡_ {A = ∃ (_∋_ xs)} (x , i) (x , j)
cong-proj₁ refl = refl

mutual
  data Inj {A : Set}: (List A) → List A → Set where
    []  : ∀ {xs} → Inj [] xs
    _∷_[_] : ∀ {xs} {y} {ys : List A} (i : y ∈ xs) (is : Inj ys xs) (pf : (i ∉ is)) → Inj (y ∷ ys) xs

  _∉_ : ∀ {A : Set}{y : A} {xs ys} → y ∈ xs → Inj ys xs → Set
  pf ∉ [] = ⊤ 
  pf ∉ (i ∷ pfs [ pf₁ ]) = False (eq-∋ (_ , pf) (_ , i)) × pf ∉ pfs


proof-irr-∉ : ∀ {A : Set}{y : A} {xs ys} → (i : y ∈ xs) → (f : Inj ys xs) → (p q : i ∉ f) → p ≡ q
proof-irr-∉ i [] p q = refl
proof-irr-∉ i (i₁ ∷ f [ pf ]) p q with eq-∋ (_ , i) (_ , i₁) 
proof-irr-∉ i (i₁ ∷ f [ pf ]) (() , _) q | yes p 
proof-irr-∉ i (i₁ ∷ f [ pf ]) p q | no ¬p = cong (_,_ _) (proof-irr-∉ i f (proj₂ p) (proj₂ q))

cong-∷[] : ∀ {A : Set}{xs : List A}{y} {ys : List A} {i j : y ∈ xs} → i ≡ j → {is js : Inj ys xs} → is ≡ js → {pf1 : (i ∉ is)}{pf2 : j ∉ js} → 
           i ∷ is [ pf1 ] ≡ j ∷ js [ pf2 ]
cong-∷[] {i = i} refl {is} refl {pf1} {pf2}  = cong (λ pf → i ∷ is [ pf ]) (proof-irr-∉ i is pf1 pf2)

mkFalse : ∀ {P : Set} → (P → ⊥) → ∀ {d : Dec P} → False d
mkFalse ¬p {yes p} = ¬p p
mkFalse ¬p {no ¬p₁} = tt 

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
quo-ext {A} {[]} eq =  refl
quo-ext {A} {x ∷ xs} eq = cong-∷[] (eq _ zero) (quo-ext (λ x₁ v → eq x₁ (suc v)))

_$_ : ∀ {A : Set} {xs ys : List A} → Inj xs ys → ∀ {x} → x ∈ xs → x ∈ ys
(i ∷ is [ pf ]) $ zero = i
(i ∷ is [ pf ]) $ suc x₂ = is $ x₂
[] $ () 

fromFalse : ∀ {P : Set} {d : Dec P} → False d → P → ⊥
fromFalse {P} {yes p} ()
fromFalse {P} {no ¬p} _ = ¬p

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

∉Im$-∉ : ∀ {A : Set} {xs ys : List A} (f : ∀ x (v : x ∈ xs) → x ∈ ys){inj} 
     → ∀ {x} (i : x ∈ ys) → (∀ (b : x ∈ xs) → i ≡ f x b → ⊥) → i ∉ (quo f {inj}) 
∉Im$-∉ f {inj} i eq = ∉Im-∉ (quo f {inj}) i (λ b x → eq b (begin i ≡⟨ x ⟩ quo f $ b ≡⟨ iso2 f inj b ⟩ f _ b ∎))

invert : ∀ {A : Set} {xs ys : List A} (i : Inj xs ys) → ∀ {t} (y : ys ∋ t) → Dec (∃ \ x → (i $ x) ≡ y) 
invert [] x = no (λ { (() , _)})
invert (i ∷ f [ pf ]) y with eq-∋ (_ , i) (_ , y) 
invert (.y₁ ∷ f [ pf ]) y₁ | yes refl = yes (zero , refl)
invert (i ∷ f [ pf ]) y₁ | no ¬p with invert f y₁ 
invert (i ∷ f [ pf ]) y₁ | no ¬p | yes p = yes (suc (proj₁ p) , (proj₂ p))
invert (i ∷ f [ pf ]) y₁ | no ¬p₁ | no ¬p = no (lemmi ¬p₁ ¬p) where
    lemmi : ∀ {t} {y : _ ∋ t} → (¬ (_ , i) ≡ (t , y)) → (¬ ∃ \ x₂ → f $ x₂ ≡ y) → Σ (_ ∷ _ ∋ _) (λ x₂ → (i ∷ f [ pf ]) $ x₂ ≡ y) → ⊥
    lemmi ¬1 ¬2 (zero , p) = ¬1 (cong (_,_ _) p)
    lemmi ¬1 ¬2 (suc n , p) = ¬2 (n , p)

abstract
  _∘i_ : ∀ {A : Set}{xs ys zs : List A} → Inj ys zs → Inj xs ys → Inj xs zs
  f ∘i g = proj₁ (quo' (λ x x₁ → f $ (g $ x₁)) {(λ x x₁ → injective g _ _ (injective f _ _ x₁))})

  id-i : ∀ {A : Set}{xs : List A} → Inj xs xs
  id-i = quo (\ _ x → x) {\ _ e → e}
  
  id-i$ : ∀ {A : Set}{xs : List A} -> ∀ {x}(v : xs ∋ x) -> id-i $ v ≡ v
  id-i$ v = iso2 _ _ v

  right-id : ∀ {A : Set}{xs ys : List A} → (i : Inj xs ys) → i ∘i id-i ≡ i
  right-id i = begin quo (λ x z → i $ (id-i $ z)) ≡⟨ quo-ext (λ x v → cong (_$_ i) (iso2 _ _ v)) ⟩ 
                     quo (λ x → _$_ i)            ≡⟨ iso1 i (λ x eq → injective i _ _ eq) ⟩ 
                     i                            ∎

  left-id : ∀ {A : Set}{xs ys : List A} → (i : Inj xs ys) → id-i ∘i i ≡ i
  left-id i = begin quo (λ x z → id-i $ (i $ z)) ≡⟨ quo-ext (λ x v → (iso2 _ _ (i $ v))) ⟩ 
                    quo (λ x → _$_ i)            ≡⟨ iso1 i (λ x eq → injective i _ _ eq) ⟩ 
                    i                            ∎

  apply-∘ : ∀ {A : Set}{xs ys zs : List A} → (j : Inj ys zs) → (i : Inj xs ys) → ∀ {x} {v : x ∈ xs} → (j ∘i i) $ v ≡ j $ (i $ v)
  apply-∘ j i {x}{v} = iso2 _ _ v

  assoc-∘i : ∀ {A : Set}{xs ys ws zs : List A} {f : Inj ws zs}{g : Inj _ ws}{h : Inj xs ys} → f ∘i (g ∘i h) ≡ (f ∘i g) ∘i h  
  assoc-∘i {f = f}{g = g}{h = h} = quo-ext λ x v → 
      begin f $ (quo (λ x₁ x₂ → g $ (h $ x₂)) $ v) ≡⟨ cong (_$_ f) (iso2 _ _ v) ⟩ 
            f $ (g $ (h $ v))                      ≡⟨ sym (iso2 _ _ (h $ v)) ⟩ 
            quo (λ x₁ x₂ → f $ (g $ x₂)) $ (h $ v) ∎

  cong-$ : ∀ {A : Set}{xs ys : List A} {f g : _} {inj1 inj2} → quo {_} {xs} {ys} f {inj1} ≡ quo g {inj2} → ∀ {s} (x : xs ∋ s) → f s x ≡ g s x
  cong-$ {A} {xs} {ys} {f} {g} eq x = begin f _ x     ≡⟨ sym (iso2 f _ x) ⟩ 
                                            quo f $ x ≡⟨ cong (λ f₁ → f₁ $ x) eq ⟩ 
                                            quo g $ x ≡⟨ iso2 g _ x ⟩ 
                                            g _ x     ∎

  ∘i-inj : ∀ {A : Set}{xs ys zs : List A} → (i : Inj ys zs) (j1 j2 : Inj xs ys) → (i ∘i j1) ≡ (i ∘i j2) → j1 ≡ j2
  ∘i-inj i j1 j2 eq = begin j1                 ≡⟨ sym (iso1 j1 (λ x x₁ → injective j1 _ _ x₁)) ⟩ 
                            quo (λ x → _$_ j1) ≡⟨ quo-ext (λ x v → injective i _ _ (cong-$ eq v)) ⟩ 
                            quo (λ x → _$_ j2) ≡⟨ iso1 j2 (λ x x₁ → injective j2 _ _ x₁) ⟩ 
                            j2                 ∎

  weak : ∀ {A : Set}{x : A}{xs ys} → Inj xs ys → Inj xs (x ∷ ys)
  weak f = quo (λ x x₁ → suc (f $ x₁)) {λ x x₁ → injective f _ _ (suc-inj1 x₁)}

  lemma : ∀ {A : Set}{xs ys ts : List A} (i : Inj xs ts)(z : _){inj1 inj2 inj3} → 
            quo (\ x v → i $ (quo {_} {ys} z {inj1} $ v)) {inj3} ≡ quo (\ x v → i $ (z _ v)) {inj2} 
  lemma i z = quo-ext (λ x₁ v → cong (_$_ i) (iso2 z _ v))

  cons : ∀ {A : Set}{x : A}{xs ys} → Inj xs ys → Inj (x ∷ xs) (x ∷ ys)
  cons z = (zero ∷ weak z [ ∉Im$-∉ (λ x x₁ → suc (z $ x₁)) zero (λ {_ ()}) ])

  cons-id : ∀ {A : Set}{x : A}{xs} -> cons id-i ≡ id-i {_} {x ∷ xs}
  cons-id = cong-∷[] refl (quo-ext (λ x v → cong suc (iso2 _ _ v)))

  cons-∘i : ∀ {A : Set}{xs ys zs : List A}{x} → (j : Inj ys zs) → (i : Inj xs ys) → cons {A} {x} (j ∘i i) ≡ cons j ∘i cons i
  cons-∘i j i = cong-∷[] refl (begin 
    quo (λ x z → suc (proj₁ (quo' (λ v v₁ → j $ (i $ v₁))) $ z)) 
      ≡⟨ quo-ext {injg = λ x x₁ → injective i _ _ (injective (weak j) _ _ x₁)} (λ x v → 
          begin suc (proj₁ (quo' (λ v₁ v₂ → j $ (i $ v₂))) $ v) ≡⟨ cong suc (iso2 _ _ v) ⟩ 
                suc (j $ (i $ v))                               ≡⟨ sym (iso2 _ _ (i $ v)) ⟩ 
                quo (λ x₁ x₂ → suc (j $ x₂)) $ (i $ v)          ∎) ⟩ 
    quo (λ x v → cons j $ suc (i $ v))                       ≡⟨ sym (lemma (cons j) (λ _ x → suc (i $ x))) ⟩ 
    quo (λ x v → cons j $ (quo (λ z x₁ → suc (i $ x₁)) $ v)) ∎)

  intersect : ∀ {A : Set} {xs ys : List A} → (i j : Inj xs ys) → ∃ \ ts → Σ (Inj ts xs) \ r → (i ∘i r) ≡ (j ∘i r) 
              × (∀ a (y : xs ∋ a) -> i $ y ≡ j $ y -> ∃ \ z -> y ≡ r $ z)
  intersect [] [] = [] , ([] , refl , (λ _ ()))
  intersect (i ∷ f [ pf ]) (i₁ ∷ g [ pf₁ ]) with intersect f g | eq-∋ (_ , i) (_ , i₁) 
  intersect (.i₁ ∷ f [ pf ]) (i₁ ∷ g [ pf₁ ]) | (ts , z , eq , c) | yes refl = _ ∷ ts , cons z ,
     cong-∷[] refl (begin 
                     quo (λ x v → (i₁ ∷ f [ pf ]) $ (quo (λ x₁ x₂ → suc (z $ x₂)) $ v))  ≡⟨ lemma (i₁ ∷ f [ pf ]) _ ⟩ 
                     quo (λ x x₁ → f $ (z $ x₁))                                         ≡⟨ eq ⟩ 
                     quo (λ x v → (i₁ ∷ g [ pf₁ ]) $ suc (z $ v))                        ≡⟨ (sym (lemma (i₁ ∷ g [ pf₁ ]) _)) ⟩ 
                     quo (λ x v → (i₁ ∷ g [ pf₁ ]) $ (quo (λ x₁ x₂ → suc (z $ x₂)) $ v)) ∎)
     , (∋-case (λ x → zero , refl) (λ a y x → (suc (proj₁ (c a y x))) , (trans (cong suc (proj₂ (c a y x))) (sym (iso2 _ _ (proj₁ (c a y x)))))))
  intersect (i ∷ f [ pf ]) (i₁ ∷ g [ pf₁ ]) | (ts , z , eq , c) | no ¬p = ts , weak z , 
            (begin quo (λ x v → (i ∷ f [ pf ]) $ (quo (λ x₁ x₂ → suc (z $ x₂)) $ v)) ≡⟨ (lemma (i ∷ f [ pf ]) _) ⟩ 
                   quo (λ x x₁ → f $ (z $ x₁))                                       ≡⟨ eq ⟩ 
                   quo (λ x v → (i₁ ∷ g [ pf₁ ]) $ suc (z $ v))                      ≡⟨ sym (lemma (i₁ ∷ g [ pf₁ ]) _) ⟩ 
                   quo (λ x v → (i₁ ∷ g [ pf₁ ]) $ (quo (λ x₁ x₂ → suc (z $ x₂)) $ v)) ∎)
     , ∋-case (λ x → ⊥-elim (¬p (cong-proj₁ x))) (λ a y x → proj₁ (c a y x) ,
                                                    trans (cong suc (proj₂ (c a y x)))
                                                    (sym (iso2 _ _ (proj₁ (c a y x)))))

  cons-inter : ∀ {A : Set} {xs ys : List A} → (i j : Inj xs ys) → ∀ {ts} → (r : Inj ts xs) -> 
               (∀ a (y : xs ∋ a) -> i $ y ≡ j $ y -> ∃ \ z -> y ≡ r $ z) ->               
               ∀ {S} -> (a : A) (y : S ∷ xs ∋ a) → cons i $ y ≡ cons j $ y → Σ (S ∷ ts ∋ a) (λ z → y ≡ cons r $ z)
  cons-inter i j r c a zero eq = zero , refl
  cons-inter i j r c a (suc y) eq = let rec = (c a y (suc-inj1 (trans (sym (iso2 _ _ y)) (trans eq (iso2 _ _ y)))))
             in (suc (proj₁ rec)) , trans (cong suc (proj₂ rec)) (sym (iso2 _ _ (proj₁ rec)))

  inter-Inj : ∀ {A : Set} {xs ys : List A} → (i j : Inj xs ys) → ∀ {ts} → (r : Inj ts xs) -> 
               (∀ a (y : xs ∋ a) -> i $ y ≡ j $ y -> ∃ \ z -> y ≡ r $ z) ->               
                {as : List A} (h : Inj as xs) → i ∘i h ≡ j ∘i h → Σ (Inj as ts) (λ z → h ≡ r ∘i z)
  inter-Inj i j r c h eq = quo (λ x x₁ → proj₁ (c _ (h $ x₁) (trans (sym (apply-∘ i h)) (trans (cong (λ f → f $ x₁) eq) (apply-∘ j h))))) 
                           {λ x x₁ → injective h _ _ (trans (proj₂ (c _ (h $ _) _)) (trans (cong (_$_ r) x₁) (sym (proj₂ (c _ (h $ _) _)))))} 
                           , trans (sym (iso1 h (λ x x₁ → injective h _ _ x₁))) (quo-ext (λ x v → trans (proj₂ (c x (h $ v) _)) (cong (_$_ r) (sym (iso2 _ _ v)))))
  
  purje : ∀ {A : Set} {D1 D2 Du : List A} → (i : Inj D1 D2)(j : Inj Du D2) → ∃ \ Dr → Σ[ h ∶ Inj Dr Du ] Σ[ k ∶ Inj Dr D1 ] (i ∘i k) ≡ j ∘i h 
                                  × (∀ (a : A) (y : Du ∋ a)(x : D1 ∋ a) -> i $ x ≡ j $ y -> (∃ \ z -> k $ z ≡ x × h $ z ≡ y))
  purje i [] = [] , [] , [] , refl , (λ _ → λ ())
  purje i (v ∷ j [ pf ]) with purje i j | invert i v
  purje i (.(i $ x) ∷ j [ pf ]) | (Dr , h , k , eq , uni) | yes (x , refl)
        = _ ∷ Dr , cons h , (x ∷ k
            [ ∉Im-∉ k x (λ b x≡k$b → ∉-∉Im j (i $ x) pf (h $ b) (begin i $ x ≡⟨ cong (_$_ i) x≡k$b ⟩ i $ (k $ b) ≡⟨ cong-$ eq b ⟩ j $ (h $ b) ∎)) ])
          , cong-∷[] refl (begin quo (λ _ v → i $ (k $ v))                        ≡⟨ quo-ext (λ x₁ v → refl) ⟩ 
                                 quo (λ _ v → i $ (k $ v))                        ≡⟨ eq ⟩ 
                                 quo (λ _ v → ((i $ x) ∷ j [ pf ]) $ suc (h $ v)) ≡⟨ sym (lemma ((i $ x) ∷ j [ pf ]) _) ⟩ 
                                 quo (λ x₁ v → ((i $ x) ∷ j [ pf ]) $ (quo (λ x₂ x₃ → suc (h $ x₃)) $ v)) ∎)
          , ∋-case (λ x₁ x₂ → (zero , (injective i _ _ (sym x₂)) , refl)) (λ a y x₁ x₂ → 
                   let rec = uni a y x₁ x₂; z = proj₁ rec; eq1 = proj₁ (proj₂ rec) ; eq2 = proj₂ (proj₂ rec)
                   in (suc z , eq1 , (trans (iso2 _ _ z) (cong suc eq2))))
  purje i (v ∷ j [ pf ]) | (Dr , h , k , eq , uni) | no ¬p = Dr , weak h , k , 
                 (begin quo (λ _ x → i $ (k $ x))                  ≡⟨ eq ⟩ 
                        quo (λ _ x → (v ∷ j [ pf ]) $ suc (h $ x)) ≡⟨ sym (lemma (v ∷ j [ pf ]) _) ⟩ 
                        quo (λ _ x → (v ∷ j [ pf ]) $ (quo (λ _ x₁ → suc (h $ x₁)) $ x)) ∎)
          , ∋-case (λ x x₁ → ⊥-elim (¬p (x , x₁))) (λ a y x x₁ → 
                   let rec = uni a y x x₁; z = proj₁ rec; eq1 = proj₁ (proj₂ rec); eq2 = proj₂ (proj₂ rec) in
                      z , eq1 , trans (iso2 _ _ z) (cong suc eq2))

  uni-pullback : ∀ {A : Set} {D1 D2 Du : List A} → (i : Inj D1 D2)(j : Inj Du D2) -> ∀ {Dr} -> (h : Inj Dr Du) (k : Inj Dr D1)
                 -> (∀ (a : A) (y : Du ∋ a)(x : D1 ∋ a) -> i $ x ≡ j $ y -> (∃ \ z -> k $ z ≡ x × h $ z ≡ y))
                 -> ∀ {Q} -> (h' : Inj Q Du) (k' : Inj Q D1) -> i ∘i k' ≡ j ∘i h' -> ∃ \ q -> k' ≡ k ∘i q × h' ≡ h ∘i q  
  uni-pullback i j h k uni h' k' eq = quo (λ x x₁ → proj₁ (uni x (h' $ x₁) (k' $ x₁) (cong-$ eq x₁))) 
     {λ x x₁ → injective k' _ _
              (trans
               (trans (sym (proj₁ (proj₂ (uni x (h' $ _) (k' $ _) _))))
                (cong (_$_ k) x₁))
               (proj₁ (proj₂ (uni x (h' $ _) (k' $ _) _))))} , 
     (trans (sym (iso1 k' (λ x x₁ → injective k' _ _ x₁))) 
       (quo-ext (λ x v → trans ((sym (proj₁ (proj₂ (uni x (h' $ v) (k' $ v) _))))) (cong (_$_ k) (sym (iso2 _ _ v)))))) 
   , trans (sym (iso1 h' (λ x x₁ → injective h' _ _ x₁)))
       (quo-ext
        (λ x v →
           trans (sym (proj₂ (proj₂ (uni x (h' $ v) (k' $ v) _))))
           (cong (_$_ h) (sym (iso2 _ _ v)))))
  flip2 : ∀ {A : Set}{xs ys} {P : ∀ (a : A) -> xs ∋ a -> ys ∋ a -> Set} -> (∀ a -> (x : xs ∋ a) -> (y : ys ∋ a) -> P a x y) -> 
         ∀ a -> (y : ys ∋ a) -> (x : xs ∋ a) -> P a x y
  flip2 f a y x = f a x y

  cons-pullback : ∀ {A : Set} {D1 D2 Du : List A} → (i : Inj D1 D2)(j : Inj Du D2) -> ∀ {Dr} -> (h : Inj Dr Du) (k : Inj Dr D1)
                 -> (∀ (a : A) (y : Du ∋ a)(x : D1 ∋ a) -> i $ x ≡ j $ y -> (∃ \ z -> k $ z ≡ x × h $ z ≡ y))
                 -> ∀ {S} -> (∀ (a : A) (y : S ∷ Du ∋ a)(x : S ∷ D1 ∋ a) -> cons i $ x ≡ cons j $ y -> (∃ \ z -> cons k $ z ≡ x × cons h $ z ≡ y))
  cons-pullback i j h k uni = ∋-case (λ x x₁ → zero , ((injective (cons i) _ _ (sym x₁)) , refl)) (flip2 
    (∋-case (λ y x → ⊥-elim (zero≢suc (trans x (iso2 (λ _ v → suc (j $ v)) _ y)))) 
            (λ a y y₁ x → let rec = uni a y₁ y (suc-inj1 (trans (sym (iso2 _ _ y)) (trans x (iso2 _ _ y₁)))) in  
                 (suc (proj₁ rec)) , ((trans (iso2 _ _ (proj₁ rec)) (cong suc (proj₁ (proj₂ rec)))) 
                 , (trans (iso2 _ _ (proj₁ rec)) (cong suc (proj₂ (proj₂ rec))))))))
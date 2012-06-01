module Injection where

open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Data.Unit
open import Data.Maybe
open import Relation.Nullary
open import Function hiding (_$_)
open import Data.Empty
open import Relation.Nullary.Decidable
open import Data.Sum

infix 4 _∋_

data _∋_ {A : Set} : List A -> A -> Set where
  zero : ∀ {G T} -> T ∷ G ∋ T
  suc : ∀ {G T S} -> G ∋ T -> S ∷ G ∋ T

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

thick-thin : ∀ {A}{G : List A}{S T} (x : G ∋ S) → (y : (G - x) ∋ T) -> thick x (thin x T y) ≡ inj₁ (y , refl)
thick-thin zero y = refl
thick-thin (suc x) zero = refl
thick-thin (suc x) (suc y) rewrite thick-thin x y = refl

_∈_ : {A : Set} -> A -> List A  -> Set
_∈_ x xs = xs ∋ x

suc-inj : ∀ {A : Set}{xs : List A}{x y z} {i : xs ∋ x}{j : xs ∋ y} -> (x , suc {S = z} i) ≡ (y , suc j) -> (x , i) ≡ (y , j)
suc-inj refl = refl

suc-inj1 : ∀ {A : Set}{xs : List A}{x z} {i : xs ∋ x}{j : xs ∋ x} -> suc {S = z} i ≡ suc j -> i ≡ j
suc-inj1 refl = refl

eq-∋ : ∀ {A : Set}{xs : List A} -> (i j : ∃ (_∋_ xs)) -> Dec (i ≡ j)
eq-∋ (.y , zero) (y , zero) = yes refl
eq-∋ (x , zero)  (y , suc j) = no (λ ())
eq-∋ (x , suc i) (y , zero) = no (λ ())
eq-∋ (x , suc i) (y , suc j) with eq-∋ (x , i) (y , j) 
eq-∋ (.y , suc .j) (y , suc j) | yes refl = yes refl
eq-∋ (x , suc i) (y , suc j) | no ¬p = no (¬p ∘ suc-inj)

infix 2 _⊇_

mutual
  data Inj {A : Set}: (List A) -> List A → Set where
    []  : ∀ {xs} -> Inj [] xs
    _∷_[_] : ∀ {xs} {y} {ys : List A} (i : y ∈ xs) (is : Inj ys xs) (pf : (i ∉ is)) → Inj (y ∷ ys) xs
  
  _⊇_ : {A : Set}(xs : List A) -> List A → Set
  xs ⊇ ys = Inj ys xs

  _∉_ : ∀ {A : Set}{y : A} {xs ys} → y ∈ xs → Inj ys xs → Set
  pf ∉ [] = ⊤ 
  pf ∉ (i ∷ pfs [ pf₁ ]) = False (eq-∋ (_ , pf) (_ , i)) × pf ∉ pfs


proof-irr-∉ : ∀ {A : Set}{y : A} {xs ys} → (i : y ∈ xs) → (f : xs ⊇ ys) -> (p q : i ∉ f) → p ≡ q
proof-irr-∉ i [] p q = refl
proof-irr-∉ i (i₁ ∷ f [ pf ]) p q with eq-∋ (_ , i) (_ , i₁) 
proof-irr-∉ i (i₁ ∷ f [ pf ]) (() , _) q | yes p 
proof-irr-∉ i (i₁ ∷ f [ pf ]) p q | no ¬p = cong (_,_ _) (proof-irr-∉ i f (proj₂ p) (proj₂ q))

cong-∷[] : ∀ {A : Set}{xs : List A}{y} {ys : List A} {i j : y ∈ xs} -> i ≡ j -> {is js : xs ⊇ ys} -> is ≡ js -> {pf1 : (i ∉ is)}{pf2 : j ∉ js} → 
           i ∷ is [ pf1 ] ≡ j ∷ js [ pf2 ]
cong-∷[] {i = i} refl {is} refl {pf1} {pf2}  = cong (λ pf → i ∷ is [ pf ]) (proof-irr-∉ i is pf1 pf2)

cong-proj₂ : ∀ {A : Set}{B : A -> Set} {x y : A} (eq : x ≡ y) {b1 : B x}{b2 : B y} -> subst B eq b1 ≡ b2 -> (x , b1) ≡ (y , b2)
cong-proj₂ refl refl = refl

get-proj₂ : ∀ {A : Set}{B : A -> Set} {x : A}{b1 b2 : B x} -> _,_  {A = A} {B = B} x b1 ≡ (x , b2) -> b1 ≡ b2
get-proj₂ refl = refl
mkFalse : ∀ {P : Set} -> (P -> ⊥) -> ∀ {d : Dec P} -> False d
mkFalse ¬p {yes p} = ¬p p
mkFalse ¬p {no ¬p₁} = tt 

quo' : ∀ {A : Set} {xs ys} -> (f : ∀ (x : A) -> x ∈ xs -> x ∈ ys){inj : ∀ x -> {i j : x ∈ xs} -> f x i ≡ f x j -> i ≡ j} -> 
    Σ (ys ⊇ xs) \ is -> (∀ x (i : x ∈ ys) -> (∀ y j -> False (eq-∋ (_ , i) (_ , f y j))) -> (i ∉ is))
quo' {_} {[]} f {inj} = [] , (λ x i x₁ → _)
quo' {_} {x ∷ xs} f {inj} = is , proof 
  module quo'-lemmas where
   rec = (quo' {_}{xs} (λ x₁ x₂ → f x₁ (suc x₂)) {(λ x₁ x₂ → suc-inj1 (inj x₁ x₂))})
   abstract
    pf : f x zero ∉
      proj₁
      (quo' (λ x₁ x₂ → f x₁ (suc x₂))
       {(λ x₁ x₂ → suc-inj1 (inj x₁ x₂))})
    pf = proj₂ rec x (f x (zero)) (λ y j → mkFalse (lemmma y j))
  
      where lemmma : ∀ y j -> (x , f x zero) ≡ (y , f y (suc j)) -> ⊥
            lemmma y j eq with cong proj₁ eq
            lemmma .x j eq | refl with f x zero | inj x {zero} {suc j}  
            lemmma ._ j refl | refl | .(f x (suc j)) | q with q refl 
            ... | ()
   is = ((f x zero) ∷ proj₁ rec [ pf ])
  
   proof : (∀ x i -> (∀ y j -> False (eq-∋ (_ , i) (_ , f y j))) -> (i ∉ is))
   proof z i e = e x zero , (proj₂ rec z i (λ y j → e y (suc j)))

quo : ∀ {A : Set} {xs ys} -> (f : ∀ (x : A) -> x ∈ xs -> x ∈ ys){inj : ∀ x -> {i j : x ∈ xs} -> f x i ≡ f x j -> i ≡ j} -> 
    (ys ⊇ xs)
quo f {inj} = proj₁ (quo' f {inj})

quo-ext : ∀ {A : Set} {xs ys} -> {f : ∀ (x : A) -> x ∈ xs -> x ∈ ys}{injf : ∀ x -> {i j : x ∈ xs} -> f x i ≡ f x j -> i ≡ j} ->
        {g : ∀ (x : A) -> x ∈ xs -> x ∈ ys}{injg : ∀ x -> {i j : x ∈ xs} -> g x i ≡ g x j -> i ≡ j} ->
        (∀ x v -> f x v ≡ g x v) -> quo f {injf} ≡ quo g {injg}
quo-ext {A} {[]} eq =  refl
quo-ext {A} {x ∷ xs} eq = cong-∷[] (eq _ zero) (quo-ext (λ x₁ v → eq x₁ (suc v)))

_$_ : ∀ {A : Set} {xs ys : List A} -> ys ⊇ xs -> ∀ {x} -> x ∈ xs -> x ∈ ys
(i ∷ is [ pf ]) $ zero = i
(i ∷ is [ pf ]) $ suc x₂ = is $ x₂
[] $ () 

fromFalse : ∀ {P : Set} {d : Dec P} -> False d -> P -> ⊥
fromFalse {P} {yes p} ()
fromFalse {P} {no ¬p} _ = ¬p

quux : ∀ {A : Set} {xs ys : List A} -> (f : ys ⊇ xs) -> ∀ {x} (i : x ∈ ys) -> i ∉ f -> ∀ b -> i ≡ f $ b -> ⊥
quux (i₁ ∷ f [ pf ]) .i₁ i∉f zero refl = fromFalse (proj₁ i∉f) refl
quux (i₁ ∷ f [ pf ]) i i∉f (suc b) eq = quux f i (proj₂ i∉f) b eq
quux [] _ _ () _

naaz' : ∀ {A : Set} {xs ys : List A} -> (f : ys ⊇ xs) -> ∀ {x} (i : x ∈ ys) -> (∀ {y} (b : y ∈ xs) -> (x , i) ≡ (y , f $ b) -> ⊥) -> i ∉ f 
naaz' [] i ¬p = _
naaz' (i ∷ f [ pf ]) i₁ ¬p = (mkFalse (λ x → ¬p zero x)) , naaz' f i₁ (λ b x → ¬p (suc b) x)


injective : ∀ {A : Set} {xs ys : List A} -> (f : ys ⊇ xs) -> ∀ {x} -> (a b : x ∈ xs) -> f $ a ≡ f $ b -> a ≡ b
injective f zero zero eq = refl
injective (i ∷ f [ pf ]) zero (suc b) eq = ⊥-elim (quux f i pf b eq)
injective (i ∷ f [ pf ]) (suc a₁) zero eq = ⊥-elim (quux f i pf a₁ (sym eq))
injective (i ∷ f [ pf ]) (suc a₁) (suc b) eq = cong suc (injective f a₁ b eq)

iso1 : ∀ {A : Set} {xs ys : List A} -> (f : ys ⊇ xs) -> (inj : _) -> proj₁ (quo' (\ x v -> f $ v) {inj}) ≡ f
iso1 [] _ = refl
iso1 (i ∷ f [ pf ]) inj = cong-∷[] refl (iso1 f (λ x₁ x₂ → suc-inj1 (inj x₁ x₂)))

iso2 : ∀ {A : Set} {xs ys : List A} -> (f : ∀ (x : A) -> x ∈ xs -> x ∈ ys)(inj : ∀ x -> {i j : x ∈ xs} -> f x i ≡ f x j -> i ≡ j)
         -> ∀ {x} (v : x ∈ xs) -> proj₁ (quo' f {inj}) $ v ≡ f x v
iso2 f inj zero = refl
iso2 f inj (suc v) = iso2 (λ x₁ x₂ → f x₁ (suc x₂)) (λ x₁ x₂ → suc-inj1 (inj x₁ x₂)) v

invert : ∀ {A : Set} {xs ys : List A} (i : ys ⊇ xs) -> ∀ {t} (y : ys ∋ t) -> Dec (∃ \ x -> (i $ x) ≡ y) 
invert [] x = no (λ { (() , _)})
invert (i ∷ f [ pf ]) y with eq-∋ (_ , i) (_ , y) 
invert (.y₁ ∷ f [ pf ]) y₁ | yes refl = yes (zero , refl)
invert (i ∷ f [ pf ]) y₁ | no ¬p with invert f y₁ 
invert (i ∷ f [ pf ]) y₁ | no ¬p | yes p = yes (suc (proj₁ p) , (proj₂ p))
invert (i ∷ f [ pf ]) y₁ | no ¬p₁ | no ¬p = no (lemmi ¬p₁ ¬p) where
    lemmi : ∀ {t} {y : _ ∋ t} -> (¬ (_ , i) ≡ (t , y)) -> (¬ ∃ \ x₂ -> f $ x₂ ≡ y) -> Σ (_ ∷ _ ∋ _) (λ x₂ → (i ∷ f [ pf ]) $ x₂ ≡ y) → ⊥
    lemmi ¬1 ¬2 (zero , p) = ¬1 (cong (_,_ _) p)
    lemmi ¬1 ¬2 (suc n , p) = ¬2 (n , p)

naaz : ∀ {A : Set} {xs ys : List A} (f : ∀ x (v : x ∈ xs) -> x ∈ ys){inj} 
     -> ∀ {x} (i : x ∈ ys) -> (∀ {y} (b : y ∈ xs) -> (x , i) ≡ (y , f y b) -> ⊥) -> i ∉ (quo f {inj}) 
naaz f {inj} i eq = naaz' (quo f {inj}) i (λ b x → eq b (trans x (cong-proj₂ refl (iso2 f inj b))))

naaaz : ∀ {A : Set} {xs ys : List A} (f : ∀ x (v : x ∈ xs) -> x ∈ ys){inj} 
     -> ∀ {x} (i : x ∈ ys) -> (∀ (b : x ∈ xs) -> i ≡ f x b -> ⊥) -> i ∉ (quo f {inj})
naaaz f {x = x} i p = naaz f i ¬p where
  ¬p : {y : _} (b : _ ∋ y) → (x , i) ≡ (y , f y b) → ⊥
  ¬p b eq with cong proj₁ eq
  ... | refl = p b (get-proj₂ eq)

naaaaz : ∀ {A : Set} {xs ys : List A} -> (f : ys ⊇ xs) -> ∀ {x} (i : x ∈ ys) -> (∀ (b : x ∈ xs) -> i ≡ f $ b -> ⊥) -> i ∉ f
naaaaz f {x} i ¬p = naaz' f i aux where
  aux : {y : _} (b : _ ∋ y) → (x , i) ≡ (y , f $ b) → ⊥
  aux b eq with cong proj₁ eq
  ... | refl = ¬p b (get-proj₂ eq)
abstract
  _∘i_ : ∀ {A : Set}{xs ys zs : List A} -> zs ⊇ ys -> ys ⊇ xs -> zs ⊇ xs
  f ∘i g = proj₁ (quo' (λ x x₁ → f $ (g $ x₁)) {(λ x x₁ → injective g _ _ (injective f _ _ x₁))})

  id-i : ∀ {A : Set}{xs : List A} -> Inj xs xs
  id-i = quo (\ _ x -> x) {\ _ e -> e}

  right-id : ∀ {A : Set}{xs ys : List A} -> (i : Inj xs ys) -> i ∘i id-i ≡ i
  right-id i = trans (quo-ext (λ x v → cong (_$_ i) (iso2 _ _ v))) (iso1 i (λ x eq → injective i _ _ eq))

  left-id : ∀ {A : Set}{xs ys : List A} -> (i : Inj xs ys) -> id-i ∘i i ≡ i
  left-id i = trans (quo-ext (λ x v → (iso2 _ _ (i $ v)))) (iso1 i (λ x eq → injective i _ _ eq))

  apply-∘ : ∀ {A : Set}{xs ys zs : List A} -> (j : zs ⊇ ys) -> (i : ys ⊇ xs) -> ∀ {x} {v : x ∈ xs} -> (j ∘i i) $ v ≡ j $ (i $ v)
  apply-∘ j i {x}{v} = iso2 _ _ v

  assoc-∘i : ∀ {A : Set}{xs ys ws zs : List A} {f : Inj ws zs}{g : Inj _ ws}{h : Inj xs ys} -> f ∘i (g ∘i h) ≡ (f ∘i g) ∘i h  
  assoc-∘i {f = f}{g = g}{h = h} = quo-ext (λ x v → trans (cong (_$_ f) (iso2 _ _ v)) (sym (iso2 _ _ (h $ v))))

  cong-$ : ∀ {A : Set}{xs ys : List A} {f g : _} {inj1 inj2} -> quo {_} {xs} {ys} f {inj1} ≡ quo g {inj2} -> ∀ {s} (x : xs ∋ s) -> f s x ≡ g s x
  cong-$ {A} {xs} {ys} {f} {g} eq x = trans (sym (iso2 f _ x)) (trans (cong (λ f₁ → f₁ $ x) eq) (iso2 g _ x))

  ∘i-inj : ∀ {A : Set}{xs ys zs : List A} -> (i : Inj ys zs) (j1 j2 : Inj xs ys) -> (i ∘i j1) ≡ (i ∘i j2) -> j1 ≡ j2
  ∘i-inj i j1 j2 eq = trans (trans (sym (iso1 j1 (λ x x₁ → injective j1 _ _ x₁))) 
           (quo-ext (λ x v → injective i _ _ (cong-$ eq v)))) (iso1 j2 (λ x x₁ → injective j2 _ _ x₁))

  weak : ∀ {A : Set}{x : A}{xs ys} -> ys ⊇ xs -> (x ∷ ys) ⊇ xs
  weak f = proj₁ (quo' (λ x x₁ → suc (f $ x₁)) {λ x x₁ → injective f _ _ (suc-inj1 x₁)})

  lemma : ∀ {A : Set}{xs ys ts : List A} (i : ts ⊇ xs)(z : _){inj1 inj2 inj3} -> 
            quo (\ x v -> i $ (quo {_} {ys} z {inj1} $ v)) {inj3} ≡ quo (\ x v -> i $ (z _ v)) {inj2} 
  lemma i z = quo-ext (λ x₁ v → cong (_$_ i) (iso2 z _ v))

  cons : ∀ {A : Set}{x : A}{xs ys} -> ys ⊇ xs -> x ∷ ys ⊇ x ∷ xs
  cons z = (zero ∷ weak z [ naaz (λ x x₁ → suc (z $ x₁)) zero (λ { _ ()}) ])

  cons-∘i : ∀ {A : Set}{xs ys zs : List A}{x} -> (j : zs ⊇ ys) -> (i : ys ⊇ xs) -> cons {A} {x} (j ∘i i) ≡ cons j ∘i cons i
  cons-∘i j i = cong-∷[] refl (trans (quo-ext {injg = λ x x₁ → injective i _ _ (injective (weak j) _ _ x₁)}(λ x v → trans (cong suc (iso2 _ _ v)) (sym (iso2 _ _ (i $ v))))) 
              (sym (lemma  (cons j) (λ _ x → suc (i $ x))))) 
  intersect : ∀ {A : Set} {xs ys : List A} -> (i j : ys ⊇ xs) -> ∃ \ ts -> Σ (xs ⊇ ts) \ r -> (i ∘i r) ≡ (j ∘i r)
  intersect [] [] = [] , ([] , refl)
  intersect (i ∷ f [ pf ]) (i₁ ∷ g [ pf₁ ]) with intersect f g | eq-∋ (_ , i) (_ , i₁) 
  intersect (.i₁ ∷ f [ pf ]) (i₁ ∷ g [ pf₁ ]) | (ts , z , eq) | yes refl = (_ ∷ ts) , cons z , 
                 cong-∷[] refl (trans (lemma (i₁ ∷ f [ pf ]) _) (trans eq (sym (lemma (i₁ ∷ g [ pf₁ ]) _))))
  intersect (i ∷ f [ pf ]) (i₁ ∷ g [ pf₁ ]) | (ts , z , eq) | no ¬p = ts , (weak z , 
               trans (lemma (i ∷ f [ pf ]) _) (trans eq (sym (lemma (i₁ ∷ g [ pf₁ ]) _))))

  purje : ∀ {A : Set} {D1 D2 Du : List A} -> (i : Inj D1 D2)(j : Inj Du D2) -> ∃ \ Dr -> Σ[ h ∶ Inj Dr Du ] Σ[ k ∶ Inj Dr D1 ] (i ∘i k) ≡ j ∘i h
  purje i [] = [] , ([] , ([] , refl))
  purje i (v ∷ j [ pf ]) with purje i j | invert i v
  purje i (.(i $ x) ∷ j [ pf ]) | (Dr , h , k , eq) | yes (x , refl) 
        = (_ ∷ Dr) , (cons h , ((x ∷ k [ naaaaz k x (λ b x≡k$b → quux j (i $ x) pf (h $ b)
                                                                 (trans (cong (_$_ i) x≡k$b) (cong-$ eq b))) ]) , 
                     (cong-∷[] refl (trans (trans (quo-ext (λ x₁ v → refl)) eq) (sym (lemma ((i $ x) ∷ j [ pf ]) _))))))

  purje i (v ∷ j [ pf ]) | (Dr , h , k , eq) | no ¬p = Dr , ((weak h) , (k , (trans eq ((sym (lemma (v ∷ j [ pf ]) _))))))


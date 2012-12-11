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

open import Vars public
open import Injection.Type public

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

mutual
  id-i : ∀ {A : Set}{xs : List A} → Inj xs xs
  id-i = quo (\ _ x → x) {\ _ e → e}

  Inj-thin : ∀ {A : Set}{x : A}{xs ys} → (v : ys ∋ x) -> Inj xs (ys - v) → Inj xs ys
  Inj-thin v f = quo (λ x x₁ → thin v x (f $ x₁)) {λ x x₁ → injective f _ _ (thin-inj v x₁)}

abstract
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
  
  
  Inj-thin-$ : ∀ {A : Set}{x : A}{xs ys} → (v : ys ∋ x) -> (f : Inj xs (ys - v)) -> ∀ {y}(u : xs ∋ y) -> Inj-thin v f $ u ≡ thin v _ (f $ u)
  Inj-thin-$ v f u = iso2 _ _ u

  Inj-thin-inj : ∀ {A : Set}{x : A}{xs ys} → (v : ys ∋ x) -> (f g : Inj xs (ys - v)) -> Inj-thin v f ≡ Inj-thin v g -> f ≡ g
  Inj-thin-inj v f g eq = ext-$ f g (λ x v₁ → thin-inj v (cong-$ eq v₁))

  Inj-thin-∘i : ∀ {A : Set}{x : A}{zs xs ys} → (v : ys ∋ x) -> (f : Inj xs (ys - v)) (m : Inj zs xs) -> Inj-thin v f ∘i m ≡ Inj-thin v (f ∘i m)
  Inj-thin-∘i v f m = quo-ext (λ x v₁ → trans (iso2 _ _ (m $ v₁)) (cong (thin v x) (sym (iso2 _ _ v₁))))

  v∉Inj-thinv : ∀ {A : Set}{x : A}{xs ys} → (v : ys ∋ x) -> (f : Inj xs (ys - v)) -> v ∉ Inj-thin v f
  v∉Inj-thinv v f = ∉Im$-∉ (λ x x₁ → thin v _ (f $ x₁)) v (λ b → x∉thinx v (f $ b))

weak : ∀ {A : Set}{x : A}{xs ys} → Inj xs ys → Inj xs (x ∷ ys)
weak f = Inj-thin zero f

_∷[]_ : ∀ {A : Set}{x : A}{xs ys} → (v : ys ∋ x) -> Inj xs (ys - v) → Inj (x ∷ xs) ys
v ∷[] f = v ∷ Inj-thin v f [ v∉Inj-thinv v f ]

cons : ∀ {A : Set}{x : A}{xs ys} → Inj xs ys → Inj (x ∷ xs) (x ∷ ys)
cons z = zero ∷[] z

abstract

  cons-id : ∀ {A : Set}{x : A}{xs} -> cons id-i ≡ id-i {_} {x ∷ xs}
  cons-id = cong-∷[] refl (quo-ext (λ x v → cong suc (iso2 _ _ v)))

  cons-∘i : ∀ {A : Set}{xs ys zs : List A}{x} → (j : Inj ys zs) → (i : Inj xs ys) → cons {A} {x} (j ∘i i) ≡ cons j ∘i cons i
  cons-∘i j i = cong-∷[] refl (begin 
    quo (λ x z → suc (proj₁ (quo' (λ v v₁ → j $ (i $ v₁))) $ z)) 
      ≡⟨ quo-ext {injg = λ x x₁ → injective i _ _ (injective (weak j) _ _ x₁)} (λ x v → 
          begin suc (proj₁ (quo' (λ v₁ v₂ → j $ (i $ v₂))) $ v) ≡⟨ cong suc (iso2 _ _ v) ⟩ 
                suc (j $ (i $ v))                               ≡⟨ sym (iso2 _ _ (i $ v)) ⟩ 
                quo (λ x₁ x₂ → suc (j $ x₂)) $ (i $ v)          ∎) ⟩ 
    quo (λ x v → cons j $ suc (i $ v))                       ≡⟨ sym (quo-ext (λ x₁ v → cong (_$_ (cons j)) (iso2 (λ _ x → suc (i $ x)) _ v))) ⟩ 
    quo (λ x v → cons j $ (quo (λ z x₁ → suc (i $ x₁)) $ v)) ∎)


∘-ext : ∀ {A : Set}{xs ys zs ws : List A} {f : Inj ys zs}{g : Inj xs ys}{f1 : Inj ws zs}{g1 : Inj xs ws} -> f ∘i g ≡ f1 ∘i g1
        -> (∀ x (v : xs ∋ x) -> f $ (g $ v) ≡ f1 $ (g1 $ v)) 
∘-ext eq = (\ x v -> trans (sym (apply-∘ _ _)) (trans (cong (\ f -> f $ v) eq) ((apply-∘ _ _))))

ext-∘ : ∀ {A : Set}{xs ys zs ws : List A} {f : Inj ys zs}{g : Inj xs ys}{f1 : Inj ws zs}{g1 : Inj xs ws} -> 
  (∀ x (v : xs ∋ x) -> f $ (g $ v) ≡ f1 $ (g1 $ v)) -> f ∘i g ≡ f1 ∘i g1
ext-∘ eq = ext-$ _ _ (\ x v -> trans (apply-∘ _ _) (trans (eq x v) (sym (apply-∘ _ _))))

-- Transforming pointwise representations of universal morphisms into Inj ones.
Equ-universal-quote : ∀ {A : Set} {xs ys : List A} → (i j : Inj xs ys) → ∀ {E} → (e : Inj E xs) -> 
               (∀ a (y : xs ∋ a) -> i $ y ≡ j $ y -> ∃ \ z -> y ≡ e $ z) ->               
                {as : List A} (h : Inj as xs) → i ∘i h ≡ j ∘i h → Σ (Inj as E) (λ z → e ∘i z ≡ h )
Equ-universal-quote {A} {xs} {ys} i j {E} e c {as} h eq = 
  quo u {λ x {v} {w} eq1 → injective h v w (begin h $ v     ≡⟨ proj₂ (f x v) ⟩
                                                  e $ u x v ≡⟨ cong (_$_ e) eq1 ⟩
                                                  e $ u x w ≡⟨ sym (proj₂ (f x w)) ⟩
                                                  h $ w     ∎)}
  , ext-$ (e ∘i quo u) h (λ x v → begin
          (e ∘i quo u) $ v ≡⟨ apply-∘ _ _ ⟩ 
          e $ (quo u $ v)  ≡⟨ cong (_$_ e) (iso2 _ _ v) ⟩
          e $ u x v        ≡⟨ sym (proj₂ (f x v)) ⟩
          h $ v            ∎)
  where 
   f : ∀ a (y : as ∋ a) -> ∃ \ z -> h $ y ≡ e $ z
   f a y = c a (h $ y) (∘-ext eq a y)
   u = (λ x v → proj₁ (f x v))

Pull-universal-quote : ∀ {A : Set} {X Y Z : List A} → (i : Inj X Z)(j : Inj Y Z) -> ∀ {P} -> (p₁ : Inj P X) (p₂ : Inj P Y)
                 -> (∀ (a : A) (y : Y ∋ a)(x : X ∋ a) -> i $ x ≡ j $ y -> (∃ \ z -> p₁ $ z ≡ x × p₂ $ z ≡ y))
                 -> ∀ {Q} -> (q₁ : Inj Q X) (q₂ : Inj Q Y) -> i ∘i q₁ ≡ j ∘i q₂ -> ∃ \ u -> q₁ ≡ p₁ ∘i u × q₂ ≡ p₂ ∘i u  
Pull-universal-quote i j p₁ p₂ uni {Q} q₁ q₂ commutes = 
     quo u {λ x {v} {w} eq → injective q₁ v w (begin q₁ $ v      ≡⟨ sym (proj₁ (proj₂ (f x v))) ⟩
                                                     p₁ $ u x v  ≡⟨ cong (_$_ p₁) eq ⟩
                                                     p₁ $ u x w  ≡⟨ proj₁ (proj₂ (f x w)) ⟩
                                                     q₁ $ w      ∎)}
     , ext-$ q₁ (p₁ ∘i quo u) (λ x v → begin 
             q₁ $ v            ≡⟨ sym (proj₁ (proj₂ (f x v))) ⟩  
             p₁ $ u x v        ≡⟨ cong (_$_ p₁) (sym (iso2 _ _ v)) ⟩
             p₁ $ (quo u $ v)  ≡⟨ sym (apply-∘ _ _) ⟩
             (p₁ ∘i quo u) $ v ∎)
     , ext-$ q₂ (p₂ ∘i quo u) (λ x v → begin
             q₂ $ v            ≡⟨ sym (proj₂ (proj₂ (f x v))) ⟩ 
             p₂ $ u x v        ≡⟨ cong (_$_ p₂) (sym (iso2 _ _ v)) ⟩
             p₂ $ (quo u $ v)  ≡⟨ sym (apply-∘ _ _) ⟩ 
             (p₂ ∘i quo u) $ v ∎)
  where
    f : ∀ a (v : Q ∋ a) -> (∃ \ z -> p₁ $ z ≡ q₁ $ v × p₂ $ z ≡ q₂ $ v)
    f a v = uni a (q₂ $ v) (q₁ $ v) (∘-ext commutes a v)
    u : ∀ a (v : Q ∋ a) -> _
    u a v = proj₁ (f a v)

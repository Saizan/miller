module Category 
  (Obj : Set)
  (_⇒_ : Obj -> Obj -> Set)
  (_∘_ : ∀ {a b c} -> b ⇒ c -> a ⇒ b -> a ⇒ c)
  (id : ∀ {a} -> a ⇒ a)
  (_==_ : ∀ {A B} (f g : A ⇒ B) -> Set)
   where

private
  infix 4 _≡_
  _≡_ : ∀ {A B} (f g : A ⇒ B) -> Set
  _≡_ = _==_

Monic : ∀ {A B} (f : A ⇒ B) -> Set
Monic {A} {B} f = ∀ {C} {g1 g2 : C ⇒ A} -> (f ∘ g1) ≡ (f ∘ g2) -> g1 ≡ g2

record IsPullback {X Y Z}(f : X ⇒ Z)(g : Y ⇒ Z)(P : Obj)(p₁ : P ⇒ X)(p₂ : P ⇒ Y) : Set where
  field
    commutes : f ∘ p₁ ≡ g ∘ p₂

    universal : ∀ {Q}(q₁ : Q ⇒ X)(q₂ : Q ⇒ Y)
              → (commutes : f ∘ q₁ ≡ g ∘ q₂) → (Q ⇒ P)

    universal-unique : ∀ {Q} {q₁ : Q ⇒ X} {q₂ : Q ⇒ Y}
                        {commutes : f ∘ q₁ ≡ g ∘ q₂}
                          (u : Q ⇒ P)
                          (p₁∘u≡q₁ : p₁ ∘ u ≡ q₁)
                          (p₂∘u≡q₂ : p₂ ∘ u ≡ q₂)
                      →   u ≡ universal q₁ q₂ commutes

    p₁∘universal≡q₁  : ∀ {Q} {q₁ : Q ⇒ X} {q₂ : Q ⇒ Y}
                          {commutes : f ∘ q₁ ≡ g ∘ q₂}
                      →   (p₁ ∘ universal q₁ q₂ commutes ≡ q₁)

    p₂∘universal≡q₂  : ∀ {Q} {q₁ : Q ⇒ X} {q₂ : Q ⇒ Y}
                          {commutes : f ∘ q₁ ≡ g ∘ q₂}
                      →   (p₂ ∘ universal q₁ q₂ commutes ≡ q₂)


record Pullback {X Y Z}(f : X ⇒ Z)(g : Y ⇒ Z) : Set where
  constructor Pull_,_,_,_
  field
    P  : Obj
    p₁ : P ⇒ X
    p₂ : P ⇒ Y
    isPullback : IsPullback f g P p₁ p₂

  open IsPullback isPullback public
  

record IsEqualizer {X Y}(f g : X ⇒ Y) (E : Obj) (e : E ⇒ X) : Set where
  field
    commutes : f ∘ e ≡ g ∘ e

    universal : ∀ {Q}(m : Q ⇒ X)
              → (commutes : f ∘ m ≡ g ∘ m) → (Q ⇒ E)

    universal-unique : ∀ {Q} {m : Q ⇒ X}
                        {commutes : f ∘ m ≡ g ∘ m}
                          (u : Q ⇒ E)
                          (e∘u≡m : e ∘ u ≡ m)
                      →   u ≡ universal m commutes

    e∘universal≡m  : ∀ {Q} {m : Q ⇒ X} 
                          {commutes : f ∘ m ≡ g ∘ m}
                      →   (e ∘ universal m commutes ≡ m)
  
record Equalizer {X Y}(f g : X ⇒ Y) : Set where
  constructor Equ_,_,_
  field
    E  : Obj
    e : E ⇒ X
    isEqualizer : IsEqualizer f g E e

  open IsEqualizer isEqualizer public


record Product (A B : Obj) : Set where
  constructor Prod
  field
    A×B : Obj
    π₁ : A×B ⇒ A
    π₂ : A×B ⇒ B
    ⟨_,_⟩ : ∀ {C} → (C ⇒ A) → (C ⇒ B) → (C ⇒ A×B)

    commute₁ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} → π₁ ∘ ⟨ f , g ⟩ ≡ f
    commute₂ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} → π₂ ∘ ⟨ f , g ⟩ ≡ g
    universal : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} {i : C ⇒ A×B}
               → π₁ ∘ i ≡ f → π₂ ∘ i ≡ g → ⟨ f , g ⟩ ≡ i

open import Relation.Binary
module Props     (assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f))
                 (identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f)
                 (identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f)

             (equiv     : ∀ {A B} → IsEquivalence (_≡_ {A} {B}))
             (∘-resp-≡  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i)
                      where
  module Dummy {A}{B} = IsEquivalence (equiv {A} {B})
  open Dummy

  convert : {X Y Z : Obj} -> (f : X ⇒ Z)(g : Y ⇒ Z) -> (prod : Product X Y) -> let open Product prod in 
             Equalizer (f ∘ π₁) (g ∘ π₂) -> Pullback f g
  convert f g prod equ = Pull E , (π₁ ∘ e) , (π₂ ∘ e) , 
        (record {
           commutes = trans (sym assoc) (trans commutes assoc);
           universal = λ q₁ q₂ commutes₁ → universal ⟨ q₁ , q₂ ⟩ (trans assoc (trans (∘-resp-≡ refl commute₁) 
                                           (trans commutes₁ (trans (sym (∘-resp-≡ refl commute₂)) (sym assoc)))));
           universal-unique = λ u p₁∘u≡q₁ p₂∘u≡q₂ → universal-unique u (sym (uniπ (trans (sym assoc) p₁∘u≡q₁) (trans (sym assoc) p₂∘u≡q₂)));
           p₁∘universal≡q₁ = trans assoc (trans (∘-resp-≡ refl e∘universal≡m) commute₁);
           p₂∘universal≡q₂ = trans assoc (trans (∘-resp-≡ refl e∘universal≡m) commute₂) })
    where
      open Product prod renaming (universal to uniπ)
      open Equalizer equ
  
  Equalizer-ext : ∀ {X Z}{f1 f2 : X ⇒ Z} -> f1 ≡ f2 -> {g1 g2 : X ⇒ Z} -> g1 ≡ g2 -> Equalizer f1 g1 -> Equalizer f2 g2
  Equalizer-ext f1≡f2 g1≡g2 pull 
   = Equ E , e ,   
      (record {
         commutes = trans (∘-resp-≡ (sym f1≡f2) refl) (trans commutes (∘-resp-≡ g1≡g2 refl));
         universal = λ m commutes₁ → universal m (trans (∘-resp-≡ f1≡f2 refl)
                                                            (trans commutes₁ (∘-resp-≡ (sym g1≡g2) refl)));
         universal-unique = universal-unique;
         e∘universal≡m = e∘universal≡m})
    where 
      open Equalizer pull

  under-assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} -> 
                ∀ {C}                  {g1 : B ⇒ C} {h1 : C ⇒ D} -> h ∘ g ≡ h1 ∘ g1 -> h ∘ (g ∘ f) ≡ h1 ∘ (g1 ∘ f)
  under-assoc eq = trans (sym assoc) (trans (∘-resp-≡ eq refl) assoc)

  mono-pullback-stable : ∀ {X Y Z : Obj} -> (f : X ⇒ Z)(g : Y ⇒ Z) -> (pull : Pullback f g) -> Monic g -> Monic (Pullback.p₁ pull)
  mono-pullback-stable f g pull g-mono {C} {g1} {g2} p₁∘g1≡p₁∘g2 = 
       trans
         (universal-unique {commutes = under-assoc commutes} g1 refl refl)
         (sym
          (universal-unique g2 (sym p₁∘g1≡p₁∘g2)
           (g-mono
            (trans (under-assoc (sym commutes))
             (trans (∘-resp-≡ refl (sym p₁∘g1≡p₁∘g2))
              (under-assoc commutes))))))
    where
      open Pullback pull

  _∘mono_ : ∀ {A B C} {f : B ⇒ C}{g : A ⇒ B} -> Monic f -> Monic g -> Monic (f ∘ g)
  f-mono ∘mono g-mono = λ x → g-mono (f-mono (trans (sym assoc) (trans x assoc)))

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
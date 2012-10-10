module Injection.Objects where

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

open import Injection
import Category

module Dummy {A : Set} where
  open Category (List A) Inj _∘i_ id-i _≡_ public
open Dummy public

abstract

  e$u≡m : ∀ {A : Set}{S T : List A}{f g : Inj S T} -> (equ : Equalizer f g) -> let open Equalizer equ in 
               (a : A) (m : S ∋ a) → f $ m ≡ g $ m → Σ (E ∋ a) (λ u → m ≡ e $ u)
  e$u≡m equ a m eq =  
    let
        open Equalizer equ
        [m] = m ∷ [] [ _ ]
        u = universal [m] (ext-∘ (λ {.a zero → eq; x (suc ())}))
    in u $ zero , sym (trans (sym (apply-∘ e u)) (cong (λ f → f $ zero) e∘universal≡m))

  p$u≡q : ∀ {A : Set} {X Y Z : List A}(f : Inj X Z)(g : Inj Y Z) -> (p : Pullback f g) -> let open Pullback p in
      (a : A) (q₂ : Y ∋ a) (q₁ : X ∋ a) → f $ q₁ ≡ g $ q₂ → Σ (P ∋ a) (λ u → p₁ $ u ≡ q₁ × p₂ $ u ≡ q₂)
  p$u≡q f g p a q₂ q₁ eq = 
   let
    open Pullback p
    [q₁] = q₁ ∷ [] [ _ ]
    [q₂] = q₂ ∷ [] [ _ ]
    u : Inj (a ∷ []) P
    u = universal [q₁] [q₂] (ext-∘ (λ {._ zero → eq; _ (suc ())}))
   in u $ zero , 
      trans (sym (apply-∘ p₁ u)) (cong (λ f₁ → f₁ $ zero) p₁∘universal≡q₁) , 
      trans (sym (apply-∘ p₂ u)) (cong (λ f₁ → f₁ $ zero) p₂∘universal≡q₂) 


[]-unique : ∀ {A : Set}{Q : List A}{f g : Inj [] Q} -> f ≡ g
[]-unique {f = []}{[]} = refl
    

weak-equalizer : ∀ {A : Set}{a : A}{S T : List A}(f g : Inj S T){E e} -> IsEqualizer f g E e -> IsEqualizer (weak {x = a} f) (weak g) E e
weak-equalizer {a = a} f g {E} {e} equ = 
   record {
     commutes = trans (Inj-thin-∘i zero f e) (trans (cong (Inj-thin zero) commutes)
                                                (sym (Inj-thin-∘i zero g e)));
     universal = λ m commutes₁ → universal m 
               (Inj-thin-inj zero (f ∘i m) (g ∘i m) (trans (sym (Inj-thin-∘i zero f m)) (trans commutes₁ (Inj-thin-∘i zero g m))));
     universal-unique = universal-unique;
     e∘universal≡m = e∘universal≡m }
  where
    open IsEqualizer equ


_→zero∷e⇒i∷f,i∷g : ∀ {A : Set}{a : A}{S T : List A}{v : T ∋ a}{f g : Inj S T}{pf pg}{E e} -> 
               IsEqualizer f g E e -> IsEqualizer (v ∷ f [ pf ]) (v ∷ g [ pg ]) (a ∷ E) (zero ∷[] e)
_→zero∷e⇒i∷f,i∷g {a = a} {v = u} {f} {g} {pf} {pg} {E} {e} equ = 
   record {
     commutes = ext-∘ aux;
     universal = λ m commutes₁ → proj₁ (uni m commutes₁);
     universal-unique = λ {Q} {m} {commutes₁} u₁ e∘u≡m → ∘i-inj (zero ∷[] e) u₁ _ (trans e∘u≡m (sym (proj₂ (uni m commutes₁))));
     e∘universal≡m = \ {Q} {m} {comm} -> proj₂ (uni m comm) }
  where
    open IsEqualizer equ
    aux : (x : _) (v : a ∷ E ∋ x) → (u ∷ f [ pf ]) $ ((zero ∷[] e) $ v) ≡ (u ∷ g [ pg ]) $ ((zero ∷[] e) $ v)
    aux .a zero = refl
    aux x (suc v) rewrite Inj-thin-$ {x = a} zero e v = ∘-ext commutes _ v
    uni : {Q : _} (m : Inj Q _) → (u ∷ f [ pf ]) ∘i m ≡ (u ∷ g [ pg ]) ∘i m → Σ (Inj Q (a ∷ E)) (λ z → (zero ∷[] e) ∘i z ≡ m )
    uni = 
      Equ-universal-quote (u ∷ f [ pf ]) (u ∷ g [ pg ]) (zero ∷[] e)
        (∋-case (λ x → zero , refl)
         (λ a₁ y x →
            let rec = e$u≡m (Equ _ , _ , equ) a₁ y x
            in suc (proj₁ rec) ,
               trans (cong suc (proj₂ rec))
               (sym (Inj-thin-$ zero e (proj₁ (e$u≡m (Equ _ , _ , equ) a₁ y x))))))
    

cons-equalizer : ∀ {A : Set}{a : A}{S T : List A}(f g : Inj S T) -> Equalizer f g -> Equalizer (cons {x = a} f) (cons g)
cons-equalizer {A} {a} f g (Equ E , e , equ) = Equ _ , _ , (weak-equalizer f g equ) →zero∷e⇒i∷f,i∷g

eta-empty : ∀ {A : Set}{Q : List A}(f g : Inj Q []) -> f ≡ g
eta-empty [] [] = refl
eta-empty (() ∷ f [ pf ]) g

empty-equalizer : ∀ {A : Set}{xs : List A} -> IsEqualizer {A}{[]}{xs} [] [] [] []
empty-equalizer {A} = record {
                    commutes = refl;
                    universal = λ m commutes → m;
                    universal-unique = λ u e∘u≡m → eta-empty _ _;
                    e∘universal≡m = eta-empty _ _ }

_,_→weake⇒i∷f,j∷g : ∀ {A : Set}{a : A}{S T : List A}{u v : T ∋ a} -> u ≢ v -> 
               ∀ {f g : Inj S T}{pf pg}{E e} -> IsEqualizer f g E e -> IsEqualizer (u ∷ f [ pf ]) (v ∷ g [ pg ]) E (weak e)
_,_→weake⇒i∷f,j∷g {a = a} {u = u}{v} u≢v {f} {g} {pf} {pg} {E} {e} equ = 
       record {
         commutes = ext-∘ aux;
         universal = λ m commutes₁ → proj₁ (uni m commutes₁);
         universal-unique = λ {Q} {m} {commutes₁} u₁ e∘u≡m → ∘i-inj (weak e) u₁ _ (trans e∘u≡m (sym (proj₂ (uni m commutes₁))));
         e∘universal≡m = \ {Q} {m} {comm} -> proj₂ (uni m comm) }
 where 
   open IsEqualizer equ
   aux : (x : _) (v₁ : E ∋ x) → (u ∷ f [ pf ]) $ (weak e $ v₁) ≡ (v ∷ g [ pg ]) $ (weak e $ v₁)
   aux x v₁ rewrite Inj-thin-$ {x = a} zero e v₁ = ∘-ext commutes _ v₁

   uni : {Q : _} (m : Inj Q _) → (u ∷ f [ pf ]) ∘i m ≡ (v ∷ g [ pg ]) ∘i m → Σ (Inj Q E) (λ z → (weak e) ∘i z ≡ m )
   uni = Equ-universal-quote (u ∷ f [ pf ]) (v ∷ g [ pg ]) (weak e) (∋-case (λ u≡v → ⊥-elim (u≢v u≡v)) 
                   (λ a₁ y x →
                        let rec : _
                            rec = e$u≡m (Equ _ , _ , equ) a₁ y x
                        in proj₁ rec ,
                           trans (cong suc (proj₂ rec))
                           (sym (Inj-thin-$ zero e (proj₁ (e$u≡m (Equ _ , _ , equ) a₁ y x))))))

equalizer : ∀ {A : Set}{S T : List A}(f g : Inj S T) -> Equalizer f g
equalizer [] [] = Equ [] , [] , empty-equalizer
equalizer (i ∷ f [ pf ])  (j ∷ g [ pf₁ ]) with eq-∋ (_ , i) (_ , j) | equalizer f g
equalizer (i ∷ f [ pf ]) (.i ∷ g [ pf₁ ]) | yes refl | Equ E , e , e⇒f,g = Equ _ ∷ E , zero ∷[] e , e⇒f,g →zero∷e⇒i∷f,i∷g
equalizer (i ∷ f [ pf ])  (j ∷ g [ pf₁ ]) | no ¬p    | Equ E , e , e⇒f,g = Equ E , weak e , i≢j , e⇒f,g →weake⇒i∷f,j∷g
  where
    i≢j : i ≢ j
    i≢j = (λ x → ¬p (cong-proj₁ x))

empty-pullback : ∀ {A : Set} {X Z : List A} → {f : Inj X Z} → IsPullback f [] [] [] []
empty-pullback {A} {X} {Z} {f} = record {
                   commutes = []-unique;
                   universal = λ q₁ q₂ commutes → q₂;
                   universal-unique = λ u p₁∘u≡q₁ p₂∘u≡q₂ → eta-empty u _;
                   p₁∘universal≡q₁ = \ {Q q₁ q₂ commutes} -> proof {Q} {q₁} {q₂} {commutes};
                   p₂∘universal≡q₂ = eta-empty _ _ }
 where
   proof : {Q : List A} {q₁ : Inj Q X} {q₂ : Inj Q []}
      {commutes : f ∘i q₁ ≡ [] ∘i q₂} →
      [] ∘i q₂ ≡ q₁
   proof {.[]} {q₁} {[]} = []-unique
   proof {._} {q₁} {() ∷ q₂ [ pf ]}

∈-pullback : ∀ {A : Set} {X Y Z P : List A} {f : Inj X Z}{g : Inj Y Z}{p₁ p₂} -> IsPullback f g P p₁ p₂ -> 
             ∀ {a x pf x∉p₁ } → IsPullback f ((f $ x) ∷ g [ pf ]) (a ∷ P) (x ∷ p₁ [ x∉p₁ ]) (zero ∷[] p₂)
∈-pullback {A}{X}{Y}{Z}{P}{f = f} {g} {p₁}{p₂}pull{a}{x}{pf}{x∉p₁}  = record {
                    commutes = ext-∘ aux;
                    universal = λ q₁ q₂ commutes₁ → proj₁ (uni q₁ q₂ commutes₁);
                    universal-unique = λ u p₁∘u≡q₁ p₂∘u≡q₂ → 
                        ∘i-inj (x ∷ p₁ [ x∉p₁ ]) u (proj₁ (uni _ _ _)) (trans p₁∘u≡q₁ (proj₁ (proj₂ (uni _ _ _))));
                    p₁∘universal≡q₁ = sym (proj₁ (proj₂ (uni _ _ _)));
                    p₂∘universal≡q₂ = sym (proj₂ (proj₂ (uni _ _ _))) }
  where
    open IsPullback pull
    abstract
      uni : ∀ {Q} -> (q₁ : Inj Q X) (q₂ : Inj Q (a ∷ Y)) -> f ∘i q₁ ≡ ((f $ x) ∷ g [ pf ]) ∘i q₂ -> 
          ∃ \ u -> q₁ ≡ (x ∷ p₁ [ x∉p₁ ]) ∘i u × q₂ ≡ (zero ∷[] p₂) ∘i u  
      uni {Q} q₁ q₂ eq = Pull-universal-quote f ((f $ x) ∷ g [ pf ]) (x ∷ p₁ [ x∉p₁ ]) (zero ∷[] p₂)  
            (∋-case (λ x₁ x₂ → zero , ((injective f x x₁ (sym x₂)) , refl)) (λ a₁ y x₁ x₂ → 
            let p : Σ _ _; p = p$u≡q f g (Pull P , p₁ , p₂ , pull) a₁ y x₁ x₂ 
            in (suc (proj₁ p)) , (proj₁ (proj₂ p)) , (trans (iso2 _ _ (proj₁ p)) (cong suc (proj₂ (proj₂ p)))))) 
            q₁ q₂ eq

    aux : ∀ t (v : _ ∋ t) -> f $ ((x ∷ p₁ [ x∉p₁ ]) $ v) ≡
      ((f $ x) ∷ g [ pf ]) $
      ((zero ∷[] p₂) $ v) 
    aux .a zero = refl
    aux t (suc v) = trans (∘-ext (IsPullback.commutes pull) _ v) (cong (_$_ ((f $ x) ∷ g [ pf ])) (sym (Inj-thin-$ zero p₂ v)))
  

comm-pullback : ∀ {A : Set} {X Y Z P : List A} {f : Inj X Z}{g : Inj Y Z}{p₁ p₂} -> IsPullback f g P p₁ p₂ -> 
                 IsPullback g f P p₂ p₁
comm-pullback pull = record {
                       commutes = sym commutes;
                       universal = λ q₁ q₂ commutes₁ → universal q₂ q₁ (sym commutes₁);
                       universal-unique = λ u p₁∘u≡q₁ p₂∘u≡q₂ → universal-unique u p₂∘u≡q₂ p₁∘u≡q₁;
                       p₁∘universal≡q₁ = p₂∘universal≡q₂;
                       p₂∘universal≡q₂ = p₁∘universal≡q₁ }
  where 
    open IsPullback pull


∉-pullback : ∀ {A : Set} {X Y Z P : List A} {f : Inj X Z}{g : Inj Y Z}{p₁ p₂} -> IsPullback f g P p₁ p₂ -> 
             ∀ {a} {i : Z ∋ a} {pf} → i ∉Im f -> IsPullback f (i ∷ g [ pf ]) P p₁ (weak p₂)
∉-pullback {A}{X}{Y}{Z}{f = f} {g = g} {p₁}{p₂}pull {a} {i} {pf} i∉f = record {
                        commutes = trans commutes (ext-∘ (λ x v →  
                                                  cong (_$_ (_ ∷ g [ _ ])) (sym (Inj-thin-$ zero p₂ v))));
                        universal = λ q₁ q₂ commutes₁ → proj₁ (uni q₁ q₂ commutes₁);
                        universal-unique = λ u p₁∘u≡q₁ p₂∘u≡q₂ → ∘i-inj p₁ u (proj₁ (uni _ _ _)) (trans p₁∘u≡q₁ (proj₁ (proj₂ (uni _ _ _))));
                        p₁∘universal≡q₁ = sym (proj₁ (proj₂ (uni _ _ _)));
                        p₂∘universal≡q₂ = sym (proj₂ (proj₂ (uni _ _ _))) }
   where 
     open IsPullback pull 
     abstract
       uni : ∀ {Q} -> (q₁ : Inj Q X) (q₂ : Inj Q (a ∷ Y)) -> f ∘i q₁ ≡ (i ∷ g [ pf ]) ∘i q₂ -> ∃ \ u -> q₁ ≡ p₁ ∘i u × q₂ ≡ (weak p₂) ∘i u  
       uni {Q} q₁ q₂ eq = Pull-universal-quote f (i ∷ g [ pf ]) p₁ (weak p₂) (∋-case (λ x x₁ → ⊥-elim (i∉f x (sym x₁))) 
         (λ a₁ y x x₁ → let p : Σ _ _
                            p = p$u≡q f g (Pull _ , p₁ , p₂ , pull) a₁ y x x₁
                        in (proj₁ p) , ((proj₁ (proj₂ p)) , trans (iso2 _ _ (proj₁ p)) (cong suc (proj₂ (proj₂ p)))))) 
         q₁ q₂ eq

pullback : ∀ {A : Set} {X Y Z : List A} → (f : Inj X Z)(g : Inj Y Z) → Pullback f g
pullback f [] = Pull [] , [] , [] , empty-pullback
pullback f (i ∷ g [ pf ]) with invert f i | pullback f g 
pullback f (.(f $ x) ∷ g [ pf ]) | yes (x , refl) | Pull P , p₁ , p₂ , p₁,p₂⇒f,g = 
                                                    Pull (_ ∷ P) , (x ∷ p₁ [ x∉p₁ ]) , (zero ∷[] p₂) , ∈-pullback p₁,p₂⇒f,g
  where
    open IsPullback p₁,p₂⇒f,g
    x∉p₁ : x ∉ p₁
    x∉p₁ = ∉Im-∉ p₁ x λ b x≡k$b → ∉-∉Im g (f $ x) pf (p₂ $ b) 
              (begin f $ x        ≡⟨ cong (_$_ f) x≡k$b ⟩ 
                     f $ (p₁ $ b) ≡⟨ ∘-ext commutes _ b ⟩ 
                     g $ (p₂ $ b) ∎)
pullback f (i ∷ g [ pf ])        | no i∉f         | Pull P , p₁ , p₂ , p₁,p₂⇒f,g = 
                                                    Pull P , p₁ , weak p₂ , ∉-pullback p₁,p₂⇒f,g (λ b x → i∉f (b , (sym x)))

weak-pullback : ∀ {A : Set} {X Y Z P : List A} {f : Inj X Z}{g : Inj Y Z}{p₁ p₂} -> IsPullback f g P p₁ p₂ -> 
                ∀ {a : A} -> IsPullback (weak {x = a} f) (weak g) P p₁ p₂
weak-pullback pull = record {
                       commutes = trans (Inj-thin-∘i zero _ _)
                                    (trans (cong (Inj-thin zero) commutes)
                                     (sym (Inj-thin-∘i zero _ _)));
                       universal = λ q₁ q₂ commutes₁ → universal q₁ q₂
                                                         (Inj-thin-inj zero (_ ∘i q₁) (_ ∘i q₂)
                                                          (trans (sym (Inj-thin-∘i zero _ q₁))
                                                           (trans commutes₁ (Inj-thin-∘i zero _ q₂))));
                       universal-unique = universal-unique;
                       p₁∘universal≡q₁ = p₁∘universal≡q₁;
                       p₂∘universal≡q₂ = p₂∘universal≡q₂ }
  where
    open IsPullback pull

cons-pullback : ∀ {A : Set}{a : A}{X Y Z : List A}(f : Inj X Z)(g : Inj Y Z) -> Pullback f g -> Pullback (cons {x = a} f) (cons g)
cons-pullback {A} {a} f g (Pull P , p₁ , p₂ , p₁,p₂⇒f,g) = Pull a ∷ P , cons p₁ , cons p₂ , 
              ∈-pullback (comm-pullback (∉-pullback (comm-pullback (weak-pullback p₁,p₂⇒f,g)) (∉-∉Im (weak g) zero (v∉Inj-thinv zero g))))



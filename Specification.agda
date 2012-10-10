module Specification where


open import Data.Product renaming (map to mapΣ)
open import Data.Nat hiding (_≤_) renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.Sum renaming (inj₁ to yes; inj₂ to no)
open import Data.Maybe
open import Category.Monad
import Level
open RawMonad (monad {Level.zero})

open import Injection
open import Injection.Objects
open import Lists

open import Syntax
open import Equality

open import DSub

Property : ∀ Sg G -> Set₁
Property Sg G = (∀ {G2} -> Sub Sg G G2 -> Set)

Unifies : ∀ {Sg G1 D S} (x y : Term Sg G1 D S) -> Property Sg G1
Unifies x y σ = eqT (subT σ x) (subT σ y)

∃⟦σ⟧_ : ∀ {Sg G1} -> Property Sg G1 -> Set
∃⟦σ⟧ P = ∃ \ G2 -> ∃ \ σ -> P {G2} ⟦ σ ⟧

∃σ_ : ∀ {Sg G1} -> Property Sg G1 -> Set
∃σ_ P = ∃ \ G2 -> ∃ \ σ -> P {G2} σ

Sup : ∀ {Sg G1} -> Property Sg G1 -> Property Sg G1
Sup P σ = (∀ {G'} ρ -> P {G'} ρ -> ρ ≤ σ)

Max : ∀ {Sg G1} -> Property Sg G1 -> Property Sg G1
Max P σ = P σ × Sup P σ

DClosed : ∀{Sg G} (P : Property Sg G) -> Set
DClosed P = ∀ {G1} f {G2} g -> f ≤ g -> P {G2} g -> P {G1} f

Extensional : ∀ {Sg G} -> Property Sg G -> Set
Extensional P = ∀ {G f g} -> (∀ S u -> f S u ≡ g S u) -> P {G} f -> P g

Spec : ∀ {Sg G1 D S} (x y : Term Sg G1 D S) -> Set
Spec x y = ∃⟦σ⟧ Max (Unifies x y) ⊎ ¬ ∃σ Unifies x y

Unifies-ext : ∀ {Sg G1 D S} (x y : Term Sg G1 D S) -> Extensional (Unifies x y)
Unifies-ext x y f≡g subfx≡subfy rewrite subT-ext f≡g x | subT-ext f≡g y = subfx≡subfy

map-Unifies : ∀ {Sg g h h' d t} {σ : Sub Sg g h}{σ' : Sub Sg g h'}-> σ ≤ σ' -> {x y : Term Sg g d t} -> Unifies x y σ' -> Unifies x y σ
map-Unifies (δ , σ≡δ∘σ') {x} {y} σ'x≡σ'y = ≡-T 
         (trans (subT-ext σ≡δ∘σ' x) 
         (trans (sym (subT-∘ x)) 
         (trans (cong (subT δ) (T-≡ σ'x≡σ'y)) 
         (sym (trans (subT-ext σ≡δ∘σ' y) 
                     (sym (subT-∘ y)))))))

optimist : ∀ {Sg l m o} (p : Sub Sg _ o) (q : Sub Sg _ l) (P Q : Property Sg m) -> Extensional Q
           -> DClosed P -> Max P p 
           -> Max (\ s -> Q (s ∘s p)) q 
           -> Max (\ s -> P s × Q s)  (q ∘s p)
optimist p q P Q Q-ext DCP (Ppa , pMax) (Qqpa , qMax) = ((DCP (q ∘s p) p (q , (λ S u → refl)) Ppa) , Qqpa) , 
  (λ ρ x → let rP : _
               rP = pMax ρ (proj₁ x)
             in let rq : _
                    rq = qMax (proj₁ rP) (Q-ext (proj₂ rP) (proj₂ x))
                  in proj₁ rq , (λ S u → trans (proj₂ rP S u) (trans (sub-ext (proj₂ rq) (p S u)) (sym (sub-∘ (p S u))))))


sandwich : ∀ {Sg G1 G2 D T} {f g : Term Sg G1 D T -> Term Sg G2 D T} -> (∀ x -> f x ≡ g x) -> ∀ {x y} -> f x ≡T f y -> g x ≡T g y
sandwich eq {x}{y} p rewrite eq x | eq y = p

shift : ∀ {Sg G G1 G2 D S} (x y : Term Sg G D S) (f : Sub Sg G G1)(g : Sub Sg G1 G2) ->
          Max (Unifies (subT f x) (subT f y)) g -> Max (\ s -> Unifies x y (s ∘s f)) g
shift x y f g (eq , max) = sandwich subT-∘ eq , (λ ρ x₁ → max ρ (sandwich (λ x₂ → sym (subT-∘ x₂)) x₁)) 

shift2 : ∀ {Sg G h1 h2 D T} (xs ys : Term Sg G D T) (σ1 : Sub Sg G h1)(σ : Sub Sg G h2) -> σ1 ≤ σ -> 
                                                    Unifies xs ys σ1 -> ∃σ (Unifies (subT σ xs) (subT σ ys))
shift2 xs ys σ1 σ (δ , σ1≡δ∘σ) eq = _ ,
                                      δ ,
                                      sandwich
                                      (λ xs₁ → sym (trans (subT-∘ xs₁) (sym (subT-ext σ1≡δ∘σ xs₁)))) eq
 
optimist-Unifies : ∀ {Sg m l o D T Ts}(x y : Tm Sg m D T)(xs ys : Tms Sg m D Ts) ->
           (p : Sub Sg m o) (q : Sub Sg o l) ->
           Max (Unifies x y) p 
           -> Max (Unifies (subT p xs) (subT p ys)) q 
           -> Max (\ s -> Unifies (Tms._∷_ x xs) (y ∷ ys) s)  (q ∘s p)

optimist-Unifies x y xs ys p q MaxP MaxQq with optimist p q (Unifies x y) (Unifies xs ys) (Unifies-ext xs ys) (λ f g x₁ x₂ → map-Unifies {σ = f} {σ' = g} x₁ {x} {y} x₂) MaxP (shift xs ys p q MaxQq)
optimist-Unifies x y xs ys p q MaxP MaxQq | (xy , xsys) , max = (xy ∷ xsys) , (λ {ρ (eqt ∷ eqts) → max ρ (eqt , eqts)})

refl-Unifies : ∀ {Sg G D T} (x : Term Sg G D T) -> ∃⟦σ⟧ Max (Unifies x x)
refl-Unifies x = (_ , ((DS (λ S x → mvar x) , inj₁ (refl , ((λ S x → mvar x) , (λ S u → sym (ren-id _))) , (λ S u → sym (ren-id _)))) 
                          , refl-T _ , (λ ρ x → ρ , (λ S u → sym (ren-id _)))))

Spec[xs,ys]⇒Spec[σxs,σys] : ∀ {Sg G G1 D T} (xs ys : Term Sg G D T) (σ : Sub Sg G G1) -> Ctx-length G ≡ Ctx-length G1 -> 
        (le : (\ S x -> mvar x) ≤ σ) -> (∀ S u -> id-s S u ≡ (σ ∘s proj₁ le) S u) -> Spec xs ys -> Spec (subT σ xs) (subT σ ys)
Spec[xs,ys]⇒Spec[σxs,σys] xs ys σ G~G1 (δ , id≡δ∘σ) id≡σ∘δ (inj₁ (_ , σ₁ , eq , max)) 
  = inj₁ (_ , ((σ₁ ∘ds (DS δ , inj₁ (sym G~G1 , (σ , id≡σ∘δ) , id≡δ∘σ))) , 
   sandwich (\ ys -> ((((trans (cong (subT ⟦ σ₁ ⟧) (trans (sym (subT-id ys)) (subT-ext id≡δ∘σ ys))) 
   (trans (subT-∘ ys) (trans (subT-ext (λ S x → subT-∘ (σ S x)) ys) (sym (subT-∘ ys))))))))) eq , 
          (λ ρ x → let rq : _
                       rq = max (ρ ∘s σ) (sandwich subT-∘ x)
                     in (proj₁ rq) , (λ S u → trans (trans (trans (sym (ren-id (ρ S u))) (cong (sub ρ) (trans refl (id≡σ∘δ S u)))) (sub-∘ {f = ρ} {σ} (δ S u))) (trans (subT-ext (proj₂ rq) (δ S u)) (sym (subT-∘ (δ S u))))))))
Spec[xs,ys]⇒Spec[σxs,σys] xs ys σ G~G1 id≤σ _ (inj₂ y) = inj₂ (λ {(_ , σ₁ , eq) → y (_ , (σ₁ ∘s σ) , (sandwich (λ x → (subT-∘ x)) eq))})

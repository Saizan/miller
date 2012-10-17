module OccursCheck where

open import Data.Product renaming (map to mapΣ)
mapΣ₂ : ∀ {a b c p q r}
        {A : Set a} {B : Set b}{C : Set c} {P : A → Set p} {Q : B → Set q} {R : C -> Set r}→
      (f : A -> B -> C) → (∀ {x y} → P x → Q y -> R (f x y)) →
      Σ A P → Σ B Q -> Σ C R
mapΣ₂ f g (x₀ , y₀) (x , y) = (f x₀ x , g y₀ y)

open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Category.Monad

open import Injection
open import Lists

open import Syntax
open import Height
open import OneHoleContext

No-Cycle : ∀ {TI Sg G D1 DI DO X} -> let TO = TI in 
         (d : DTm Sg G (DI , TI) X) (ps : Context Sg G X (DO , TO)) 
         (t : Term Sg G D1 TO) (i : Inj D1 DI)(j : Inj D1 DO) -> 
         ¬ renT i t ≡ ∫ (d ∷ ps) (renT j t)
No-Cycle d ps t i j eq = ≡-or-> (cong heightT eq) r
  where open ≤-Reasoning 
        open import Data.Nat.Properties
        r = begin
              suc (heightT (renT i t)) ≡⟨ cong suc (sym (renT-height i t)) ⟩
              suc (heightT t) ≡⟨ cong suc (renT-height j t) ⟩
              suc (heightT (renT j t)) ≤⟨ s≤s (OnHeight.∫-height ps (renT j t)) ⟩
              suc (heightT (∫ ps (renT j t))) ≤⟨ OnHeight.∫once-height d (∫ ps (renT j t)) ⟩ 
              heightT (∫once d (∫ ps (renT j t))) ∎
        ≡-or-> : ∀ {m n} -> m ≡ n -> n > m -> ⊥
        ≡-or-> refl (s≤s ge) = ≡-or-> refl ge

_[_]OccursIn_ : ∀ {Sg G D D' T S} (u : G ∋ S) (j : Inj (ctx S) D') (t : Term Sg G D T) → Set
u [ j ]OccursIn t = Σ (Context _ _ _ (_ , inj₁ _) ) \ C → ∫ C (fun u j) ≡ t

_OccursIn_ : ∀ {Sg G D T S} (u : G ∋ S) (t : Term Sg G D T) → Set
_OccursIn_ u t = ∃ \ D' → Σ (Inj _ D') \ j → u [ j ]OccursIn t

_NotOccursIn_ : ∀ {Sg G D T S} (u : G ∋ S) (t : Term Sg G D T) → Set
u NotOccursIn t = (∃ \ s → subT (\ S v → mvar (thin u S v)) s ≡ t)

Dec_OccursIn_ : ∀ {Sg G D T S} (u : G ∋ S) (t : Term Sg G D T) → Set
Dec u OccursIn t = u NotOccursIn t ⊎ u OccursIn t

map-occ : ∀ {Sg G S D T D' T'}{u : G ∋ S}{t : Term Sg G D T} (d : DTm Sg G (D' , T') (D , T)) → u OccursIn t → u OccursIn ∫once d t
map-occ d (Dj , j , C , eq) = (Dj , j , (d ∷ C) , cong (∫once d) eq)

_∙_ : ∀ {Sg G S D T D' T'}{u : G ∋ S}{t : Term Sg G D T} (d : DTm Sg (G - u) (D' , T') (D , T)) 
        → Dec u OccursIn t → Dec u OccursIn ∫once (subD (λ S₁ v → mvar (thin u S₁ v)) d) t
_∙_ {u = u} d (inj₂ occ) = inj₂ (map-occ (subD (λ S₁ v → mvar (thin u S₁ v)) d) occ)
_∙_ {u = u} d (inj₁ (s , eq)) = inj₁ (∫once d s , trans (∫once-sub _ d s) (cong (∫once (subD (λ S₁ v → mvar (thin u S₁ v)) d)) eq))

mutual
  check : ∀ {Sg G D T S} (u : G ∋ S) (t : Tm Sg G D T) → Dec u OccursIn t
  check u (con c ts) = con c ∙ checks u ts 
  check u (fun w j) with thick u w
  ... | inj₁ (z , eq) = inj₁ (fun z j , cong₂ fun eq (right-id j))
  check u (fun .u j) | inj₂ refl = inj₂ (_ , (j , ([] , refl)))
  check u (var x ts) = var x ∙ checks u ts
  check u (lam t) = lam ∙ check u t
  
  checks : ∀ {Sg G D Ts S} (u : G ∋ S) (ts : Tms Sg G D Ts) → Dec u OccursIn ts
  checks u [] = inj₁ ([] , refl)
  checks u (t ∷ ts) with check u t | checks u ts 
  ... | inj₂ x | _ = inj₂ (map-occ (head ts) x)
  ... | inj₁ x | inj₁ xs = inj₁ (mapΣ₂ _∷_ (cong₂ _∷_) x xs)
  ... | _ | inj₂ xs = inj₂ (map-occ (tail t) xs)


module Syntax.No-Cycle where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality

open import Support.Product

open import Injections

open import Syntax.Type
open import Syntax.OneHoleContext

Height = ℕ

mutual
  height : ∀ {Sg G D T b} -> Tm< b > Sg G D T -> Height
  height (con c ts) = suc (heights ts)
  height (var x ts) = suc (heights ts)
  height (lam t)    = suc (height t)
  height (mvar u j) = 0

  heights : ∀ {Sg G D T b} -> Tms< b > Sg G D T -> Height
  heights []       = 0
  heights (t ∷ ts) = suc (height t ⊔ heights ts)

heightT : ∀ {Sg G D T b} -> Term< b > Sg G D T -> Height
heightT {T = inj₁ _} = height
heightT {T = inj₂ _} = heights

renT-height : ∀ {T Sg G D D1 b} -> (i : Inj D D1) -> (t : Term< b > Sg G D T) -> heightT t ≡ heightT (renT i t)
renT-height {inj₁ ._} i (con c ts) = cong suc (renT-height i ts)
renT-height {inj₁ ._} i (mvar u j) = refl
renT-height {inj₁ ._} i (var x ts) = cong suc (renT-height i ts)
renT-height {inj₁ ._} i (lam t) = cong suc (renT-height _ t)
renT-height {inj₂ .[]} i [] = refl
renT-height {inj₂ ._} i (t ∷ t₁) = cong₂ (\ x y -> suc (x ⊔ y)) (renT-height i t) (renT-height i t₁)

open import Data.Nat  

private
  n≤m⊔n : ∀ m n → (m ⊔ n) ≥ n
  n≤m⊔n zero    _       = begin _ ∎
  n≤m⊔n (suc m) zero    = z≤n
  n≤m⊔n (suc m) (suc n) = s≤s (n≤m⊔n m n)

∫once-height : ∀ {Sg G DI TI DO TO b} → (d : DTm< b > Sg G (DI , TI) (DO , TO)) → (t : Term< b > Sg G DO TO) → heightT (∫once d t) > heightT t
∫once-height lam t = s≤s (begin heightT t ∎)
∫once-height (head ts) t = s≤s (m≤m⊔n (height t) (heights ts))
∫once-height (tail t) ts = s≤s (n≤m⊔n (height t) (heights ts))
∫once-height (con c) t = s≤s (begin heightT t ∎)
∫once-height (var x) t = s≤s (begin heightT t ∎)

∫-height : ∀ {Sg G I O b} → (ps : Context< b > Sg G I O) → (t : Term< b > Sg G (proj₁ O) (proj₂ O)) → heightT (∫ ps t) ≥ heightT t
∫-height []       t = begin heightT t ∎
∫-height (x ∷ ps) t = begin heightT t                  ≤⟨ ≤-step (∫-height ps t) ⟩ 
                            suc (heightT (∫ ps t))     ≤⟨ ∫once-height x (∫ ps t) ⟩ 
                            heightT (∫once x (∫ ps t)) ∎

No-Cycle : ∀ {b TI Sg G D1 DI DO X} -> let TO = TI in 
         (d : DTm< b > Sg G (DI , TI) X) (ps : Context< b > Sg G X (DO , TO)) 
         (t : Term< b > Sg G D1 TO) (i : Inj D1 DI)(j : Inj D1 DO) -> 
         ¬ renT i t ≡ ∫ (d ∷ ps) (renT j t)
No-Cycle d ps t i j eq = ≡-or-> (cong heightT eq) 
           (begin
              suc (heightT (renT i t))            ≡⟨ cong suc (sym (renT-height i t)) ⟩
              suc (heightT t)                     ≡⟨ cong suc (renT-height j t) ⟩
              suc (heightT (renT j t))            ≤⟨ s≤s (∫-height ps (renT j t)) ⟩
              suc (heightT (∫ ps (renT j t)))     ≤⟨ ∫once-height d (∫ ps (renT j t)) ⟩ 
              heightT (∫once d (∫ ps (renT j t))) ∎)
  where
    ≡-or-> : ∀ {m n} -> m ≡ n -> n > m -> ⊥
    ≡-or-> refl (s≤s ge) = ≡-or-> refl ge

module Unification.OccursCheck where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum renaming (inj₁ to no; inj₂ to yes)

open import Support.Equality

open import Injection hiding (Dec)

open import Syntax

-- No-Cycle proves that Even under different renamings a term can't
-- appear inside itself: it wouldn't be well-founded. 
-- We'll use this to show (mvar u i) and (∫ (d ∷ ps) (mvar u j)) not
-- unifiable in Unif.flexAny.
No-Cycle : ∀ {b TI Sg G D1 DI DO X} -> let TO = TI in 
         (d : DTm< b > Sg G (DI , TI) X) (ps : Context< b > Sg G X (DO , TO)) 
         (t : Term< b > Sg G D1 TO) (i : Inj D1 DI)(j : Inj D1 DO) -> 
         ¬ renT i t ≡ ∫ (d ∷ ps) (renT j t)
No-Cycle d ps t i j eq = ≡-or-> (cong heightT eq) r
  where open ≤-Reasoning 
        open import Data.Nat.Properties
        r = begin
              suc (heightT (renT i t))            ≡⟨ cong suc (sym (renT-height i t)) ⟩
              suc (heightT t)                     ≡⟨ cong suc (renT-height j t) ⟩
              suc (heightT (renT j t))            ≤⟨ s≤s (OnHeight.∫-height ps (renT j t)) ⟩
              suc (heightT (∫ ps (renT j t)))     ≤⟨ OnHeight.∫once-height d (∫ ps (renT j t)) ⟩ 
              heightT (∫once d (∫ ps (renT j t))) ∎
        ≡-or-> : ∀ {m n} -> m ≡ n -> n > m -> ⊥
        ≡-or-> refl (s≤s ge) = ≡-or-> refl ge

_OccursIn_ : ∀ {Sg G D T S} (u : G ∋ S) (t : Term Sg G D T) → Set
_OccursIn_ u t = ∃ \ D' → Σ (Inj _ D') \ j → Σ (Context _ _ _ (_ , inj₁ _) ) \ C → ∫ C (mvar u j) ≡ t
  where open import Data.Sum

_NotOccursIn_ : ∀ {Sg G D T S} (u : G ∋ S) (t : Term Sg G D T) → Set
u NotOccursIn t = ∃ \ (s : Term _ _ _ _) → subT (thin-s u) s ≡ t

Dec_OccursIn_ : ∀ {Sg G D T S} (u : G ∋ S) (t : Term Sg G D T) → Set
Dec u OccursIn t = u NotOccursIn t ⊎ u OccursIn t

map-occ : ∀ {Sg G S D T D' T'}{u : G ∋ S}{t : Term Sg G D T} (d : DTm Sg G (D' , T') (D , T)) → u OccursIn t → u OccursIn ∫once d t
map-occ d (Dj , j , C , eq) = (Dj , j , (d ∷ C) , cong (∫once d) eq)

_∙_ : ∀ {Sg G S D T D' T'}{u : G ∋ S}{t : Term Sg G D T} (d : DTm Sg (G - u) (D' , T') (D , T)) 
        → Dec u OccursIn t → Dec u OccursIn ∫once (subD (thin-s u) d) t
_∙_ {u = u} d (yes occ)     = yes (map-occ (subD (thin-s u) d) occ)
_∙_ {u = u} d (no (s , eq)) = no  (∫once d s , trans (∫once-sub _ d s) (cong (∫once (subD (thin-s u) d)) eq))

-- The actual occurs check, deciding whether u appears anywhere in t.
-- We should note that in case we wanted to relax the pattern
-- condition we'd have to be more precise here, and distinguish
-- between different contexts in which u could appear.
mutual
  check : ∀ {Sg G D T S} (u : G ∋ S) (t : Tm Sg G D T) → Dec u OccursIn t
  check u (con c ts) = con c ∙ checks u ts 
  check u (mvar w j) with thick u w
  ...                 | no  (z , eq)      = no  (mvar z j , cong₂ mvar eq (right-id j))
  check u (mvar .u j) | yes (refl , refl) = yes (_ , (j , ([] , refl)))
  check u (var x ts) = var x ∙ checks u ts
  check u (lam t) = lam ∙ check u t
  
  checks : ∀ {Sg G D Ts S} (u : G ∋ S) (ts : Tms Sg G D Ts) → Dec u OccursIn ts
  checks u [] = no ([] , refl)
  checks u (t ∷ ts) with check u t | checks u ts 
  ... | yes x | _      = yes (map-occ (head ts) x)
  ... | _     | yes xs = yes (map-occ (tail t) xs)
  ... | no  x | no  xs = no  (mapΣ₂ _∷_ (cong₂ _∷_) x xs)


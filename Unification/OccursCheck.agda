module Unification.OccursCheck where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum renaming (inj₁ to no; inj₂ to yes)

open import Support.Equality

open import Injections hiding (Dec)

open import Syntax

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

-- "check" decides whether u occurs in t.
-- Note: without the pattern condition we'd have to consider
--       the occurrences' "rigid"-ness. 
mutual
  check : ∀ {Sg G D T S} (u : G ∋ S) (t : Tm Sg G D T) → Dec u OccursIn t
  check u (con c ts) = con c ∙ checks u ts 
  check u (var x ts) = var x ∙ checks u ts
  check u (lam t)    = lam   ∙ check u t
  check u (mvar w j) with thick u w
  ...                 | no  (z , eq) = no  (mvar z j , cong₂ mvar eq (right-id j))
  check u (mvar .u j) | yes refl`    = yes (_ , j , [] , refl)
  
  checks : ∀ {Sg G D Ts S} (u : G ∋ S) (ts : Tms Sg G D Ts) → Dec u OccursIn ts
  checks u []       = no ([] , refl)
  checks u (t ∷ ts) 
   with check u t | checks u ts 
  ... | yes x     | _           = yes (map-occ (head ts) x)
  ... | _         | yes xs      = yes (map-occ (tail t) xs)
  ... | no  x     | no  xs      = no  (mapΣ₂ _∷_ (cong₂ _∷_) x xs)


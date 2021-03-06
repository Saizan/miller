module Unification.Inversion where

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Sum renaming (inj₁ to yes; inj₂ to no)

open import Injections

open import Syntax
open import Unification.Pruning


NotInv : ∀ {Sg G D D' T} (i : Inj D D') (t : Term Sg G D' T) → Set
NotInv {Sg} {G} i t = ∀ {G1} (σ : Sub< false > Sg G G1) -> ¬ ∃ \ s -> renT i s ≡T subT σ t 

map-NI : ∀ {Sg G DI D T D' T'}{i : Inj D' DI}{t : Term Sg G D T} 
         (d : DTm Sg G (DI , T') (D , T)) → NotInv (wrapD-Inj d i) t → NotInv i (wrapD d t)
map-NI lam       notinv σ (lam s     , lam eq)      = notinv σ (s , eq)
map-NI (head ts) notinv σ (s ∷ ss    , eq ∷ eq')    = notinv σ (s , eq)
map-NI (tail t)  notinv σ (s ∷ ss    , eq ∷ eq')    = notinv σ (ss , eq')
map-NI (con c)   notinv σ (con .c ss , con refl eq) = notinv σ (ss , eq)
map-NI (var ._)  notinv σ (var x  ss , var refl eq) = notinv σ (ss , eq)
map-NI (con c)   notinv σ (var x ss  , ())
map-NI (con c)   notinv σ (mvar u j  , ()) 
map-NI (var x)   notinv σ (con c ss  , ())
map-NI (var x)   notinv σ (mvar u j  , ())

NI-var : ∀ {Sg G D D1 Ss B} {i : Inj D D1} {ts : Tms Sg G D1 Ss} {x : D1 ∋ (Ss ->> B)} 
         → ¬ ∃ (λ y → i $ y ≡ x) → NotInv {T = inj₁ _} i (var x ts)
NI-var ¬∃y[iy≡x] σ (con c ts , ())
NI-var ¬∃y[iy≡x] σ (mvar u j , ())
NI-var ¬∃y[iy≡x] σ (var y _ , var iy≡x _) = ¬∃y[iy≡x] (y , iy≡x)

mutual
  invertTm' : ∀ {Sg G Ss D T} (i : Inj Ss D) (t : Tm Sg G D T) →
              AllMV∈ i t → i ⁻¹ t ⊎ NotInv i t
  invertTm' i (con c ts) (con m) = map⊎ (con c) (map-NI (con c)) (invertTm's i ts m)
  invertTm' i (mvar v h) (mvar (k , comm)) = yes (mvar v (k , comm))
  invertTm' i (var x ts) (var m) 
   with invert i x     | invertTm's i ts m 
  ... | yes (y , iy≡x) | yes i⁻¹ts  = yes (var y iy≡x i⁻¹ts)
  ... | _              | no  NI[ts] = no (map-NI (var x) NI[ts])
  ... | no  ¬∃y[iy≡x]  | _          = no (NI-var ¬∃y[iy≡x])
  invertTm' i (lam t) (lam m) = map⊎ lam (map-NI {t = t} lam) (invertTm' (cons i) t m)

  invertTm's : ∀ {Sg G Ss D T} (i : Inj Ss D) (t : Tms Sg G D T) → 
               AllMV∈ i t → i ⁻¹ t ⊎ NotInv i t
  invertTm's i [] m = yes []
  invertTm's i (t ∷ ts) (mt ∷ mts) 
   with invertTm' i t mt | invertTm's i ts mts
  ... | yes p              | yes ps = yes (p ∷ ps) 
  ... | yes p              | no ¬ps = no (map-NI (tail t) ¬ps) 
  ... | no ¬p              | _      = no (map-NI {t = t} (head ts) ¬p)

invertTm : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tm Sg G D T) → (ρ : Sub Sg G G1) → ρ / t ∈ i 
           → (∃ \ s → ren i s ≡ sub ρ t) ⊎ NotInv i (sub ρ t)
invertTm i t ρ m = map⊎ forget (λ x → x) (invertTm' i (sub ρ t) m)


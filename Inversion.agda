module Inversion where

open import Data.Product renaming (map to mapΣ)
open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Sum renaming (map to map⊎)
open import Data.Sum renaming (inj₁ to yes; inj₂ to no)
open import Data.Maybe
open import Category.Monad
import Level
open RawMonad (monad {Level.zero})

open import Injection
open import Lists

open import Syntax
open import OneHoleContext
open import Pruning
open import RenOrn
open import MetaRens
open import Equality

NotInv : ∀ {Sg G D D' T} (i : Inj D D') (t : Term Sg G D' T) → Set
NotInv i t = ∀ {G1}(σ : Sub _ _ G1) -> ¬ ∃ \ s -> renT i s ≡T subT σ t 

map-NI : ∀ {Sg G DI D T D' T' }{i : Inj D' DI}{t : Term Sg G D T} (d : DTm Sg G (DI , T') (D , T) ) → NotInv (∫oInj d i) t → NotInv i (∫once d t)
map-NI lam notinv σ (lam s , lam eq) = notinv σ (s , eq)
map-NI (head ts) notinv σ (t₁ ∷ s , eq ∷ eq₁) = notinv σ (t₁ , eq)
map-NI (tail t₁) notinv σ (t₂ ∷ s , eq ∷ eq₁) = notinv σ (s , eq₁)
map-NI (con c) notinv σ (con .c ts , con refl eq) = notinv σ (ts , eq)
map-NI (con c) notinv σ (fun u j , ())
map-NI (con c) notinv σ (var x ts , ())
map-NI (var x) notinv σ (con c ts , ())
map-NI (var x) notinv σ (fun u j , ())
map-NI (var ._) notinv σ (var x₁ ts , var refl eq) = notinv σ (ts , eq)

mutual
  invertTm' : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tm Sg G D T) → (ρ : Sub Sg G G1) → ρ / t ∈ i
    → RTm i (sub ρ t) ⊎ NotInv i t
  invertTm' i (con c ts) r (con m) = map⊎ (con c) (map-NI (con c)) (invertTm's i ts r m)
  invertTm' i (fun u j) r (fun v h eq k comm) rewrite eq = yes (fun v k comm)
  invertTm' i (var x ts) r (var m) 
   with invert i x   | invertTm's i ts r m 
  ... | yes (y , eq) | yes p₁ = yes (var y eq p₁)
  ... | yes p        | no ¬p  = no (map-NI (var x) ¬p)
  ... | no ¬p        | q      = no (λ σ → λ {(var z ts , var eqz eqts) → ¬p (z , eqz); (con _ _ , ()); (fun _ _ , ())})
  invertTm' i (lam t) r (lam m) = map⊎ lam (map-NI {t = t} lam) (invertTm' (cons i) t r m)

  invertTm's : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tms Sg G D T) → (ρ : Sub Sg G G1) → ρ / t ∈ i 
                → RTms i (subs ρ t) ⊎ NotInv i t
  invertTm's i [] r m = yes []
  invertTm's i (t ∷ ts) r (mt ∷ mts) 
   with invertTm' i t r mt | invertTm's i ts r mts
  ... | yes p              | yes ps = yes (p ∷ ps) 
  ... | yes p              | no ¬ps = no (map-NI (tail t) ¬ps) 
  ... | no ¬p              | _      = no (map-NI {t = t} (head ts) ¬p)

invertTm : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tm Sg G D T) → (ρ : Sub Sg G G1) → ρ / t ∈ i → (∃ \ s → ren i s ≡ sub ρ t) ⊎ (NotInv i t)
invertTm i t ρ m = map⊎ forget (\ x -> x) (invertTm' i t ρ m)


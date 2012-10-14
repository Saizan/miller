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
notInv : ∀ {Sg G D D' T} (i : Inj D D') (t : Term Sg G D' T) → Set
notInv i t = ∀ {G1}(σ : Sub _ _ G1) -> ¬ ∃ \ s -> renT i s ≡T subT σ t 

Inv : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Term Sg G D T) → (ρ : MetaRen G G1) → Set
Inv i t ρ = (∃ \ s → renT i s ≡ subT (toSub ρ) t)

map-occ : ∀ {Sg G DI D T D' T' }{i : Inj D' DI}{t : Term Sg G D T} (d : DTm Sg G (DI , T') (D , T) ) → notInv (∫oInj d i) t → notInv i (∫once d t)
map-occ lam notinv σ (lam s , lam eq) = notinv σ (s , eq)
map-occ (head ts) notinv σ (t₁ ∷ s , eq ∷ eq₁) = notinv σ (t₁ , eq)
map-occ (tail t₁) notinv σ (t₂ ∷ s , eq ∷ eq₁) = notinv σ (s , eq₁)
map-occ (con c) notinv σ (con .c ts , con refl eq) = notinv σ (ts , eq)
map-occ (con c) notinv σ (fun u j , ())
map-occ (con c) notinv σ (var x ts , ())
map-occ (var x) notinv σ (con c ts , ())
map-occ (var x) notinv σ (fun u j , ())
map-occ (var ._) notinv σ (var x₁ ts , var refl eq) = notinv σ (ts , eq)

mutual
  invertTm' : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tm Sg G D T) → (ρ : Sub Sg G G1) → ρ / t ∈ i
    → RTm Sg G1 Ss D i T (sub ρ t) ⊎ notInv i t
  invertTm' i (con c ts) r m = map⊎ (con c) (map-occ (con c)) (invertTm's i ts r m)
  invertTm' i (fun u j) r (H , v , h , eq , k , comm) rewrite eq = yes (fun v k comm)
  invertTm' i (var x ts) r m 
   with invert i x   | invertTm's i ts r m 
  ... | yes (y , eq) | yes p₁ = yes (var y eq p₁)
  ... | yes p        | no ¬p  = no (map-occ (var x) ¬p)
  ... | no ¬p        | q      = no (λ σ → λ {(var z ts , var eqz eqts) → ¬p (z , eqz); (con _ _ , ()); (fun _ _ , ())})
  invertTm' i (lam t) r m = map⊎ lam (map-occ {t = t} lam) (invertTm' (cons i) t r m)

  invertTm's : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tms Sg G D T) → (ρ : Sub Sg G G1) → ρ /s t ∈ i 
                → RTms Sg G1 Ss D i T (subs ρ t) ⊎ notInv i t
  invertTm's i [] r m = yes []
  invertTm's i (t ∷ ts) r (mt , mts) 
   with invertTm' i t r mt | invertTm's i ts r mts
  ... | yes p              | yes ps = yes (p ∷ ps) 
  ... | yes p              | no ¬ps = no (map-occ (tail t) ¬ps) 
  ... | no ¬p              | _      = no (map-occ {t = t} (head ts) ¬p)

invertTm : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tm Sg G D T) → (ρ : Sub Sg G G1) → ρ / t ∈ i → (∃ \ s → ren i s ≡ sub ρ t) ⊎ (notInv i t)
invertTm i t ρ m = Data.Sum.map forget (\ x -> x) (invertTm' i t ρ m)


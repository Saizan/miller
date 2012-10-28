module Equality where
open import Data.Product renaming (map to mapΣ)
open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality renaming (sym to ≡-sym; cong to ≡-cong; trans to ≡-trans)
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Maybe
open import Category.Monad
import Level
open RawMonad (monad {Level.zero})

open import Injection
open import Lists
open import Syntax

data _≡T_ {Sg} {G} {D} : {T : Ty ⊎ List Ty} -> (x y : Term Sg G D T) -> Set where 
  con : ∀ {Ss B}{cx : _ ∋ (Ss ->> B)}{xs}{cy ys} -> cx ≡ cy -> xs ≡T ys -> con cx xs ≡T con cy ys
  var : ∀ {Ss B}{x : _ ∋ (Ss ->> B)}{xs}{y ys} -> x ≡ y -> xs ≡T ys -> var x xs ≡T var y ys
  lam : ∀ {S Ss B}{tx ty : Tm Sg G (S ∷ D) (Ss ->> B)} -> tx ≡T ty -> lam tx ≡T lam ty
  fun : ∀ {Ss B} {ux uy : G ∋ (B <<- Ss)}{i j} -> ux ≡ uy -> i ≡ j -> fun ux i ≡T fun uy j
  [] : Tms.[] ≡T []
  _∷_ : ∀ {S Ss}{tx ty : Tm Sg G D S}{tsx tsy : Tms Sg G D Ss} -> tx ≡T ty -> tsx ≡T tsy -> (Tms._∷_ tx tsx) ≡T (ty ∷ tsy)


con-inj₁ : ∀ {Sg G D B Ss1 Ss2} {x : _ ∋ (Ss1 ->> B)}{y : _ ∋ (Ss2 ->> B)} {xs : Tms Sg G D _}{ys} -> Tm.con x xs ≡T con y ys 
         -> _≡_ {A = ∃ \ T -> Sg ∋ T} (_ , x) (_ , y)
con-inj₁ (con refl eq) = refl 

var-inj₁ : ∀ {Sg G D B Ss1 Ss2} {x : _ ∋ (Ss1 ->> B)}{y : _ ∋ (Ss2 ->> B)} {xs : Tms Sg G D _}{ys} -> Tm.var x xs ≡T var y ys 
         -> _≡_ {A = ∃ \ T -> D ∋ T} (_ , x) (_ , y)
var-inj₁ (var refl eq) = refl 

mutual
  refl-Tm : ∀ {Sg G D T} -> (x : Tm Sg G D T) -> x ≡T x
  refl-Tm (con c ts) = con refl (refl-Tms ts)
  refl-Tm (fun u j) = fun refl refl
  refl-Tm (var x ts) = var refl (refl-Tms ts)
  refl-Tm (lam x) = lam (refl-Tm x)

  refl-Tms : ∀ {Sg G D T} -> (x : Tms Sg G D T) -> x ≡T x
  refl-Tms [] = []
  refl-Tms (t ∷ x) = (refl-Tm t) ∷ (refl-Tms x)

refl-T : ∀ {Sg G D T} -> (x : Term Sg G D T) -> x ≡T x
refl-T {T = inj₁ _} = refl-Tm
refl-T {T = inj₂ _} = refl-Tms

≡-T : ∀ {Sg G D T} -> {x y : Term Sg G D T} -> x ≡ y -> x ≡T y
≡-T {x = x} eq = subst (λ y → _ ≡T y) eq (refl-T x)

T-≡ : ∀ {Sg G D T} -> {x y : Term Sg G D T} -> x ≡T y -> x ≡ y
T-≡ (con refl eq) = ≡-cong (con _) (T-≡ eq)
T-≡ (var refl eq) = ≡-cong (var _) (T-≡ eq)
T-≡ (lam eq) = ≡-cong lam (T-≡ eq)
T-≡ (fun refl refl) = refl
T-≡ [] = refl
T-≡ (eq ∷ eq₁) = cong₂ _∷_ (T-≡ eq) (T-≡ eq₁)

module T where
  sym : ∀ {Sg G D T}{x y : Term Sg G D T} -> x ≡T y -> y ≡T x
  sym {x = x} {y} eq = ≡-T (≡-sym (T-≡ eq))

  cong : ∀ {Sg Sg1 G G1 D D1 T T1}(f : Term Sg G D T -> Term Sg1 G1 D1 T1){x y : Term Sg G D T} -> x ≡T y -> f x ≡T f y
  cong f eq = ≡-T (≡-cong f (T-≡ eq))

  trans : ∀ {Sg G D T}{x y z : Term Sg G D T} -> x ≡T y -> y ≡T z -> x ≡T z
  trans x≡y y≡z = ≡-T (≡-trans (T-≡ x≡y) (T-≡ y≡z))

module Syntax where
open import Data.Product renaming (map to mapΣ)
open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Maybe
open import Category.Monad
import Level
open RawMonad (monad {Level.zero})

open import Injection
open import Lists

postulate
  -- it'd more properly be a module parameter
  Base : Set

data Ty : Set where
  _->>_ : Fwd Ty → Base → Ty

!_ : Base → Ty
!_ B = !> ->> B

infixl 40 _->>_

Ctx : Set
Ctx = Bwd Ty

record MTy : Set where
  constructor _<<-_
  field
    type : Base
    ctx : Ctx

open MTy public
infixr 40 _<<-_

MCtx : Set
MCtx = Bwd MTy

mutual
  data Tm (Sg : Ctx)(G : MCtx)(D : Ctx) : Ty → Set where
    con : {Ss : Fwd Ty}{B : Base} →
          (c : Sg ∋ (Ss ->> B)) → (ts : Tms Sg G D Ss) → Tm Sg G D (! B)
    fun : {S : MTy} ->
          (u : G ∋ S) → (j : Inj (ctx S) D) → Tm Sg G D (! (type S))
    var : forall {Ss B} → 
          (x : D ∋ (Ss ->> B)) → (ts : Tms Sg G D Ss) → Tm Sg G D (! B)
    lam : {S : Ty}{Ss : Fwd Ty}{B : Base} →
          (t : Tm Sg G (D <: S) (Ss ->> B)) → Tm Sg G D (S :> Ss ->> B)

  data Tms (Sg : Ctx)(G : MCtx)(D : Ctx) : Fwd Ty → Set where
    [] : Tms Sg G D !>
    _∷_ : {S : Ty}{Ss : Fwd Ty} →
           (t : Tm Sg G D S) → (ts : Tms Sg G D Ss) → Tms Sg G D (S :> Ss)

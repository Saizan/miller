module Syntax.Type where

open import Data.Sum public using (_⊎_; module _⊎_)
open _⊎_ public
open import Data.Bool public

open import Support.Equality
open ≡-Reasoning
open import Support.List public

open import Injections

postulate
  -- it'd more properly be a module parameter
  Base : Set


-- Ty contains the types of our STLC:
-- t1 → ... → tn → b is represented as [t1, ... , tn] ->> b.
data Ty : Set where
  _->>_ : Fwd Ty → Base → Ty

!_ : Base → Ty
!_ B = !> ->> B

infixl 40 _->>_

-- Typing contexts are snoc-lists of types:
-- lambdas are cuter this way.
Ctx : Set
Ctx = Bwd Ty

-- Meta-variables have their own context, rather than a function type. 
record MTy : Set where
  constructor _<<-_
  field
    type : Base
    ctx : Ctx

open MTy public
infixr 40 _<<-_

-- Meta-Context to type meta-vars.
MCtx : Set
MCtx = Bwd MTy

-- Tm Sg G D T represents lambda terms in beta-short, eta-long normal form with added meta-vars.
-- The pattern condition is ensured by providing meta-vars arguments through injective renamings.
--
-- Sg - context for top level constants i.e. signature
-- G  - context for meta-vars
-- D  - context for object-vars (or just vars)
-- T  - term's type
-- 
-- We use the "spiny" representation where each var/constant is paired with as many arguments as its type requires.
mutual
  data Tm<_> (b : Bool) (Sg : Ctx)(G : MCtx)(D : Ctx) : Ty → Set where
    con : ∀ {Ss B} →
          (c : Sg ∋ (Ss ->> B)) → (ts : Tms< b > Sg G D Ss) → Tm< b > Sg G D (! B)
    mvar : ∀ {Ss B} → 
           (u : G ∋ (B <<- Ss)) → (j : Args b Sg G D Ss) → Tm< b > Sg G D (! B)
    var : ∀ {Ss B} → 
          (x : D ∋ (Ss ->> B)) → (ts : Tms< b > Sg G D Ss) → Tm< b > Sg G D (! B)
    lam : ∀ {S Ss B} →
          (t : Tm< b > Sg G (D <: S) (Ss ->> B)) → Tm< b > Sg G D (S :> Ss ->> B)

  data Tms<_> (b : Bool) (Sg : Ctx)(G : MCtx)(D : Ctx) : Fwd Ty → Set where
    [] : Tms< b > Sg G D !>
    _∷_ : {S : Ty}{Ss : Fwd Ty} →
           (t : Tm< b > Sg G D S) → (ts : Tms< b > Sg G D Ss) → Tms< b > Sg G D (S :> Ss)

  Args : Bool -> (Sg : Ctx)(G : MCtx)(D : Ctx) -> Fwd Ty -> Set
  Args true Sg G D Ss = Inj Ss D
  Args false Sg G D Ss = Tms< false > Sg G D Ss

module Tm = Tm<_>
module Tms = Tms<_>

Tm : (Sg : Ctx)(G : MCtx)(D : Ctx) -> Ty → Set
Tm = Tm< true >

Tms : (Sg : Ctx)(G : MCtx)(D : Ctx) -> Fwd Ty → Set
Tms = Tms< true >

Term<_> : (b : Bool)(Sg : Ctx)(G : MCtx)(DI : Ctx) (TI : Ty ⊎ Fwd Ty) → Set
Term< b > Sg G D (inj₁ T) = Tm< b > Sg G D T 
Term< b > Sg G D (inj₂ Ts) = Tms< b > Sg G D Ts

Term : (Sg : Ctx)(G : MCtx)(DI : Ctx) (TI : Ty ⊎ Fwd Ty) → Set
Term = Term< true >

-- ren makes Tm a functor over Inj
mutual
  ren : ∀ {b Sg G D D0}{T : Ty} → Inj D D0 → Tm< b > Sg G D T → Tm< b > Sg G D0 T
  ren rho (con c ts) = con c (rens rho ts) 
  ren rho (mvar f xs) = mvar f (renArgs rho xs)
  ren rho (var x xs) = var (rho $ x) (rens rho xs)
  ren rho (lam t) = lam (ren (cons rho) t)

  rens : ∀ {b Sg G D D0}{Ts : Fwd Ty} → Inj D D0 → Tms< b > Sg G D Ts → Tms< b > Sg G D0 Ts
  rens rho [] = []
  rens rho (x ∷ ts) = ren rho x ∷ rens rho ts

  renArgs : ∀ {b Sg G D D0}{Ts : Fwd Ty} → Inj D D0 → Args b Sg G D Ts → Args b Sg G D0 Ts
  renArgs {true} rho xs = rho ∘i xs
  renArgs {false} rho xs = rens rho xs

renT : ∀ {T Sg G D1 D2 b} -> (Inj D1 D2) -> Term< b > Sg G D1 T -> Term< b > Sg G D2 T
renT {inj₁ _} i t = ren i t
renT {inj₂ _} i ts = rens i ts

mutual
  ren-∘ : ∀ {b Sg G1 D1 D2 D3 T} {j : Inj D2 D3} {i : Inj D1 D2} (t : Tm< b > Sg G1 D1 T) → ren (j ∘i i) t ≡ ren j (ren i t)
  ren-∘ (con c ts) = cong (con c) (rens-∘ ts)
  ren-∘ (mvar u j₁) = cong (mvar u) (renAs-∘ j₁)
  ren-∘ (var x ts) = cong₂ var (apply-∘ _ _) (rens-∘ ts)
  ren-∘ (lam t) = cong lam (trans (cong (λ k → ren k t) (cons-∘i _ _)) (ren-∘ t))
  
  rens-∘ : ∀ {b Sg G1 D1 D2 D3 T} {j : Inj D2 D3} {i : Inj D1 D2} (t : Tms< b > Sg G1 D1 T) → rens (j ∘i i) t ≡ rens j (rens i t)
  rens-∘ [] = refl
  rens-∘ (t ∷ ts) = cong₂ _∷_ (ren-∘ t) (rens-∘ ts)

  renAs-∘ : ∀ {b Sg G1 D1 D2 D3 T} {j : Inj D2 D3} {i : Inj D1 D2} (t : Args b Sg G1 D1 T) → renArgs (j ∘i i) t ≡ renArgs j (renArgs i t)
  renAs-∘ {true} t = sym assoc-∘i
  renAs-∘ {false} t = rens-∘ t

mutual
  ren-id : ∀ {b Sg G D T} (t : Tm< b > Sg G D T) → ren id-i t ≡ t
  ren-id (con c ts) = cong (con c) (rens-id ts)
  ren-id (mvar u j) = cong (mvar u) (renAs-id j)
  ren-id (var x ts) = cong₂ var (id-i$ x) (rens-id ts)
  ren-id (lam t) = cong lam (trans (cong (λ k → ren k t) cons-id) (ren-id t))
  
  rens-id : ∀ {b Sg G D T} (t : Tms< b > Sg G D T) → rens id-i t ≡ t
  rens-id [] = refl
  rens-id (t ∷ ts) = cong₂ _∷_ (ren-id t) (rens-id ts)

  renAs-id : ∀ {b Sg G D T} (t : Args b Sg G D T) → renArgs id-i t ≡ t
  renAs-id {true} j = left-id j
  renAs-id {false} xs = rens-id xs

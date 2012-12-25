module Syntax where
open import Data.Product renaming (map to mapΣ)
open import Data.Nat hiding (_≤_) renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Sum

open import Injection
open import Data.List.Extras public

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
  data Tm (Sg : Ctx)(G : MCtx)(D : Ctx) : Ty → Set where
    con : ∀ {Ss B} →
          (c : Sg ∋ (Ss ->> B)) → (ts : Tms Sg G D Ss) → Tm Sg G D (! B)
    mvar : ∀ {Ss B} → 
           (u : G ∋ (B <<- Ss)) → (j : Inj Ss D) → Tm Sg G D (! B)
    var : ∀ {Ss B} → 
          (x : D ∋ (Ss ->> B)) → (ts : Tms Sg G D Ss) → Tm Sg G D (! B)
    lam : ∀ {S Ss B} →
          (t : Tm Sg G (D <: S) (Ss ->> B)) → Tm Sg G D (S :> Ss ->> B)

  data Tms (Sg : Ctx)(G : MCtx)(D : Ctx) : Fwd Ty → Set where
    [] : Tms Sg G D !>
    _∷_ : {S : Ty}{Ss : Fwd Ty} →
           (t : Tm Sg G D S) → (ts : Tms Sg G D Ss) → Tms Sg G D (S :> Ss)

Term : (Sg : Ctx)(G : MCtx)(DI : Ctx) (TI : Ty ⊎ Fwd Ty) → Set
Term Sg G D (inj₁ T) = Tm Sg G D T 
Term Sg G D (inj₂ Ts) = Tms Sg G D Ts

-- Injective renamings Inj D D0 do actually rename.
mutual
  ren : ∀ {Sg G D D0}{T : Ty} → Inj D D0 → Tm Sg G D T → Tm Sg G D0 T
  ren rho (con c ts) = con c (rens rho ts) 
  ren rho (mvar f xs) = mvar f (rho ∘i xs)
  ren rho (var x xs) = var (rho $ x) (rens rho xs)
  ren rho (lam t) = lam (ren (cons rho) t)

  rens : ∀ {Sg G D D0}{Ts : Fwd Ty} → Inj D D0 → Tms Sg G D Ts → Tms Sg G D0 Ts
  rens rho [] = []
  rens rho (x ∷ ts) = ren rho x ∷ rens rho ts

renT : ∀ {T Sg G D1 D2} -> (Inj D1 D2) -> Term Sg G D1 T -> Term Sg G D2 T
renT {inj₁ _} i t = ren i t
renT {inj₂ _} i ts = rens i ts

-- The type of meta-substitutions, the only ones we care about.
Sub : Ctx → MCtx → MCtx → Set
Sub Sg G1 G2 = ∀ S → G1 ∋ S → Tm Sg G2 (ctx S) (! type S)

_≡s_ : ∀ {Sg G G1}(s s₁ : Sub Sg G G1) -> Set
s ≡s s₁ = ∀ S u -> s S u ≡ s₁ S u
 
thin-s : ∀ {Sg}{G T} -> (u : G ∋ T) -> Sub Sg (G - u) G
thin-s u = \ S v -> mvar (thin u S v) id-i

mutual
  sub : ∀ {Sg G1 G2 D T} → Sub Sg G1 G2 → Tm Sg G1 D T → Tm Sg G2 D T
  sub s (con x x₁) = con x (subs s x₁)
  sub s (mvar u x₁) = ren x₁ (s _ u)
  sub s (var x xs) = var x (subs s xs)
  sub s (lam t) = lam (sub s t)

  subs : ∀ {Sg G1 G2 D Ss} → Sub Sg G1 G2 → Tms Sg G1 D Ss → Tms Sg G2 D Ss
  subs s [] = []
  subs s (x ∷ ts) = sub s x ∷ subs s ts

id-s : ∀ {Sg G} -> Sub Sg G G
id-s = \ S x -> mvar x id-i

_∘s_ : ∀ {Sg G1 G2 G3} -> Sub Sg G2 G3 -> Sub Sg G1 G2 -> Sub Sg G1 G3
r ∘s s = λ S x → sub r (s S x)

-- f ≤ g iff g can be specialized to f 
_≤_ : ∀ {Sg D C1 C2} -> Sub Sg D C1 -> Sub Sg D C2 -> Set
f ≤ g = ∃ \ r -> ∀ S u -> f S u ≡ (r ∘s g) S u

subT : ∀ {T Sg G1 G2 D} -> (Sub Sg G1 G2) -> Term Sg G1 D T -> Term Sg G2 D T
subT {inj₁ _} i t = sub i t
subT {inj₂ _} i ts = subs i ts

-- Tm is bifunctorial over renamings and substitutions, if one is categorically minded
mutual
  ren-∘ : ∀ {Sg G1 D1 D2 D3 T} {j : Inj D2 D3} {i : Inj D1 D2} (t : Tm Sg G1 D1 T) → ren (j ∘i i) t ≡ ren j (ren i t)
  ren-∘ (con c ts) = cong (con c) (rens-∘ ts)
  ren-∘ (mvar u j₁) = cong (mvar u) (sym assoc-∘i)
  ren-∘ (var x ts) = cong₂ var (apply-∘ _ _) (rens-∘ ts)
  ren-∘ (lam t) = cong lam (trans (cong (λ k → ren k t) (cons-∘i _ _)) (ren-∘ t))
  
  rens-∘ : ∀ {Sg G1 D1 D2 D3 T} {j : Inj D2 D3} {i : Inj D1 D2} (t : Tms Sg G1 D1 T) → rens (j ∘i i) t ≡ rens j (rens i t)
  rens-∘ [] = refl
  rens-∘ (t ∷ ts) = cong₂ _∷_ (ren-∘ t) (rens-∘ ts)

mutual
  ren-id : ∀ {Sg G D T} (t : Tm Sg G D T) → ren id-i t ≡ t
  ren-id (con c ts) = cong (con c) (rens-id ts)
  ren-id (mvar u j) = cong (mvar u) (left-id j)
  ren-id (var x ts) = cong₂ var (id-i$ x) (rens-id ts)
  ren-id (lam t) = cong lam (trans (cong (λ k → ren k t) cons-id) (ren-id t))
  
  rens-id : ∀ {Sg G D T} (t : Tms Sg G D T) → rens id-i t ≡ t
  rens-id [] = refl
  rens-id (t ∷ ts) = cong₂ _∷_ (ren-id t) (rens-id ts)

mutual
  sub-nat : ∀ {Sg G1 G2 D1 D2 T} {f : Sub Sg G1 G2} {i : Inj D1 D2} (t : Tm Sg G1 D1 T) → sub f (ren i t) ≡ ren i (sub f t)
  sub-nat (con c ts) = cong (con c) (sub-nats ts)
  sub-nat (mvar u j) = ren-∘ _
  sub-nat (var x ts) = cong (var _) (sub-nats ts)
  sub-nat (lam t) = cong lam (sub-nat t)
  
  sub-nats : ∀ {Sg G1 G2 D1 D2 T} {f : Sub Sg G1 G2} {i : Inj D1 D2} (t : Tms Sg G1 D1 T) → subs f (rens i t) ≡ rens i (subs f t)
  sub-nats [] = refl
  sub-nats (t ∷ ts) = cong₂ _∷_ (sub-nat t) (sub-nats ts)

mutual
  sub-∘ : ∀ {Sg G1 G2 G3 D T} {f : Sub Sg G2 G3}{g} (t : Tm Sg G1 D T) → sub f (sub g t) ≡ sub (f ∘s g) t
  sub-∘ (con c ts) = cong (con c) (subs-∘ ts)
  sub-∘ {g = g} (mvar u j) = sub-nat (g _ u)
  sub-∘ (var x ts) = cong (var x) (subs-∘ ts)
  sub-∘ (lam t) = cong lam (sub-∘ t)
  
  subs-∘ : ∀ {Sg G1 G2 G3 D T} {f : Sub Sg G2 G3}{g} (t : Tms Sg G1 D T) → subs f (subs g t) ≡ subs (f ∘s g) t
  subs-∘ [] = refl
  subs-∘ (t ∷ t₁) = cong₂ _∷_ (sub-∘ t) (subs-∘ t₁)

mutual
  sub-id : ∀ {Sg G D T} (t : Tm Sg G D T) → sub id-s t ≡ t
  sub-id (con c ts) = cong (con c) (subs-id ts)
  sub-id (mvar u j) = cong (mvar u) (right-id j)
  sub-id (var x ts) = cong (var x) (subs-id ts)
  sub-id (lam t) = cong lam (sub-id t)
  
  subs-id : ∀ {Sg G D T} (t : Tms Sg G D T) → subs id-s t ≡ t
  subs-id [] = refl
  subs-id (t ∷ ts) = cong₂ _∷_ (sub-id t) (subs-id ts)


-- Substitution respects pointwise equality.
mutual
  sub-ext : ∀ {Sg G1 G2 D T} {f g : Sub Sg G1 G2} → f ≡s g → (t : Tm Sg G1 D T) → sub f t ≡ sub g t
  sub-ext q (con c ts) = cong (con c) (subs-ext q ts)
  sub-ext q (mvar u j) = cong (ren j) (q _ u)
  sub-ext q (var x ts) = cong (var x) (subs-ext q ts)
  sub-ext q (lam t) = cong lam (sub-ext q t)

  subs-ext : ∀ {Sg G1 G2 D T} {f g : Sub Sg G1 G2} → f ≡s g → (t : Tms Sg G1 D T) → subs f t ≡ subs g t
  subs-ext q [] = refl
  subs-ext q (t ∷ ts) = cong₂ _∷_ (sub-ext q t) (subs-ext q ts)

subT-id : ∀ {Sg G D T} (t : Term Sg G D T) → subT id-s t ≡ t
subT-id {Sg} {G} {D} {inj₁ x} t = sub-id t
subT-id {Sg} {G} {D} {inj₂ y} t = subs-id t

subT-ext : ∀ {Sg G1 G2 D T} {f g : Sub Sg G1 G2} → f ≡s g → (t : Term Sg G1 D T) → subT f t ≡ subT g t
subT-ext {Sg} {G1} {G2} {D} {inj₁ x} eq t = sub-ext eq t
subT-ext {Sg} {G1} {G2} {D} {inj₂ y} eq t = subs-ext eq t

subT-∘ : ∀ {Sg G1 G2 G3 D T} {f : Sub Sg G2 G3}{g} (t : Term Sg G1 D T) → subT f (subT g t) ≡ subT (f ∘s g) t
subT-∘ {Sg} {G1} {G2} {G3} {D} {inj₁ x} t = sub-∘ t
subT-∘ {Sg} {G1} {G2} {G3} {D} {inj₂ y} t = subs-∘ t

module ShapeOrn where

open import Data.Sum
open import Data.Product renaming (map to mapΣ)
mapΣ₂ : ∀ {a b c p q r}
        {A : Set a} {B : Set b}{C : Set c} {P : A → Set p} {Q : B → Set q} {R : C -> Set r}→
      (f : A -> B -> C) → (∀ {x y} → P x → Q y -> R (f x y)) →
      Σ A P → Σ B Q -> Σ C R
mapΣ₂ f g (x₀ , y₀) (x , y) = (f x₀ x , g y₀ y)

open import Relation.Binary.PropositionalEquality

open import Injection
open import Lists

open import Syntax hiding 
  (ren; ren-id; ren-∘; rens; rens-id; 
  rens-∘; renT; sub; sub-id; sub-∘; 
  sub-ext; subT; subs; subs-id; 
  subs-∘; subs-ext; sub-nat; sub-nats; 
  _∘s_)

mutual
  data Shape : Set where
    con : (ts : Shapes) → Shape
    fun : Shape
    var : (ts : Shapes) → Shape
    lam : (t : Shape) → Shape

  data Shapes : Set where
    [] : Shapes
    _∷_ : (t : Shape) → (ts : Shapes) → Shapes

mutual
  shape : ∀ {Sg G D T} -> Tm Sg G D T -> Shape
  shape (con c ts) = (con (shapes ts))
  shape (fun u j) = fun
  shape (var x ts) = var (shapes ts)
  shape (lam t) = lam (shape t)

  shapes : ∀ {Sg G D T} -> Tms Sg G D T -> Shapes
  shapes [] = []
  shapes (t ∷ ts) = shape t ∷ shapes ts

mutual
  data STm (Sg : Ctx)(G : MCtx)(D : Ctx) : Ty → Shape -> Set where
    con : {Ss : Fwd Ty}{B : Base} {ss : Shapes} →
          (c : Sg ∋ (Ss ->> B)) → (ts : STms Sg G D Ss ss) → STm Sg G D (! B) (con ss)
    fun : ∀ {Ss B} →
          (u : G ∋ (B <<- Ss)) → (j : Inj Ss D) → STm Sg G D (! B) fun
    var : forall {Ss B ss} → 
          (x : D ∋ (Ss ->> B)) → (ts : STms Sg G D Ss ss) → STm Sg G D (! B) (var ss)
    lam : {S : Ty}{Ss : Fwd Ty}{B : Base}{s : Shape} →
          (t : STm Sg G (D <: S) (Ss ->> B) s) → STm Sg G D (S :> Ss ->> B) (lam s)

  data STms (Sg : Ctx)(G : MCtx)(D : Ctx) : Fwd Ty → Shapes -> Set where
    [] : STms Sg G D !> []
    _∷_ : {S : Ty}{Ss : Fwd Ty}{s : _}{ss : _} →
           (t : STm Sg G D S s) → (ts : STms Sg G D Ss ss) → STms Sg G D (S :> Ss) (s ∷ ss)

-- could reduce boilerplate with zippers?
mutual 
  forget : ∀ {Sg G D T s} -> STm Sg G D T s -> ∃ \ (t : Tm Sg G D T) -> shape t ≡ s
  forget (con c ts) = mapΣ (con c) (cong con) (forgets ts)
  forget (fun u j) = fun u j , refl
  forget (var x ts) = mapΣ (var x) (cong var) (forgets ts)
  forget (lam t) = mapΣ lam (cong lam) (forget t)

  forgets : ∀ {Sg G D T s} -> STms Sg G D T s -> ∃ \ (t : Tms Sg G D T) -> shapes t ≡ s
  forgets [] = [] , refl
  forgets (t ∷ ts) = mapΣ₂ _∷_ (cong₂ _∷_) (forget t) (forgets ts)


mutual
  remember :  ∀ {Sg G D T} -> (t : Tm Sg G D T) -> ∃ \ (st : STm Sg G D T (shape t)) -> proj₁ (forget st) ≡ t
  remember (con c ts) = mapΣ (con c) (cong (con c)) (remembers ts)
  remember (fun u j) = (fun u j) , refl
  remember (var x ts) = mapΣ (var x) (cong (var x)) (remembers ts)
  remember (lam t) = mapΣ lam (cong lam) (remember t)

  remembers :  ∀ {Sg G D T} -> (t : Tms Sg G D T) -> ∃ \ (st : STms Sg G D T (shapes t)) -> proj₁ (forgets st) ≡ t
  remembers [] = [] , refl
  remembers (t ∷ ts) = mapΣ₂ _∷_ (cong₂ _∷_) (remember t) (remembers ts)

mutual
  iren : ∀ {Sg G D D0}{T : Ty}{s} → Inj D D0 → STm Sg G D T s → STm Sg G D0 T s
  iren rho (con c ts) = con c (irens rho ts) 
  iren rho (fun f xs) = fun f (rho ∘i xs)
  iren rho (var x xs) = var (rho $ x) (irens rho xs)
  iren rho (lam t) = lam (iren (cons rho) t)

  irens : ∀ {Sg G D D0}{Ts : Fwd Ty}{ss} → Inj D D0 → STms Sg G D Ts ss → STms Sg G D0 Ts ss
  irens rho [] = []
  irens rho (x ∷ ts) = iren rho x ∷ irens rho ts

mutual
  ren : ∀ {Sg G D D0}{T : Ty} → Inj D D0 → Tm Sg G D T → Tm Sg G D0 T
  ren i t = proj₁ (forget (iren i (proj₁ (remember t))))
  rens : ∀ {Sg G D D0}{Ts : Fwd Ty} → Inj D D0 → Tms Sg G D Ts → Tms Sg G D0 Ts
  rens i ts = proj₁ (forgets (irens i (proj₁ (remembers ts))))

renT : ∀ {T Sg G D1 D2} -> (Inj D1 D2) -> Term Sg G D1 T -> Term Sg G D2 T
renT {inj₁ _} i t = ren i t
renT {inj₂ _} i ts = rens i ts

mutual
  ren-∘ : ∀ {Sg G1 D1 D2 D3 T} {j : Inj D2 D3} {i : Inj D1 D2} (t : Tm Sg G1 D1 T) → ren (j ∘i i) t ≡ ren j (ren i t)
  ren-∘ (con c ts) = cong (con c) (rens-∘ ts)
  ren-∘ (fun u j₁) = cong (fun u) (sym assoc-∘i)
  ren-∘ (var x ts) = cong₂ var (apply-∘ _ _) (rens-∘ ts)
  ren-∘ (lam t) = cong lam (trans (cong (λ k → ren k t) (cons-∘i _ _)) (ren-∘ t))
  
  rens-∘ : ∀ {Sg G1 D1 D2 D3 T} {j : Inj D2 D3} {i : Inj D1 D2} (t : Tms Sg G1 D1 T) → rens (j ∘i i) t ≡ rens j (rens i t)
  rens-∘ [] = refl
  rens-∘ (t ∷ ts) = cong₂ _∷_ (ren-∘ t) (rens-∘ ts)

mutual
  ren-id : ∀ {Sg G D T} (t : Tm Sg G D T) → ren id-i t ≡ t
  ren-id (con c ts) = cong (con c) (rens-id ts)
  ren-id (fun u j) = cong (fun u) (left-id j)
  ren-id (var x ts) = cong₂ var (id-i$ x) (rens-id ts)
  ren-id (lam t) = cong lam (trans (cong (λ k → ren k t) cons-id) (ren-id t))
  
  rens-id : ∀ {Sg G D T} (t : Tms Sg G D T) → rens id-i t ≡ t
  rens-id [] = refl
  rens-id (t ∷ ts) = cong₂ _∷_ (ren-id t) (rens-id ts)

mutual
  subShape : ∀ {Sg G1 G2 D T} -> Sub Sg G1 G2 → Tm Sg G1 D T -> Shape
  subShape s (con c ts) = con (subShapes s ts)
  subShape s (fun u j) = shape (s _ u)
  subShape s (var x ts) = var (subShapes s ts)
  subShape s (lam t) = lam (subShape s t)

  subShapes : ∀ {Sg G1 G2 D T} -> Sub Sg G1 G2 → Tms Sg G1 D T -> Shapes
  subShapes s [] = []
  subShapes s (t ∷ ts) = (subShape s t) ∷ (subShapes s ts)

mutual
  isub : ∀ {Sg G1 G2 D T} → (σ : Sub Sg G1 G2) → (t : Tm Sg G1 D T) → STm Sg G2 D T (subShape σ t)
  isub s (con x x₁) = con x (isubs s x₁)
  isub s (fun u x₁) = iren x₁ (proj₁ (remember (s _ u)))
  isub s (var x xs) = var x (isubs s xs)
  isub s (lam t) = lam (isub s t)

  isubs : ∀ {Sg G1 G2 D Ss} → (σ : Sub Sg G1 G2) → (ts : Tms Sg G1 D Ss) → STms Sg G2 D Ss (subShapes σ ts)
  isubs s [] = []
  isubs s (x ∷ ts) = isub s x ∷ isubs s ts

mutual
  sub : ∀ {Sg G1 G2 D T} → Sub Sg G1 G2 → Tm Sg G1 D T → Tm Sg G2 D T
  sub s t = proj₁ (forget (isub s t))
  subs : ∀ {Sg G1 G2 D Ss} → Sub Sg G1 G2 → Tms Sg G1 D Ss → Tms Sg G2 D Ss
  subs s ts = proj₁ (forgets (isubs s ts))

_∘s_ : ∀ {Sg G1 G2 G3} -> Sub Sg G2 G3 -> Sub Sg G1 G2 -> Sub Sg G1 G3
r ∘s s = λ S x → sub r (s S x)

mutual
  sub-nat : ∀ {Sg G1 G2 D1 D2 T} {f : Sub Sg G1 G2} {i : Inj D1 D2} (t : Tm Sg G1 D1 T) → sub f (ren i t) ≡ ren i (sub f t)
  sub-nat (con c ts) = cong (con c) (sub-nats ts)
  sub-nat {f = f} (fun u j) = ren-∘ (f _ u)
  sub-nat (var x ts) = cong (var _) (sub-nats ts)
  sub-nat (lam t) = cong lam (sub-nat t)
  
  sub-nats : ∀ {Sg G1 G2 D1 D2 T} {f : Sub Sg G1 G2} {i : Inj D1 D2} (t : Tms Sg G1 D1 T) → subs f (rens i t) ≡ rens i (subs f t)
  sub-nats [] = refl
  sub-nats (t ∷ ts) = cong₂ _∷_ (sub-nat t) (sub-nats ts)

mutual
  sub-∘ : ∀ {Sg G1 G2 G3 D T} {f : Sub Sg G2 G3}{g} (t : Tm Sg G1 D T) → sub f (sub g t) ≡ sub (f ∘s g) t
  sub-∘ (con c ts) = cong (con c) (subs-∘ ts)
  sub-∘ {g = g} (fun u j) = sub-nat (g _ u)
  sub-∘ (var x ts) = cong (var x) (subs-∘ ts)
  sub-∘ (lam t) = cong lam (sub-∘ t)
  
  subs-∘ : ∀ {Sg G1 G2 G3 D T} {f : Sub Sg G2 G3}{g} (t : Tms Sg G1 D T) → subs f (subs g t) ≡ subs (f ∘s g) t
  subs-∘ [] = refl
  subs-∘ (t ∷ t₁) = cong₂ _∷_ (sub-∘ t) (subs-∘ t₁)

mutual
  sub-id : ∀ {Sg G D T} (t : Tm Sg G D T) → sub (\ S u -> fun u id-i) t ≡ t
  sub-id (con c ts) = cong (con c) (subs-id ts)
  sub-id (fun u j) = cong (fun u) (right-id j)
  sub-id (var x ts) = cong (var x) (subs-id ts)
  sub-id (lam t) = cong lam (sub-id t)
  
  subs-id : ∀ {Sg G D T} (t : Tms Sg G D T) → subs (\ S u -> fun u id-i) t ≡ t
  subs-id [] = refl
  subs-id (t ∷ ts) = cong₂ _∷_ (sub-id t) (subs-id ts)

mutual
  sub-ext : ∀ {Sg G1 G2 D T} {f g : Sub Sg G1 G2} → (∀ S x → f S x ≡ g S x) → (t : Tm Sg G1 D T) → sub f t ≡ sub g t
  sub-ext q (con c ts) = cong (con c) (subs-ext q ts)
  sub-ext q (fun u j) = cong (ren j) (q _ u)
  sub-ext q (var x ts) = cong (var x) (subs-ext q ts)
  sub-ext q (lam t) = cong lam (sub-ext q t)

  subs-ext : ∀ {Sg G1 G2 D T} {f g : Sub Sg G1 G2} → (∀ S x → f S x ≡ g S x) → (t : Tms Sg G1 D T) → subs f t ≡ subs g t
  subs-ext q [] = refl
  subs-ext q (t ∷ ts) = cong₂ _∷_ (sub-ext q t) (subs-ext q ts)

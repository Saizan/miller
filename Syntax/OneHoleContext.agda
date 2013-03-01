module Syntax.OneHoleContext where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Sum

open import Support.Product

open import Injections

open import Syntax.Type
open import Syntax.Sub
open import Syntax.Equality


-- Given an inductive type T = F T we can build the type of its one
-- hole contexts as List (F' T) where F' is the derivative of F,
-- i.e. the elements of F' x are the same as F x with one occurrence
-- of x removed.  The same holds for indexed types when we lift the
-- construction pointwise.
--
-- In our case T = Term Sg G and we define:
--    DTm Sg G      as F' T, 
--    Context Sg G  as List (F' T).

Index = Ctx × (Ty ⊎ List Ty)

data DTm<_> (b : Bool) (Sg : Ctx)(G : MCtx) : Index -> Index → Set where
  lam : ∀ {D S Ss B} → DTm< b > Sg G (D , inj₁ (S :> Ss ->> B)) (D <: S , inj₁ (Ss ->> B))
  head : ∀ {D S Ss} → (ts : Tms< b > Sg G D Ss) → DTm< b > Sg G (D , inj₂ (S :> Ss)) (D , inj₁ S)
  tail : ∀ {D S Ss} → (t : Tm< b > Sg G D S) → DTm< b > Sg G (D , inj₂ (S :> Ss)) (D , inj₂ Ss)
  con : ∀ {D Ss B} → (c : Sg ∋ (Ss ->> B)) → DTm< b > Sg G (D , inj₁ (! B)) (D , inj₂ Ss)
  var : ∀ {D Ss B} → (x : D ∋ (Ss ->> B)) → DTm< b > Sg G (D , inj₁ (! B)) (D , inj₂ Ss)

DTm : (Sg : Ctx)(G : MCtx) -> Index -> Index → Set
DTm = DTm< true >

data IList {I : Set}(T : I → I → Set) (i : I) : (j : I) → Set where
  [] : IList T i i
  _∷_ : ∀ {k j} → T i k → (xs : IList T k j) → IList T i j

Context<_> : (b : Bool) (Sg : Ctx)(G : MCtx) → Index -> Index → Set
Context< b > Sg G = IList (DTm< b > Sg G)

Context : (Sg : Ctx)(G : MCtx) → Index -> Index → Set
Context = Context< true >

-- Given a Context and an index-compatible filling we can rebuild a Term
wrapD : ∀ {Sg G DI TI DO TO b} → DTm< b > Sg G (DI , TI) (DO , TO) → Term< b > Sg G DO TO → Term< b > Sg G DI TI
wrapD lam       t = lam t
wrapD (head ts) t = t ∷ ts
wrapD (tail t) ts = t ∷ ts
wrapD (con c)  ts = con c ts
wrapD (var x)  ts = var x ts

wrap : ∀ {Sg G I O b} → Context< b > Sg G I O → Term< b > Sg G (proj₁ O) (proj₂ O) → Term< b > Sg G (proj₁ I) (proj₂ I)
wrap []      t = t
wrap (d ∷ c) t = wrapD d (wrap c t)


-- To move a renaming past a λ we need to handle the extra variable,
-- wrapoInj takes care of the induced action of a DTm on Inj.
wrapD-Ctx : ∀ {Sg G I1 I2 b} -> DTm< b > Sg G I1 I2 -> Ctx -> Ctx
wrapD-Ctx (lam {S = S}) D = S ∷ D
wrapD-Ctx _             D = D

wrapD-Inj : ∀ {Sg G DI I1 I2 b} -> (d : DTm< b > Sg G I1 I2) -> Inj DI (proj₁ I1) -> Inj (wrapD-Ctx d DI) (proj₁ I2)
wrapD-Inj lam       i = cons i
wrapD-Inj (head ts) i = i
wrapD-Inj (tail t)  i = i
wrapD-Inj (con c)   i = i
wrapD-Inj (var x)   i = i


subD : ∀ {Sg G1 G2 TI TO b1 b2} -> Sub< b1 > Sg G1 G2 -> DTm< b2 > Sg G1 TI TO -> DTm< b2 ∧ b1 > Sg G2 TI TO
subD s lam       = lam
subD s (head ts) = head (subs s ts)
subD s (tail t)  = tail (sub s t)
subD s (con c)   = con c
subD s (var x)   = var x


subC : ∀ {Sg G1 G2 TI TO b1 b2} -> (Sub< b1 > Sg G1 G2) -> Context< b2 > Sg G1 TI TO -> Context< b2 ∧ b1 > Sg G2 TI TO
subC s []      = []
subC s (x ∷ c) = subD s x ∷ (subC s c)

wrapD-sub : ∀ {Sg G1 G2 TI TO b1 b2} -> (s : Sub< b1 > Sg G1 G2) -> (d : DTm< b2 > Sg G1 TI TO) -> 
            ∀ t -> subT s (wrapD d t) ≡ wrapD (subD s d) (subT s t)
wrapD-sub s lam       t = refl
wrapD-sub s (head ts) t = refl
wrapD-sub s (tail t) ts = refl
wrapD-sub s (con c)  ts = refl
wrapD-sub s (var x)  ts = refl

wrap-sub : ∀ {Sg G1 G2 TI TO b1 b2} -> (s : Sub< b1 > Sg G1 G2) -> (c : Context< b2 > Sg G1 TI TO) -> 
           ∀ t -> subT s (wrap c t) ≡ wrap (subC s c) (subT s t)
wrap-sub s []      t = refl
wrap-sub s (d ∷ c) t = trans (wrapD-sub s d _) (cong (wrapD (subD s d)) (wrap-sub s c t))


cong-wrapD : ∀ {Sg G1 G2 TI TO b1 b2} -> {s : Sub< b1 > Sg G1 G2} -> (d : DTm< b2 > Sg G1 TI TO) -> 
             ∀ {x y} -> subT s x ≡T subT s y -> subT s (wrapD d x) ≡T subT s (wrapD d y)
cong-wrapD {s = s} d {x} {y} eq = ≡-T 
   (begin
      subT s (wrapD d x)          ≡⟨ wrapD-sub s d x ⟩
      wrapD (subD s d) (subT s x) ≡⟨ cong (wrapD (subD s d)) (T-≡ eq) ⟩
      wrapD (subD s d) (subT s y) ≡⟨ sym (wrapD-sub s d y) ⟩
      subT s (wrapD d y)          ∎)

wrapD-inj : ∀ {Sg G1 TI TO b} -> (d : DTm< b > Sg G1 TI TO) -> ∀ {x y} -> wrapD d x ≡ wrapD d y -> x ≡ y
wrapD-inj lam       refl = refl
wrapD-inj (head ts) refl = refl
wrapD-inj (tail t)  refl = refl
wrapD-inj (con c)   refl = refl
wrapD-inj (var x)   refl = refl

inv-wrapD : ∀ {Sg G1 G2 TI TO b1 b2} -> {s : Sub< b1 > Sg G1 G2} -> (d : DTm< b2 > Sg G1 TI TO) -> 
            ∀ {x y} -> subT s (wrapD d x) ≡T subT s (wrapD d y) -> subT s x ≡T subT s y
inv-wrapD {s = s} d {x} {y} eq = ≡-T (wrapD-inj (subD s d)  
   (begin
      wrapD (subD s d) (subT s x) ≡⟨ sym (wrapD-sub s d x) ⟩
      subT s (wrapD d x)          ≡⟨ T-≡ eq ⟩
      subT s (wrapD d y)          ≡⟨ wrapD-sub s d y ⟩ 
      wrapD (subD s d) (subT s y) ∎))

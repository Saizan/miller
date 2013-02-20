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
Context< b > Sg G = IList (\ i j → DTm< b > Sg G i j)

Context : (Sg : Ctx)(G : MCtx) → Index -> Index → Set
Context = Context< true >

-- Given a Context and an index-compatible filling we can rebuild a Term
∫once : ∀ {Sg G DI TI DO TO b} → DTm< b > Sg G (DI , TI) (DO , TO) → Term< b > Sg G DO TO → Term< b > Sg G DI TI
∫once lam t = lam t
∫once (head ts) t = t ∷ ts
∫once (tail t) ts = t ∷ ts
∫once (con c) ts = con c ts
∫once (var x) ts = var x ts

∫ : ∀ {Sg G I O b} → Context< b > Sg G I O → Term< b > Sg G (proj₁ O) (proj₂ O) → Term< b > Sg G (proj₁ I) (proj₂ I)
∫ [] t = t
∫ (x ∷ c) t = ∫once x (∫ c t)


-- To move a renaming past a λ we need to handle the extra variable,
-- ∫oInj takes care of the induced action of a DTm on Inj.
∫oCtx : ∀ {Sg G I1 I2 b} -> DTm< b > Sg G I1 I2 -> Ctx -> Ctx
∫oCtx (lam {S = S}) D = S ∷ D
∫oCtx _ D = D

∫oInj : ∀ {Sg G DI I1 I2 b} -> (d : DTm< b > Sg G I1 I2) -> Inj DI (proj₁ I1) -> Inj (∫oCtx d DI) (proj₁ I2)
∫oInj lam i = cons i
∫oInj (head ts) i = i
∫oInj (tail t) i = i
∫oInj (con c) i = i
∫oInj (var x) i = i


subD : ∀ {Sg G1 G2 TI TO b1 b2} -> (Sub< b1 > Sg G1 G2) -> DTm< b2 > Sg G1 TI TO -> DTm< b2 ∧ b1 > Sg G2 TI TO
subD s lam = lam
subD s (head ts) = head (subs s ts)
subD s (tail t) = tail (sub s t)
subD s (con c) = con c
subD s (var x) = var x


subC : ∀ {Sg G1 G2 TI TO b1 b2} -> (Sub< b1 > Sg G1 G2) -> Context< b2 > Sg G1 TI TO -> Context< b2 ∧ b1 > Sg G2 TI TO
subC s [] = []
subC s (x ∷ c) = subD s x ∷ (subC s c)

∫once-sub : ∀ {Sg G1 G2 TI TO b1 b2} -> (s : Sub< b1 > Sg G1 G2) -> (d : DTm< b2 > Sg G1 TI TO) -> 
            ∀ t -> subT s (∫once d t) ≡ ∫once (subD s d) (subT s t)
∫once-sub s lam t = refl
∫once-sub s (head ts) t = refl
∫once-sub s (tail t) t₁ = refl
∫once-sub s (con c) t = refl
∫once-sub s (var x) t = refl

∫-sub : ∀ {Sg G1 G2 TI TO b1 b2} -> (s : Sub< b1 > Sg G1 G2) -> (c : Context< b2 > Sg G1 TI TO) -> 
        ∀ t -> subT s (∫ c t) ≡ ∫ (subC s c) (subT s t)
∫-sub s [] t = refl
∫-sub s (x ∷ c) t = trans (∫once-sub s x _) (cong (∫once (subD s x)) (∫-sub s c t))


cong-∫once : ∀ {Sg G1 G2 TI TO b1 b2} -> {s : Sub< b1 > Sg G1 G2} -> (d : DTm< b2 > Sg G1 TI TO) -> 
             ∀ {x y} -> subT s x ≡T subT s y -> subT s (∫once d x) ≡T subT s (∫once d y)
cong-∫once {s = s} d {x} {y} eq = ≡-T 
   (begin
      subT s (∫once d x)          ≡⟨ ∫once-sub s d x ⟩
      ∫once (subD s d) (subT s x) ≡⟨ cong (∫once (subD s d)) (T-≡ eq) ⟩
      ∫once (subD s d) (subT s y) ≡⟨ sym (∫once-sub s d y) ⟩
      subT s (∫once d y)          ∎)

∫once-inj : ∀ {Sg G1 TI TO b} -> (d : DTm< b > Sg G1 TI TO) -> ∀ {x y} -> ∫once d x ≡ ∫once d y -> x ≡ y
∫once-inj lam refl = refl
∫once-inj (head ts) refl = refl
∫once-inj (tail t) refl = refl
∫once-inj (con c) refl = refl
∫once-inj (var x) refl = refl

inv-∫once : ∀ {Sg G1 G2 TI TO b1 b2} -> {s : Sub< b1 > Sg G1 G2} -> (d : DTm< b2 > Sg G1 TI TO) -> 
            ∀ {x y} -> subT s (∫once d x) ≡T subT s (∫once d y) -> subT s x ≡T subT s y
inv-∫once {s = s} d {x} {y} eq = ≡-T (∫once-inj (subD s d)  
   (begin
      ∫once (subD s d) (subT s x) ≡⟨ sym (∫once-sub s d x) ⟩
      subT s (∫once d x)          ≡⟨ T-≡ eq ⟩
      subT s (∫once d y)          ≡⟨ ∫once-sub s d y ⟩ 
      ∫once (subD s d) (subT s y) ∎))

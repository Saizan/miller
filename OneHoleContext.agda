module OneHoleContext where

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

open import Syntax
open import Equality

Index = Ctx × (Ty ⊎ List Ty)

data DTm (Sg : Ctx)(G : MCtx) : Index -> Index → Set where
  lam : ∀ {D S Ss B} → DTm Sg G (D , inj₁ (S :> Ss ->> B)) (D <: S , inj₁ (Ss ->> B))
  head : ∀ {D S Ss} → (ts : Tms Sg G D Ss) → DTm Sg G (D , inj₂ (S :> Ss)) (D , inj₁ S)
  tail : ∀ {D S Ss} → (t : Tm Sg G D S) → DTm Sg G (D , inj₂ (S :> Ss)) (D , inj₂ Ss)
  con : ∀ {D Ss B} → (c : Sg ∋ (Ss ->> B)) → DTm Sg G (D , inj₁ (! B)) (D , inj₂ Ss)
  var : ∀ {D Ss B} → (x : D ∋ (Ss ->> B)) → DTm Sg G (D , inj₁ (! B)) (D , inj₂ Ss)

data IList {I : Set}(T : I → I → Set) (i : I) : (j : I) → Set where
  [] : IList T i i
  _∷_ : ∀ {k j} → T i k → (xs : IList T k j) → IList T i j

Context : (Sg : Ctx)(G : MCtx) → Index -> Index → Set
Context Sg G = IList (\ i j → DTm Sg G i j)

∫oCtx : ∀ {Sg G I1 I2} -> DTm Sg G I1 I2 -> Ctx -> Ctx
∫oCtx (lam {S = S}) D = S ∷ D
∫oCtx _ D = D

∫oInj : ∀ {Sg G DI I1 I2} -> (d : DTm Sg G I1 I2) -> Inj DI (proj₁ I1) -> Inj (∫oCtx d DI) (proj₁ I2)
∫oInj lam i = cons i
∫oInj (head ts) i = i
∫oInj (tail t) i = i
∫oInj (con c) i = i
∫oInj (var x) i = i

subD : ∀ {Sg G1 G2 TI TO} -> (Sub Sg G1 G2) -> DTm Sg G1 TI TO -> DTm Sg G2 TI TO
subD s lam = lam
subD s (head ts) = head (subs s ts)
subD s (tail t) = tail (sub s t)
subD s (con c) = con c
subD s (var x) = var x

subC : ∀ {Sg G1 G2 TI TO} -> (Sub Sg G1 G2) -> Context Sg G1 TI TO -> Context Sg G2 TI TO
subC s [] = []
subC s (x ∷ c) = subD s x ∷ (subC s c)

∫once : ∀ {Sg G DI TI DO TO} → DTm Sg G (DI , TI) (DO , TO) → Term Sg G DO TO → Term Sg G DI TI
∫once lam t = lam t
∫once (head ts) t = t ∷ ts
∫once (tail t) ts = t ∷ ts
∫once (con c) ts = con c ts
∫once (var x) ts = var x ts

∫ : ∀ {Sg G I O} → Context Sg G I O → Term Sg G (proj₁ O) (proj₂ O) → Term Sg G (proj₁ I) (proj₂ I)
∫ [] t = t
∫ (x ∷ c) t = ∫once x (∫ c t)

module OnHeight where
  open import Height
  open ≤-Reasoning
  open import Data.Nat.Properties
  private
    n≤m⊔n : ∀ m n → Data.Nat._≤_ n (m ⊔ n)
    n≤m⊔n zero    _       = begin _ ∎
    n≤m⊔n (suc m) zero    = z≤n
    n≤m⊔n (suc m) (suc n) = s≤s (n≤m⊔n m n)

  ∫once-height : ∀ {Sg G DI TI DO TO} → (d : DTm Sg G (DI , TI) (DO , TO)) → (t : Term Sg G DO TO) → heightT (∫once d t) > heightT t
  ∫once-height lam t = s≤s (begin heightT t ∎)
  ∫once-height (head ts) t = s≤s (m≤m⊔n (height t) (heights ts))
  ∫once-height (tail t) ts = s≤s (n≤m⊔n (height t) (heights ts))
  ∫once-height (con c) t = s≤s (begin heightT t ∎)
  ∫once-height (var x) t = s≤s (begin heightT t ∎)

  ∫-height : ∀ {Sg G I O} → (ps : Context Sg G I O) → (t : Term Sg G (proj₁ O) (proj₂ O)) → heightT (∫ ps t) ≥ heightT t
  ∫-height [] t = begin heightT t ∎
  ∫-height (x ∷ ps) t = begin heightT t                  ≤⟨ ≤-step (∫-height ps t) ⟩ 
                              suc (heightT (∫ ps t))     ≤⟨ ∫once-height x (∫ ps t) ⟩ 
                              heightT (∫once x (∫ ps t)) ∎

∫once-sub : ∀ {Sg G1 G2 TI TO} -> (s : Sub Sg G1 G2) -> (d : DTm Sg G1 TI TO) -> ∀ t -> subT s (∫once d t) ≡ ∫once (subD s d) (subT s t)
∫once-sub s lam t = refl
∫once-sub s (head ts) t = refl
∫once-sub s (tail t) t₁ = refl
∫once-sub s (con c) t = refl
∫once-sub s (var x) t = refl

∫-sub : ∀ {Sg G1 G2 TI TO} -> (s : Sub Sg G1 G2) -> (c : Context Sg G1 TI TO) -> ∀ t -> subT s (∫ c t) ≡ ∫ (subC s c) (subT s t)
∫-sub s [] t = refl
∫-sub s (x ∷ c) t = trans (∫once-sub s x _) (cong (∫once (subD s x)) (∫-sub s c t))

open ≡-Reasoning

cong-∫once : ∀ {Sg G1 G2 TI TO} -> {s : Sub Sg G1 G2} -> (d : DTm Sg G1 TI TO) -> 
             ∀ {x y} -> subT s x ≡T subT s y -> subT s (∫once d x) ≡T subT s (∫once d y)
cong-∫once {s = s} d {x} {y} eq = ≡-T (
  begin
    subT s (∫once d x)          ≡⟨ ∫once-sub s d x ⟩
    ∫once (subD s d) (subT s x) ≡⟨ cong (∫once (subD s d)) (T-≡ eq) ⟩
    ∫once (subD s d) (subT s y) ≡⟨ sym (∫once-sub s d y) ⟩
    subT s (∫once d y)          ∎)

∫once-inj : ∀ {Sg G1 TI TO} -> (d : DTm Sg G1 TI TO) -> ∀ {x y} -> ∫once d x ≡ ∫once d y -> x ≡ y
∫once-inj lam refl = refl
∫once-inj (head ts) refl = refl
∫once-inj (tail t) refl = refl
∫once-inj (con c) refl = refl
∫once-inj (var x) refl = refl

inv-∫once : ∀ {Sg G1 G2 TI TO} -> {s : Sub Sg G1 G2} -> (d : DTm Sg G1 TI TO) -> 
            ∀ {x y} -> subT s (∫once d x) ≡T subT s (∫once d y) -> subT s x ≡T subT s y
inv-∫once {s = s} d {x} {y} eq = ≡-T (∫once-inj (subD s d)  
   (begin
      ∫once (subD s d) (subT s x) ≡⟨ sym (∫once-sub s d x) ⟩
      subT s (∫once d x)          ≡⟨ T-≡ eq ⟩
      subT s (∫once d y)          ≡⟨ ∫once-sub s d y ⟩ 
      ∫once (subD s d) (subT s y) ∎))

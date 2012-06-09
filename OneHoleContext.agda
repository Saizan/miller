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

_⊹_ : ∀ {I : Set}{T : I -> I -> Set}{i j k} -> IList T i j -> IList T j k -> IList T i k
[] ⊹ ys = ys
(x ∷ xs) ⊹ ys = x ∷ (xs ⊹ ys)

Context : (Sg : Ctx)(G : MCtx) → Index -> Index → Set
Context Sg G = IList (\ i j → DTm Sg G i j)
∫oCtx : ∀ {Sg G I1 I2} -> DTm Sg G I1 I2 -> Ctx -> Ctx
∫oCtx (lam {S = S}) D = S ∷ D
∫oCtx _ D = D
∫Ctx : ∀ {Sg G I1 I2} -> Context Sg G I1 I2 -> Ctx -> Ctx
∫Ctx [] D = D
∫Ctx (x ∷ c) D = (∫Ctx c (∫oCtx x D))
{-
∫oInj : ∀ {Sg G DI DO I1 I2} -> (d : DTm Sg G I1 I2) -> Inj DI DO -> Inj (∫oCtx d DI) (∫oCtx d DO)
∫oInj lam i = cons i
∫oInj (head ts) i = i
∫oInj (tail t) i = i
∫oInj (con c) i = i
∫oInj (var x) i = i
∫Inj : ∀ {Sg G DI DO I1 I2} -> (c : Context Sg G I1 I2) -> Inj DI DO -> Inj (∫Ctx c DI) (∫Ctx c DO)
∫Inj [] i = i
∫Inj (x ∷ c) i = (∫Inj c (∫oInj x i))
-}

∫oInj : ∀ {Sg G DI I1 I2} -> (d : DTm Sg G I1 I2) -> Inj DI (proj₁ I1) -> Inj (∫oCtx d DI) (proj₁ I2)
∫oInj lam i = cons i
∫oInj (head ts) i = i
∫oInj (tail t) i = i
∫oInj (con c) i = i
∫oInj (var x) i = i

∫Inj : ∀ {Sg G DI I1 I2} -> (c : Context Sg G I1 I2) -> Inj DI (proj₁ I1) -> Inj (∫Ctx c DI) (proj₁ I2)
∫Inj [] i = i
∫Inj (x ∷ c) i = ∫Inj c (∫oInj x i)

toInj : ∀ {Sg G I1 I2} -> Context Sg G I1 I2 -> Inj (proj₁ I1) (proj₁ I2)
toInj [] = id-i
toInj (lam ∷ c) = toInj c ∘i weak id-i 
toInj (head _ ∷ c) = toInj c
toInj (tail _ ∷ c) =  toInj c
toInj (con _ ∷ c) = toInj c
toInj (var _ ∷ c) = toInj c

subD : ∀ {Sg G1 G2 TI TO} -> (Sub Sg G1 G2) -> DTm Sg G1 TI TO -> DTm Sg G2 TI TO
subD s lam = lam
subD s (head ts) = head (subs s ts)
subD s (tail t) = tail (sub s t)
subD s (con c) = con c
subD s (var x) = var x

subC : ∀ {Sg G1 G2 TI TO} -> (Sub Sg G1 G2) -> Context Sg G1 TI TO -> Context Sg G2 TI TO
subC s [] = []
subC s (x ∷ c) = subD s x ∷ (subC s c)

∫Inj-subC : ∀ {Sg G1 G2 DI I1 I2}{s : Sub Sg G1 G2} -> (c : Context Sg G1 I1 I2) -> (i : Inj DI (proj₁ I1)) 
                        -> _≡_ {A = Σ Ctx \ D -> Inj D (proj₁ I2)} (∫Ctx c DI , ∫Inj c i) (∫Ctx (subC s c) DI , ∫Inj (subC s c) i)
∫Inj-subC [] i = refl
∫Inj-subC (_∷_ lam c) i = ∫Inj-subC c (cons i)
∫Inj-subC (_∷_ (head ts) c) i = ∫Inj-subC c i
∫Inj-subC (_∷_ (tail t) c) i = ∫Inj-subC c i
∫Inj-subC (_∷_ (con c) c₁) i = ∫Inj-subC c₁ i
∫Inj-subC (_∷_ (var x) c) i = ∫Inj-subC c i

∫once : ∀ {Sg G DI TI DO TO} → DTm Sg G (DI , TI) (DO , TO) → Term Sg G DO TO → Term Sg G DI TI
∫once lam t = lam t
∫once (head ts) t = t ∷ ts
∫once (tail t) ts = t ∷ ts
∫once (con c) ts = con c ts
∫once (var x) ts = var x ts

∫ : ∀ {Sg G I O} → Context Sg G I O → Term Sg G (proj₁ O) (proj₂ O) → Term Sg G (proj₁ I) (proj₂ I)
∫ [] t = t
∫ (x ∷ c) t = ∫once x (∫ c t)

∫once-sub : ∀ {Sg G1 G2 TI TO} -> (s : Sub Sg G1 G2) -> (d : DTm Sg G1 TI TO) -> ∀ t -> subT s (∫once d t) ≡ ∫once (subD s d) (subT s t)
∫once-sub s lam t = refl
∫once-sub s (head ts) t = refl
∫once-sub s (tail t) t₁ = refl
∫once-sub s (con c) t = refl
∫once-sub s (var x) t = refl

∫-sub : ∀ {Sg G1 G2 TI TO} -> (s : Sub Sg G1 G2) -> (c : Context Sg G1 TI TO) -> ∀ t -> subT s (∫ c t) ≡ ∫ (subC s c) (subT s t)
∫-sub s [] t = refl
∫-sub s (x ∷ c) t = trans (∫once-sub s x _) (cong (∫once (subD s x)) (∫-sub s c t))

⊹-snoc : ∀ {Sg G I O D T} (ps : Context Sg G I O) (x : DTm _ _ _ (D , T)) t -> ∫ ps (∫once x t) ≡ ∫ (ps ⊹ (x ∷ [])) t
⊹-snoc [] x t = refl
⊹-snoc (x ∷ ps) x₁ t = cong (∫once x) (⊹-snoc ps x₁ t)

data View {Sg G D T D1} : ∀ {DI TI} (ps : Context Sg G (DI , TI) (D , T))(t : Term Sg G D1 TI) (i : Inj D1 DI) (s : Term Sg G D T) -> Set where
  [] : ∀ {t i s} -> renT i t ≡ s -> View [] t i s
  lam∷ : ∀ {DI S Ss B ps}{t : Tm _ _ (S ∷ D1) (Ss ->> B)}{i : Inj _ DI}{s} -> ren (cons i) t ≡ ∫ ps s -> View (lam ∷ ps) (lam t) i s
  head∷ : ∀ {DI S Ss ps}{t : Tm _ _ D1 S}{ts : Tms _ _ D1 Ss}{i : Inj _ DI}{s} -> ren i t ≡ ∫ ps s -> View (head (rens i ts) ∷ ps) (t ∷ ts) i s
  tail∷ : ∀ {DI S Ss ps}{t : Tm _ _ D1 S}{ts : Tms _ _ D1 Ss}{i : Inj _ DI}{s} -> rens i ts ≡ ∫ ps s -> View (tail (ren i t) ∷ ps) (t ∷ ts) i s
  con∷ : ∀ {DI Ss B ps}{c : Sg ∋ (Ss ->> B)}{ts : Tms _ _ D1 Ss}{i : Inj _ DI}{s} -> rens i ts ≡ ∫ ps s -> View (con c ∷ ps) (con c ts) i s
  var∷ : ∀ {DI Ss B ps}{x : D1 ∋ (Ss ->> B)}{ts : Tms _ _ D1 Ss}{i : Inj _ DI}{s} -> rens i ts ≡ ∫ ps s -> View (var (i $ x) ∷ ps) (var x ts) i s

view : ∀ {Sg G DI TI D T D1} (ps : Context Sg G (DI , TI) (D , T))(t : Term Sg G D1 _) (i : Inj D1 DI) (s : Term Sg G D T) 
     -> renT i t ≡ ∫ ps s -> View ps t i s
view [] t i ts eq = [] eq
view (_∷_ {.(_ ∷ _) , .(inj₁ (_ ->> _))} {_ , _} lam ps) (lam t) i ts eq with ∫ ps ts | lam∷ {ps = ps} {t} {i} {ts}
view (_∷_ lam ps) (lam t) i ts refl | .(ren (cons i) t) | q = q refl
view (_∷_ {_ , ._} {_ , _} (head ts) ps) (t ∷ t₁) i ts₁ eq with ∫ ps ts₁ | head∷ {ps = ps} {t} {t₁} {i} {ts₁} 
view (_∷_ (head .(rens i t₁)) ps) (t ∷ t₁) i ts₁ refl | .(ren i t) | q = q refl
view (_∷_ {_ , ._} {_ , _} (tail t) ps) (t₁ ∷ t₂) i ts eq with ∫ ps ts | tail∷ {ps = ps} {t₁}{t₂} {i} {ts} 
view (_∷_ (tail .(ren i t₁)) ps) (t₁ ∷ t₂) i ts refl | .(rens i t₂) | q = q refl
view (_∷_ {_ , ._} {_ , _} (con c) ps) (con c₁ ts) i ts₁ eq with ∫ ps ts₁ | eq
view (_∷_ {_ , ._} {_ , _} (con c) ps) (con .c ts) i ts₁ eq | .(rens i ts) | refl with ∫ ps ts₁ | con∷ {ps = ps} {c} {ts} {i} {ts₁} 
view (_∷_ (con c) ps) (con .c ts) i ts₁ refl | .(rens i ts) | refl | .(rens i ts) | q = q refl
view (_∷_ {_ , ._} (con c) ps) (fun u j) i ts ()
view (_∷_ {_ , ._} (con c) ps) (var x ts) i ts₁ ()
view (_∷_ {_ , ._} (var x) ps) (con c ts) i ts₁ ()
view (_∷_ {_ , ._} (var x) ps) (fun u j) i ts ()
view (_∷_ {_ , ._} {_ , _} (var x) ps) (var x₁ ts) i ts₁ eq with ∫ ps ts₁ | eq 
view (_∷_ {_ , ._} {_ , _} (var .(i $ x₁)) ps) (var x₁ ts) i ts₁ eq | .(rens i ts) | refl with ∫ ps ts₁ | var∷ {ps = ps} {x₁}{ts} {i} {ts₁} 
view (_∷_ (var .(i $ x₁)) ps) (var x₁ ts) i ts₁ refl | .(rens i ts) | refl | .(rens i ts) | q = q refl

ren-∫ : ∀ {Sg G DI TI D D1 Ss B} (x : D ∋ (Ss ->> B)) (ps : Context Sg G (DI , TI) (D , inj₁ (! B)))(t : Term Sg G D1 _) (i : Inj D1 DI) 
      (ts : Tms Sg G D Ss) -> renT i t ≡ ∫ ps (var x ts) -> ∃ \ b -> x ≡ ∫Inj ps i $ b
ren-∫ x ps t i ts eq with view ps t i (var x ts) eq
ren-∫ x [] (con c ts) i ts₁ () | [] x₁
ren-∫ x [] (fun u j) i ts () | [] x₁ 
ren-∫ .(i $ x₁) [] (var x₁ ts) i .(rens i ts) refl | [] x₂ = x₁ , refl
ren-∫ x .(lam ∷ ps) .(lam t) i ts eq | lam∷ {._} {S} {Ss₁} {B₁} {ps} {t} x₁ = ren-∫ x ps t (cons i) ts x₁
ren-∫ x .(head (rens i ts₁) ∷ ps) .(t ∷ ts₁) i ts eq | head∷ {._} {S} {Ss₁} {ps} {t} {ts₁} x₁ = ren-∫ x ps t i ts x₁
ren-∫ x .(tail (ren i t) ∷ ps) .(t ∷ ts₁) i ts eq | tail∷ {._} {S} {Ss₁} {ps} {t} {ts₁} x₁ = ren-∫ x ps ts₁ i ts x₁
ren-∫ x .(con c ∷ ps) .(con c ts₁) i ts eq | con∷ {._} {Ss₁} {B₁} {ps} {c} {ts₁} x₁ = ren-∫ x ps ts₁ i ts x₁
ren-∫ x .(var (i $ x₁) ∷ ps) .(var x₁ ts₁) i ts eq | var∷ {._} {Ss₁} {B₁} {ps} {x₁} {ts₁} x₂ = ren-∫ x ps ts₁ i ts x₂

module OccursCheck where

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
open import OneHoleContext

mutual
  data MRTm (Sg : Ctx)(G : MCtx)(D : Ctx)(K : MCtx) (i : ∀ S → G ∋ S → K ∋ S) : (T : Ty) → Tm Sg K D T → Set where
    con : {Ss : Fwd Ty}{B : Base} →
          (c : Sg ∋ (Ss ->> B)) → ∀ {tms} → (MRTms Sg G D K i Ss tms) → MRTm Sg G D K i (! B) (con c tms)
    fun : {Ss : Bwd Ty}{B : Base} →
              (u : G ∋ (B <<- Ss)) → (j : Inj Ss D) → ∀ {v} → i _ u ≡ v → MRTm Sg G D K i (! B) (fun v j)
    var : forall {Ss B} → (x : D ∋ (Ss ->> B)) → ∀ {tms} → MRTms Sg G D K i Ss tms → MRTm Sg G D K i (! B) (var x tms)
    lam : {S : Ty}{Ss : Fwd Ty}{B : Base} → ∀ {b} →
          MRTm Sg G (D <: S) K i (Ss ->> B) b → MRTm Sg G D K i (S :> Ss ->> B) (lam b)

  data MRTms (Sg : Ctx)(G : MCtx)(D : Ctx)(K : MCtx)(i : ∀ S → G ∋ S → K ∋ S) : (Ss : Fwd Ty) → Tms Sg K D Ss → Set where
    [] : MRTms Sg G D K i !> []
    _∷_ : {S : Ty}{Ss : Fwd Ty} → ∀ {x xs} →
           MRTm Sg G D K i S x → MRTms Sg G D K i Ss xs → MRTms Sg G D K i (S :> Ss) (x ∷ xs)

mvar : ∀ {Sg}{G T} → T ∈ G → Tm Sg G (ctx T) (! (type T))
mvar u = fun u id-i

mutual
  forget : ∀ {Sg G D K T}{i}{t} → MRTm Sg G D K i T t → ∃ \ s → sub (\ s v → mvar (i s v)) s ≡ t
  forget (con c ts) = mapΣ (con c) (cong (con c)) (forgets ts)
  forget (fun u j refl) = (fun u j) , cong (fun _) (right-id j)
  forget (var x ts) = mapΣ (var x) (cong (var x)) (forgets ts)
  forget (lam t) = mapΣ lam (cong lam) (forget t)
  
  forgets : ∀ {Sg G D K T}{i}{t} → MRTms Sg G D K i T t → ∃ \ s → subs (\ s v → mvar (i s v)) s ≡ t
  forgets [] = [] , refl
  forgets (t ∷ ts) = proj₁ (forget t) ∷ proj₁ (forgets ts) , (cong₂ _∷_ (proj₂ (forget t)) (proj₂ (forgets ts)))

no-confusion : ∀ {R : Set}{I}{T : I -> I -> Set}{i k j} -> (ps : IList T k j) {x : T j i} -> _≡_ {A = Σ I (\ i -> IList T k i)} (i , (ps ⊹ (x ∷ []))) (k , []) -> R
no-confusion [] ()
no-confusion (x ∷ ps) ()

not-nil : ∀ {R : Set}{I}{T : I -> I -> Set}{i k j} -> (ps : IList T k j) {x : T i k} -> 
        _≡_ {A = Σ I (\ j -> IList T i j)} (j , (x ∷ ps)) (i , []) -> R
not-nil ps ()

No-Cycle : ∀ {TI Sg G D1 DI DO} -> let TO = TI in (ps : Context Sg G (DI , TI) (DO , TO)) (t : Term Sg G D1 TO) (i : Inj D1 DI)(j : Inj D1 DO) -> 
                        renT i t ≡ ∫ ps (renT j t) -> _≡_ {A = Σ Index \ D -> Context Sg G (DI , TI) D} ((DO , TO) , ps) ((DI , TI) , [])
No-Cycle ps t i j eq with view ps t i (renT j t) eq
No-Cycle .[] t i j eq | [] = refl
No-Cycle .(lam ∷ ps) .(lam t) i j eq | lam∷ {DO} {S} {Ss} {B} {ps} {t} x = 
  no-confusion ps (No-Cycle (ps ⊹ (lam ∷ [])) t (cons i) (cons j) (trans x (⊹-snoc ps lam (ren (cons j) t))))
No-Cycle .(head (rens i ts) ∷ ps) .(t ∷ ts) i j eq | head∷ {DO} {S} {Ss} {ps} {t} {ts} x = 
  no-confusion ps (No-Cycle (ps ⊹ (head _ ∷ [])) t i j (trans x (⊹-snoc ps (head _) (ren j t))))
No-Cycle .(tail (ren i t) ∷ ps) .(t ∷ ts) i j eq | tail∷ {DO} {S} {Ss} {ps} {t} {ts} x = 
  no-confusion ps (No-Cycle (ps ⊹ (tail _ ∷ [])) ts i j (trans x (⊹-snoc ps (tail _) (rens j ts))))
No-Cycle .(con c ∷ ps) .(con c ts) i j eq | con∷ {DO} {Ss} {B} {ps} {c} {ts} x = 
  no-confusion ps (No-Cycle (ps ⊹ (con c ∷ [])) ts i j (trans x (⊹-snoc ps (con c) (rens j ts))))
No-Cycle .(var (i $ x) ∷ ps) .(var x ts) i j eq | var∷ {DO} {Ss} {B} {ps} {x} {ts} x₁ = 
  no-confusion ps (No-Cycle (ps ⊹ (var _ ∷ [])) ts i j (trans x₁ (⊹-snoc ps (var _) (rens j ts))))

_[_]OccursIn_ : ∀ {Sg G D D' T S} (u : G ∋ S) (j : Inj (ctx S) D') (t : Term Sg G D T) → Set
u [ j ]OccursIn t = Σ (Context _ _ _ (_ , inj₁ _) ) \ C → ∫ C (fun u j) ≡ t

_OccursIn_ : ∀ {Sg G D T S} (u : G ∋ S) (t : Term Sg G D T) → Set
_OccursIn_ u t = ∃ \ D' → Σ (Inj _ D') \ j → u [ j ]OccursIn t

map-occ : ∀ {Sg G S D T D' T' }{u : G ∋ S}{t : Term Sg G D T} (d : DTm Sg G (D' , T') (D , T)) → u OccursIn t → u OccursIn ∫once d t
map-occ d (Dj , j , C , eq) = (Dj , j , (d ∷ C) , cong (∫once d) eq)
  
mutual
  check' : ∀ {Sg G D T S} (u : G ∋ S) (t : Tm Sg G D T) → MRTm Sg (G - u) D G (thin u) T t ⊎ u OccursIn t
  check' u (con c ts) = Data.Sum.map (con c) (map-occ (con c)) (check's u ts) 
  check' u (fun w j) with thick u w
  ... | inj₁ (z , eq) = inj₁ (fun z j eq)
  check' u (fun .u j) | inj₂ refl = inj₂ (_ , (j , ([] , refl)))
  check' u (var x ts) = Data.Sum.map (var x) (map-occ (var x)) (check's u ts)
  check' u (lam t) = Data.Sum.map lam (map-occ lam) (check' u t)
  
  check's : ∀ {Sg G D Ts S} (u : G ∋ S) (ts : Tms Sg G D Ts) → MRTms Sg (G - u) D G (thin u) Ts ts ⊎ u OccursIn ts
  check's u [] = inj₁ []
  check's u (t ∷ ts) with check' u t | check's u ts 
  ... | inj₂ x | _ = inj₂ (map-occ (head ts) x)
  ... | inj₁ x | inj₁ xs = inj₁ (x ∷ xs)
  ... | _ | inj₂ xs = inj₂ (map-occ (tail t) xs)

check : ∀ {Sg G D T S} (u : G ∋ S) (t : Tm Sg G D T) → (∃ \ s → sub (\ S v → mvar (thin u S v)) s ≡ t) ⊎ u OccursIn t
check u t = Data.Sum.map forget (\ x → x) (check' u t)

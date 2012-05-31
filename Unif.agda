module Unif where

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
open import OccursCheck


mutual
  data RTm (Sg : Ctx)(G : MCtx)(D : Ctx)(K : Ctx) (i : Inj D K) : (T : Ty) → Tm Sg G K T → Set where
    con : {Ss : Fwd Ty}{B : Base} →
          (c : Sg ∋ (Ss ->> B)) → ∀ {tms} → (RTms Sg G D K i Ss tms) → RTm Sg G D K i (! B) (con c tms)
    fun : {Ss : Bwd Ty}{B : Base} →
              (u : G ∋ (B <<- Ss)) → (j : Inj Ss D) → ∀ {k} → (i ∘i j) ≡ k → RTm Sg G D K i (! B) (fun u k)
    var : forall {Ss B} → (v : D ∋ (Ss ->> B)) → ∀ {x} → (i $ v) ≡ x → ∀ {tms} → RTms Sg G D K i Ss tms → RTm Sg G D K i (! B) (var x tms)
    lam : {S : Ty}{Ss : Fwd Ty}{B : Base} → ∀ {b} →
          RTm Sg G (D <: S) (K <: S) (cons i) (Ss ->> B) b → RTm Sg G D K i (S :> Ss ->> B) (lam b)

  data RTms (Sg : Ctx)(G : MCtx)(D K : Ctx)(i : Inj D K) : (Ss : Fwd Ty) → Tms Sg G K Ss → Set where
    [] : RTms Sg G D K i !> []
    _∷_ : {S : Ty}{Ss : Fwd Ty} → ∀ {x xs} →
           RTm Sg G D K i S x → RTms Sg G D K i Ss xs → RTms Sg G D K i (S :> Ss) (x ∷ xs)


mutual
  unique : ∀ {Sg G D D0}{T : Ty} → {i : Inj D D0} → {t : Tm Sg G D0 T} → (x y : RTm Sg G D D0 i T t) → x ≡ y
  unique (con c x) (con .c x₁) = cong (con c) (uniques x x₁)
  unique {i = i} (fun u j eq1)(fun .u j₁ eq2) with  ∘i-inj i j j₁ (trans eq1 (sym eq2)) | eq1 | eq2
  unique {i = i} (fun u .j₁ eq1) (fun .u j₁ eq2) | refl | refl | refl = refl
  unique {i = i} (var v x₁ x₂) (var v₁ x₃ x₄) with injective i v v₁ (trans x₁ (sym x₃)) 
  unique (var .v₁ refl x₂) (var v₁ e x₄) | refl with e 
  ... | refl = cong (var v₁ refl) (uniques x₂ x₄)
  unique (lam x) (lam y) = cong lam (unique x y)
  
  uniques : ∀ {Sg G D D0}{Ss : Fwd Ty} → {i : Inj D D0} → {t : Tms Sg G D0 Ss} → (x y : RTms Sg G D D0 i Ss t) → x ≡ y
  uniques [] [] = refl
  uniques (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (unique x y) (uniques xs ys)

mutual
  ren : ∀ {Sg G D D0}{T : Ty} → Inj D D0 → Tm Sg G D T → Tm Sg G D0 T
  ren rho (con c ts) = con c (rens rho ts) 
  ren rho (fun f xs) = fun f (rho ∘i xs)
  ren rho (var x xs) = var (rho $ x) (rens rho xs)
  ren rho (lam t) = lam (ren (cons rho) t)

  rens : ∀ {Sg G D D0}{Ts : Fwd Ty} → Inj D D0 → Tms Sg G D Ts → Tms Sg G D0 Ts
  rens rho [] = []
  rens rho (x ∷ ts) = ren rho x ∷ rens rho ts

mutual
  forget : ∀ {Sg G D D0}{T : Ty} → {i : Inj D D0} → {t : Tm Sg G D0 T} → (x : RTm Sg G D D0 i T t) → Σ (Tm Sg G D T) \ s → ren i s ≡ t
  forget (con c x) = mapΣ (con c) (cong (con c)) (forgets x)
  forget (fun u j eq) = fun u j , cong (fun u) eq
  forget {i = i} (var v refl x₂) = mapΣ (var v) (cong (var (i $ v))) (forgets x₂)
  forget (lam x) = mapΣ lam (cong lam) (forget x) 
  
  forgets : ∀ {Sg G D D0}{Ts} → {i : Inj D D0} → {t : Tms Sg G D0 Ts} → (x : RTms Sg G D D0 i Ts t) → Σ (Tms Sg G D Ts) \ s → rens i s ≡ t
  forgets [] = [] , refl
  forgets (x₁ ∷ x₂) = ((proj₁ (forget x₁)) ∷ (proj₁ (forgets x₂))) , (cong₂ _∷_ (proj₂ (forget x₁)) (proj₂ (forgets x₂)))


Sub : Ctx → MCtx → MCtx → Set
Sub Sg G1 G2 = ∀ S → G1 ∋ S → Tm Sg G2 (ctx S) (! type S)

mutual
  sub : ∀ {Sg G1 G2 D T} → Sub Sg G1 G2 → Tm Sg G1 D T → Tm Sg G2 D T
  sub s (con x x₁) = con x (subs s x₁)
  sub s (fun u x₁) = ren x₁ (s _ u)
  sub s (var x xs) = var x (subs s xs)
  sub s (lam t) = lam (sub s t)

  subs : ∀ {Sg G1 G2 D Ss} → Sub Sg G1 G2 → Tms Sg G1 D Ss → Tms Sg G2 D Ss
  subs s [] = []
  subs s (x ∷ ts) = sub s x ∷ subs s ts
mutual
  ren-∘ : ∀ {Sg G1 D1 D2 D3 T} {j : Inj D2 D3} {i : Inj D1 D2} (t : Tm Sg G1 D1 T) -> ren (j ∘i i) t ≡ ren j (ren i t)
  ren-∘ (con c ts) = cong (con c) (rens-∘ ts)
  ren-∘ (fun u j₁) = cong (fun u) (sym assoc-∘i)
  ren-∘ (var x ts) = cong₂ var (apply-∘ _ _) (rens-∘ ts)
  ren-∘ (lam t) = cong lam (trans (cong (λ k → ren k t) (cons-∘i _ _)) (ren-∘ t))
  
  rens-∘ : ∀ {Sg G1 D1 D2 D3 T} {j : Inj D2 D3} {i : Inj D1 D2} (t : Tms Sg G1 D1 T) -> rens (j ∘i i) t ≡ rens j (rens i t)
  rens-∘ [] = refl
  rens-∘ (t ∷ ts) = cong₂ _∷_ (ren-∘ t) (rens-∘ ts)
mutual
  sub-nat : ∀ {Sg G1 G2 D1 D2 T} {f : Sub Sg G1 G2} {i : Inj D1 D2} (t : Tm Sg G1 D1 T) -> sub f (ren i t) ≡ ren i (sub f t)
  sub-nat (con c ts) = cong (con c) (sub-nats ts)
  sub-nat (fun u j) = ren-∘ _
  sub-nat (var x ts) = cong (var _) (sub-nats ts)
  sub-nat (lam t) = cong lam (sub-nat t)
  
  sub-nats : ∀ {Sg G1 G2 D1 D2 T} {f : Sub Sg G1 G2} {i : Inj D1 D2} (t : Tms Sg G1 D1 T) -> subs f (rens i t) ≡ rens i (subs f t)
  sub-nats [] = refl
  sub-nats (t ∷ ts) = cong₂ _∷_ (sub-nat t) (sub-nats ts)
mutual
  sub-∘ : ∀ {Sg G1 G2 G3 D T} {f : Sub Sg G2 G3}{g} (t : Tm Sg G1 D T) -> sub f (sub g t) ≡ sub (\ _ t -> sub f (g _ t)) t
  sub-∘ (con c ts) = cong (con c) (subs-∘ ts)
  sub-∘ {g = g} (fun u j) = sub-nat (g _ u)
  sub-∘ (var x ts) = cong (var x) (subs-∘ ts)
  sub-∘ (lam t) = cong lam (sub-∘ t)
  
  subs-∘ : ∀ {Sg G1 G2 G3 D T} {f : Sub Sg G2 G3}{g} (t : Tms Sg G1 D T) -> subs f (subs g t) ≡ subs (\ _ t -> sub f (g _ t)) t
  subs-∘ [] = refl
  subs-∘ (t ∷ t₁) = cong₂ _∷_ (sub-∘ t) (subs-∘ t₁)

Bwd-len : ∀ {A : Set} → Bwd A → Nat
Bwd-len !> = zero
Bwd-len (x :> xs) = suc (Bwd-len xs)

Ctx-len : MCtx → Nat
Ctx-len <! = zero
Ctx-len (x <: (_ <<- f)) = suc (Bwd-len f + (Ctx-len x))

data Subs (Sg : Ctx) : MCtx → Nat → Set where
  nil : ∀ {G} → Subs Sg G (Ctx-len G)
  _◇_ : ∀ {n G D} → Sub Sg G D → (ss : Subs Sg D n) → Subs Sg G (suc n)

MetaRen : MCtx → MCtx → Set
MetaRen G D = ∀ S → G ∋ S → ∃ \ Ψ → D ∋ (type S <<- Ψ) × Inj Ψ (ctx S)

_∘mr_ : ∀ {G1 G2 G3} → MetaRen G2 G3 → MetaRen G1 G2 → MetaRen G1 G3
f ∘mr g = λ S x → let gr = g S x; Ψ = proj₁ gr; v = proj₁ (proj₂ gr); j = proj₂ (proj₂ gr) 
                      fr = f _ v; fΨ = proj₁ fr; fv = proj₁ (proj₂ fr); fj = proj₂ (proj₂ fr)  in
                  fΨ , (fv , j ∘i fj)

singleton : ∀ {G S} → (u : G ∋ S) → ∀ {Ψ} → Inj Ψ (ctx S) -> MetaRen G ((G - u) <: (type S <<- Ψ))
singleton u j T v with thick u v
singleton {G} {type <<- ctx} u j T v | inj₁ x = _ , ((suc (proj₁ x)) , (quo (λ _ x₁ → x₁) {λ _ e → e}))
singleton {G} {type <<- ctx} .v j .(type <<- ctx) v | inj₂ refl = _ , (zero , j) 

mutual
  MRProp : ∀ {Sg : Ctx} {G1 G2 : MCtx} → MetaRen G1 G2 → ∀ {D1 D2 : Ctx} → Inj D1 D2 → ∀ {T} → Tm Sg G1 D2 T → Set
  MRProp r i (con x x₁) = MRProps r i x₁
  MRProp r i (fun u j) = Σ (_ ⊇ proj₁ (r _ u)) (λ k → i ∘i k ≡ j ∘i proj₂ (proj₂ (r _ u)))
  MRProp r i (var x x₁) = MRProps r i x₁
  MRProp r i (lam t) = MRProp r (cons i) t

  MRProps : ∀ {Sg : Ctx} {G1 G2 : MCtx} → MetaRen G1 G2 → ∀ {D1 D2 : Ctx} → Inj D1 D2 → ∀ {Ts} → Tms Sg G1 D2 Ts → Set
  MRProps r i [] = ⊤
  MRProps r i (x ∷ ts) = MRProp r i x × MRProps r i ts

toSub : ∀ {Sg G D} → MetaRen G D → Sub Sg G D
toSub r = λ S x → fun (proj₁ (proj₂ (r S x))) (proj₂ (proj₂ (r S x)))

-- downward closed
mutual
  DClosedMRP : ∀ {Sg G1 G2 G3} (f : MetaRen G2 G3)(g : MetaRen G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tm Sg G1 D2 T) → MRProp g i t → MRProp (_∘mr_ f g) i t
  DClosedMRP f g i (con c ts) m = DClosedMRPs f g i ts m
  DClosedMRP f g i (fun u j) (h , i∘h≡j∘gu) = h ∘i fj , trans assoc-∘i (trans (cong (λ k → k ∘i fj) i∘h≡j∘gu) (sym assoc-∘i)) where
    fr = f _ (proj₁ (proj₂ (g _ u)))
    fj = proj₂ (proj₂ fr)
  DClosedMRP f g i (var x ts) m = DClosedMRPs f g i ts m
  DClosedMRP f g i (lam t) m = DClosedMRP f g (cons i) t m
  
  DClosedMRPs : ∀ {Sg G1 G2 G3} → (f : MetaRen G2 G3)(g : MetaRen G1 G2) → ∀ {D1 D2 : Ctx} → (i : Inj D1 D2) ->
               ∀ {T} → (t : Tms Sg G1 D2 T) → MRProps g i t → MRProps (_∘mr_ f g) i t
  DClosedMRPs f g i [] m = _
  DClosedMRPs f g i (t ∷ ts) m = (DClosedMRP f g i t (proj₁ m)) , (DClosedMRPs f g i ts (proj₂ m))

  step-MRP : ∀ {Sg G1 G2 G3} (f : MetaRen G2 G3)(g : MetaRen G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tm Sg G1 D2 T) → MRProp f i (sub (toSub g) t) → MRProp (f ∘mr g) i t
  step-MRP f g i (con c ts) m = step-MRPs f g i ts m
  step-MRP f g i (fun u j) (k , p) = k , trans p (sym assoc-∘i)
  step-MRP f g i (var x ts) m = step-MRPs f g i ts m
  step-MRP f g i (lam t) m = step-MRP f g (cons i) t m
  
  step-MRPs : ∀ {Sg G1 G2 G3} (f : MetaRen G2 G3)(g : MetaRen G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tms Sg G1 D2 T) → MRProps f i (subs (toSub g) t) → MRProps (f ∘mr g) i t
  step-MRPs f g i [] ms = _
  step-MRPs f g i (t ∷ ts) ms = (step-MRP f g i t (proj₁ ms)) , (step-MRPs f g i ts (proj₂ ms))
{-# NO_TERMINATION_CHECK #-}
mutual
  
  purge : ∀ {Sg G D1 D2 T} -> (i : Inj D1 D2) -> (t : Tm Sg G D2 T) -> (∃ \ G1 -> Σ (MetaRen G G1) \ ρ -> MRProp ρ i t)
  purge i (con c ts) = purges i ts
  purge i (fun u j) = _ , (singleton u (proj₁ (proj₂ r)) , aux) where
    r = purje i j
    aux : Σ (_ ⊇ proj₁ (singleton u (proj₁ (proj₂ r)) _  u))
           (λ k →
                i ∘i k ≡
                     j ∘i
                  proj₂
                    (proj₂
              (singleton u (proj₁ (proj₂ r)) _ u)))
    aux rewrite thick-refl u = proj₂ (proj₂ r)
  purge i (var x ts) = purges i ts
  purge i (lam t) = purge (cons i) t

  purges : ∀ {Sg G D1 D2 T} -> (i : Inj D1 D2) -> (t : Tms Sg G D2 T) -> (∃ \ G1 -> Σ (MetaRen G G1) \ ρ -> MRProps ρ i t)
  purges {Sg}{G} i [] = G , (λ S x → _ , (x , (quo (λ x₁ x₂ → x₂) {\ _ eq -> eq}))) , tt
  purges i (t ∷ t₁) with purge i t
  ... | (G1 , ρ , p) with purges i (subs (toSub ρ) t₁)
  ... | (G2 , ρ2 , p2) = G2 , ((ρ2 ∘mr ρ) , ((DClosedMRP ρ2 ρ i t p) , step-MRPs ρ2 ρ i t₁ p2))

mutual
  invertTm : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tm Sg G D T) → (ρ : MetaRen G G1) → MRProp ρ i t
    → Dec (RTm Sg G1 Ss D i T (sub (toSub ρ) t))
  invertTm i (con x x₁) r m with invertTms i x₁ r m
  invertTm i (con x x₁) r m | yes p = yes (con x p)
  invertTm i (con x x₁) r m | no ¬p = no (λ {(con .x ys) → ¬p ys})
  invertTm i (fun u j) r m = yes (fun (proj₁ (proj₂ (r _ u))) (proj₁ m) (proj₂ m))
  invertTm i (var x x₁) r m with invert (i) x | invertTms i x₁ r m 
  invertTm i (var x x₁) r m | yes (y , eq) | yes p₁ = yes (var y eq p₁)
  invertTm i (var x x₁) r m | yes p | no ¬p = no λ {(var y eq xs) → ¬p xs}
  invertTm i (var x x₁) r m | no ¬p | q = no λ {(var y eq xs) → ¬p (y , eq)}
  invertTm i (lam t) r m with invertTm (cons i) t r m
  invertTm i (lam t) r m | yes p = yes (lam p)
  invertTm i (lam t) r m | no ¬p = no (λ {(lam q) → ¬p q})

  invertTms : ∀ {Sg G G1 Ss D T} (i : Inj Ss D) → (t : Tms Sg G D T) → (ρ : MetaRen G G1) → MRProps ρ i t 
            → Dec (RTms Sg G1 Ss D i T (subs (toSub ρ) t))
  invertTms i [] r m = yes []
  invertTms i (x ∷ t) r m with invertTm i x r (proj₁ m) | invertTms i t r (proj₂ m)
  invertTms i (x ∷ t) r m | yes p | yes p₁ = yes (p ∷ p₁)
  invertTms i (x ∷ t) r m | yes p | no ¬p = no λ {(y ∷ ys) → ¬p ys}
  invertTms i (x ∷ t) r m | no ¬p | z = no λ {(y ∷ ys) → ¬p y}

{-# NO_TERMINATION_CHECK #-}
mutual
  unify : ∀ {Sg G D T} → (x y : Tm Sg G D T) → Maybe (∃ \ G1 -> Σ (Sub Sg G G1) \ s -> sub s x ≡ sub s y)
  unify (con x xs) (con y ys) with eq-∋ (_ , x) (_ , y) 
  ... | no _ = nothing
  unify (con x xs) (con .x ys) | yes refl with unifyTms xs ys
  ... | nothing = nothing
  ... | just (_ , σ , eq) = just (_ , σ , cong (con x) eq)

  unify (fun x xs) t with check x t 
  unify (fun x xs) t | inj₁ x₁  = {!!} -- needs forget-MRTm
  unify (fun x xs) .(fun x j) | inj₂ (_ , j , [] , refl) = just (_ , (toSub (singleton x k)) , aux) where
    r = intersect xs j
    k = proj₁ (proj₂ r)
    aux : ren xs (toSub (singleton x k) _ x) ≡ sub (toSub (singleton x k)) (fun x j)
    aux rewrite thick-refl x = cong (fun zero) (proj₂ (proj₂ r))
  unify (fun x xs) .(∫once x₁ (∫ ps (fun x j))) | inj₂ (proj₁ , j , x₁ ∷ ps , refl) = nothing
  unify s (fun y ys) = {!!} -- mirror
  unify (var x xs) (var y ys) = {!!} -- like con
  unify (lam x) (lam y) with unify x y
  ... | nothing = nothing
  ... | just (_ , σ , eq) = just (_ , σ , cong lam eq)
  unify _ _ = nothing


  
  unifyTms : ∀ {Sg G D Ts} → (x y : Tms Sg G D Ts) → Maybe (∃ \ G1 -> Σ (Sub Sg G G1) \ s -> subs s x ≡ subs s y)
  unifyTms [] [] = just (_ , ((λ S x → fun x (quo (λ _ x₁ → x₁) {λ _ e → e})) , refl))
  unifyTms (s ∷ xs) (t ∷ ys) with unify s t 
  ... | nothing = nothing
  ... | just (_ , σ , eq) with unifyTms (subs σ xs) (subs σ ys) 
  ... | nothing = nothing
  ... | just (_ , σ1 , eq1) = just (_ , ((λ S x → sub σ1 (σ S x)) , 
    cong₂ _∷_ (trans (trans (sym (sub-∘ s)) (cong (sub σ1) eq)) (sub-∘ t)) (trans (trans (sym (subs-∘ xs)) eq1) (subs-∘ ys)))) -- XXX sub assoc
{-
mutual
  unify : ∀ {Sg G D T} → (x y : Tm Sg G D T) → ∀ {n} → Subs Sg G n → Maybe (Subs Sg G n)
  unify (con x xs) (con y ys) a with eq-∋ (_ , x) (_ , y)
  unify (con x xs) (con .x ys) a | yes refl = unifyTms xs ys a
  unify (con x xs) (con y ys) a | no y₁ = nothing
  unify (fun x xs) (fun y ys) nil = {!!}
  unify (fun x xs) t nil = {!!}
  unify s (fun y ys) nil = {!!}
  unify (var x xs) (var y ys) a with eq-∋ (_ , x) (_ , y) 
  unify (var x xs) (var .x ys) a | yes refl = unifyTms xs ys a
  unify (var x xs) (var y ys) a | no y₁ = nothing
  unify (lam x) (lam y) a = unify x y a
  unify s t (s₁ ◇ a) = _◇_ s₁ <$> unify (sub s₁ s) (sub s₁ t) a
  unify _ _ _ = nothing

  unifyTms : ∀ {Sg G D Ts} → (x y : Tms Sg G D Ts) → ∀ {n} → Subs Sg G n → Maybe (Subs Sg G n)
  unifyTms [] [] a = just a
  unifyTms (x ∷ xs) (y ∷ ys) a = unify x y a >>= unifyTms xs ys
-}

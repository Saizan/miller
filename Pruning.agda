module Pruning where

open import Data.Product renaming (map to mapΣ)
open import Data.Nat hiding (_≤_) renaming (ℕ to Nat)
open import Relation.Nullary
open import Relation.Binary
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)         
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Sum

open import Injection
open import Injection.Objects
open import Lists

open import Syntax
open import Equality
open import MetaRens

data Prunes {Sg : Ctx} {G1 G2 : MCtx} (s : Sub Sg G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) : ∀ {T} → Term Sg G1 D2 T → Set where
  [] : Prunes s i {inj₂ []} []
  _∷_ : ∀ {S Ss t ts} -> (m : Prunes s i {inj₁ S} t) -> (ms : Prunes s i {inj₂ Ss} ts) -> Prunes s i {inj₂ (S ∷ Ss)} (t ∷ ts)
  con : ∀ {Ss B c ts} -> (ms : Prunes s i {inj₂ Ss} ts) -> Prunes s i {inj₁ (! B)} (con c ts)
  var : ∀ {Ss B x ts} -> (ms : Prunes s i {inj₂ Ss} ts) -> Prunes s i {inj₁ (! B)} (var x ts)
  lam : ∀ {S Ss B t} -> (m : Prunes s (cons i) {inj₁ (Ss ->> B)} t) -> Prunes s i {inj₁ ((S ∷ Ss) ->> B)} (lam t)
  fun : ∀ {Ss B u j H} -> ∀ v (h : Inj H _) -> (eq : s (B <<- Ss) u ≡ fun v h) -> ∀ k -> (i∘k≡j∘h : i ∘i k ≡ j ∘i h) 
                       -> Prunes s i {inj₁ (! B)} (fun u j)

_/_∈_ : ∀ {Sg : Ctx} {G1 G2 : MCtx} (s : Sub Sg G1 G2) → ∀ {D1 D2 : Ctx} → ∀ {T} → Term Sg G1 D2 T → Inj D1 D2 → Set
_/_∈_ s t i = Prunes s i t

DClosedMRP : ∀ {Sg G1 G2 G3} (f : MetaRen G2 G3){g : Sub Sg G1 G2} {D1 D2 : Ctx} {i : Inj D1 D2} ->
               ∀ {T} → {t : Term Sg G1 D2 T} → g / t ∈ i → (toSub f ∘s g) / t ∈ i
DClosedMRP f [] = []
DClosedMRP f (m ∷ ms) = DClosedMRP f m ∷ DClosedMRP f ms
DClosedMRP f (con ms) = con (DClosedMRP f ms)
DClosedMRP f (var ms) = var (DClosedMRP f ms)
DClosedMRP f (lam m) = lam (DClosedMRP f m)
DClosedMRP f {i = i} (fun {j = j} v h eq k i∘k≡j∘h) rewrite eq = fun (body (f _ v)) (h ∘i fj) (cong (sub _) eq) (k ∘i fj) 
  (begin
     i ∘i (k ∘i fj) ≡⟨ assoc-∘i ⟩
     (i ∘i k) ∘i fj ≡⟨ cong (λ k₁ → k₁ ∘i fj) i∘k≡j∘h ⟩
     (j ∘i h) ∘i fj ≡⟨ sym assoc-∘i ⟩ 
     j ∘i (h ∘i fj) ∎)  
 where
      fr = f _ v
      fj = ρ-env fr

mutual
  step-MRP : ∀ {Sg G1 G2 G3} {f : Sub Sg G2 G3}(g : MetaRen G1 G2) {D1 D2 : Ctx} {i : Inj D1 D2} ->
               ∀ {T} → (t : Tm Sg G1 D2 T) → f / sub (toSub g) t ∈ i → (f ∘s toSub g) / t ∈ i
  step-MRP g (con c ts) (con m) = con (step-MRPs g ts m)
  step-MRP {f = f} g {i = i} (fun u j) (fun v h eq k p) 
    = fun v (ρ-env (g _ u) ∘i h) (cong (ren _) eq) k
      (begin
             i ∘i k                    ≡⟨ p ⟩
             (j ∘i ρ-env (g _ u)) ∘i h ≡⟨ sym assoc-∘i ⟩
             j ∘i (ρ-env (g _ u) ∘i h) ∎)
  step-MRP g (var x ts) (var m) = var (step-MRPs g ts m)
  step-MRP g (lam t) (lam m) = lam (step-MRP g t m)
  
  step-MRPs : ∀ {Sg G1 G2 G3} {f : Sub Sg G2 G3}(g : MetaRen G1 G2) {D1 D2 : Ctx} {i : Inj D1 D2} ->
               ∀ {T} → (t : Tms Sg G1 D2 T) → f / subs (toSub g) t ∈ i  → (f ∘s toSub g) / t ∈ i
  step-MRPs g [] ms = []
  step-MRPs g (t ∷ ts) (mt ∷ mts) = step-MRP g t mt ∷ step-MRPs g ts mts

mutual
  MRP-ext : ∀ {Sg : Ctx} {G1 G2 : MCtx} → {f g : Sub Sg G1 G2} → f ≡s g -> 
            ∀ {D1 D2 : Ctx} → {i : Inj D1 D2} →  ∀ {T} → {t : Term Sg G1 D2 T} → f / t ∈ i -> g / t ∈ i
  MRP-ext f≡g (con ms) = con (MRP-ext f≡g ms)
  MRP-ext f≡g (fun v h eq k i∘k≡j∘h) = fun v h (trans (sym (f≡g _ _)) eq) k i∘k≡j∘h
  MRP-ext f≡g (var ms) = var (MRP-ext f≡g ms)
  MRP-ext f≡g (lam m) = lam (MRP-ext f≡g m)
  MRP-ext f≡g [] = []
  MRP-ext f≡g (m ∷ ms) = MRP-ext f≡g m ∷ MRP-ext f≡g ms

open import DSub

Pruner : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Term Sg G D2 T) → Set
Pruner {Sg} {G} i t = ∃ \ G1 → Σ (MetaRen G G1) \ ρ → Decreasing {Sg} (toSub ρ) × toSub ρ / t ∈ i

_∙_ : ∀ {Sg G D1 D2 T} → {i : Inj D1 D2} → {t : Term Sg G D2 T} ->
        ∀ {D1 D2 T} → {j : Inj D1 D2} → {s : Term Sg G D2 T} ->
        (∀ {G1}{σ : Sub Sg G G1} -> σ / t ∈ i -> σ / s ∈ j) -> Pruner i t -> Pruner j s
f ∙ (_ , ρ , ρ-decr , m) = _ , ρ , ρ-decr , f m

mutual
  
  prune' : ∀ {Sg G D1 D2 T} {i : Inj D1 D2} → (t : Tm Sg G D2 T) → ∃ (\ n -> n ≥ Ctx-length G) 
            -> Pruner i t
  prune' (con c ts) l = con ∙ prune's ts l
  prune' {i = i} (fun u j) l = _ , singleton u p₂ , decr , fun _ _ refl (proj₁ aux) (proj₂ aux) where
    open Pullback (pullback i j)
    aux : ∃ \ k -> i ∘i k ≡ j ∘i ρ-env (singleton u p₂ _ u)
    aux rewrite thick-refl u = p₁ , commutes
    decr = singleton-Decreasing p₂ u (pullback-Decr i j)
  prune' (var x ts) l = var ∙ prune's ts l
  prune' (lam t) l = lam ∙ prune' t l

  prune's : ∀ {Sg G D1 D2 T} → {i : Inj D1 D2} → (t : Tms Sg G D2 T) → ∃ (\ n -> n ≥ Ctx-length G) 
           -> Pruner i t
  prune's {Sg}{G} [] _ = G , idmr , inj₁ (refl , IsIso-id) , []
  prune's (t ∷ ts) l = given (prune' t l) prune's ts l

  given_prune's  : ∀ {Sg G D1 D2 T Ts } {i : Inj D1 D2} {t : Tm Sg G D2 T} -> Pruner i t → (ts : Tms Sg G D2 Ts) → ∃ (\ n -> n ≥ Ctx-length G) 
                -> Pruner i (t ∷ ts)

  given (_ , σ , (inj₁ (eq , (δ , iso1) , iso2)) , p1) prune's ts l with prune's ts l 
  ... | G1 , ρ , ρ-decr , p 
      = G1 , ρ , ρ-decr , MRP-ext ρ∘δ'∘σ≡ρ (DClosedMRP (ρ ∘mr δ') p1) ∷ p
    where 
      δ' = proj₁ (toMRen δ ((toSub σ) , iso2))
      δ'≡δ = proj₂ (toMRen δ ((toSub σ) , iso2))
      ρ∘δ'∘σ≡ρ : ∀ S u -> (toSub (ρ ∘mr δ') ∘s toSub σ) S u ≡ (toSub ρ) S u 
      ρ∘δ'∘σ≡ρ S u = 
        begin (toSub (ρ ∘mr δ') ∘s toSub σ) S u             ≡⟨ (cong (λ j → fun (body (((ρ ∘mr δ') ∘mr σ) _ u)) j) assoc-∘i) ⟩
              sub (toSub ρ) (sub (toSub δ') (toSub σ S u))  ≡⟨ cong (sub (toSub ρ)) (sub-ext δ'≡δ (toSub σ _ u)) ⟩ 
              sub (toSub ρ) (sub δ          (toSub σ S u))  ≡⟨ cong (sub (toSub ρ)) (sym (iso1 S u)) ⟩ 
              sub (toSub ρ) (id-s S u)                      ≡⟨ ren-id (toSub ρ _ u) ⟩ 
              toSub ρ S u                                   ∎
  given (_ , σ , (inj₂ G>G2) , p1) prune's ts (n , n≥length) 
   with under σ prune's ts (n , n≥length) (≤-trans G>G2 n≥length)
  ... | (G2 , ρ2 , ρ2-decr , p2) = G2 ,
                                     ρ2 ∘mr σ ,
                                     decreasing ((DS toSub ρ2 , ρ2-decr) ∘ds (DS toSub σ , inj₂ G>G2)) 
                                   , DClosedMRP ρ2 p1 ∷ step-MRPs σ ts p2

  under_prune's : ∀ {Sg G D1 D2 T} {i : Inj D1 D2} → ∀ {G2} (σ : MetaRen G G2) -> (ts : Tms Sg G D2 T) → 
                ∀ (u : ∃ (\ n -> n ≥ Ctx-length G)) -> proj₁ u > Ctx-length G2 -> 
                Pruner i (subs (toSub σ) ts)
  under σ prune's ts (.(suc n) , _) (s≤s {._} {n} u>smt) = prune's (subs (toSub σ) ts) (n , u>smt)


open import RenOrn

mutual
  lift-pullback : ∀ {X Y Z} {i : Inj X Z}{j : Inj Y Z} (pull : Pullback i j) -> let open Pullback pull in 
                  ∀ {Sg G T} (t : Tm Sg G _ T) s -> ren i t ≡T ren j s -> RTm p₂ s
  lift-pullback pull (con c ts) (con .c ts₁) (con refl eq) = con c (lifts-pullback pull ts ts₁ eq)
  lift-pullback pull (con c ts) (fun u j₁) ()
  lift-pullback pull (con c ts) (var x ts₁) ()
  lift-pullback pull (fun u j₁) (con c ts) ()
  lift-pullback pull (fun u q₁) (fun .u q₂) (fun refl i∘q₁≡j∘q₂) = fun u (universal q₁ q₂ i∘q₁≡j∘q₂) p₂∘universal≡q₂
    where open Pullback pull
  lift-pullback pull (fun u j₁) (var x ts) ()
  lift-pullback pull (var x ts) (con c ts₁) ()
  lift-pullback pull (var x ts) (fun u j₁) ()
  lift-pullback pull (var x ts) (var x₁ ts₁) (var i$x≡j$x₁ eqts) = var (proj₁ r) (proj₂ (proj₂ r)) (lifts-pullback pull ts ts₁ eqts)
    where r = p$u≡q _ _ pull _ x₁ x i$x≡j$x₁ 
  lift-pullback pull (lam t) (lam s) (lam eq) = lam (lift-pullback (cons-pullback _ _ pull) t s eq)

  lifts-pullback : ∀ {X Y Z} {i : Inj X Z}{j : Inj Y Z} (pull : Pullback i j) -> let open Pullback pull in 
                  ∀ {Sg G T} (t : Tms Sg G _ T) s -> rens i t ≡T rens j s -> RTms p₂ s
  lifts-pullback pull [] [] eq = []
  lifts-pullback pull (t ∷ ts) (t₁ ∷ ts₁) (eqt ∷ eqts) = (lift-pullback pull t t₁ eqt) ∷ (lifts-pullback pull ts ts₁ eqts)
 
open import Specification
mutual
  prune-sup : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tm Sg G D2 T) → ∀ l -> 
              ∀ {G2} -> (s : Sub Sg G G2) -> (z : Tm Sg G2 D1 T) -> ren i z ≡T sub s t -> s ≤ toSub (proj₁ (proj₂ (prune' {i = i} t l)))
  prune-sup i (con c ts) l s (con c₁ ts₁) (con _ eq) = prune-sups i ts l s ts₁ eq
  prune-sup i (con c ts) l s (fun u j) ()
  prune-sup i (con c ts) l s (var x ts₁) ()
  prune-sup {Sg} {G} i (fun {Ss = Ss} {B} u j) l {G2} s z eq = δ , s≡δ∘pruner
    where 
      pull = pullback i j
      open Pullback pull
      open Σ (forget (lift-pullback pull z (s (B <<- Ss) u) eq)) renaming
        (proj₁ to x; proj₂ to ren[p₂,x]≡s[u])  
      δ : (S : MTy) → B <<- P ∷ G - u ∋ S → Tm Sg G2 (ctx S) ([] ->> type S)
      δ .(B <<- P) zero = x
      δ S (suc v) = s S (thin u S v)
      s≡δ∘pruner : (S : MTy) (v : G ∋ S) → s S v ≡ sub δ (toSub (singleton u p₂) S v)
      s≡δ∘pruner S v with thick u v 
      s≡δ∘pruner S .(thin u S v) | inj₁ (v , refl) = sym (ren-id _)
      s≡δ∘pruner .(B <<- Ss) .u  | inj₂ refl       = sym ren[p₂,x]≡s[u]
   
  prune-sup i (var x ts) l s (con c ts₁) ()
  prune-sup i (var x ts) l s (fun u j) ()
  prune-sup i (var x ts) l s (var x₁ ts₁) (var eqv eq) = prune-sups i ts l s ts₁ eq
  prune-sup i (lam t) l s (lam z) (lam eq) = prune-sup (cons i) t l s z eq

  prune-sups : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tms Sg G D2 T) → ∀ l ->
              ∀ {G2} -> (s : Sub Sg G G2) -> (z : Tms Sg G2 D1 T) -> rens i z ≡T subs s t -> s ≤ toSub (proj₁ (proj₂ (prune's {i = i} t l)))
  prune-sups i [] l s [] eq = s , (λ S u → sym (ren-id _))
  prune-sups i (t ∷ ts) l s (z ∷ zs) (eqt ∷ eqts) with prune-sup i t l s z eqt 
  ... | (r , s≡r∘ρ) with prune' {i = i} t l 
  ...               | _ , ρ , inj₁ _    , p1 = prune-sups i ts l s zs eqts
  ...               | _ , ρ , inj₂ G>G1 , p1 
   with l              | ≤-trans G>G1 (proj₂ l)    
  ... | (.(suc n) , _) | s≤s {._} {n} n≥G1 
      = ≤-∘ s (toSub ρ) (toSub ρ1) (r , s≡r∘ρ) 
            (prune-sups i (subs (toSub ρ) ts) (n , n≥G1) r zs
             (≡-T
              (begin
                 rens i zs ≡⟨ T-≡ eqts ⟩
                 subs s ts ≡⟨ subs-ext s≡r∘ρ ts ⟩
                 subs (r ∘s toSub ρ) ts ≡⟨ sym (subs-∘ ts) ⟩
                 subs r (subs (toSub ρ) ts) ∎)))
    where
      ρ1 = proj₁ (proj₂ (prune's {i = i} (subs (toSub ρ) ts) (n , n≥G1)))

prune : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tm Sg G D2 T) -> 
              Σ (Pruner i t) \ pr -> 
              ∀ {G2} -> (s : Sub Sg G G2) -> (z : Tm Sg G2 D1 T) -> ren i z ≡T sub s t -> s ≤ toSub (proj₁ (proj₂ pr))
prune i t = prune' t (_ , ≤-refl) , prune-sup i t (_ , ≤-refl) 

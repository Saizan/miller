module Pruning where

open import Data.Product renaming (map to mapΣ)
open import Data.Nat hiding (_≤_) renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.Maybe
open import Category.Monad
import Level
open RawMonad (monad {Level.zero})

open import Injection
open import Injection.Objects
open import Lists

open import Syntax
open import Equality
open import MetaRens

mutual
  _/_∈_ : ∀ {Sg : Ctx} {G1 G2 : MCtx} → Sub Sg G1 G2 → ∀ {D1 D2 : Ctx} → ∀ {T} → Tm Sg G1 D2 T → Inj D1 D2 → Set
  r / con c ts ∈ i = r /s ts ∈ i
  r / fun u j ∈ i = ∃ \ H -> ∃ \ v -> ∃ \ (h : Inj H _) -> r _ u ≡ fun v h × ∃ (λ k → i ∘i k ≡ j ∘i h)
  r / var x ts ∈ i = r /s ts ∈ i
  r / lam t ∈ i = r / t ∈ cons i

  _/s_∈_ : ∀ {Sg : Ctx} {G1 G2 : MCtx} → Sub Sg G1 G2 → ∀ {D1 D2 : Ctx} → ∀ {Ts} → Tms Sg G1 D2 Ts → Inj D1 D2 → Set
  r /s [] ∈ i = ⊤
  r /s (x ∷ ts) ∈ i = r / x ∈ i × r /s ts ∈ i

-- downward closed
mutual
  DClosedMRP : ∀ {Sg G1 G2 G3} (f : MetaRen G2 G3)(g : Sub Sg G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tm Sg G1 D2 T) → g / t ∈ i → (toSub f ∘s g) / t ∈ i
  DClosedMRP f g i (con c ts) m = DClosedMRPs f g i ts m
  DClosedMRP f g i (fun u j) (H , v , k , eq , h , i∘h≡j∘gu) rewrite eq = _ , body (f _ v) , k ∘i fj  , refl , h ∘i fj , 
       (begin i ∘i (h ∘i fj)             ≡⟨ assoc-∘i ⟩ 
              (i ∘i h) ∘i fj             ≡⟨ cong (λ k → k ∘i fj) i∘h≡j∘gu ⟩ 
              (j ∘i k) ∘i fj ≡⟨ sym assoc-∘i ⟩ 
              j ∘i (k ∘i fj) ∎)
    where
      fr = f _ v
      fj = ρ-env fr

  DClosedMRP f g i (var x ts) m = DClosedMRPs f g i ts m
  DClosedMRP f g i (lam t) m = DClosedMRP f g (cons i) t m
  
  DClosedMRPs : ∀ {Sg G1 G2 G3} → (f : MetaRen G2 G3)(g : Sub Sg G1 G2) → ∀ {D1 D2 : Ctx} → (i : Inj D1 D2) ->
               ∀ {T} → (t : Tms Sg G1 D2 T) → g /s t ∈ i → (toSub f ∘s g) /s t ∈ i
  DClosedMRPs f g i [] m = _
  DClosedMRPs f g i (t ∷ ts) (mt , mts) = DClosedMRP f g i t mt , DClosedMRPs f g i ts mts

  step-MRP : ∀ {Sg G1 G2 G3} (f : Sub Sg G2 G3)(g : MetaRen G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tm Sg G1 D2 T) → f / sub (toSub g) t ∈ i → (f ∘s toSub g) / t ∈ i
  step-MRP f g i (con c ts) m = step-MRPs f g i ts m
  step-MRP f g i (fun u j) (H , v , h , eq , k , p) rewrite eq 
    = _ , v , ρ-env (g _ u) ∘i h , refl , k ,
      (begin
             i ∘i k                    ≡⟨ p ⟩
             (j ∘i ρ-env (g _ u)) ∘i h ≡⟨ sym assoc-∘i ⟩
             j ∘i (ρ-env (g _ u) ∘i h) ∎)
  step-MRP f g i (var x ts) m = step-MRPs f g i ts m
  step-MRP f g i (lam t) m = step-MRP f g (cons i) t m
  
  step-MRPs : ∀ {Sg G1 G2 G3} (f : Sub Sg G2 G3)(g : MetaRen G1 G2) {D1 D2 : Ctx} (i : Inj D1 D2) ->
               ∀ {T} → (t : Tms Sg G1 D2 T) → f /s subs (toSub g) t ∈ i  → (f ∘s toSub g) /s t ∈ i
  step-MRPs f g i [] ms = _
  step-MRPs f g i (t ∷ ts) (mt , mts) = step-MRP f g i t mt , step-MRPs f g i ts mts

mutual
  MRP-ext : ∀ {Sg : Ctx} {G1 G2 : MCtx} → (f g : Sub Sg G1 G2) → (∀ S u -> f S u ≡ g S u) -> 
            ∀ {D1 D2 : Ctx} → (i : Inj D1 D2) →  ∀ {T} → (t : Tm Sg G1 D2 T) → f / t ∈ i -> g / t ∈ i
  MRP-ext f g eq i (con c ts) m = MRPs-ext f g eq i ts m
  MRP-ext f g eq i (fun u j) m rewrite eq _ u = m
  MRP-ext f g eq i (var x ts) m = MRPs-ext f g eq i ts m
  MRP-ext f g eq i (lam t) m = MRP-ext f g eq (cons i) t m

  MRPs-ext : ∀ {Sg : Ctx} {G1 G2 : MCtx} → (f g : Sub Sg G1 G2) → (∀ S u -> f S u ≡ g S u) -> 
            ∀ {D1 D2 : Ctx} → (i : Inj D1 D2) →  ∀ {T} → (t : Tms Sg G1 D2 T) → f /s t ∈ i -> g /s t ∈ i
  MRPs-ext f g eq i [] m = _
  MRPs-ext f g eq i (t ∷ ts) (mt , mts) = MRP-ext f g eq i t mt , MRPs-ext f g eq i ts mts

open import DSub

mutual
  
  prune : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tm Sg G D2 T) → ∃ (\ n -> n ≥ Ctx-length G) 
            -> ∃ \ G1 → Σ (MetaRen G G1) \ ρ → Decreasing {Sg} (toSub ρ) × toSub ρ / t ∈ i
  prune i (con c ts) l = prunes i ts l
  prune i (fun u j) l = _ , (singleton u p₂ , decr , _ , _ , _ , refl , aux) where
    open Pullback (pullback i j)
    aux : ∃ (λ k → i ∘i k ≡ j ∘i ρ-env (singleton u p₂ _ u))
    aux rewrite thick-refl u = p₁ , commutes
    decr = singleton-Decreasing p₂ u (pullback-Decr i j)
  prune i (var x ts) l = prunes i ts l
  prune i (lam t) l = prune (cons i) t l

  prunes : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tms Sg G D2 T) → ∃ (\ n -> n ≥ Ctx-length G) 
           -> ∃ \ G1 → Σ (MetaRen G G1) \ ρ → Decreasing (toSub ρ) × toSub ρ /s t ∈ i
  prunes {Sg}{G} i [] _ = G , idmr , inj₁ (refl , IsIso-id) , tt
  prunes i (t ∷ ts) l = helper-pur i t ts l (prune i t l)

  helper-pur : ∀ {Sg G D1 D2 T Ts } → (i : Inj D1 D2) → (t : Tm Sg G D2 T)(ts : Tms Sg G D2 Ts) → ∃ (\ n -> n ≥ Ctx-length G) 
               -> (∃ \ G1 → Σ (MetaRen G G1) \ ρ → Decreasing {Sg} (toSub ρ) × toSub ρ / t ∈ i)
               -> ∃ \ G1 → Σ (MetaRen G G1) \ ρ → Decreasing {Sg} (toSub ρ) × toSub ρ /s (t ∷ ts) ∈ i

  helper-pur i t ts l (_ , σ , (inj₁ (eq , (δ , iso1) , iso2)) , p1) with prunes i ts l 
  ... | (G1 , ρ , ρ-decr , p) 
    = G1 , ρ , ρ-decr ,
        MRP-ext (toSub (ρ ∘mr δ') ∘s toSub σ) (toSub ρ)
        (λ S u →
           trans
           (cong (λ i₁ → fun (body (((ρ ∘mr δ') ∘mr σ) _ u)) i₁) assoc-∘i)
           (sym
            (trans (sym (ren-id (toSub ρ _ u)))
             (cong (sub (toSub ρ))
              (trans (iso1 S u) (sym (sub-ext δ≡δ' (toSub σ _ u))))))))
        i t (DClosedMRP (ρ ∘mr δ') (toSub σ) i t p1)
        , p
    where δ' = proj₁ (toMRen δ ((toSub σ) , iso2))
          δ≡δ' = proj₂ (toMRen δ ((toSub σ) , iso2))
  helper-pur i t ts (n , n≥length) (_ , σ , (inj₂ G>G2) , p1) with 
             let open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎) in  
               helper-pur2 i ts σ (n , n≥length) (≤-begin _ ≤⟨ G>G2 ⟩ _ ≤⟨ n≥length ⟩ (_ ≤-∎))
  ... | (G2 , ρ2 , ρ2-decr , p2) = G2 ,
                                     ρ2 ∘mr σ ,
                                     decreasing ((DS toSub ρ2 , ρ2-decr) ∘ds (DS toSub σ , inj₂ G>G2)) 
                                   , DClosedMRP ρ2 (toSub σ) i t p1 , step-MRPs (toSub ρ2) σ i ts p2

  helper-pur2 : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tms Sg G D2 T) → 
             ∀ {G2} (σ : MetaRen G G2) -> ∀ (u : ∃ (\ n -> n ≥ Ctx-length G)) -> proj₁ u > Ctx-length G2 -> 
             ∃ \ G1 → Σ (MetaRen G2 G1) \ ρ → Decreasing {Sg} (toSub ρ) × toSub ρ /s (subs (toSub σ) t) ∈ i
  helper-pur2 i t σ (.(suc n) , _) (s≤s {._} {n} u>smt) = prunes i (subs (toSub σ) t) (n , u>smt)


open import RenOrn

mutual
  lift-pullback : ∀ {X Y Z} {i : Inj X Z}{j : Inj Y Z} (pull : Pullback i j) -> let open Pullback pull in 
                  ∀ {Sg G T} (t : Tm Sg G _ T) s -> (ren i t) ≡T (ren j s) -> RTm Sg G P Y p₂ _ s
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
                  ∀ {Sg G T} (t : Tms Sg G _ T) s -> (rens i t) ≡T (rens j s) -> RTms Sg G P Y p₂ _ s
  lifts-pullback pull [] [] eq = []
  lifts-pullback pull (t ∷ ts) (t₁ ∷ ts₁) (eqt ∷ eqts) = (lift-pullback pull t t₁ eqt) ∷ (lifts-pullback pull ts ts₁ eqts)
 
mutual
  prune-gen : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tm Sg G D2 T) → ∀ l -> 
              ∀ {G2} -> (s : Sub Sg G G2) -> (z : Tm Sg G2 D1 T) -> ren i z ≡T sub s t -> s ≤ toSub (proj₁ (proj₂ (prune i t l)))
  prune-gen i (con c ts) l s (con c₁ ts₁) (con _ eq) = prune-gens i ts l s ts₁ eq
  prune-gen i (con c ts) l s (fun u j) ()
  prune-gen i (con c ts) l s (var x ts₁) ()
  prune-gen {Sg} {G} i (fun {Ss = Ss} {B} u j) l {G2} s z eq = dif , proof
    where 
      pull = pullback i j
      open Pullback pull
      uniT = forget (lift-pullback pull z (s (B <<- Ss) u) eq)
      dif : (S₁ : MTy) → B <<- P ∷ G - u ∋ S₁ → Tm Sg G2 (ctx S₁) ([] ->> type S₁)
      dif .(B <<- P) zero = proj₁ uniT
      dif S₁ (suc v) = s S₁ (thin u S₁ v)
      proof : (S₁ : MTy) (u₁ : G ∋ S₁) → s S₁ u₁ ≡ ren (ρ-env (singleton u p₂ S₁ u₁))
                                                         (dif _ (body (singleton u p₂ S₁ u₁)))
      proof S₁ u₁ with thick u u₁ 
      proof S₁ .(thin u S₁ v) | inj₁ (v , refl) = sym (ren-id _)
      proof ._ ._ | inj₂ refl = sym ((proj₂ uniT))
   
  prune-gen i (var x ts) l s (con c ts₁) ()
  prune-gen i (var x ts) l s (fun u j) ()
  prune-gen i (var x ts) l s (var x₁ ts₁) (var eqv eq) = prune-gens i ts l s ts₁ eq
  prune-gen i (lam t) l s (lam z) (lam eq) = prune-gen (cons i) t l s z eq

  prune-gens : ∀ {Sg G D1 D2 T} → (i : Inj D1 D2) → (t : Tms Sg G D2 T) → ∀ l ->
              ∀ {G2} -> (s : Sub Sg G G2) -> (z : Tms Sg G2 D1 T) -> eqT (rens i z) (subs s t) -> s ≤ toSub (proj₁ (proj₂ (prunes i t l)))
  prune-gens i [] l s [] eq = s , (λ S u → sym (ren-id _))
  prune-gens i (t ∷ ts) l s (z ∷ zs) (eqt ∷ eqts) with prune-gen i t l s z eqt 
  ... | (r , s≡r∘ρ) with prune i t l 
  prune-gens i (t ∷ ts) l s (z ∷ zs) (eqt ∷ eqts) | r , s≡r∘ρ | proj₁ , σ , inj₁ x , p1 = prune-gens i ts l s zs eqts
  prune-gens i (t ∷ ts) (n , n≥length) s (z ∷ zs) (eqt ∷ eqts) | r , s≡r∘ρ | proj₁ , σ , inj₂ y , p1 with
    let open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎) in  
               (≤-begin _ ≤⟨ y ⟩ _ ≤⟨ n≥length ⟩ (_ ≤-∎)) 
  prune-gens i (t ∷ ts) (.(suc n) , n≥length) s (z ∷ zs) (eqt ∷ eqts) | r , s≡r∘ρ | _ , σ , inj₂ y , p1 | s≤s {._} {n} ww 
   with prune-gens i (subs (toSub σ) ts) (n , ww) r zs (≡-T (trans (T-≡ eqts) 
                         (trans (subs-ext s≡r∘ρ ts) (sym (subs-∘ ts)))))
  ... | (r1 , r≡r1∘ρ1) = r1 , (λ S u → trans (s≡r∘ρ S u) (trans (sub-ext r≡r1∘ρ1 (toSub ρ S u)) (sym (sub-∘ {f = r1} {g = toSub ρ1} (toSub ρ S u)))))
    where
      ρ = σ
      ρ1 = proj₁ (proj₂ (prunes i (subs (toSub ρ) ts) (n , ww)))




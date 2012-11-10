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
open import RenOrn
open import MetaRens
open import DSub
open import Specification

data AllMV∈  {Sg : Ctx} {G : MCtx} {D0 D : Ctx} (i : Inj D0 D) : ∀ {T} → Term Sg G D T → Set where
  [] : AllMV∈ i {inj₂ []} []
  _∷_ : ∀ {S Ss t ts} → (m : AllMV∈ i {inj₁ S} t) → (ms : AllMV∈ i {inj₂ Ss} ts) → AllMV∈ i {inj₂ (S ∷ Ss)} (t ∷ ts)
  con : ∀ {Ss B c ts} → (ms : AllMV∈ i {inj₂ Ss} ts) → AllMV∈ i {inj₁ (! B)} (con c ts)
  var : ∀ {Ss B x ts} → (ms : AllMV∈ i {inj₂ Ss} ts) → AllMV∈ i {inj₁ (! B)} (var x ts)
  lam : ∀ {S Ss B t} → (m : AllMV∈ (cons i) {inj₁ (Ss ->> B)} t) → AllMV∈ i {inj₁ ((S ∷ Ss) ->> B)} (lam t)
  fun : ∀ {Ss B} {v : G ∋ (B <<- Ss)}{h} → (∃ \ k → i ∘i k ≡ h) → AllMV∈ i {inj₁ (! B)} (fun v h)

-- s / t ∈ i holds iff all the variables appearing as arguments to
-- meta-vars in (sub s t) are present in the image of i
_/_∈_ : ∀ {Sg G1 G2 D1 D2 T} → Sub Sg G1 G2 → Term Sg G1 D2 T → Inj D1 D2 → Set
_/_∈_ s t i = AllMV∈ i (subT s t)

-- (\ s -> s / t ∈ i) is closed under pre-composition, we'll need this in the _∷_ case of prune.
_/_∈_-∘Closed : ∀ {Sg G1 G2 G3 D1 D2 T} (f : Sub Sg G2 G3) {g : Sub Sg G1 G2} {i : Inj D1 D2} →
                ∀ {t : Term Sg G1 D2 T} → g / t ∈ i → (f ∘s g) / t ∈ i
_/_∈_-∘Closed f m = subst (AllMV∈ _) (subT-∘ _) (go f m) where
  mutual
    go2 : ∀ {Sg G X Y Z T} {i : Inj Y Z} {h : Inj X Z} → (∃ \ k → i ∘i k ≡ h) → 
          (t : Tm Sg G X T) → AllMV∈ i (renT h t)
    go2 le (con c ts) = con (go2s le ts)
    go2 le (var x ts) = var (go2s le ts)
    go2 (k , i∘k≡h) (lam t)   = lam (go2 (cons k , trans (sym (cons-∘i _ _)) (cong cons i∘k≡h)) t)
    go2 (k , i∘k≡h) (fun u j) = fun (k ∘i j , trans assoc-∘i (cong (λ h → h ∘i j) i∘k≡h))
  
    go2s : ∀ {Sg G X Y Z T} {i : Inj Y Z}{h : Inj X Z} → (∃ \ k → i ∘i k ≡ h) → 
           (t : Tms Sg G X T) → AllMV∈ i (renT h t)
    go2s le [] = []
    go2s le (t ∷ ts) = go2 le t ∷ go2s le ts

  go : ∀ {Sg G1 G3 D1 D2 T} (f : Sub Sg G1 G3) {i : Inj D1 D2} →
       {t : Term Sg G1 D2 T} → AllMV∈ i t → f / t ∈ i
  go f [] = []
  go f (m ∷ ms) = go f m ∷ go f ms
  go f (con ms) = con (go f ms)
  go f (var ms) = var (go f ms)
  go f (lam m) = lam (go f m)
  go f {i = i} (fun {v = v} {h = h} (k , i∘k≡h)) = go2 (k , i∘k≡h) (f _ v)

   
-- A few properties of substitutions that carry over to _/_∈_
_/_∈_-∘ : ∀ {Sg G1 G2 G3 D1 D2 T} {f : Sub Sg G2 G3} (g : Sub Sg G1 G2) {i : Inj D1 D2} →
          ∀ (t : Term Sg G1 D2 T) → f / subT g t ∈ i → (f ∘s g) / t ∈ i
_/_∈_-∘ g t m = subst (AllMV∈ _) (subT-∘ _) m

_/_∈_-ext : ∀ {Sg G G1 D1 D2 T} {i : Inj D1 D2} {f g : Sub Sg G G1} → 
            f ≡s g → ∀ {t : Term Sg G D2 T} → f / t ∈ i → g / t ∈ i
_/_∈_-ext f≡g m = subst (AllMV∈ _) (subT-ext f≡g _) m 


-- In the flexible-rigid case we'll need to find z and ρ such that ren i z ≡ sub ρ t, 
-- this module is about finding such a ρ, which we call the pruner.
-- Its role is to handle occurrences in t like (fun u j) where there are variables in j 
-- which are not in i: ρ will substitute u with a term that ignores them, 
-- since their presence would make finding z impossible.
record Pruner {Sg G D1 D2 T} (i : Inj D1 D2) (t : Term Sg G D2 T) : Set where
  constructor Pr_,_,_
  field
    {G1} : MCtx
    pruner : Sub Sg G G1
    decr : Decreasing {Sg} (pruner)
    prunes : pruner / t ∈ i

open Pruner using (pruner)

_∙_ : ∀ {Sg G D1 D2 T} → {i : Inj D1 D2} {t : Term Sg G D2 T} →
      ∀      {D1 D2 T} → {j : Inj D1 D2} {s : Term Sg G D2 T} →
      (∀ {G1}{σ : Sub Sg G G1} → σ / t ∈ i → σ / s ∈ j) → Pruner i t → Pruner j s
f ∙ (Pr ρ , ρ-decr , m) = Pr ρ , ρ-decr , f m

-- The computation of a Pruner would be straightforward, with (fun u j)
-- the only interesting case, but we have some trouble with showing
-- termination.
-- In the (t ∷ ts) case, having found the pruner σ of t, we need to
-- recurse on (subs σ ts), which is not structurally smaller than (t ∷ ts): 
-- we work around this issue by using the size of the meta-context
-- as a measure that pruners decrease unless they are isomorphisms.
-- Agda's termination checker accepts the definition because we
-- simultaneously recurse on (an upper bound of) this size and the
-- structure of terms.
mutual
  prune' : ∀ {Sg G D1 D2 T} {i : Inj D1 D2} (t : Tm Sg G D2 T) 
           → ∃ (\ n → n ≥ Ctx-length G) → Pruner i t
  -- congruence cases
  prune' (con c ts) l = con ∙ prune's ts l
  prune' (var x ts) l = var ∙ prune's ts l
  prune' (lam t)    l = lam ∙ prune'  t  l

  prune' {i = i} (fun u j) l = Pr (toSub (singleton u p₂)) , decr , fun aux where
    open Pullback (pullback i j)
    -- (toSub (singleton u p₂)) (fun u j) = fun zero (j ∘i p₂), so we
    -- need aux to show that (j ∘i p₂) only contains variables in i
    aux : ∃ \ k → i ∘i k ≡ j ∘i ρ-env (singleton u p₂ _ u)
    aux rewrite thick-refl u = p₁ , commutes
    decr = singleton-Decreasing p₂ u (pullback-Decr i j)

  prune's : ∀ {Sg G D1 D2 T} {i : Inj D1 D2} (t : Tms Sg G D2 T) 
            → ∃ (\ n → n ≥ Ctx-length G) → Pruner i t
  prune's []       _ = Pr id-s , inj₁ (refl , IsIso-id) , []
  prune's (t ∷ ts) l = given t , prune' t l prune's ts l

  given_,_prune's  : ∀ {Sg G D1 D2 T Ts} {i : Inj D1 D2} (t : Tm Sg G D2 T) → Pruner i t 
                     → (ts : Tms Sg G D2 Ts) → ∃ (\ n → n ≥ Ctx-length G) → Pruner i (t ∷ ts)
  given t , (Pr σ , (inj₁ (eq , (δ , iso1) , iso2)) , p0) prune's ts l with prune's ts l 
  ... | Pr ρ , ρ-decr , p 
      = Pr ρ , ρ-decr , (_/_∈_-ext ρ∘δ∘σ≡ρ {t = t} (_/_∈_-∘Closed (ρ ∘s δ) {t = t} p0) ∷ p)
    where
      ρ∘δ∘σ≡ρ : ∀ S u → ((ρ ∘s δ) ∘s σ) S u ≡ ρ S u 
      ρ∘δ∘σ≡ρ S u = begin ((ρ ∘s δ) ∘s σ) S u   ≡⟨ sym (sub-∘ (σ S u)) ⟩ 
                          sub ρ (sub δ (σ S u)) ≡⟨ cong (sub ρ) (sym (iso1 _ _)) ⟩ 
                          sub ρ (id-s S u)      ≡⟨ ren-id _ ⟩ 
                          ρ S u                 ∎ 
  given t , (Pr σ , (inj₂ G>G2) , p0) prune's ts (n , n≥length) 
   with under σ prune's ts (n , n≥length) (≤-trans G>G2 n≥length)
  ... | (Pr ρ , ρ-decr , p) = Pr (ρ ∘s σ)
                                 , decreasing ((DS ρ , ρ-decr) ∘ds (DS σ , inj₂ G>G2)) 
                                 , (_/_∈_-∘Closed ρ {t = t} p0 ∷ _/_∈_-∘ σ ts p)

  under_prune's : ∀ {Sg G D1 D2 T} {i : Inj D1 D2} {G2} (σ : Sub Sg G G2) (ts : Tms Sg G D2 T) → 
                  ∀ (u : ∃ (\ n → n ≥ Ctx-length G)) → proj₁ u > Ctx-length G2 → Pruner i (subs σ ts)
  under σ prune's ts (.(suc n) , _) (s≤s {._} {n} u>smt) = prune's (subs σ ts) (n , u>smt)


mutual
  lift-pullback : ∀ {X Y Z} {i : Inj X Z}{j : Inj Y Z} (pull : Pullback i j) → let open Pullback pull in 
                  ∀ {Sg G T} (t : Tm Sg G _ T) s → ren i t ≡T ren j s → p₂ ⁻¹ s
  lift-pullback pull (con c ts) (fun u j₁) ()
  lift-pullback pull (con c ts) (var x ts₁) ()
  lift-pullback pull (fun u j₁) (con c ts) ()
  lift-pullback pull (fun u j₁) (var x ts) ()
  lift-pullback pull (var x ts) (con c ts₁) ()
  lift-pullback pull (var x ts) (fun u j₁) ()

  lift-pullback pull (con c ts) (con .c ts₁) (con refl eq) = con c (lifts-pullback pull ts ts₁ eq)
  lift-pullback pull (lam t)    (lam s)      (lam eq)      = lam (lift-pullback (cons-pullback _ _ pull) t s eq)
  lift-pullback pull (fun u q₁) (fun .u q₂)  (fun refl i∘q₁≡j∘q₂) = fun u (universal q₁ q₂ i∘q₁≡j∘q₂) p₂∘universal≡q₂
    where open Pullback pull
  lift-pullback pull (var x ts) (var x₁ ts₁) (var i$x≡j$x₁ eqts) = var (proj₁ r) (proj₂ (proj₂ r)) (lifts-pullback pull ts ts₁ eqts)
    where r = p$u≡q _ _ pull _ x₁ x i$x≡j$x₁ 

  lifts-pullback : ∀ {X Y Z} {i : Inj X Z}{j : Inj Y Z} (pull : Pullback i j) → let open Pullback pull in 
                  ∀ {Sg G T} (t : Tms Sg G _ T) s → rens i t ≡T rens j s → p₂ ⁻¹ s
  lifts-pullback pull []       []         eq           = []
  lifts-pullback pull (t ∷ ts) (t₁ ∷ ts₁) (eqt ∷ eqts) = (lift-pullback pull t t₁ eqt) ∷ (lifts-pullback pull ts ts₁ eqts)

-- prune-sup makes use of the universal property of pullbacks to prove
-- that the pruner computed above is more general than any possible
-- solution to the equation runT i z ≡ sub s t from which we started.
mutual
  prune-sup : ∀ {Sg G D1 D2 T} (i : Inj D1 D2) (t : Tm Sg G D2 T) l → 
              ∀ {G1} (s : Sub Sg G G1) z → ren i z ≡T sub s t → s ≤ (pruner (prune' {i = i} t l))
  prune-sup i (con c ts) l s (con c₁ ts₁) (con _ eq)   = prune-sups i ts l s ts₁ eq
  prune-sup i (var x ts) l s (var x₁ ts₁) (var eqv eq) = prune-sups i ts l s ts₁ eq
  prune-sup i (lam t)    l s (lam z)      (lam eq)     = prune-sup (cons i) t l s z eq

  prune-sup i (con c ts) l s (fun u j) ()
  prune-sup i (con c ts) l s (var x ts₁) ()
  prune-sup i (var x ts) l s (con c ts₁) ()
  prune-sup i (var x ts) l s (fun u j) ()

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
   

  prune-sups : ∀ {Sg G D1 D2 T} (i : Inj D1 D2) (t : Tms Sg G D2 T) l →
               ∀ {G1} (s : Sub Sg G G1) z → rens i z ≡T subs s t → s ≤ (pruner (prune's {i = i} t l))
  prune-sups i []       l s []       eq           = s , (λ S u → sym (ren-id _))
  prune-sups i (t ∷ ts) l s (z ∷ zs) (eqt ∷ eqts) 
   with prune' {i = i} t l | prune-sup i t l s z eqt 
  ... | Pr ρ , inj₁ _    , p1 | _           = prune-sups i ts l s zs eqts
  ... | Pr ρ , inj₂ G>G1 , p1 | (δ , s≡δ∘ρ) 
   with l              | ≤-trans G>G1 (proj₂ l)    
  ... | (.(suc n) , _) | s≤s {._} {n} n≥G1 
      = ≤-∘ s ρ ρ1 (δ , s≡δ∘ρ) 
            (prune-sups i (subs ρ ts) (n , n≥G1) δ zs
             (≡-T
              (begin
                 rens i zs          ≡⟨ T-≡ eqts ⟩
                 subs s ts          ≡⟨ subs-ext s≡δ∘ρ ts ⟩
                 subs (δ ∘s ρ) ts   ≡⟨ sym (subs-∘ ts) ⟩
                 subs δ (subs ρ ts) ∎)))
    where
      ρ1 = pruner (prune's {i = i} (subs ρ ts) (n , n≥G1))

prune : ∀ {Sg G D1 D2 T} (i : Inj D1 D2) (t : Tm Sg G D2 T) →
        Σ (Pruner i t) λ pr → ∀ {G1} (s : Sub Sg G G1) z → ren i z ≡T sub s t → s ≤ (pruner pr)
prune i t = prune' t (_ , ≤-refl) , prune-sup i t (_ , ≤-refl)


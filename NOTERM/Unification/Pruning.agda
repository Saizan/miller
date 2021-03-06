module NOTERM.Unification.Pruning where

open import Data.Empty
open import Data.Sum

open import Support.Equality
open ≡-Reasoning

open import Injections
open import MetaRens

open import Syntax

open import NOTERM.Unification.Specification
open import Unification.MetaRens
open import Unification.Injections
open import Unification.Pruning.Epi-Decr

data AllMV∈  {Sg : Ctx} {G : MCtx} {D0 D : Ctx} (i : Inj D0 D) : ∀ {T} → Term Sg G D T → Set where
  [] : AllMV∈ i {inj₂ []} []
  _∷_ : ∀ {S Ss t ts} → (m : AllMV∈ i {inj₁ S} t) → (ms : AllMV∈ i {inj₂ Ss} ts) → AllMV∈ i {inj₂ (S ∷ Ss)} (t ∷ ts)
  con : ∀ {Ss B c ts} → (ms : AllMV∈ i {inj₂ Ss} ts) → AllMV∈ i {inj₁ (! B)} (con c ts)
  var : ∀ {Ss B x ts} → (ms : AllMV∈ i {inj₂ Ss} ts) → AllMV∈ i {inj₁ (! B)} (var x ts)
  lam : ∀ {S Ss B t} → (m : AllMV∈ (cons i) {inj₁ (Ss ->> B)} t) → AllMV∈ i {inj₁ ((S ∷ Ss) ->> B)} (lam t)
  mvar : ∀ {Ss B} {v : G ∋ (B <<- Ss)}{h} → (∃ \ k → i ∘i k ≡ h) → AllMV∈ i {inj₁ (! B)} (mvar v h)

-- s / t ∈ i holds iff all the variables appearing as arguments to
-- meta-vars in (sub s t) are present in the image of i
_/_∈_ : ∀ {Sg G1 G2 D1 D2 T} → Sub Sg G1 G2 → Term Sg G1 D2 T → Inj D1 D2 → Set
_/_∈_ s t i = AllMV∈ i (subT s t)

-- (\ s -> s / t ∈ i) is closed under post-composition, we'll need this in the _∷_ case of prune.
_/_∈_-∘Closed : ∀ {Sg G1 G2 G3 D1 D2 T} (f : Sub Sg G2 G3) {g : Sub Sg G1 G2} {i : Inj D1 D2} →
                ∀ {t : Term Sg G1 D2 T} → g / t ∈ i → (f ∘s g) / t ∈ i
_/_∈_-∘Closed f m = subst (AllMV∈ _) (subT-∘ _) (go f m) where
  mutual
    go2 : ∀ {Sg G X Y Z T} {i : Inj Y Z} {h : Inj X Z} → (∃ \ k → i ∘i k ≡ h) → 
          (t : Tm Sg G X T) → AllMV∈ i (renT h t)
    go2 le (con c ts) = con (go2s le ts)
    go2 le (var x ts) = var (go2s le ts)
    go2 (k , i∘k≡h) (lam t)    = lam (go2 (cons k , trans (sym (cons-∘i _ _)) (cong cons i∘k≡h)) t)
    go2 (k , i∘k≡h) (mvar u j) = mvar (k ∘i j , trans assoc-∘i (cong (λ h → h ∘i j) i∘k≡h))
  
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
  go f {i = i} (mvar {v = v} {h = h} (k , i∘k≡h)) = go2 (k , i∘k≡h) (f _ v)

   
-- A few properties of substitutions respected by _/_∈_
_/_∈_-∘ : ∀ {Sg G1 G2 G3 D1 D2 T} {f : Sub Sg G2 G3} (g : Sub Sg G1 G2) {i : Inj D1 D2} →
          ∀ (t : Term Sg G1 D2 T) → f / subT g t ∈ i → (f ∘s g) / t ∈ i
_/_∈_-∘ g t m = subst (AllMV∈ _) (subT-∘ _) m

_/_∈_-ext : ∀ {Sg G G1 D1 D2 T} {i : Inj D1 D2} {f g : Sub Sg G G1} → 
            f ≡s g → ∀ {t : Term Sg G D2 T} → f / t ∈ i → g / t ∈ i
_/_∈_-ext f≡g {t} m = subst (AllMV∈ _) (subT-ext f≡g t) m 

-- In the flexible-rigid case we'll need to find z and ρ such that ren i z ≡ sub ρ t, 
-- this module is about finding such a ρ, which we call the pruner.
-- Its role is to handle occurrences in t like (mvar u j) where there are variables in j 
-- which are not in i: ρ will substitute u with a term that ignores them, 
-- since their presence would make finding z impossible.
record Pruner {Sg G D1 D2 T} (i : Inj D1 D2) (t : Term Sg G D2 T) : Set where
  constructor Pr_,_
  field
    {G1} : MCtx
    pruner : MetaRen G G1
    prunes : toSub pruner / t ∈ i

record PrunerSub {Sg G D1 D2 T} (i : Inj D1 D2) (t : Term Sg G D2 T) : Set where
  constructor Pr_,_
  field
    {G1} : MCtx
    pruner : Sub Sg G G1
    prunes : pruner / t ∈ i

open Pruner using (pruner; prunes)

_∙_ : ∀ {Sg G D1 D2 T} → {i : Inj D1 D2} {t : Term Sg G D2 T} →
      ∀      {D1 D2 T} → {j : Inj D1 D2} {s : Term Sg G D2 T} →
      (∀ {G1}{σ : Sub Sg G G1} → σ / t ∈ i → σ / s ∈ j) → Pruner i t → Pruner j s
f ∙ (Pr ρ , m) = Pr ρ , f m

mutual
  prune' : ∀ {Sg G D1 D2 T} {i : Inj D1 D2} (t : Tm Sg G D2 T) 
            → Pruner i t
  -- congruence cases
  prune' (con c ts) = con ∙ prune's ts
  prune' (var x ts) = var ∙ prune's ts
  prune' (lam t)    = lam ∙ prune'  t 

  prune' {i = i} (mvar u j) = Pr singleton u p₂ , mvar aux where
    open Pullback (pullback i j)
    -- (toSub (singleton u p₂)) (mvar u j) = mvar zero (j ∘i p₂), so we
    -- need aux to show that (j ∘i p₂) only contains variables in i
    aux : ∃ \ k → i ∘i k ≡ j ∘i ρ-env (singleton u p₂ _ u)
    aux rewrite thick-refl u = p₁ , commutes

  prune's : ∀ {Sg G D1 D2 T} {i : Inj D1 D2} (t : Tms Sg G D2 T) 
            → Pruner i t
  prune's         []       = Pr idmr , []
  prune's {i = i} (t ∷ ts) = Pr p₁ ∘mr pruner pr-t , (prunes[t] ∷ prunes[ts])
   where
     pr-t = prune' {i = i} t
     pr-ts = prune's {i = i} ts
     push = (pushout (pruner pr-t) (pruner pr-ts))
     open Mixed.Pushout push
     prunes[t]  = _/_∈_-∘Closed (toSub p₁) {toSub (pruner pr-t)} {i} {t} (prunes pr-t) 
     prunes[ts] = _/_∈_-ext {f = toSub (p₂ ∘mr pruner pr-ts)} (λ S u → ↓↓-inj (sym ([]eq commutes S u)))
                            (_/_∈_-∘Closed (toSub p₂) {_} {i} {ts} (prunes pr-ts)) 


-- prune-sup makes use of the universal property of pullbacks to prove
-- that the pruner computed above is more general than any possible
-- solution to the equation runT i z ≡ sub s t from which we started.
mutual
  prune-sup : ∀ {Sg G D1 D2 T} (i : Inj D1 D2) (t : Tm Sg G D2 T)  → 
              ∀ {G1} (s : Sub< false > Sg G G1) z → ren i z ≡T sub s t → s ≤ toSub (pruner (prune' {i = i} t))
  prune-sup i (con c ts) s (con c₁ ts₁) (con _ eq)   = prune-sups i ts s ts₁ eq
  prune-sup i (var x ts) s (var x₁ ts₁) (var eqv eq) = prune-sups i ts s ts₁ eq
  prune-sup i (lam t)    s (lam z)      (lam eq)     = prune-sup (cons i) t s z eq

  prune-sup i (con c ts) s (mvar u j) ()
  prune-sup i (con c ts) s (var x ts₁) ()
  prune-sup i (var x ts) s (con c ts₁) ()
  prune-sup i (var x ts) s (mvar u j) ()

  prune-sup {Sg} {G} i (mvar {Ss = Ss} {B} u j) {G2} s z eq = δ , s≡δ∘pruner
    where 
      pull = pullback i j
      open Pullback pull
      open Σ (forget (lift-pullback pull z (s (B <<- Ss) u) eq)) renaming
        (proj₁ to x; proj₂ to ren[p₂,x]≡s[u])  
      δ : (S : MTy) → B <<- P ∷ G - u ∋ S → Tm< false > Sg G2 (ctx S) ([] ->> type S)
      δ .(B <<- P) zero = x
      δ S (suc v) = s S (thin u S v)
      s≡δ∘pruner : (S : MTy) (v : G ∋ S) → s S v ≡ sub δ (toSub (singleton u p₂) S v)
      s≡δ∘pruner S v with thick u v 
      s≡δ∘pruner S .(thin u S v) | inj₁ (v , refl) = sym (ren-id _)
      s≡δ∘pruner .(B <<- Ss) .u  | inj₂ refl`      = sym ren[p₂,x]≡s[u]
   

  prune-sups : ∀ {Sg G D1 D2 T} (i : Inj D1 D2) (t : Tms Sg G D2 T) →
               ∀ {G1} (s : Sub< false > Sg G G1) z → rens i z ≡T subs s t → s ≤ toSub (pruner (prune's {i = i} t))
  prune-sups i []       s []       eq           = s , (λ S u → sym (ren-id _))
  prune-sups {Sg} {G} i (t ∷ ts) s (z ∷ zs) (eqt ∷ eqts) = down uni , (λ S u →
     begin
       s S u                                               ≡⟨ proj₂ s≤pr-t S u ⟩
       (proj₁ s≤pr-t ∘s toSub (pruner pr-t)) S u           ≡⟨ sub-ext (λ S₁ u₁ → sym (uni∘p₁≡q₁ S₁ u₁)) (toSub (pruner pr-t) S u) ⟩ 
       ((down uni ∘s toSub p₁) ∘s toSub (pruner pr-t)) S u ≡⟨ sym (Sub∘.subT-∘ {f = down uni} {g = toSub p₁}
                                                                           (toSub (pruner pr-t) S u)) ⟩ 
       (down uni ∘s (toSub p₁ ∘s toSub (pruner pr-t))) S u ∎)
   where
     pr-t = prune' {i = i} t 
     pr-ts = prune's {i = i} ts 
     push = pushout (pruner pr-t) (pruner pr-ts)
     open Mixed.Pushout {Sg} push
     s≤pr-t : s ≤ toSub (pruner (prune' {i = i} t))
     s≤pr-t = prune-sup i t s z eqt
     s≤pr-ts : s ≤ toSub (pruner (prune's {i = i} ts))
     s≤pr-ts = prune-sups i ts s zs eqts
     eq = ES (λ S u → cong ↓↓ (trans (sym (proj₂ s≤pr-t S u)) (proj₂ s≤pr-ts S u)))
     uni = (ESub.⟦ universal (ι (proj₁ s≤pr-t)) (ι (proj₁ s≤pr-ts)) eq ⟧)
     uni∘p₁≡q₁ : (down uni ∘s toSub p₁) ≡s proj₁ s≤pr-t
     uni∘p₁≡q₁ = \ S u -> trans (≅-to-≡ (↓↓-comm uni (toSub p₁ S u))) 
                                ([]eq (p₁∘universal≡q₁ {q₁ = ι (proj₁ s≤pr-t)} {q₂ = ι (proj₁ s≤pr-ts)} {eq}) S u)

prune : ∀ {Sg G D1 D2 T} (i : Inj D1 D2) (t : Tm Sg G D2 T) →
        Σ (PrunerSub i t) λ pr → ∀ {G1} (s : Sub< false > Sg G G1) z → ren i z ≡T sub s t → s ≤ PrunerSub.pruner pr
prune i t = (Pr toSub (pruner pr) , prunes pr) , prune-sup i t
  where
    pr = prune' {i = i} t


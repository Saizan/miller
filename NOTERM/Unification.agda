module NOTERM.Unification where

open import Data.Nat hiding (_≤_)
open import Relation.Binary
open DecTotalOrder Data.Nat.decTotalOrder 
  using () renaming (refl to ≤-refl; trans to ≤-trans)         
open import Data.Empty
open import Data.Sum renaming (inj₁ to yes; inj₂ to no; map to map⊎)

open import Support.Equality
open ≡-Reasoning

open import Injections
open import MetaRens

open import Syntax

open import NOTERM.Unification.Specification
open import Unification.MetaRens
open import Unification.Injections
open import Unification.OccursCheck
open import NOTERM.Unification.Pruning
open import NOTERM.Unification.Inversion


flexSame : ∀ {Sg G D S} → (u : G ∋ S) → (i j : Inj (ctx S) D) → ∃σ-pat Max (Unifies {Sg} (Tm.mvar u i) (mvar u j))
flexSame {Sg} {G} {D} {B <<- Ss} u i j = _ , σ 
                                           , [σ]Unifies[mvar[u,i],mvar[u,j]] 
                                           , sup-σ
  where
    i,j⇒e = equalizer i j
    open Equalizer i,j⇒e

    σ = toSub (singleton u e)

    [σ]Unifies[mvar[u,i],mvar[u,j]] : ren i (σ _ u) ≡T ren j (σ _ u)
    [σ]Unifies[mvar[u,i],mvar[u,j]] rewrite thick-refl u = ≡-T (cong (mvar zero) commutes)

    sup-σ : Sup (Unifies (mvar u i) (mvar u j)) σ
    sup-σ {G'} ρ ρ-unifies = δ , ρ≡δ∘σ where

      ∃s[ren[e,s]≡ρ[u]] = forget (lift-equalizer i,j⇒e (ρ (B <<- Ss) u) ρ-unifies)
  
      δ : Sub< false > Sg (B <<- E ∷ G - u) G'
      δ ._ zero = proj₁ ∃s[ren[e,s]≡ρ[u]]
      δ S₁ (suc v) = ρ _ (thin u _ v)

      ρ≡δ∘σ : ρ ≡s (δ ∘s σ)
      ρ≡δ∘σ S v          with thick u v 
      ρ≡δ∘σ S .(thin u S w) | inj₁ (w , refl) = sym (ren-id (ρ S (thin u S w)))
      ρ≡δ∘σ .(B <<- Ss) .u  | inj₂ refl`      = sym (proj₂ ∃s[ren[e,s]≡ρ[u]])


flexRigid : ∀ {Sg G D S} (u : G ∋ S) (i : Inj (ctx S) D) (s : Tm Sg (G - u) D (! type S)) → Spec (mvar u i) (sub (thin-s u) s)
flexRigid {Sg} {G} {S = S} u i s with prune i s 
... | ((Pr ρ , m) , ρ-sup) 
 with invertTm i s ρ m 
... | no  NotInv                  = no  λ {(_ , σ , σ-unifies) → 
     let 
         eq = begin 
                 ren i (σ S u)              ≡⟨ T-≡ σ-unifies ⟩ 
                 subT σ (subT (thin-s u) s) ≡⟨ Sub∘.subT-∘ s ⟩ 
                 subT (σ ∘s thin-s u) s     ∎ 
         σ≤ρ = ρ-sup (σ ∘s thin-s u) (σ S u) (≡-T eq)

     in NotInv (proj₁ σ≤ρ) (σ S u , ≡-T (begin ren i (σ S u)               ≡⟨ eq ⟩ 
                                               subT (σ ∘s thin-s u) s      ≡⟨ subT-ext (proj₂ σ≤ρ) s ⟩ 
                                               subT (proj₁ σ≤ρ ∘s ρ) s     ≡⟨ sym (Sub∘.subT-∘ s) ⟩ 
                                               subT (proj₁ σ≤ρ) (subT ρ s) ∎))}

... | yes (t , ren[i,t]≡sub[ρ,s]) = yes 
 (_ , σ , 
   ≡-T (begin
     ren i (σ _ u)            ≡⟨ cong (ren i) σ[u]≡t ⟩ 
     ren i t                  ≡⟨ ren[i,t]≡sub[ρ,s] ⟩ 
     sub ρ s                  ≡⟨ sub-ext ρ≡σ∘thin[u] s ⟩ 
     sub (σ ∘s thin-s u) s    ≡⟨ sym (sub-∘ s) ⟩ 
     sub σ (sub (thin-s u) s) ∎) , σ-sup )
    where
      σ : Sub Sg G _
      σ S v with thick u v
      σ S v   | inj₁ (w , eq) = ρ _ w
      σ ._ .u | inj₂ refl`    = t

      σ[u]≡t : σ _ u ≡ t
      σ[u]≡t rewrite thick-refl u = refl

      ρ≡σ∘thin[u] : ρ ≡s (σ ∘s thin-s u)
      ρ≡σ∘thin[u] S y rewrite thick-thin u y = sym (ren-id _)

      σ-sup : Sup (Unifies (mvar u i) (sub (thin-s u) s)) σ
      σ-sup ρ₁ ρ₁-unifies = δ , ρ₁≡δ∘σ where
        ren[i,ρ₁[u]]≡sub[ρ₁∘thin[u],s] = begin 
           sub ρ₁ (mvar u i)         ≡⟨ T-≡ ρ₁-unifies ⟩
           sub ρ₁ (sub (thin-s u) s) ≡⟨ Sub∘.subT-∘ s ⟩
           sub (ρ₁ ∘s thin-s u) s    ∎

        ρ₁∘thin[u]≤ρ = ρ-sup (ρ₁ ∘s thin-s u) (ρ₁ _ u) (≡-T ren[i,ρ₁[u]]≡sub[ρ₁∘thin[u],s])
        δ = proj₁ ρ₁∘thin[u]≤ρ
        ρ₁∘thin[u]≡δ∘ρ = proj₂ ρ₁∘thin[u]≤ρ 

        ρ₁≡δ∘σ : ρ₁ ≡s (δ ∘s σ)
        ρ₁≡δ∘σ S u₁ with thick u u₁
        ρ₁≡δ∘σ S ._  | inj₁ (v , refl) = begin
                                           ρ₁ S (thin u S v)     ≡⟨ sym (ren-id (ρ₁ S (thin u S v))) ⟩
                                           sub ρ₁ (thin-s u S v) ≡⟨ ρ₁∘thin[u]≡δ∘ρ S v ⟩ 
                                           sub δ (ρ S v) ∎
        ρ₁≡δ∘σ ._ .u | inj₂ refl`      = ren-inj i (ρ₁ _ u) (sub δ t) -- crucial use of injectivity to show
          (begin                                                      -- that we got the most general solution
                 ren i (ρ₁ _ u)         ≡⟨ ren[i,ρ₁[u]]≡sub[ρ₁∘thin[u],s] ⟩ 
                 sub (ρ₁ ∘s thin-s u) s ≡⟨ sub-ext ρ₁∘thin[u]≡δ∘ρ s ⟩ 
                 sub (δ ∘s ρ) s         ≡⟨ sym (Sub∘.subT-∘ s) ⟩ 
                 sub δ (sub ρ s)        ≡⟨ cong (sub δ) (sym ren[i,t]≡sub[ρ,s]) ⟩ 
                 sub δ (ren i t)        ≡⟨ sub-nat t ⟩ 
                 ren i (sub δ t)        ∎)


flexAny : ∀ {Sg G D S} → (u : G ∋ S) → (i : Inj (ctx S) D) → (t : Tm Sg G D (! (type S))) → Spec (mvar u i) t
flexAny u i t                       with check u t 
flexAny u i .(sub (thin-s u) s)        | inj₁ (s , refl)             = flexRigid u i s
flexAny u i .(mvar u j)                | inj₂ (G1 , j , []    , refl) = yes (flexSame u i j)
flexAny u i .(wrap (d ∷ c) (mvar u j)) | inj₂ (G1 , j , d ∷ c , refl) = no  λ {(D1 , s , eq) → 
      No-Cycle (subD s d) (subC s c) (s _ u) i j
        (trans (T-≡ eq) (wrap-sub s (d ∷ c) (mvar u j)))} 

{-# NO_TERMINATION_CHECK #-}
mutual
  unify : ∀ {Sg G D T} → (x y : Tm Sg G D T) → Spec x y
  -- congruence and directly failing cases
  unify (con c xs) (con c₁ ys) with c ≅∋? c₁ 
  unify (con c xs) (con c₁ ys) | no  c≢c₁  = no (λ {(_ , _ , eq) → c≢c₁ (con-inj₁ eq)})
  unify (con c xs) (con .c ys) | yes refl` = cong-spec (con c) (unifyTms xs ys)
  unify (var x xs) (var y  ys) with x ≅∋? y 
  unify (var x xs) (var y  ys) | no  x≢y   = no (λ {(_ , _ , eq) → x≢y (var-inj₁ eq)})
  unify (var x xs) (var .x ys) | yes refl` = cong-spec (var x) (unifyTms xs ys)
  unify (lam x)    (lam y)     = cong-spec lam {x} {y} (unify x y)
  unify (con _ _)  (var _ _)   = no λ {(_ , _ , ())}
  unify (var _ _)  (con _ _)   = no λ {(_ , _ , ())}

  -- flexible cases
  unify (mvar u i) t          = flexAny u i t
  unify t          (mvar u i) = spec-comm (mvar u i) t (flexAny u i t)
 
  unifyTms : ∀ {Sg G D Ts} → (x y : Tms Sg G D Ts) → Spec x y
  unifyTms []       []       = yes (∃σMax[Unifies[x,x]] [])
  unifyTms (s ∷ xs) (t ∷ ys) 
   with unify s t
  ... | no  ¬unify[s,t]        = no λ {(_ , ρ , eq ∷ _) → ¬unify[s,t] (_ , ρ , eq)}
  ... | yes (_ , σ , eq , sup) 
     with unifyTms (subs σ xs) (subs σ ys)
  ...   | no  ¬unify[σxs,σys]       = no  λ {(_ , σ1 , eqt ∷ eqts) → ¬unify[σxs,σys] (shift eqts under σ by sup σ1 eqt) }
  ...   | yes (_ , σ1 , eq1 , sup1) = yes (_ , (σ1 ∘s σ) , optimist s t xs ys σ σ1 (eq , sup) (eq1 , sup1))

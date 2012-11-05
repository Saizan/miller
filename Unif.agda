module Unif where

open import Data.Product.Extras
open import Data.Nat hiding (_≤_) renaming (ℕ to Nat)
open import Relation.Nullary
open import Relation.Binary
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)         
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Sum renaming (inj₁ to yes; inj₂ to no)

open import Injection
open import Injection.Objects
open import Lists
open import Data.List

open import Syntax
open import Equality
open import RenOrn
open import OneHoleContext
open import OccursCheck
open import Pruning
open import Inversion

open import DSub
open import Specification
open import MetaRens

mutual
  lift-equalizer : ∀ {Sg G X Y S} {i j : Inj X Y} -> (equ : Equalizer i j) -> (t : Tm Sg G X S) 
                   -> ren i t ≡T ren j t -> let open Equalizer equ in RTm e t
  lift-equalizer equ (con c ts) (con refl eq) = con c (lifts-equalizer equ ts eq)
  lift-equalizer equ (fun u j₁) (fun refl eq) = fun u (universal j₁ eq) e∘universal≡m
    where open Equalizer equ
  lift-equalizer equ (var x ts) (var eqv eqts) = var (proj₁ r) (sym (proj₂ r)) (lifts-equalizer equ ts eqts)
    where r = e$u≡m equ _ x eqv
  lift-equalizer equ (lam t) (lam eq) = lam (lift-equalizer (cons-equalizer _ _ equ) t eq)

  lifts-equalizer : ∀ {Sg G X Y S} {i j : Inj X Y} -> (equ : Equalizer i j) -> (t : Tms Sg G X S) 
                    -> rens i t ≡T rens j t -> let open Equalizer equ in RTms e t
  lifts-equalizer equ [] eq = []
  lifts-equalizer equ (t ∷ ts) (eqt ∷ eqts) = (lift-equalizer equ t eqt) ∷ (lifts-equalizer equ ts eqts)

flexSame : ∀ {Sg G D S} → (u : G ∋ S) → (i j : Inj (ctx S) D) → ∃⟦σ⟧ Max (Unifies {Sg} (Tm.fun u i) (fun u j))
flexSame {Sg} {G} {D} {B <<- Ss} u i j = _ , (DS σ , singleton-Decreasing e u (equalizer-Decr i j)) 
                                           , [σ]Unifies[fun[u,i],fun[u,j]] 
                                           , sup-σ
  where
    i,j⇒e = equalizer i j
    open Equalizer i,j⇒e

    σ = toSub (singleton u e)

    [σ]Unifies[fun[u,i],fun[u,j]] : ren i (σ _ u) ≡T ren j (σ _ u)
    [σ]Unifies[fun[u,i],fun[u,j]] rewrite thick-refl u = ≡-T (cong (fun zero) commutes)

    sup-σ : Sup (Unifies (fun u i) (fun u j)) σ
    sup-σ {G'} ρ ρ-unifies = δ , ρ≡δ∘σ where

      δ : Sub Sg (B <<- E ∷ G - u) G'
      δ ._ zero = proj₁ (RenOrn.forget (lift-equalizer i,j⇒e (ρ (B <<- Ss) u) ρ-unifies))
      δ S₁ (suc v) = ρ _ (thin u _ v)

      ρ≡δ∘σ : ρ ≡s (δ ∘s σ)
      ρ≡δ∘σ S v          with thick u v 
      ρ≡δ∘σ S .(thin u S w) | inj₁ (w , refl) = sym (ren-id (ρ S (thin u S w)))
      ρ≡δ∘σ .(B <<- Ss) .u  | inj₂ refl = sym (proj₂ (RenOrn.forget (lift-equalizer i,j⇒e (ρ (B <<- Ss) u) ρ-unifies)))


flexRigid : ∀ {Sg G D S} (u : G ∋ S) (i : Inj (ctx S) D) (s : Tm Sg (G - u) D (! type S)) → Spec (fun u i) (sub (thin-s u) s)
flexRigid {Sg} {G} {S = S} u i s with prune i s 
... | ((Pr ρ , decr , m) , ρ-sup) 
 with invertTm i s ρ m 
... | no  NotInv                  = no  λ {(_ , σ , eq) → 
     let eq' = begin 
                 ren i (σ S u)              ≡⟨ T-≡ eq ⟩ 
                 subT σ (subT (thin-s u) s) ≡⟨ subT-∘ s ⟩ 
                 subT (σ ∘s thin-s u) s     ∎ 
         σ≤ρ = ρ-sup (σ ∘s thin-s u) (σ S u) (≡-T eq')
     in NotInv (proj₁ σ≤ρ) (σ S u , ≡-T (begin ren i (σ S u)                       ≡⟨ eq' ⟩ 
                                               subT (σ ∘s thin-s u) s              ≡⟨ subT-ext (proj₂ σ≤ρ) s ⟩ 
                                               subT (proj₁ σ≤ρ ∘s ρ) s       ≡⟨ sym (subT-∘ s) ⟩ 
                                               subT (proj₁ σ≤ρ) (subT ρ s) ∎))}
... | yes (t , ren[i,t]≡sub[ρ,s]) = yes 
 (_ , (DS σ , inj₂ (rigid-decr u (map⊎ proj₁ (\ x -> x) decr))) , 
   ≡-T (begin
     ren i (σ _ u)            ≡⟨ cong (ren i) σ[u]≡t ⟩ 
     ren i t                  ≡⟨ ren[i,t]≡sub[ρ,s] ⟩ 
     sub ρ s          ≡⟨ sub-ext ρ≡σ∘thin[u] s ⟩ 
     sub (σ ∘s thin-s u) s    ≡⟨ sym (sub-∘ s) ⟩ 
     sub σ (sub (thin-s u) s) ∎) , σ-sup )
    where
      σ : Sub Sg G _
      σ S v with thick u v
      σ S v   | inj₁ (w , eq) = ρ _ w
      σ ._ .u | inj₂ refl     = t

      σ[u]≡t : σ _ u ≡ t
      σ[u]≡t rewrite thick-refl u = refl

      ρ≡σ∘thin[u] : ρ ≡s (σ ∘s thin-s u)
      ρ≡σ∘thin[u] S y rewrite thick-thin u y = sym (ren-id _)

      σ-sup : Sup (Unifies (fun u i) (sub (thin-s u) s)) σ
      σ-sup ρ₁ ρ₁-unifies = δ , ρ₁≡δ∘σ where
        ren[i,ρ₁[u]]≡sub[ρ₁∘thin[u],s] = begin 
           sub ρ₁ (fun u i)                  ≡⟨ T-≡ ρ₁-unifies ⟩
           sub ρ₁ (sub (thin-s u) s)         ≡⟨ sub-∘ s ⟩
           sub (ρ₁ ∘s thin-s u) s            ∎

        ρ₁∘thin[u]≤ρ = ρ-sup (ρ₁ ∘s thin-s u) (ρ₁ _ u) (≡-T ren[i,ρ₁[u]]≡sub[ρ₁∘thin[u],s])
        δ = proj₁ ρ₁∘thin[u]≤ρ
        ρ₁∘thin[u]≡δ∘ρ = proj₂ ρ₁∘thin[u]≤ρ 

        ρ₁≡δ∘σ : ρ₁ ≡s (δ ∘s σ)
        ρ₁≡δ∘σ S u₁ with thick u u₁
        ρ₁≡δ∘σ S ._  | inj₁ (v , refl) = begin ρ₁ S (thin u S v)    ≡⟨ sym (ren-id _) ⟩ 
                                               (ρ₁ ∘s thin-s u) S v ≡⟨ ρ₁∘thin[u]≡δ∘ρ _ v ⟩ 
                                               sub δ (ρ S v)        ∎
        ρ₁≡δ∘σ ._ .u | inj₂ refl       = ren-inj i (ρ₁ _ u) (sub δ t) 
          (begin 
                 ren i (ρ₁ _ u)         ≡⟨ ren[i,ρ₁[u]]≡sub[ρ₁∘thin[u],s] ⟩ 
                 sub (ρ₁ ∘s thin-s u) s ≡⟨ sub-ext ρ₁∘thin[u]≡δ∘ρ s ⟩ 
                 sub (δ ∘s ρ) s         ≡⟨ sym (sub-∘ s) ⟩ 
                 sub δ (sub ρ s)        ≡⟨ cong (sub δ) (sym ren[i,t]≡sub[ρ,s]) ⟩ 
                 sub δ (ren i t)        ≡⟨ sub-nat t ⟩ 
                 ren i (sub δ t)        ∎)


flexAny : ∀ {Sg G D S} → (u : G ∋ S) → (i : Inj (ctx S) D) → (t : Tm Sg G D (! (type S))) → Spec (fun u i) t
flexAny u i t                                 with check u t 
flexAny u i .(sub (λ S v → mvar (thin u S v)) s) | inj₁ (s , refl)               = flexRigid u i s
flexAny u i .(fun u j)                           | inj₂ (G1 , j , [] , refl)     = yes (flexSame u i j)
flexAny u i .(∫once x (∫ ps (fun u j)))          | inj₂ (G1 , j , x ∷ ps , refl) = no  λ {(D1 , s , eq) → 
        No-Cycle (subD s x) (subC s ps) (s _ u) i j
          (trans (T-≡ eq) (∫-sub s (x ∷ ps) (fun u j)))} 


unify-comm : ∀ {Sg G D T} → (x y : Term Sg G D T) → ∃σ Unifies x y → ∃σ Unifies y x
unify-comm _ _ (G , σ , eq) = (G , σ , T.sym eq)

spec-comm : ∀ {Sg G D T} → (x y : Term Sg G D T) → Spec x y → Spec y x
spec-comm _ _ = map⊎ (λ {(G , σ , eq , max) → G , σ , T.sym eq , (λ {_} ρ x → max ρ (T.sym x))}) (λ x x₁ → x (unify-comm _ _ x₁))

mutual
  unify : ∀ {Sg G D T} → (x y : Tm Sg G D T) → ∃ (\ n -> n ≥ Ctx-length G) -> Spec x y
  -- congruence and directly failing cases
  unify (con c xs) (con c₁ ys) l with eq-∋ (_ , c) (_ , c₁) 
  unify (con c xs) (con c₁ ys) l | no  c≢c₁ = no (λ {(_ , _ , eq) → c≢c₁ (con-inj₁ eq)})
  unify (con c xs) (con .c ys) l | yes refl = cong-spec (con c) (unifyTms xs ys l)
  unify (var x xs) (var y  ys) l with eq-∋ (_ , x) (_ , y) 
  unify (var x xs) (var y  ys) l | no  x≢y  = no (λ {(_ , _ , eq) → x≢y (var-inj₁ eq)})
  unify (var x xs) (var .x ys) l | yes refl = cong-spec (var x) (unifyTms xs ys l)
  unify (lam x)    (lam y)     l = cong-spec lam {x} {y} (unify x y l)
  unify (con _ _)  (var _ _)   l = no λ {(_ , _ , ())}
  unify (var _ _)  (con _ _)   l = no λ {(_ , _ , ())}

  -- flexible cases
  unify (fun u i) t         l = flexAny u i t
  unify t         (fun u i) l = spec-comm (fun u i) t (flexAny u i t)
 
  unifyTms : ∀ {Sg G D Ts} → (x y : Tms Sg G D Ts) → ∃ (\ n -> n ≥ Ctx-length G) -> Spec x y
  unifyTms []       []       _ = yes (∃σMax[Unifies[x,x]] [])
  unifyTms (s ∷ xs) (t ∷ ys) l 
   with unify s t l
  ... | no  ¬unify[s,t]        = no λ {(_ , ρ , eq ∷ _) → ¬unify[s,t] (_ , ρ , eq)}
  ... | yes (_ , σ , eq , sup) 
     with under σ unifyTms xs ys l
  ...   | no  ¬unify[σxs,σys]       = no  λ {(_ , σ1 , eqt ∷ eqts) → ¬unify[σxs,σys] (shift eqts under ⟦ σ ⟧ by sup σ1 eqt) }
  ...   | yes (_ , σ1 , eq1 , sup1) = yes (_ , (σ1 ∘ds σ) , optimist s t xs ys ⟦ σ ⟧ ⟦ σ1 ⟧ (eq , sup) (eq1 , sup1))

  -- termination overhead
  under_unifyTms : ∀ {Sg G D Ts} -> 
             ∀ {G1} (σ : DSub Sg G G1) -> (xs ys : Tms Sg G D Ts) -> ∃ (\ n -> n ≥ Ctx-length G) -> Spec (subs ⟦ σ ⟧ xs) (subs ⟦ σ ⟧ ys)
  under (DS σ , inj₁ (G~G1 , σ-is-iso)) unifyTms xs ys l = Spec[xs,ys]⇒Spec[σxs,σys] σ G~G1 σ-is-iso (unifyTms xs ys l)
  under (DS σ , inj₂ G>G1) unifyTms xs ys (n , n≥G) = under-not-iso σ unifyTms xs ys (n , n≥G) (≤-trans G>G1 n≥G) 

  under-not-iso_unifyTms : ∀ {Sg G D Ts} -> 
             ∀ {G1} (σ : Sub Sg G G1) -> (xs ys : Tms Sg G D Ts) -> 
             (u : ∃ (\ n -> n ≥ Ctx-length G)) -> proj₁ u > Ctx-length G1 -> Spec (subs σ xs) (subs σ ys)
  under-not-iso σ unifyTms xs ys (.(suc n) , n≥G) (s≤s {._} {n} z) = unifyTms (subs σ xs) (subs σ ys) (n , z)

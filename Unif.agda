module Unif where


open import Data.Product renaming (map to mapΣ)
open import Data.Nat hiding (_≤_) renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.Sum renaming (inj₁ to yes; inj₂ to no)
open import Data.Maybe
open import Category.Monad
import Level
open RawMonad (monad {Level.zero})

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
                 -> (ren i t) ≡T (ren j t) -> let open Equalizer equ in RTm Sg G E X e _ t
  lift-equalizer equ (con c ts) (con refl eq) = con c (lifts-equalizer equ ts eq)
  lift-equalizer equ (fun u j₁) (fun refl eq) = fun u (universal j₁ eq) e∘universal≡m
    where open Equalizer equ
  lift-equalizer equ (var x ts) (var eqv eqts) = var (proj₁ r) (sym (proj₂ r)) (lifts-equalizer equ ts eqts)
    where r = e$u≡m equ _ x eqv
  lift-equalizer equ (lam t) (lam eq) = lam (lift-equalizer (cons-equalizer _ _ equ) t eq)

  lifts-equalizer : ∀ {Sg G X Y S} {i j : Inj X Y} -> (equ : Equalizer i j) -> (t : Tms Sg G X S) 
                 -> (rens i t) ≡T (rens j t) -> let open Equalizer equ in RTms Sg G E X e _ t
  lifts-equalizer equ [] eq = []
  lifts-equalizer equ (t ∷ ts) (eqt ∷ eqts) = (lift-equalizer equ t eqt) ∷ (lifts-equalizer equ ts eqts)

flexSame : ∀ {Sg G D S} → (u : G ∋ S) → (i j : Inj (ctx S) D) → ∃⟦σ⟧ Max (Unifies {Sg} (Tm.fun u i) (fun u j))
flexSame {Sg} {G} {D} {B <<- Ss} u i j = _ , (DS σ , singleton-Decreasing e u (equalizer-Decr i j)) , aux , maxprop
  where
    i,j⇒e = equalizer i j
    open Equalizer i,j⇒e
    σ = (toSub (singleton u e))
    aux : eqT (ren i (σ _ u)) (ren j (σ _ u))
    aux rewrite thick-refl u = ≡-T (cong (fun zero) commutes)
    maxprop : {G' : List MTy}
      (ρ : (S : MTy) → G ∋ S → Tm Sg G' (ctx S) (! type S)) →
      eqT (ren i (ρ _ u)) (ren j (ρ _ u)) → ρ ≤ σ
    maxprop {G'} ρ eq = dif , proof where
      dif : (S₁ : MTy) →
        B <<- E ∷ G - u ∋ S₁ →
        Tm Sg G' (ctx S₁) ([] ->> type S₁)
      dif ._ zero = proj₁ (RenOrn.forget (lift-equalizer i,j⇒e (ρ (B <<- Ss) u) eq))
      dif S₁ (suc v) = ρ _ (thin u _ v)
      proof : (S₁ : MTy) (u₁ : G ∋ S₁) → ρ S₁ u₁ ≡ (dif ∘s σ) S₁ u₁
      proof S₁ u₁ with thick u u₁ 
      proof S₁ u₁ | inj₁ (v , eq') rewrite eq' = sym (ren-id (ρ _ u₁))
      proof .(B <<- Ss) .u | inj₂ refl = sym (proj₂ (RenOrn.forget (lift-equalizer i,j⇒e (ρ (B <<- Ss) u) eq)))

flexRigid : ∀ {Sg G D S} →
               (u : G ∋ S) →
               (i : Inj (ctx S) D) →
               (s : Tm Sg (G - u) D (! type S)) → (p : ∃ \ G1 → Σ (MetaRen (G - u) G1) \ ρ → Decreasing {Sg} (toSub ρ) × toSub ρ / s ∈ i) ->
               (∀ {G1} (σo : Sub Sg G G1) -> sub σo (fun u i) ≡ sub (\ S v -> σo _ ((thin u S v))) s 
                  -> (\ S v -> σo _ ((thin u S v))) ≤ toSub (proj₁ (proj₂ p))) ->
               Spec (fun u i) (sub (\ S v -> mvar (thin u S v)) s)
flexRigid {S = S} u i s (G1 , ρ , decr , m) maxρ with invertTm i s (toSub ρ) m 
flexRigid {S = S} u i .(∫ C (var x ys)) (G1 , ρ , decr , m) _ | inj₂ (D1 , _ , _ , x , ys , C , refl , x∉i) = no (aux x∉i) where
  aux : x ∉ ∫Inj C i -> ∃σ (Unifies (fun u i) (sub (λ S v → mvar (thin u S v)) (∫ C (var x ys)))) → ⊥
  aux x∉i (_ , σ , eq) with ren-∫ x (subC _ C) (σ _ u) i (subs _ ys) (trans (T-≡ eq) (trans (sub-∘ (∫ C (var x ys))) (∫-sub _ C (var x ys))))
                       | ∫Ctx C (ctx S) | ∫Inj C i | ∫Inj-subC {s = (λ z t → ren id-i (σ z (thin u z t)))} C i
  ... | (b , x≡i$b) | ._ | ._ | refl = ∉-∉Im (∫Inj (subC (λ z t → ren id-i (σ z (thin u z t))) C) i) x x∉i b x≡i$b

flexRigid {Sg} {G} u i s (G1 , ρ , decr , m) maxρ | inj₁ (t , renit≡subρs) 
 = yes (G1 , (DS σ , inj₂ (rigid-decr u (Data.Sum.map proj₁ (\ x -> x) decr))) , 
   ≡-T (begin
     ren i (σ _ u)                              ≡⟨ cong (ren i) σx≡t' ⟩ 
     ren i t                                    ≡⟨ renit≡subρs ⟩ 
     sub (toSub ρ) s                            ≡⟨ sub-ext σthiny≡toSubρy s ⟩ 
     sub (λ S v → sub σ (mvar (thin u S v))) s  ≡⟨ sym (sub-∘ s) ⟩ 
     sub σ (sub (λ S v → mvar (thin u S v)) s)  ∎) , maxprop )
    where
      σ : (S : MTy) → G ∋ S → Tm Sg G1 (ctx S) (! (type S))
      σ S v with thick u v
      σ S v | inj₁ (w , eq) = toSub ρ _ w
      σ ._ .u | inj₂ refl = t
      σx≡t' : σ _ u ≡ t
      σx≡t' rewrite thick-refl u = refl
      σthiny≡toSubρy : (S : MTy) (x₁ : G - u ∋ S) → toSub ρ _ x₁ ≡ sub σ (mvar (thin u S x₁))
      σthiny≡toSubρy S y rewrite thick-thin u y | left-id (ρ-env (ρ S y)) = refl
      maxprop : {G' : List MTy}
        (ρ₁ : (S : MTy) → G ∋ S → Tm Sg G' (ctx S) ([] ->> type S)) →
        (ren i (ρ₁ _ u)) ≡T (sub ρ₁ (sub (λ S v → mvar (thin u S v)) s)) → ρ₁ ≤ σ
      maxprop {G'} ρ₁ eq1 = r , propp where
        eq11 = (trans (T-≡ eq1) (trans (sub-∘ s) (sub-ext (λ S x → ren-id _) s)))
        r = proj₁ (maxρ ρ₁ eq11)
        ρ₁∘thin≡rr∘ρ = proj₂ (maxρ ρ₁ eq11)
        propp : (S : MTy) (u₁ : G ∋ S) → ρ₁ S u₁ ≡ sub r (σ S u₁)
        propp S u₁ with thick u u₁
        propp S ._ | inj₁ (v , refl) = ρ₁∘thin≡rr∘ρ _ v
        propp ._ .u | inj₂ refl = ren-inj i (ρ₁ _ u) (sub r t) 
          (begin ren i (ρ₁ _ u) ≡⟨ eq11 ⟩ 
                 sub (λ S v → ρ₁ _ (thin u S v)) s ≡⟨ sub-ext ρ₁∘thin≡rr∘ρ s ⟩ 
                 sub (r ∘s toSub ρ) s ≡⟨ sym (sub-∘ s) ⟩ 
                 sub r (sub (toSub ρ) s) ≡⟨ cong (sub r) (sym renit≡subρs) ⟩ 
                 sub r (ren i t) ≡⟨ sub-nat t ⟩ 
                 ren i (sub r t) ∎)


flexAny : ∀ {Sg G D S} → (u : G ∋ S) → (i : Inj (ctx S) D) → (t : Tm Sg G D (! (type S))) → Spec (fun u i) t
flexAny u i t with check u t 
flexAny u i .(sub (λ S v → mvar (thin u S v)) s) | inj₁ (s , refl) = flexRigid u i s (prune i s (_ , (≤-begin _ ∎-≤))) (λ σo x → 
        prune-gen i s (_ , (≤-begin _ ∎-≤)) (λ S x₁ → σo _ ((thin u S x₁))) (σo _ u) (≡-T x)) 
    where 
      open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _∎-≤) 
flexAny u i .(fun u j) | inj₂ (G1 , j , [] , refl) = yes (flexSame u i j)
flexAny u i .(∫once x (∫ ps (fun u j))) | inj₂ (G1 , j , x ∷ ps , refl) = no λ {(D1 , s , eq) → 
        not-nil (subC s ps) (No-Cycle (subC s (x ∷ ps)) (s _ u) i j (trans (T-≡ eq) (∫-sub s (x ∷ ps) (fun u j))))}


unify-comm : ∀ {Sg G D T} → (x y : Term Sg G D T) → ∃σ Unifies x y → ∃σ Unifies y x
unify-comm _ _ (G , σ , eq) = (G , σ , T.sym eq)

spec-comm : ∀ {Sg G D T} → (x y : Term Sg G D T) → Spec x y → Spec y x
spec-comm _ _ = Data.Sum.map (λ {(G , σ , eq , max) → G , σ , T.sym eq , (λ {_} ρ x → max ρ (T.sym x))}) (λ x x₁ → x (unify-comm _ _ x₁))

mutual
  unify : ∀ {Sg G D T} → (x y : Tm Sg G D T) → ∃ (\ n -> n ≥ Ctx-length G) -> Spec x y
  unify (con x xs) (con y ys) l with eq-∋ (_ , x) (_ , y) 
  ... | no ¬p = no (λ {(_ , _ , eq) → ¬p (con-inj₁ eq)})
  unify (con x xs) (con .x ys) l | yes refl with unifyTms xs ys l
  ... | no p = no (λ { (_ , σ , con _ eq) → p (_ , (σ , eq))})
  ... | yes (_ , σ , eq , max) = yes (_ , σ , T.cong (con x) eq , λ { ρ (con _ eq) → max ρ eq})
  unify (fun x xs) t l = flexAny x xs t
  unify s (fun y ys) l = spec-comm (fun y ys) s (flexAny y ys s)
  unify (var x xs) (var y ys) l with eq-∋ (_ , x) (_ , y) 
  ... | no ¬p = no (λ {(_ , _ , eq) → ¬p (var-inj₁ eq)})
  unify (var x xs) (var .x ys) l | yes refl with unifyTms xs ys l
  ... | no p = no λ {(_ , σ , var _ eq) → p (_ , σ , eq)}
  ... | yes (_ , σ , eq , max) = yes (_ , σ , T.cong (var x) eq , λ { ρ (var _ eq) → max ρ eq})
  unify (lam x) (lam y) l with unify x y l
  ... | no p = no λ {(_ , σ , lam eq) → p (_ , σ , eq)}
  ... | yes (_ , σ , eq , max) = yes (_ , σ , T.cong lam eq , λ {ρ (lam eq) → max ρ eq})
  unify (con _ _) (var _ _) l = no λ {(_ , _ , ())}
  unify (var _ _) (con _ _) l = no λ {(_ , _ , ())}
 

  unifyTms : ∀ {Sg G D Ts} → (x y : Tms Sg G D Ts) → ∃ (\ n -> n ≥ Ctx-length G) -> Spec x y
  unifyTms [] [] _ = yes (refl-Unifies [])
  unifyTms (s ∷ xs) (t ∷ ys) l with unify s t l
  ... | no p = no λ {(_ , ρ , eq ∷ _) → p (_ , ρ , eq)}
  ... | yes (_ , σ , eq , max) with helper l σ xs ys
  ... | no p = no λ {(_ , σ1 , eqt ∷ eqts) → p (shift2 xs ys σ1 ⟦ σ ⟧ (max σ1 eqt) eqts) }
  ... | yes (_ , σ1 , eq1 , max1) = yes (_ , (σ1 ∘ds σ) , optimist-Unifies s t xs ys ⟦ σ ⟧ ⟦ σ1 ⟧ (eq , max) (eq1 , max1))



  helper : ∀ {Sg G D Ts} -> ∃ (\ n -> n ≥ Ctx-length G) ->
             ∀ {G1} (σ : DSub Sg G G1) -> (xs ys : Tms Sg G D Ts) -> Spec (subs ⟦ σ ⟧ xs) (subs ⟦ σ ⟧ ys)
  helper l (DS σ , inj₁ (eq , σ-is-iso)) xs ys = Spec[xs,ys]⇒Spec[σxs,σys] xs ys σ eq (proj₁ σ-is-iso) (proj₂ σ-is-iso) (unifyTms xs ys l)
  helper (n , n≥length) (DS σ , inj₂ G>G1) xs ys = helper2 (n , n≥length) σ xs ys (≤-begin _ ≤⟨ G>G1 ⟩ _ ≤⟨ n≥length ⟩ (_ ≤-∎)) 
         where open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎)

  helper2 : ∀ {Sg G D Ts} -> (u : ∃ (\ n -> n ≥ Ctx-length G)) ->
             ∀ {G1} (σ : Sub Sg G G1) -> (xs ys : Tms Sg G D Ts) -> proj₁ u > Ctx-length G1 -> Spec (subs σ xs) (subs σ ys)
  helper2 (.(suc n) , n≥length) σ xs ys (s≤s {._} {n} z) = unifyTms (subs σ xs) (subs σ ys) (n , z)

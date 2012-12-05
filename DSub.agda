module DSub where

open import Data.Nat renaming (_≤_ to _≤ℕ_)
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
import Relation.Binary.HeterogeneousEquality as Het
open Het using (_≅_; refl)
open import Relation.Nullary
open import Data.Nat.Properties
open import Algebra
open CommutativeSemiring commutativeSemiring using (+-comm; +-assoc)
open import Data.Sum
open import Data.Product

open import Injection
open import Injection.Objects
open import Syntax
open import MetaRens

-- We define a measure of meta-contexts to help with proving
-- termination of the main unification algorithm and pruning.
Ctx-length : MCtx -> ℕ
Ctx-length [] = zero
Ctx-length (type <<- ctx ∷ m) = suc (length ctx + Ctx-length m)

IsIso : ∀ {Sg G1 G2} -> (s : Sub Sg G1 G2) -> Set
IsIso s = Σ (id-s ≤ s) \le -> id-s ≡s (s ∘s proj₁ le)
 
-- The substitutions we produce are going to either be isomorphims or
-- produce terms in a smaller context, so it'll be fine to recurse on
-- their results.
Decreasing : ∀ {Sg G1 G2} -> (s : Sub Sg G1 G2) -> Set
Decreasing {Sg} {G1} {G2} s = (Ctx-length G1 ≡ Ctx-length G2 × IsIso s) 
                            ⊎ (Ctx-length G1 > Ctx-length G2) 

record DSub (Sg : Ctx) (G1 : MCtx) (G2 : MCtx) : Set where
  constructor DS_,_
  field
    ⟦_⟧ : Sub Sg G1 G2
    decreasing : Decreasing ⟦_⟧

open DSub public

-- Below we prove that DSub forms a category and that other
-- substitutions of interest are Decreasing.

Ctx-length-lemma : ∀ {G Ss B} -> (u  : G ∋ B <<- Ss) -> Ctx-length G ≡ Ctx-length (G - u <: B <<- Ss)
Ctx-length-lemma zero = refl
Ctx-length-lemma {._ ∷ G} {Ss} (suc {S = _ <<- ctx} u) = 
  begin
    suc (length ctx) + Ctx-length G                           ≡⟨ cong (_+_ (suc (length ctx))) (Ctx-length-lemma u) ⟩
    suc (length ctx) + (suc (length Ss) + Ctx-length (G - u)) ≡⟨ sym (+-assoc (suc (length ctx)) (suc (length Ss)) _) ⟩
    suc (length ctx) + suc (length Ss) + Ctx-length (G - u)   ≡⟨ cong (λ x → x + Ctx-length (G - u)) (+-comm (suc (length ctx)) (suc (length Ss))) ⟩ 
    suc (length Ss) + suc (length ctx) + Ctx-length (G - u)   ≡⟨ +-assoc (suc (length Ss)) (suc (length ctx)) _ ⟩ 
    suc (length Ss) + (suc (length ctx) + Ctx-length (G - u)) ∎
  where open ≡-Reasoning

abstract
  toMRen : ∀ {Sg G G1} (s : Sub Sg G G1) -> (id-s ≤ s) -> Σ (MetaRen G G1) \ ρ -> toSub ρ ≡s s
  toMRen {Sg} {G} {G1} s (δ , id≡δ∘s) = (λ S x → proj₁ (aux S x)) , (λ S x → proj₂ (aux S x)) where
    aux : ∀ S x -> ∃ \ (c : VarClosure G1 S) -> Tm.fun (body c) (ρ-env c) ≡ s S x
    aux S x with s S x | id≡δ∘s S x
    aux S x | con c ts | ()
    aux S x | fun u j | w = (j / u) , refl
    aux S x | var x₁ ts | ()


IsIso-id : ∀ {Sg G} -> IsIso {Sg} {G} {G} id-s
IsIso-id = λ {Sg} {G} → (id-s , (λ S u → sym (ren-id _))) , (λ S u → sym (ren-id _))

IsIso-∘ : ∀ {Sg G1 G2 G3} -> (s : Sub Sg G2 G3) -> (s' : Sub Sg G1 G2) -> IsIso s -> IsIso s' -> IsIso (s ∘s s')
IsIso-∘ s s' ((δ , p) , p') ((δ' , q) , q') = (δ' ∘s δ ,
 (λ S u →
      begin
      fun u id-i                      ≡⟨ q S u ⟩
      sub δ' (s' S u)                 ≡⟨ cong (sub δ') (sym (sub-id (s' S u))) ⟩
      sub δ' (sub id-s (s' S u))      ≡⟨ cong (sub δ') (sub-ext p (s' S u)) ⟩
      sub δ' (sub (δ ∘s s) (s' S u))  ≡⟨ cong (sub δ') (sym (sub-∘ (s' S u))) ⟩
      sub δ' (sub δ (sub s (s' S u))) ≡⟨ sub-∘ {f = δ'} {g = δ} (sub s (s' S u)) ⟩
      sub (δ' ∘s δ) (sub s (s' S u))  ∎)),

 (λ S u →
      begin
        fun u id-i                      ≡⟨ p' S u ⟩
        sub s (δ S u)                   ≡⟨ cong (sub s) (sym (sub-id (δ S u))) ⟩
        sub s (sub id-s (δ S u))        ≡⟨ cong (sub s) (sub-ext q' (δ S u)) ⟩
        sub s (sub (s' ∘s δ') (δ S u))  ≡⟨ cong (sub s) (sym (sub-∘ {f = s'} {g = δ'} (δ S u))) ⟩
        sub s (sub s' (sub δ' (δ S u))) ≡⟨ sub-∘ (sub δ' (δ S u)) ⟩ 
        sub (s ∘s s') (sub δ' (δ S u))  ∎)
                                                   
  where open ≡-Reasoning

trans-> : ∀ {m n o} -> m > n -> n > o -> m > o
trans-> (s≤s m≤n) (s≤s z≤n) = s≤s z≤n
trans-> (s≤s m≤n) (s≤s (s≤s m≤n₁)) = s≤s (trans-> m≤n (s≤s m≤n₁))

open ≤-Reasoning

trans-dec : ∀ {Sg G1 G2 G3} -> (s : Sub Sg G2 G3) -> Decreasing s -> (s' : Sub Sg G1 G2) -> Decreasing s' -> Decreasing (s ∘s s')
trans-dec s (inj₁ (G2~G3 , s-is-iso)) s' (inj₁ (G1~G2 , s'-is-iso )) 
  = inj₁ (trans G1~G2 G2~G3 , IsIso-∘ s s' s-is-iso s'-is-iso )
trans-dec {Sg} {G1} {G2} {G3} s (inj₁ (G2~G3 , _)) s' (inj₂ G1>G2) 
  = inj₂
      (begin
       suc (Ctx-length G3) ≡⟨ sym (cong suc G2~G3) ⟩
       suc (Ctx-length G2) ≤⟨ G1>G2 ⟩ 
       Ctx-length G1       ∎)
trans-dec {Sg} {G1} {G2} {G3} s (inj₂ G2>G3) s' (inj₁ (G1~G2 , _)) 
  = inj₂
      (begin
       suc (Ctx-length G3) ≤⟨ G2>G3 ⟩
       Ctx-length G2       ≡⟨ sym G1~G2 ⟩ 
       Ctx-length G1       ∎)
trans-dec s (inj₂ y) s' (inj₂ y₁) = inj₂ (trans-> y₁ y) 

_∘ds_ : ∀ {Sg G1 G2 G3} -> DSub Sg G2 G3 -> DSub Sg G1 G2 -> DSub Sg G1 G3
(DS σ , G2>G3) ∘ds (DS σ₁ , G1>G2) = DS (σ ∘s σ₁) , trans-dec σ G2>G3 σ₁ G1>G2
  
⟦⟧-∘ : ∀ {Sg g h i} (s : DSub Sg h i) (s₁ : DSub Sg g h) -> ⟦ s ∘ds s₁ ⟧ ≡s (⟦ s ⟧ ∘s ⟦ s₁ ⟧)
⟦⟧-∘ s s1 S x = refl


Decr-i : ∀ {A : Set}{X Y : List A} -> Inj X Y -> Set
Decr-i {A} {E} {S} e = (E ≡ S × e ≅ id-i {xs = E}) ⊎ length S > length E

equalizer-Decr : ∀ {A : Set}{S T : List A}(f g : Inj S T) -> let open Equalizer (equalizer f g) in Decr-i e
equalizer-Decr [] [] = inj₁ (refl , Het.refl)
equalizer-Decr (i ∷ f [ pf ]) (j ∷ g [ pf₁ ]) with eq-∋ (_ , i) (_ , j) | equalizer f g | equalizer-Decr f g 
equalizer-Decr (i ∷ f [ pf ]) (.i ∷ g [ pf₁ ]) | yes refl | Equ E , .id-i , e⇒f,g | inj₁ (refl , Het.refl) = inj₁ (refl , Het.≡-to-≅ cons-id)
equalizer-Decr (i ∷ f [ pf ]) (.i ∷ g [ pf₁ ]) | yes refl | equ | inj₂ y₁ = inj₂ (s≤s y₁)
equalizer-Decr (i ∷ f [ pf ]) (j ∷ g [ pf₁ ]) | no ¬p | Equ E , e , e⇒f,g | inj₁ (refl , _) = inj₂ (s≤s (begin _ ∎))
equalizer-Decr (i ∷ f [ pf ]) (j ∷ g [ pf₁ ]) | no ¬p | equ | inj₂ y₁ = inj₂ (≤-step y₁)

pullback-Decr : ∀ {A : Set} {X Y Z : List A} → (f : Inj X Z)(g : Inj Y Z) -> let open Pullback (pullback f g) in Decr-i p₂
pullback-Decr f [] = inj₁ (refl , Het.refl)
pullback-Decr f (i ∷ g [ pf ]) with invert f i | pullback f g | pullback-Decr f g
pullback-Decr f (.(f $ x) ∷ g [ pf ]) | yes (x , refl) | Pull P , p₁ , .id-i , p₁,p₂⇒f,g | inj₁ (refl , Het.refl) = inj₁ (refl , Het.≡-to-≅ cons-id)
pullback-Decr f (.(f $ x) ∷ g [ pf ]) | yes (x , refl) | q | inj₂ y₁ = inj₂ (s≤s y₁)
pullback-Decr f (i ∷ g [ pf ]) | no ¬p | Pull P , _ , _ , _ | inj₁ (refl , _) = inj₂ (s≤s (begin _ ∎))
pullback-Decr f (i ∷ g [ pf ]) | no ¬p | pull | inj₂ y₁ = inj₂ (≤-step y₁)


singleton-Decreasing : ∀ {Sg G E Ss B} (e : Inj E Ss) (u : G ∋ B <<- Ss) -> Decr-i e -> Decreasing {Sg} (toSub (singleton u e))
singleton-Decreasing {Sg} {G} {.Ss} {Ss} {B} .id-i u (inj₁ (refl , Het.refl)) = inj₁ (Ctx-length-lemma u , (δ , eq1) , (λ S u₁ → eq2 S u₁)) where
  δ : (S : MTy) → B <<- Ss ∷ G - u ∋ S → Tm Sg G (ctx S) ([] ->> type S)
  δ .(B <<- Ss) zero = fun u id-i
  δ S (suc u₁) = fun (thin u S u₁) id-i
  eq1 : id-s ≡s (δ ∘s toSub (singleton u id-i))
  eq1 S u₁ with thick u u₁ 
  eq1 S .(thin u S x) | inj₁ (x , refl) = cong (fun _) (sym (right-id id-i))
  eq1 .(B <<- Ss) .u | inj₂ (refl , refl) = cong (fun u) (sym (right-id id-i))

  eq2 : id-s ≡s (toSub (singleton u id-i) ∘s δ)
  eq2 ._ (zero {._} {.(_ <<- _)}) rewrite thick-refl u = cong (fun _) (sym (right-id id-i))
  eq2 S (suc {._} {._} {.(_ <<- _)} v) rewrite thick-thin u v = cong (fun _) (sym (right-id id-i))
  
singleton-Decreasing {Sg} {G} {E} {Ss} {B} e u (inj₂ Ss>E) 
  = inj₂
      (begin
       suc (suc (length E) + Ctx-length (G - u)) ≤⟨ s≤s (Ss>E +-mono (begin Ctx-length (G - u) ∎)) ⟩
       Ctx-length (G - u <: B <<- Ss)            ≡⟨ sym (Ctx-length-lemma u) ⟩ 
       Ctx-length G                              ∎)

rigid-decr : ∀ {G G1}{x}(u : G ∋ x) -> Ctx-length (G - u) ≥ Ctx-length G1
                                    -> Ctx-length G > Ctx-length G1  
rigid-decr {G} {G1} {type <<- ctx} u G-u≤G1 = 
     begin suc (Ctx-length G1)                ≤⟨ s≤s G-u≤G1 ⟩ 
           suc (Ctx-length (G - u))           ≤⟨ s≤s (n≤m+n (length ctx) (Ctx-length (G - u))) ⟩ 
           Ctx-length (G - u <: type <<- ctx) ≡⟨ sym (Ctx-length-lemma u) ⟩ 
           Ctx-length G                       ∎

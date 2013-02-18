module Unification.Pruning.Epi-Decr where

open import Data.Nat hiding (_≤_)
open import Data.Nat.Properties
open import Data.Empty
open import Data.Sum

open import Support.Equality

open import Injections
open import MetaRens

open import Syntax

open import Unification.Specification.Decr-Sub
open import Unification.Injections

Epi : _ -> _ -> Set
Epi G G1 = ∃ \ (f : MetaRen G G1) -> MRop.Monic f

Inj-incr : ∀ {A : Set}{X : List A}{Y} -> Inj X Y -> length Y ≥ length X
Inj-incr [] = z≤n
Inj-incr {A} {x ∷ xs} {Y} (u ∷ i [ pf ]) rewrite length-del u = s≤s (Inj-incr j)
  where
    jf : (x₁ : A) → xs ∋ x₁ → Y - u ∋ x₁
    jf _ v with thick u (i $ v)
    ...       | inj₁ (w , _)     = w
    jf ._ v   | inj₂ (refl , eq) = ⊥-elim (∉-∉Im i u pf v (≅-to-≡ eq))

    jf-inj : (x : A) {a b : xs ∋ x} -> jf x a ≡ jf x b -> a ≡ b
    jf-inj x {a} {b} eq 
                 with thick u (i $ a)  | thick u (i $ b)
    jf-inj x₁ refl  | inj₁ (._ , eq1)  | inj₁ (_ , eq2)   = injective i _ _ (trans (sym eq1) eq2)
    jf-inj ._ _     | inj₁ x₂          | inj₂ (refl , eq) = ⊥-elim (∉-∉Im i u pf _ (≅-to-≡ eq))
    jf-inj ._ _     | inj₂ (refl , eq) | p                = ⊥-elim (∉-∉Im i u pf _ (≅-to-≡ eq))

    j : Inj xs (Y - u)
    j = quo jf {jf-inj}


punchout : ∀ {x G G1} -> (f : Epi (x ∷ G) G1) -> Epi G G1 ⊎ Epi G (G1 - body (proj₁ f _ zero))
punchout {x} {G} {G1} (f , f-epic) 
 with any? (λ v → body (f _ (suc v)) ≅∋? body (f _ zero))
... | yes (_ , v , eqty , eqbody) = inj₁ ((λ S x → f S (suc x)) , fsuc-epic)
 where            
  fsuc-epic : MRop.Monic (λ S x → f S (suc x))
  fsuc-epic {C} {g1} {g2} eq = f-epic {C} {g1} {g2} (∋-case (cong (map-Vc (ρ-env (f _ zero))) aux) eq)
    where
      aux : g1 _ (body (f _ zero)) ≡ g2 _ (body (f _ zero))
      aux with type x <<- Ψ (f _ zero) | body (f _ zero) | eqty | eqbody
      aux    | ._                      | ._              | refl | refl = map-Vc-inj (ρ-env (f _ (suc v))) (to-vc (eq _ v))
... | no ¬p = inj₂ (f' , f'-epic) where
  u = body (f _ zero)

  f' : MetaRen G (G1 - u)
  f' S x  with f S (suc x) | inspect (f S) (suc x)
  f' S x     |      i /  v | ⌞ eq ⌟ with thick u v
  ...                               | inj₁ x₂    = i / proj₁ x₂
  f' (._ <<- _) x | i / ._ | ⌞ eq ⌟ | inj₂ refl` = ⊥-elim (¬p (_ , _ , cong (_<<-_ _) (_≈vc_.Ψeq (to-vc eq)) , _≈vc_.beq (to-vc eq)))

  f'-epic : MRop.Monic f'
  f'-epic {C} {g1} {g2} eq S y = wk-inj 
    (begin wk (g1 S y)             ≡⟨ sym (shift-thin g1 S y) ⟩ 
           shift g1 S (thin u S y) ≡⟨ f-epic {_} {shift g1} {shift g2} (∋-case zero-eq suc-eq) S (thin u S y) ⟩
           shift g2 S (thin u S y) ≡⟨ shift-thin g2 S y ⟩ 
           wk (g2 S y)             ∎ )
   where
    open ≡-Reasoning
    shift : MetaRen (G1 - u) C -> MetaRen G1 (_ ∷ C)
    shift g1 S x with thick u x
    shift g1 S₁ x₁  | inj₁ x₂            = wk (g1 _ (proj₁ x₂))
    shift g1 ._ ._  | inj₂ refl` = id-i / zero

    shift-thin : ∀ g S y -> shift g _ (thin u S y) ≡ wk (g S y)
    shift-thin g S y rewrite thick-thin u y = refl

    shift-refl : ∀ g -> shift g _ u ≡ id-i / zero
    shift-refl g rewrite thick-refl u = refl

    shift-refl2 : ∀ {S}{v : _ ∋ S} g g1 -> u ≅∋ v -> shift g _ v ≡ shift g1 _ v
    shift-refl2 {.(type x) <<- .(Ψ (f x zero))} g g1 refl` = trans (shift-refl g) (sym (shift-refl g1))

    zero-eq = cong (map-Vc _) (begin shift g1 _ u ≡⟨ shift-refl g1 ⟩ 
                                     id-i / zero  ≡⟨ sym (shift-refl g2) ⟩ 
                                     shift g2 _ u ∎)

    suc-eq : (shift g1 ∘mr (\ S y -> f S (suc y))) ≡mr (shift g2 ∘mr (\ S y -> f S (suc y)))
    suc-eq S x with thick u (body (f S (suc x))) | eq S x | shift-refl2 {v = (body (f S (suc x)))} g1 g2 
    suc-eq S₁ x₁  | inj₁ x₂                      | p      | _ = cong wk p
    suc-eq S₁ x₁  | inj₂ y₁                      | p      | q = cong (map-Vc _) (q y₁)

  
epi-decr : ∀ {G G1} -> Epi G G1 -> Ctx-length G ≥ Ctx-length G1
epi-decr {[]} {[]}     (f , f-epic) = z≤n
epi-decr {[]} {x ∷ G1} (f , f-epic) 
 with f-epic {x ∷ x ∷ G1} {∋-case (id-i / zero)     (\ _ x -> id-i / suc (suc x))} 
                          {∋-case (id-i / suc zero) (\ _ x -> id-i / suc (suc x))} 
             (\ _ ()) _ zero 
... | () 
epi-decr {x ∷ G} (f , f-epic)   with f _ zero | Data.Sum.map epi-decr epi-decr (punchout (f , f-epic))
epi-decr {x ∷ G} {G1} (f , f-epic) | i / u    | inj₁ G≥G1  = begin
                                                               Ctx-length G1      ≤⟨ G≥G1 ⟩
                                                               Ctx-length G       ≤⟨ n≤m+n (suc (length (ctx x))) (Ctx-length G) ⟩
                                                               Ctx-length (x ∷ G) ∎ where open ≤-Reasoning
epi-decr {x ∷ G} {G1} (f , f-epic) | i / u    | inj₂ G≥G1-u rewrite Ctx-length-lemma u = s≤s (Inj-incr i) +-mono G≥G1-u


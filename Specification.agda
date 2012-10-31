module Specification where

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

open import Injection
open import Injection.Objects
open import Lists

open import Syntax
open import Equality
open import OneHoleContext

open import DSub

Property : ∀ Sg G -> Set₁
Property Sg G = (∀ {G2} -> Sub Sg G G2 -> Set)

Unifies : ∀ {Sg G1 D S} (x y : Term Sg G1 D S) -> Property Sg G1
Unifies x y σ = subT σ x ≡T subT σ y

∃⟦σ⟧_ : ∀ {Sg G1} -> Property Sg G1 -> Set
∃⟦σ⟧ P = ∃ \ G2 -> ∃ \ σ -> P {G2} ⟦ σ ⟧

∃σ_ : ∀ {Sg G1} -> Property Sg G1 -> Set
∃σ_ P = ∃ \ G2 -> ∃ \ σ -> P {G2} σ

Sup : ∀ {Sg G1} -> Property Sg G1 -> Property Sg G1
Sup P σ = (∀ {G'} ρ -> P {G'} ρ -> ρ ≤ σ)

Max : ∀ {Sg G1} -> Property Sg G1 -> Property Sg G1
Max P σ = P σ × Sup P σ

Extensional : ∀ {Sg G} -> Property Sg G -> Set
Extensional P = ∀ {G f g} -> f ≡s g -> P {G} f -> P g

Spec : ∀ {Sg G1 D S} (x y : Term Sg G1 D S) -> Set
Spec x y = ∃⟦σ⟧ Max (Unifies x y) ⊎ ¬ ∃σ Unifies x y

Unifies-ext : ∀ {Sg G1 D S} (x y : Term Sg G1 D S) -> Extensional (Unifies x y)
Unifies-ext x y f≡g subfx≡subfy rewrite subT-ext f≡g x | subT-ext f≡g y = subfx≡subfy

≤-∘ : ∀ {Sg g g1 g2 g3}(ρ : Sub Sg g g1)(p : Sub Sg g g2)(q : Sub Sg g2 g3) -> (ρ≤p : ρ ≤ p) -> proj₁ ρ≤p ≤ q -> ρ ≤ (q ∘s p) 
≤-∘ ρ p q (δ , ρ≡δ∘p) (δ' , δ'≡δ∘q) 
  = δ' , λ S u → begin ρ S u                    ≡⟨ ρ≡δ∘p S u ⟩
                       sub δ (p S u)            ≡⟨ sub-ext δ'≡δ∘q (p S u) ⟩ 
                       subT (δ' ∘s q) (p S u)   ≡⟨ sym (subT-∘ (p S u)) ⟩
                       subT δ' (subT q (p S u)) ∎


sandwich : ∀ {Sg G1 G2 D T} {f g : Term Sg G1 D T -> Term Sg G2 D T} -> (∀ x -> f x ≡ g x) -> ∀ {x y} -> f x ≡T f y -> g x ≡T g y
sandwich eq {x}{y} p rewrite eq x | eq y = p

map-Unifies : ∀ {Sg g h h' d t} {σ : Sub Sg g h}{σ' : Sub Sg g h'}-> σ ≤ σ' -> {x y : Term Sg g d t} -> Unifies x y σ' -> Unifies x y σ
map-Unifies {σ = σ} {σ'} (δ , σ≡δ∘σ') {x} {y} σ'Unifies[x,y] = ≡-T 
         (begin subT σ x           ≡⟨ subT-ext σ≡δ∘σ' x ⟩
                subT (δ ∘s σ') x   ≡⟨ T-≡ (sandwich subT-∘ (T.cong (subT δ) σ'Unifies[x,y])) ⟩
                subT (δ ∘s σ') y   ≡⟨ sym (subT-ext σ≡δ∘σ' y) ⟩
                subT σ y           ∎)

shift_under_by_ : ∀ {Sg G h1 h2 D T} {xs ys : Term Sg G D T} {σ1 : Sub Sg G h1} 
                  -> Unifies xs ys σ1 -> (σ : Sub Sg G h2) -> σ1 ≤ σ -> ∃σ Unifies (subT σ xs) (subT σ ys)
shift_under_by_ eq σ (δ , σ1≡δ∘σ) = _ , δ , sandwich (λ xs₁ → sym (trans (subT-∘ xs₁) (sym (subT-ext σ1≡δ∘σ xs₁)))) eq

cong-spec : ∀ {Sg G D D' T T'} → (d : DTm Sg G (D' , T') (D , T)) -> {x y : Term Sg G D T} → Spec x y → Spec (∫once d x) (∫once d y)
cong-spec d (inj₁ (_ , σ , unifies , sup)) = inj₁ (_ , (σ , (cong-∫once d unifies , (λ ρ ρ-unifies → sup ρ (inv-∫once d ρ-unifies)))))
cong-spec d (inj₂ no-unifier) = inj₂ (λ {(_ , σ , σ-unifies) → no-unifier (_ , (σ , inv-∫once d σ-unifies)) })

optimist : ∀ {Sg m l o D T Ts}(x y : Tm Sg m D T)(xs ys : Tms Sg m D Ts) ->
           (p : Sub Sg m o) (q : Sub Sg o l) ->
           Max (Unifies x y) p 
           -> Max (Unifies (subT p xs) (subT p ys)) q 
           -> Max (Unifies (x ∷ xs) (y ∷ ys)) (q ∘s p)

optimist x y xs ys p q ([p]Unifies[x,y] , sup-p) ([q]Unifies[px,py] , sup-q) = 
             (map-Unifies (q , λ S u → refl) {x} {y} [p]Unifies[x,y] ∷ sandwich subT-∘ [q]Unifies[px,py]) , 
             (λ { ρ ([ρ]Unifies[x,y] ∷ [ρ]Unifies[xs,ys]) → 
               let ρ≤p = sup-p ρ [ρ]Unifies[x,y]
                   δ = proj₁ ρ≤p
                   ρ≡δ∘p = proj₂ ρ≤p
                   δ≤q = sup-q δ (sandwich (λ x₁ → sym (subT-∘ x₁))
                                    (Unifies-ext xs ys ρ≡δ∘p [ρ]Unifies[xs,ys]))
                in ≤-∘ ρ p q ρ≤p δ≤q })


∃σMax[Unifies[x,x]] : ∀ {Sg G D T} (x : Term Sg G D T) -> ∃⟦σ⟧ Max (Unifies x x)
∃σMax[Unifies[x,x]] x = _ ,
                 (DS id-s , inj₁ (refl , IsIso-id)) ,
                 refl-T _ ,
                 (λ ρ x₁ → ρ , (λ S u → sym (ren-id _)))

Spec[xs,ys]⇒Spec[σxs,σys] : ∀ {Sg G G1 D T} {xs ys : Term Sg G D T} (σ : Sub Sg G G1) -> Ctx-length G ≡ Ctx-length G1 -> 
                            IsIso σ -> Spec xs ys -> Spec (subT σ xs) (subT σ ys)
Spec[xs,ys]⇒Spec[σxs,σys] {xs = xs} {ys = ys} σ G~G1 ((δ , id≡δ∘σ) , id≡σ∘δ) (yes (_ , σ₁ , [σ₁]Unifies[xs,ys] , sup-σ₁)) 
   = yes (_ , σ₁ ∘ds (DS δ , inj₁ (sym G~G1 , (σ , id≡σ∘δ) , id≡δ∘σ)) , [σ₁∘δ]Unifies[σxs,σys] , sup-[σ₁∘δ])
  where
    [σ₁∘δ]Unifies[σxs,σys] = sandwich (λ ys →
          begin subT ⟦ σ₁ ⟧ ys                 ≡⟨ cong (subT ⟦ σ₁ ⟧) (trans (sym (subT-id ys)) (subT-ext id≡δ∘σ ys)) ⟩
                subT ⟦ σ₁ ⟧ (subT (δ ∘s σ) ys) ≡⟨ subT-∘ ys ⟩
                subT (⟦ σ₁ ⟧ ∘s (δ ∘s σ)) ys   ≡⟨ subT-ext (λ S x → subT-∘ (σ S x)) ys ⟩
                subT ((⟦ σ₁ ⟧ ∘s δ) ∘s σ) ys   ≡⟨ sym (subT-∘ ys) ⟩
                subT (⟦ σ₁ ⟧ ∘s δ) (subT σ ys) ∎)
          [σ₁]Unifies[xs,ys]

    sup-[σ₁∘δ] : Sup (Unifies (subT σ xs) (subT σ ys)) (⟦ σ₁ ⟧ ∘s δ)
    sup-[σ₁∘δ] ρ [ρ]Unifies[σxs,σys] = δ' , λ S u →
            begin
              ρ S u                       ≡⟨ sym (ren-id (ρ S u)) ⟩
              sub ρ (fun u id-i)          ≡⟨ cong (sub ρ) (trans refl (id≡σ∘δ S u)) ⟩
              sub ρ (sub σ (δ S u))       ≡⟨ sub-∘ {f = ρ} {σ} (δ S u) ⟩
              subT (ρ ∘s σ) (δ S u)       ≡⟨ subT-ext (proj₂ ρ∘σ≤σ₁) (δ S u) ⟩
              subT (δ' ∘s ⟦ σ₁ ⟧) (δ S u) ≡⟨ sym (subT-∘ (δ S u)) ⟩
              subT δ' (subT ⟦ σ₁ ⟧ (δ S u)) ∎
       where
         ρ∘σ≤σ₁ = sup-σ₁ (ρ ∘s σ) (sandwich subT-∘ [ρ]Unifies[σxs,σys])
         δ' = proj₁ ρ∘σ≤σ₁
      
Spec[xs,ys]⇒Spec[σxs,σys] σ G~G1 _ (no ¬p) = no (λ {(_ , σ₁ , eq) → ¬p (_ , σ₁ ∘s σ , sandwich subT-∘ eq)})


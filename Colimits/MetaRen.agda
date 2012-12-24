module Colimits.MetaRen where
open import Data.Product renaming (map to mapΣ)
open import Data.Nat hiding (_≤_) renaming (ℕ to Nat)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality hiding ([_])
import Relation.Binary.HeterogeneousEquality as Het
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; _≇_ ; refl; ≅-to-≡)
open ≡-Reasoning
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.List.All
open import Data.List hiding ([_])

open import Injection
open import Limits.Injection
open import Lists
open import Vars2 

open import Syntax
open import Equality
open import NatCat
open import MetaRens


coproduct : ∀ {A B} -> MRop.Product A B
coproduct {A} {B} = MRop.Prod (A ++ B) inl inr ⟨_,_⟩ 
          (λ {_} {f} {g} S x → trans left-map[id]
            (cong [ f S , g S ]′ (split∘glue≡id (inj₁ x)))) 
          (λ {_} {f} {g} S x → trans left-map[id]
            (cong [ f S , g S ]′ (split∘glue≡id (inj₂ x)))) 
          universal
 where
  inj : ∀ {S} -> A ∋ S ⊎ B ∋ S -> VarClosure (A ++ B) S
  inj x = idmr _ (glue x)

  inl : ∀ S -> A ∋ S  -> VarClosure (A ++ B) S
  inl S x = inj (inj₁ x)

  inr : ∀ S -> B ∋ S  -> VarClosure (A ++ B) S
  inr S x = inj (inj₂ x)

  ⟨_,_⟩ : ∀ {C} → (MetaRen A C) → (MetaRen B C) → (MetaRen (A ++ B) C)
  ⟨ f , g ⟩ S x = [ f S , g S ]′ (split x)
  
  universal : ∀ {C} {f : MetaRen A C} {g : MetaRen B C} {i : MetaRen (A ++ B) C}
               → (i ∘mr inl) ≡mr f → (i ∘mr inr) ≡mr g  → ∀ S x -> ⟨ f , g ⟩ S x ≡ i S x
  universal {C} {f} {g} {i} i∘inl≡f i∘inr≡g S x with split# A x | glue∘split≡id {_} {A} x 
  universal i∘inl≡f i∘inr≡g S .(glue# A (inj₁ x))  | inj₁ x     | refl = sym (trans (sym left-map[id]) (i∘inl≡f S x))
  universal i∘inl≡f i∘inr≡g S .(glue# A (inj₂ y))  | inj₂ y     | refl = sym (trans (sym left-map[id]) (i∘inr≡g S y))


coequalizer-step : ∀ {τ Z X} → (f : All (VarClosure X) Z)(g : All (VarClosure X) Z) 
                 → (equ : MRop.Equalizer (eval f) (eval g)) → let open MRop.Equalizer equ in
                 ∀ (u v : VarClosure X τ) (eu : VarClosure E (type τ <<- Ψ u)) (ev : VarClosure E (type τ <<- Ψ v))
                 → eu ≈vc e _ (body u) → ev ≈vc e _ (body v)
                 → MRop.Equalizer (eval (u ∷ f)) (eval (v ∷ g))
coequalizer-step {τ <<- Ss} {Z} {X} f g (Equ E , e , equ) (i / u) (j / v) (ieu / eu) (jev / ev) eu≈e[u] ev≈e[v] with thick[ eu , ev ]-refl₂ 
coequalizer-step {τ <<- Ss} {Z} {X} f g (Equ E , e , equ) (i / u) (j / v) (ieu / eu) (jev / .eu) (vc refl eq2 eq3) (vc eq4 eq5 eq6) | one refl , eq₁ 
  = MRop.Equ E' , e' , 
    (record {
       commutes = ∋-case commz comms;
       universal = Universal.universal';
       universal-unique = Universal.universal-unique' _ _;
       e∘universal≡m = Universal.universal∘e'≡m _ _ })
  where
   open MRop.IsEqualizer equ
   equ0 = equalizer (i ∘i ieu) (j ∘i jev)
  
   E' : MCtx
   E' = τ <<- _ ∷ E -[ eu , eu ]

   e''' : ∀ S → (x : E ∋ S) → Thick eu eu x → VarClosure E' S
   e''' ._ x (one⊎other (one _))        = Equalizer.e equ0 / zero
   e''' ._ x (one⊎other (other neq eq)) = ⊥-elim (neq refl eq)
   e''' S  x (neither w eq)             = id-i / suc w
   e'' : MetaRen E E'
   e'' S x = e''' S x (thick[ eu , eu ] x)
   e' : MetaRen X E'
   e' = e'' ∘mr e

   eu≈e[u] : (ieu / eu) ≈vc (e _ u)
   eu≈e[u] = vc refl eq2 eq3
   ev≈e[v] : (jev / eu) ≈vc (e _ v)
   ev≈e[v] = vc eq4 eq5 eq6

   e'[u]≡e/zero : e' _ u ≡ (ieu ∘i Equalizer.e equ0) / zero
   e'[u]≡e/zero = trans (cong (bind e'') (sym (promote eu≈e[u]))) (cong (λ th → map-Vc ieu (e''' _ eu th)) thick[ eu , eu ]-refl)

   commz' : map-Vc i (bind e'' (ieu / eu)) ≡ map-Vc j (bind e'' (jev / eu))
   commz' rewrite thick[ eu , eu ]-refl = cong₂ _/_ (trans assoc-∘i (trans (Equalizer.commutes equ0) (sym assoc-∘i))) refl

   commz : map-Vc i (bind e'' (e _ u)) ≡ map-Vc j (bind e'' (e _ v))
   commz = subst₂ (λ eu ev → map-Vc i (bind e'' eu) ≡ map-Vc j (bind e'' ev)) (promote eu≈e[u]) (promote ev≈e[v]) commz'

   comms : (e' ∘mr eval f) ≡mr (e' ∘mr eval g)
   comms S y with e _ (body (eval f S y))  | e _ (body (eval g S y)) | to-vc (commutes S y)
   comms S y    | _ / .w                   | _ / w                   | vc refl eq7 refl 
     = cong₂ _/_ (trans assoc-∘i (trans (cong (λ j₁ → j₁ ∘i ρ-env (e'' _ w)) (≅-to-≡ eq7)) (sym assoc-∘i))) refl

   module Universal {Q : List MTy} (m : MetaRen X Q)
      (m-comm : (m ∘mr eval ((i / u) ∷ f)) ≡mr (m ∘mr eval ((j / v) ∷ g))) where 

    uni = universal m (λ S₁ x₁ → m-comm S₁ (suc x₁))
    e∘uni≡m = e∘universal≡m {_} {m} {(λ S₁ x₁ → m-comm S₁ (suc x₁))}

    abstract
      uni⋆e[u],uni⋆e[v]⇒i,j : map-Vc i (uni ⋆ (ieu / eu)) ≡
                              map-Vc j (uni ⋆ (jev / eu))
      uni⋆e[u],uni⋆e[v]⇒i,j = 
        subst₂ (\ a b → map-Vc i (bind uni a) ≡ map-Vc j (bind uni b)) (sym (promote eu≈e[u])) (sym (promote ev≈e[v])) 
                 (trans (cong (map-Vc i) (e∘uni≡m _ u)) 
                   (trans (m-comm _ zero) 
                   (sym (cong (map-Vc j) (e∘uni≡m _ v)))))

      uni[eu]⇒i∘ieu,j∘jev : (i ∘i ieu) ∘i ρ-env (uni _ eu) ≡ (j ∘i jev) ∘i ρ-env (uni _ eu)
      uni[eu]⇒i∘ieu,j∘jev = (trans (sym assoc-∘i) (trans (≅-to-≡ (_≈vc_.ρeq (to-vc uni⋆e[u],uni⋆e[v]⇒i,j))) assoc-∘i)) 

    universal' : MetaRen E' Q
    universal' ._ zero = Equalizer.universal equ0 (ρ-env (uni _ eu)) uni[eu]⇒i∘ieu,j∘jev / body (uni _ eu)
    universal' S (suc x) = uni S (thin[ eu , eu ] x)

    universal∘e'≡m : ∀ S (x : X ∋ S) → bind universal' (e' _ x) ≡ m _ x
    universal∘e'≡m S x       with e _ x     | thick[ eu , eu ] (body (e _ x)) | e∘uni≡m _ x
    universal∘e'≡m S x          | jex / ex  | neither w eq                    | pr rewrite eq | right-id jex = pr
    universal∘e'≡m (.τ <<- _) x | jex / ex  | one⊎other (other neq eq)        | pr = ⊥-elim (neq refl eq)
    universal∘e'≡m (.τ <<- _) x | jex / .eu | one⊎other (one refl)            | pr = trans (cong₂ _/_ (trans (sym assoc-∘i) 
                                                                                     (cong (_∘i_ jex) (Equalizer.e∘universal≡m equ0))) refl) pr

    universal-unique' : (u : MetaRen E' Q) (e∘u≡m : (u ∘mr e') ≡mr m) → 
                        u ≡mr universal'
    universal-unique' u₁ u∘e'≡m ._ zero    
      = map-Vc-inj (ieu ∘i Equalizer.e equ0) (to-vc
           (begin
              bind u₁ ((ieu ∘i Equalizer.e equ0) / zero) ≡⟨ sym (cong (bind u₁) e'[u]≡e/zero) ⟩
              bind u₁ (e' _ u)                           ≡⟨ u∘e'≡m _ u ⟩
              m _ u                                      ≡⟨ sym (e∘uni≡m _ u) ⟩
              bind uni (e _ u)                           ≡⟨ cong (bind uni) (sym (promote eu≈e[u])) ⟩
              bind uni (ieu / eu)                        ≡⟨ cong₂ _/_
                                                             (trans (cong (_∘i_ ieu) (sym (Equalizer.e∘universal≡m equ0))) assoc-∘i)
                                                             refl ⟩ 
              _ ∎)) 
    universal-unique' u₁ u∘e'≡m  S (suc x) = trans u₁∘suc≡u₂∘thin (universal-unique u₂ u₂∘e≡m S (thin[ eu , eu ] x))
      where
        u₂ : MetaRen E Q
        u₂ S x with thick[ eu , eu ] x
        u₂ .(τ <<- _) x₁ | one⊎other (one eq) = map-Vc (Equalizer.e equ0) (u₁ _ zero)
        u₂ .(τ <<- _) x₁ | one⊎other (other neq eq) = ⊥-elim (neq refl eq)
        u₂ S₁ x₁ | neither w eq = u₁ S₁ (suc w)

        u₁∘suc≡u₂∘thin : u₁ S (suc x) ≡ u₂ S (thin[ eu , eu ] x)
        u₁∘suc≡u₂∘thin rewrite thick[ eu , eu ]-thin x = refl

        u₂∘e≡m : (u₂ ∘mr e) ≡mr m
        u₂∘e≡m _ x with        e _ x    | thick[ eu , eu ] (body (e _ x)) | u∘e'≡m _ x
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (one eq)              | qq = trans (cong₂ _/_ assoc-∘i refl) qq
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (other neq eq)        | qq = ⊥-elim (neq refl eq)
        u₂∘e≡m S₁ x₁         | jex / ex | neither w eq                    | qq rewrite right-id jex = qq

... | other neq eq , eq₁ 
 = MRop.Equ E' , e' , 
    (record {
       commutes = ∋-case commz comms;
       universal = Universal.universal';
       universal-unique = Universal.universal-unique' _ _;
       e∘universal≡m = Universal.universal∘e'≡m _ _})
  where
   open MRop.IsEqualizer equ
   pull0 = pullback (i ∘i ieu) (j ∘i jev)

   E' : MCtx
   E' = τ <<- _ ∷ E -[ eu , ev ]

   e''' : ∀ S → (x : E ∋ S) → Thick eu ev x → VarClosure E' S
   e''' ._ x (one⊎other (one _))        = Pullback.p₁ pull0 / zero
   e''' ._ x (one⊎other (other neq eq)) = Pullback.p₂ pull0 / zero
   e''' S  x (neither w eq)             = id-i / suc w
   e'' : MetaRen E E'
   e'' S x = e''' S x (thick[ eu , ev ] x)
   e' : MetaRen X E'
   e' = e'' ∘mr e

   e'[u]≡p₁/zero : e' _ u ≡ (ieu ∘i Pullback.p₁ pull0) / zero
   e'[u]≡p₁/zero = trans (cong (bind e'') (sym (promote eu≈e[u]))) (cong (λ th → map-Vc ieu (e''' _ eu th)) thick[ eu , ev ]-refl)

   commz' : map-Vc i (bind e'' (ieu / eu)) ≡ map-Vc j (bind e'' (jev / ev))
   commz' rewrite thick[ eu , ev ]-refl 
    with thick[ eu , ev ] ev | thick[ eu , ev ]-refl₂₂ neq
   ... | ._                  | (_ , refl) 
     = cong₂ _/_ (trans assoc-∘i (trans (Pullback.commutes pull0) (sym assoc-∘i))) refl

   commz : map-Vc i (bind e'' (e _ u)) ≡ map-Vc j (bind e'' (e _ v))
   commz rewrite sym (promote eu≈e[u]) | sym (promote ev≈e[v]) = commz'

   comms : ∀ S y → bind e' (eval f S y) ≡ bind e' (eval g S y)
   comms S y with e _ (body (eval f S y))  | e _ (body (eval g S y)) | to-vc (commutes S y)
   comms S y    | _ / .w                   | _ / w                   | vc refl eq7 refl 
      = cong₂ _/_ (trans assoc-∘i
                     (trans (cong (λ j₁ → j₁ ∘i ρ-env (e'' _ w)) (≅-to-≡ eq7))
                      (sym assoc-∘i))) refl

   module Universal {Q : List MTy} (m : MetaRen X Q)
      (m-comm : (m ∘mr eval ((i / u) ∷ f)) ≡mr (m ∘mr eval ((j / v) ∷ g))) where

    uni = universal m (λ S₁ x₁ → m-comm S₁ (suc x₁))
    e∘uni≡m = e∘universal≡m {_} {m} {(λ S₁ x₁ → m-comm S₁ (suc x₁))}

    abstract
      uni⋆e[u],uni⋆e[v]⇒i,j : map-Vc i (bind uni (ieu / eu)) ≈vc
                              map-Vc j (bind uni (jev / ev))
      uni⋆e[u],uni⋆e[v]⇒i,j = 
        to-vc (subst₂ (\ a b → map-Vc i (bind uni a) ≡ map-Vc j (bind uni b)) (sym (promote eu≈e[u])) (sym (promote ev≈e[v])) 
                        (trans (cong (map-Vc i) (e∘uni≡m _ u)) 
                        (trans (m-comm _ zero) 
                        (sym (cong (map-Vc j) (e∘uni≡m _ v))))))

      helper : ∀ {D} (eq : _ ≡ D) → j ∘i (jev ∘i ρ-env (uni _ ev)) ≅ j ∘i (jev ∘i subst (λ D → Inj D _) eq (ρ-env (uni _ ev)))
      helper refl = refl

      uni[eu],uni[ev]⇒i∘ieu,j∘jev : (i ∘i ieu) ∘i ρ-env (uni _ eu) ≡ 
                                    (j ∘i jev) ∘i subst (λ D → Inj D _) (sym (_≈vc_.Ψeq uni⋆e[u],uni⋆e[v]⇒i,j)) (ρ-env (uni _ ev))
      uni[eu],uni[ev]⇒i∘ieu,j∘jev with uni⋆e[u],uni⋆e[v]⇒i,j 
      uni[eu],uni[ev]⇒i∘ieu,j∘jev | vc eq1 eq2 eq3 = (trans (sym assoc-∘i) (trans (≅-to-≡ (Het.trans eq2 (helper (sym eq1)))) assoc-∘i)) 

    universal' : MetaRen E' Q
    universal' ._ zero = Pullback.universal pull0 (ρ-env (uni _ eu)) (subst (λ D → Inj D _) 
                          (sym (_≈vc_.Ψeq uni⋆e[u],uni⋆e[v]⇒i,j)) (ρ-env (uni _ ev))) uni[eu],uni[ev]⇒i∘ieu,j∘jev 
                         / body (uni _ eu)
    universal' S (suc x) = uni S (thin[ eu , ev ] x)

    universal∘e'≡m : ∀ S (x : X ∋ S) → bind universal' (e' _ x) ≡ m _ x
    universal∘e'≡m S x       with e _ x     | thick[ eu , ev ] (body (e _ x)) | e∘uni≡m _ x
    universal∘e'≡m S x          | ex        | neither w eq₂                   | eq₃ rewrite eq₂ | right-id (ρ-env ex) = eq₃
    universal∘e'≡m (.τ <<- _) x | jex / .eu | one⊎other (one refl)            | eq₃
      = trans (cong₂ _/_ (trans (sym assoc-∘i) (cong (_∘i_ jex) (Pullback.p₁∘universal≡q₁ pull0))) refl) eq₃
    universal∘e'≡m (.τ <<- _) x | jex / .ev | one⊎other (other neq₁ refl)     | eq₃
      = trans (promote (vc (_≈vc_.Ψeq uni⋆e[u],uni⋆e[v]⇒i,j) (Het.trans (Het.≡-to-≅ (sym assoc-∘i))
            (Het.trans (Het.≡-to-≅ (cong (_∘i_ jex) (Pullback.p₂∘universal≡q₂ pull0))) 
            (helper2 (sym (_≈vc_.Ψeq uni⋆e[u],uni⋆e[v]⇒i,j))))) (_≈vc_.beq uni⋆e[u],uni⋆e[v]⇒i,j))) eq₃
     where
       helper2 : ∀ {D} (eq : _ ≡ D) → jex ∘i subst (λ D → Inj D _) eq (ρ-env (uni _ ev)) ≅ jex ∘i ρ-env (uni _ ev) 
       helper2 refl = refl

    universal-unique' : (u : MetaRen E' Q) (e∘u≡m : (u ∘mr e') ≡mr m) → 
                        u ≡mr universal'
    universal-unique' u₁ u∘e'≡m ._ zero    = map-Vc-inj (ieu ∘i Pullback.p₁ pull0) (to-vc (begin
                bind u₁ ((ieu ∘i Pullback.p₁ pull0) / zero) ≡⟨ sym (cong (bind u₁) e'[u]≡p₁/zero) ⟩
                bind u₁ (e' _ u)                            ≡⟨ u∘e'≡m _ u ⟩
                m _ u                                       ≡⟨ sym (e∘uni≡m _ u) ⟩ 
                bind uni (e _ u)                            ≡⟨ cong (bind uni) (sym (promote eu≈e[u])) ⟩ 
                (bind uni (ieu / eu))                       ≡⟨ cong₂ _/_ (trans (cong (_∘i_ ieu) 
                                                               (sym (Pullback.p₁∘universal≡q₁ pull0))) assoc-∘i) refl ⟩ 
                _ ∎))

    universal-unique' u₁ u∘e'≡m  S (suc x) = trans u₁∘suc≡u₂∘thin (universal-unique u₂ u₂∘e≡m S (thin[ eu , ev ] x))
      where
        u₂ : MetaRen E Q
        u₂ S x with thick[ eu , ev ] x
        u₂ .(τ <<- _) x₁ | one⊎other (one eq) = map-Vc (Pullback.p₁ pull0) (u₁ _ zero)
        u₂ .(τ <<- _) x₁ | one⊎other (other neq eq) = map-Vc (Pullback.p₂ pull0) (u₁ _ zero)
        u₂ S₁ x₁ | neither w eq = u₁ S₁ (suc w)

        u₁∘suc≡u₂∘thin : u₁ S (suc x) ≡ u₂ S (thin[ eu , ev ] x)
        u₁∘suc≡u₂∘thin rewrite thick[ eu , ev ]-thin x = refl
        u₂∘e≡m : (S₁ : MTy) (x₁ : X ∋ S₁) → (u₂ ∘mr e) S₁ x₁ ≡ m S₁ x₁
        u₂∘e≡m _ x        with e _ x    | thick[ eu , ev ] (body (e _ x)) | u∘e'≡m _ x
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (one eq)              | qq = trans (cong₂ _/_ assoc-∘i refl) qq
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (other neq eq)        | qq = trans (cong₂ _/_ assoc-∘i refl) qq
        u₂∘e≡m S₁ x₁         | jex / ex | neither w eq                    | qq rewrite right-id jex = qq


coequalizer : ∀ {Z X} → (f : All (VarClosure X) Z)(g : All (VarClosure X) Z) → MRop.Equalizer (eval f) (eval g)
coequalizer []          []          = MRop.Equ _ , idmr , 
     (record {
        commutes = λ S x → refl;
        universal = λ m commutes → m;
        universal-unique = λ u e∘u≡m S x → trans (cong₂ _/_ (sym (left-id _)) refl) (e∘u≡m S x);
        e∘universal≡m = λ S x → cong₂ _/_ (left-id _) refl })
coequalizer (i / u ∷ f) (j / v ∷ g) = coequalizer-step f g coequ (i / u) (j / v) (e _ u) (e _ v) (to-vc refl) (to-vc refl)
  where
    coequ = coequalizer f g
    open MRop.Equalizer coequ

pushout' : ∀ {Z Y X} → (f : MetaRen Z X)(g : MetaRen Z Y) → MRop.Pullback f g
pushout' {Z} {Y} {X} f g = MRopProps.convert f g coprod 
                            (MRopProps.Equalizer-ext (proj₂ (reify (π₁ ∘mr f))) 
                                                     (proj₂ (reify (π₂ ∘mr g))) 
                                        (coequalizer (proj₁ (reify (π₁ ∘mr f))) 
                                                     (proj₁ (reify (π₂ ∘mr g)))))
   where
    coprod = coproduct {X} {Y}
    open MRop.Product coprod

abstract
  pushout : ∀ {Z Y X} → (f : MetaRen Z X)(g : MetaRen Z Y) → MRop.Pullback f g
  pushout = pushout'


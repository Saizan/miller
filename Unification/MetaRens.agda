module Unification.MetaRens where

open import Data.Empty
open import Data.Sum
open import Data.List.All

open import Support.Equality
open ≡-Reasoning

open import Injection
open import Injection.Limits
open import Vars.MatchTwo 
open import Vars.SumIso

open import Syntax
open import MetaRens hiding (_⋆_)


record ESub (Sg : Ctx) (G : MCtx) (G1 : MCtx) : Set where
  constructor ι_
  field 
    {cond} : Bool
    ⟦_⟧ : Sub< cond > Sg G G1

open ESub

toESub : ∀ {Sg G G1} -> MetaRen G G1 -> ESub Sg G G1
toESub r = ι (toSub r)

id-e : ∀ {Sg G} -> ESub Sg G G
id-e = ι \ S x -> mvar x id-i

_∘e_ : ∀ {Sg G1 G2 G3} -> ESub Sg G2 G3 -> ESub Sg G1 G2 -> ESub Sg G1 G3
r ∘e s = ι (⟦ r ⟧ ∘s ⟦ s ⟧)

record _≡e_ {Sg G G1} (s : ESub Sg G G1) (s1 : ESub Sg G G1) : Set where
  constructor ES
  field
    []eq : down ⟦ s ⟧ ≡s down ⟦ s1 ⟧

open _≡e_ public

import Category

module ESubop {Sg} = Category MCtx (λ X Y → ESub Sg Y X) (λ f g → g ∘e f) id-e _≡e_
module ESubop2 {Sg} = Category MCtx (λ X Y → ESub Sg Y X) (λ f g → g ∘e f) id-e (\ f g -> ∀ S x -> ⟦ f ⟧ S x ≡d ⟦ g ⟧ S x)

module ESubopProps {Sg : Ctx} where
  module X = ESubop {Sg} 
  module D = X.Props (\ {A} {B} {C} {D} {f} {g} {h} -> ES λ S u → cong-↓↓ (∧-assoc {cond h}) (Sub∘.sub-∘ (⟦ h ⟧ S u)))
                     (λ {A} {B} {f} -> ES \ S u → cong ↓↓ (ren-id (⟦ f ⟧ S u))) 
                     (λ {A} {B} {f} -> ES \ S u → cong-↓↓ (Subid.x∧true≡x {cond f}) (Subid.sub-id (⟦ f ⟧ S u))) 
                     (λ {A} {B} →
                          record {
                          refl = ES λ S x₁ → refl;
                          sym = λ x -> ES \ S x₁ → sym ([]eq x _ _);
                          trans = λ x x₁ -> ES \ S x₂ → trans ([]eq x S x₂) ([]eq x₁ S x₂) }) 
                     (λ { {A} {B} {C} {ι f} {ι h} {ι g} {ι i} eq1 eq2 -> ES \ S u →
                          trans (cong-sub g {f S u} {h S u} ([]eq eq1 S u)) (sub-extd g i (h S u) ([]eq eq2))})
  open D public

module Mixed {Sg : Ctx} where
  module X = ESubop {Sg}
  record Pushout {X Y Z}(f : MetaRen Z X)(g : MetaRen Z Y) : Set where
    constructor Pull_,_,_,_
    field
      P  : MCtx
      p₁ : MetaRen X P
      p₂ : MetaRen Y P
      isPullback : X.IsPullback (toESub f) (toESub g) P (toESub p₁) (toESub p₂)

    open X.IsPullback isPullback public
    
    to-sub : X.Pullback (toESub f) (toESub g)
    to-sub = X.Pull P , toESub p₁ , toESub p₂ , isPullback

  record Coequalizer {X Y}(f g : MetaRen Y X) : Set where
    constructor Equ_,_,_
    field
      E  : MCtx
      e : MetaRen X E
      isEqualizer : X.IsEqualizer (toESub f) (toESub g) E (toESub e)

    open X.IsEqualizer isEqualizer public

    to-sub : X.Equalizer (toESub f) (toESub g)
    to-sub = X.Equ E , toESub e , isEqualizer

  record Coproduct (A B : MCtx) : Set where
    constructor Prod
    field
      A×B : MCtx
      π₁ : MetaRen A A×B
      π₂ : MetaRen B A×B
      ⟨_,_⟩ : ∀ {C} → (ESub Sg A C) → (ESub Sg B C) → (ESub Sg A×B C)

      commute₁ : ∀ {C} {f : ESub Sg A C} {g : ESub Sg B C} → (⟨ f , g ⟩ ∘e toESub π₁) ≡e f
      commute₂ : ∀ {C} {f : ESub Sg A C} {g : ESub Sg B C} → (⟨ f , g ⟩ ∘e toESub π₂) ≡e g
      universal : ∀ {C} {f : ESub Sg A C} {g : ESub Sg B C} {i : ESub Sg A×B C}
                  → (i ∘e toESub π₁) ≡e f → (i ∘e toESub π₂) ≡e g → ⟨ f , g ⟩ ≡e i

    to-sub : X.Product A B
    to-sub = X.Prod A×B (toESub π₁) (toESub π₂) ⟨_,_⟩ commute₁ commute₂ universal


eta : ∀ {Sg G S} -> VarClosure G S -> Tm Sg G (ctx S) (! type S)
eta cl = mvar (body cl) (ρ-env cl)

eta-inj : ∀ {Sg G S} -> (c1 c2 : VarClosure G S) -> eta {Sg} c1 ≡ eta c2 -> c1 ≡ c2
eta-inj (i / v) (.i / .v) refl = refl

↓ : ∀ {Sg G S} -> VarClosure G S -> Tm< false > Sg G (ctx S) (! type S)
↓ cl = ↓↓ (eta cl) 

 
↓-inj : ∀ {Sg G S} -> (c1 c2 : VarClosure G S) -> ↓ {Sg} c1 ≡ ↓ c2 -> c1 ≡ c2
↓-inj c1 c2 eq = eta-inj c1 c2 (↓↓-inj eq)

_⋆_ : ∀ {b Sg G D} → Sub< b > Sg G D → ∀ {S} → VarClosure G S → Tm< b > Sg D (ctx S) (! type S)
f ⋆ (i / u) = ren i (f _ u)

epic-from-sub : ∀ {X Y Sg} -> (f : MetaRen X Y) -> ESubop.Monic {Sg} (toESub f) -> MRop.Monic f
epic-from-sub f f-epic {C} {g1} {g2} eq S u = ↓-inj _ _
     ([]eq
        (f-epic {C} {toESub g1} {toESub g2}
         (ES (λ S₁ u₁ → cong ↓ (eq S₁ u₁))))
        S u)

epic-to-sub2 : ∀ {X Y Sg} -> (f : MetaRen X Y) -> MRop.Monic f -> ESubop2.Monic {Sg} (toESub f)
epic-to-sub2 f f-epic {C} {g1} {g2} eq S u 
 with epic-inv f f-epic S u 
... | (_ , y , j , eq')                                   with f _ y    | eq _ y 
epic-to-sub2 f f-epic {C} {g1} {g2} eq S u | _ , y , j , refl | .(j / u) | z = ren-injd j (⟦ g1 ⟧ S u) (⟦ g2 ⟧ S u) z

epic-to-sub : ∀ {X Y Sg} -> (f : MetaRen X Y) -> MRop.Monic f -> ESubop.Monic {Sg} (toESub f)
epic-to-sub f f-epic {C} {g1} {g2} eq = ES (epic-to-sub2 f f-epic {C} {g1} {g2} ([]eq eq))


mutual
  lift-equalizer : ∀ {b Sg G X Y S} {i j : Inj X Y} (equ : Equalizer i j) (t : Tm< b > Sg G X S) →
                   let open Equalizer equ in ren i t ≡T ren j t → e ⁻¹ t
  lift-equalizer equ (con c ts) (con refl eq) = con c (lifts-equalizer equ ts eq)
  lift-equalizer {true} equ (mvar u j₁) (mvar refl eq) = mvar u ((universal j₁ eq) , e∘universal≡m)
    where open Equalizer equ
  lift-equalizer {false} equ (mvar u ts) (mvar refl eq) = mvar u (lifts-equalizer equ ts (≡-T eq)) 
  lift-equalizer equ (var x ts) (var eqv eqts) = var (proj₁ r) (sym (proj₂ r)) (lifts-equalizer equ ts eqts)
    where r = e$u≡m equ _ x eqv
  lift-equalizer equ (lam t) (lam eq) = lam (lift-equalizer (cons-equalizer _ _ equ) t eq)

  lifts-equalizer : ∀ {Sg G X Y S b} {i j : Inj X Y} (equ : Equalizer i j) (t : Tms< b > Sg G X S) → 
                    let open Equalizer equ in rens i t ≡T rens j t → e ⁻¹ t
  lifts-equalizer equ [] eq = []
  lifts-equalizer equ (t ∷ ts) (eqt ∷ eqts) = lift-equalizer equ t eqt ∷ lifts-equalizer equ ts eqts

mutual
  lift-pullback : ∀ {b X Y Z} {i : Inj X Z}{j : Inj Y Z} (pull : Pullback i j) → let open Pullback pull in 
                  ∀ {Sg G T} (t : Tm< b > Sg G _ T) s → ren i t ≡T ren j s → p₂ ⁻¹ s
  lift-pullback pull (con c ts) (mvar u j₁) ()
  lift-pullback pull (con c ts) (var x ts₁) ()
  lift-pullback pull (mvar u j₁) (con c ts) ()
  lift-pullback pull (mvar u j₁) (var x ts) ()
  lift-pullback pull (var x ts) (con c ts₁) ()
  lift-pullback pull (var x ts) (mvar u j₁) ()

  lift-pullback pull (con c ts) (con .c ts₁) (con refl eq) = con c (lifts-pullback pull ts ts₁ eq)
  lift-pullback pull (lam t)    (lam s)      (lam eq)      = lam (lift-pullback (cons-pullback _ _ pull) t s eq)
  lift-pullback {true} pull (mvar u q₁) (mvar .u q₂)  (mvar refl i∘q₁≡j∘q₂) = mvar u (universal q₁ q₂ i∘q₁≡j∘q₂ , p₂∘universal≡q₂)
    where open Pullback pull
  lift-pullback {false} pull (mvar u q₁) (mvar .u q₂)  (mvar refl eq) = mvar u (lifts-pullback pull q₁ q₂ (≡-T eq))
  lift-pullback pull (var x ts) (var x₁ ts₁) (var i$x≡j$x₁ eqts) = var (proj₁ r) (proj₂ (proj₂ r)) (lifts-pullback pull ts ts₁ eqts)
    where r = p$u≡q _ _ pull _ x₁ x i$x≡j$x₁ 

  lifts-pullback : ∀ {b X Y Z} {i : Inj X Z}{j : Inj Y Z} (pull : Pullback i j) → let open Pullback pull in 
                  ∀ {Sg G T} (t : Tms< b > Sg G _ T) s → rens i t ≡T rens j s → p₂ ⁻¹ s
  lifts-pullback pull []       []         eq           = []
  lifts-pullback pull (t ∷ ts) (t₁ ∷ ts₁) (eqt ∷ eqts) = (lift-pullback pull t t₁ eqt) ∷ (lifts-pullback pull ts ts₁ eqts)

lift-pullback-other : ∀ {b X Y Z} {i : Inj X Z}{j : Inj Y Z} (pull : Pullback i j) → let open Pullback pull in 
                      ∀ {Sg G T} (t : Tm< b > Sg G _ T) s → ren i t ≡ ren j s → (p₂⁻¹s : p₂ ⁻¹ s) 
                      -> let z = proj₁ (forget p₂⁻¹s) in ren p₁ z ≡ t
lift-pullback-other {i = i} {j = j} pull t s eq p₂⁻¹s = ren-inj i _ _
                                                          (trans (sym (ren-∘ z))
                                                           (trans (cong (λ j₁ → ren j₁ z) commutes)
                                                            (trans (ren-∘ _) 
                                                             (trans (cong (ren j) ren[p₂,z]≡s) (sym eq)))))
  where
    open Pullback pull
    z = proj₁ (forget p₂⁻¹s)
    ren[p₂,z]≡s = proj₂ (forget p₂⁻¹s)

coequalizer-step : ∀ {τ Z X} (f : All (VarClosure X) Z)(g : All (VarClosure X) Z) {Sg} ->
                 (equ : Mixed.Coequalizer {Sg} (eval f) (eval g)) → let open Mixed.Coequalizer equ in 
                 ∀ (u v : VarClosure X τ) (eu : VarClosure E (type τ <<- Ψ u)) (ev : VarClosure E (type τ <<- Ψ v))
                 → eu ≈vc e _ (body u) → ev ≈vc e _ (body v)
                 → Mixed.Coequalizer {Sg} (eval (u ∷ f)) (eval (v ∷ g))
coequalizer-step {τ <<- Ss} {Z} {X} f g {Sg} equ (i / u) (j / v) (ieu / eu) (jev / ev) eu≈e[u] ev≈e[v] with thick[ eu , ev ]-refl₂ 
coequalizer-step {τ <<- Ss} {Z} {X} f g {Sg} equ (i / u) (j / v) (ieu / eu) (jev / .eu) (vc refl eq2 eq3) (vc eq4 eq5 eq6) | one refl , eq₁ 
  = Mixed.Equ E' , e' , 
    (record {
       commutes = ES (∋-case (cong ↓ commz) (λ a y → cong ↓ (comms a y)));
       universal = λ m m-comm → ι Universal.universal' m m-comm;
       universal-unique = λ {Q} {m} {m-comm} x y → ES (Universal.universal-unique' m m-comm {cond x} ⟦ x ⟧ ([]eq y));
       e∘universal≡m = \ {Q} {m} {m-comm} -> ES (Universal.universal∘e'≡m m m-comm) }) 
  where
   open Mixed.Coequalizer equ
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

   commutes-mr : (e ∘mr eval f) ≡mr (e ∘mr eval g)
   commutes-mr S y = (↓-inj (bind e ((eval f S y))) (bind e ((eval g S y))) ([]eq commutes S y))

   commz' : map-Vc i (bind e'' (ieu / eu)) ≡ map-Vc j (bind e'' (jev / eu))
   commz' rewrite thick[ eu , eu ]-refl = cong₂ _/_ (trans assoc-∘i (trans (Equalizer.commutes equ0) (sym assoc-∘i))) refl

   commz : map-Vc i (bind e'' (e _ u)) ≡ map-Vc j (bind e'' (e _ v))
   commz = subst₂ (λ eu ev → map-Vc i (bind e'' eu) ≡ map-Vc j (bind e'' ev)) (promote eu≈e[u]) (promote ev≈e[v]) commz'

   comms : (e' ∘mr eval f) ≡mr (e' ∘mr eval g)
   comms S y with e _ (body (eval f S y))  | e _ (body (eval g S y)) | to-vc (commutes-mr S y)
   comms S y    | _ / .w                   | _ / w                   | vc refl eq7 refl 
     = cong₂ _/_ (trans assoc-∘i (trans (cong (λ j₁ → j₁ ∘i ρ-env (e'' _ w)) (≅-to-≡ eq7)) (sym assoc-∘i))) refl

   module Universal {Q : List MTy} (m : ESub Sg X Q)
      (m-comm : (m ∘e toESub (eval ((i / u) ∷ f))) ≡e (m ∘e toESub (eval ((j / v) ∷ g)))) where 

    uni = ⟦ universal m (ES (λ S₁ x₁ → []eq m-comm S₁ (suc x₁))) ⟧
    buni = cond (universal m (ES (λ S₁ x₁ → []eq m-comm S₁ (suc x₁))))
    e∘uni≡m = []eq (e∘universal≡m {_} {m} {ES (λ S₁ x₁ → []eq m-comm S₁ (suc x₁))})

    abstract
      uni⋆e[u],uni⋆e[v]⇒i,j : ren i (uni ⋆ (ieu / eu)) ≡d
                              ren j (uni ⋆ (jev / eu))
      uni⋆e[u],uni⋆e[v]⇒i,j = 
        subst₂ (\ a b → ren i (uni ⋆ a) ≡d ren j (uni ⋆ b)) (sym (promote eu≈e[u])) (sym (promote ev≈e[v])) 
                 (trans (cong-ren {b1 = buni} {b2 = cond m} i (e∘uni≡m _ u))
                   (trans ([]eq m-comm _ zero)
                   (sym (cong-ren {b1 = buni} {b2 = cond m} j (e∘uni≡m _ v)))))

      uni[eu]⇒i∘ieu,j∘jev : ren (i ∘i ieu) (uni _ eu) ≡d ren (j ∘i jev) (uni _ eu)
      uni[eu]⇒i∘ieu,j∘jev = trans (cong ↓↓ (ren-∘ (uni _ eu))) (trans uni⋆e[u],uni⋆e[v]⇒i,j (sym (cong ↓↓ (ren-∘ (uni _ eu)))))
    
    equ0⁻¹uni[eu] = forget (lift-equalizer equ0 (uni _ eu) (≡-T (↓↓-inj uni[eu]⇒i∘ieu,j∘jev)))

    universal' : Sub< _ > Sg E' Q
    universal' ._ zero = proj₁ equ0⁻¹uni[eu]
    universal' S (suc x) = uni S (thin[ eu , eu ] x)

    universal∘e'≡m : ∀ S (x : X ∋ S) → (universal' ⋆ (e' _ x)) ≡d ⟦ m ⟧ _ x
    universal∘e'≡m S x       with e _ x     | thick[ eu , eu ] (body (e _ x)) | e∘uni≡m _ x
    universal∘e'≡m S x          | jex / ex  | neither w eq                    | pr rewrite eq | right-id jex = pr
    universal∘e'≡m (.τ <<- _) x | jex / ex  | one⊎other (other neq eq)        | pr = ⊥-elim (neq refl eq)
    universal∘e'≡m (.τ <<- _) x | jex / .eu | one⊎other (one refl)            | pr 
                   = trans (cong ↓↓ (trans (ren-∘ _) (cong (ren _) (proj₂ equ0⁻¹uni[eu])))) pr

    universal-unique' : ∀ {b} -> (u : Sub< b > Sg E' Q) (e∘u≡m : ∀ S x -> (u ∘s toSub e') S x ≡d ⟦ m ⟧ S x) → ∀ S x -> u S x ≡d universal' S x
    universal-unique' {b} u₁ u∘e'≡m ._ zero    
      = ren-injd {b1 = b} {b2 = buni} (ieu ∘i Equalizer.e equ0) _ _
          (begin
           ↓↓ (u₁ ⋆ ((ieu ∘i Equalizer.e equ0) / zero)) ≡⟨ cong ↓↓ (sym (cong (_⋆_ u₁) e'[u]≡e/zero)) ⟩
           ↓↓ (u₁ ⋆ e' _ u)                             ≡⟨ u∘e'≡m _ u ⟩
           ↓↓ (⟦ m ⟧ _ u)                               ≡⟨ sym (e∘uni≡m _ u) ⟩
           ↓↓ (uni ⋆ e _ u)                             ≡⟨ cong ↓↓ (cong (_⋆_ uni) (sym (promote eu≈e[u]))) ⟩
           ↓↓ (uni ⋆ (ieu / eu))                        ≡⟨ cong ↓↓ (sym (trans (ren-∘ _) (cong (ren _) (proj₂ equ0⁻¹uni[eu])))) ⟩ 
           ↓↓ (ren (ieu ∘i Equalizer.e equ0) (proj₁ equ0⁻¹uni[eu]))  ∎)
    universal-unique' u₁ u∘e'≡m  S (suc x) = trans (cong ↓↓ u₁∘suc≡u₂∘thin) ([]eq (universal-unique (ι u₂) (ES u₂∘e≡m)) S (thin[ eu , eu ] x))
      where
        u₂ : Sub< _ > Sg E Q
        u₂ S x with thick[ eu , eu ] x
        u₂ .(τ <<- _) x₁ | one⊎other (one eq) = ren (Equalizer.e equ0) (u₁ _ zero)
        u₂ .(τ <<- _) x₁ | one⊎other (other neq eq) = ⊥-elim (neq refl eq)
        u₂ S₁ x₁ | neither w eq = u₁ S₁ (suc w)

        u₁∘suc≡u₂∘thin : u₁ S (suc x) ≡ u₂ S (thin[ eu , eu ] x)
        u₁∘suc≡u₂∘thin rewrite thick[ eu , eu ]-thin x = refl

        u₂∘e≡m : ∀ S x -> (u₂ ∘s toSub e) S x ≡d ⟦ m ⟧ S x
        u₂∘e≡m _ x with        e _ x    | thick[ eu , eu ] (body (e _ x)) | u∘e'≡m _ x
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (one eq)              | qq = trans (cong ↓↓ (sym (ren-∘ (u₁ _ zero)))) qq
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (other neq eq)        | qq = ⊥-elim (neq refl eq)
        u₂∘e≡m S₁ x₁         | jex / ex | neither w eq                    | qq rewrite right-id jex = qq

... | other neq eq , eq₁ 
 = Mixed.Equ E' , e' , 
    (record {
       commutes = ES (∋-case (cong ↓ commz) (λ a y → cong ↓ (comms a y)));
       universal = λ m m-comm → ι Universal.universal' m m-comm;
       universal-unique = λ {Q} {m} {m-comm} x y →
                              ES (Universal.universal-unique' m m-comm {cond x} ⟦ x ⟧ ([]eq y));
       e∘universal≡m = λ {Q} {m} {m-comm} → ES (Universal.universal∘e'≡m m m-comm)})
  where
   open Mixed.Coequalizer equ
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

   commutes-mr : (e ∘mr eval f) ≡mr (e ∘mr eval g)
   commutes-mr S y = (↓-inj (bind e ((eval f S y))) (bind e ((eval g S y))) ([]eq commutes S y))

   commz' : map-Vc i (bind e'' (ieu / eu)) ≡ map-Vc j (bind e'' (jev / ev))
   commz' rewrite thick[ eu , ev ]-refl 
    with thick[ eu , ev ] ev | thick[ eu , ev ]-refl₂₂ neq
   ... | ._                  | (_ , refl) 
     = cong₂ _/_ (trans assoc-∘i (trans (Pullback.commutes pull0) (sym assoc-∘i))) refl

   commz : map-Vc i (bind e'' (e _ u)) ≡ map-Vc j (bind e'' (e _ v))
   commz rewrite sym (promote eu≈e[u]) | sym (promote ev≈e[v]) = commz'

   comms : ∀ S y → bind e' (eval f S y) ≡ bind e' (eval g S y)
   comms S y with e _ (body (eval f S y))  | e _ (body (eval g S y)) | to-vc (commutes-mr S y)
   comms S y    | _ / .w                   | _ / w                   | vc refl eq7 refl 
      = cong₂ _/_ (trans assoc-∘i
                     (trans (cong (λ j₁ → j₁ ∘i ρ-env (e'' _ w)) (≅-to-≡ eq7))
                      (sym assoc-∘i))) refl

   module Universal {Q : List MTy} (m : ESub Sg X Q)
      (m-comm : (m ∘e toESub (eval ((i / u) ∷ f))) ≡e (m ∘e toESub (eval ((j / v) ∷ g)))) where

    uni' = universal m (ES λ S₁ x₁ → []eq m-comm S₁ (suc x₁))
    uni = ⟦ uni' ⟧
    buni = cond uni'
    e∘uni≡m = []eq (e∘universal≡m {_} {m} {(ES λ S₁ x₁ → []eq m-comm S₁ (suc x₁))})

    abstract
      uni⋆e[u],uni⋆e[v]⇒i,j : ren i (uni ⋆ (ieu / eu)) ≡d
                              ren j (uni ⋆ (jev / ev))
      uni⋆e[u],uni⋆e[v]⇒i,j = 
        (subst₂ (\ a b → ren i (uni ⋆ a) ≡d ren j (uni ⋆ b)) (sym (promote eu≈e[u])) (sym (promote ev≈e[v])) 
                        (trans (cong-ren {b1 = buni} {b2 = cond m} i (e∘uni≡m _ u)) 
                        (trans ([]eq m-comm _ zero) 
                          (sym (cong-ren {b1 = buni} {b2 = cond m} j (e∘uni≡m _ v))))))

      uni[eu],uni[ev]⇒i∘ieu,j∘jev : ren (i ∘i ieu) (uni _ eu) ≡d 
                                    ren (j ∘i jev) (uni _ ev)
      uni[eu],uni[ev]⇒i∘ieu,j∘jev = trans (cong ↓↓ (ren-∘ (uni _ eu))) (trans uni⋆e[u],uni⋆e[v]⇒i,j (sym (cong ↓↓ (ren-∘ (uni _ ev)))))

    p₂⁻¹uni[ev] = lift-pullback pull0 (uni _ eu) (uni _ ev) (≡-T (↓↓-inj uni[eu],uni[ev]⇒i∘ieu,j∘jev))

    z = proj₁ (forget p₂⁻¹uni[ev])

    ren[p₂,z]≡uni[ev] = proj₂ (forget p₂⁻¹uni[ev])
    ren[p₁,z]≡uni[eu] = lift-pullback-other pull0 (uni _ eu) (uni _ ev) (↓↓-inj uni[eu],uni[ev]⇒i∘ieu,j∘jev) p₂⁻¹uni[ev] 
                     
    universal' : Sub< _ > Sg E' Q
    universal' ._ zero    = z
    universal'  S (suc x) = uni S (thin[ eu , ev ] x)

    universal∘e'≡m : ∀ S (x : X ∋ S) → (universal' ⋆ (e' _ x)) ≡d ⟦ m ⟧ _ x
    universal∘e'≡m S x       with e _ x     | thick[ eu , ev ] (body (e _ x)) | e∘uni≡m _ x
    universal∘e'≡m S x          | ex        | neither w eq₂                   | eq₃ rewrite eq₂ | right-id (ρ-env ex) = eq₃
    universal∘e'≡m (.τ <<- _) x | jex / .eu | one⊎other (one refl)            | eq₃
      = trans (cong ↓↓ (trans (ren-∘ _) (cong (ren jex) ren[p₁,z]≡uni[eu]))) eq₃
    universal∘e'≡m (.τ <<- _) x | jex / .ev | one⊎other (other neq₁ refl)     | eq₃
      = trans (cong ↓↓ (trans (ren-∘ _) (cong (ren jex) ren[p₂,z]≡uni[ev]))) eq₃

    universal-unique' : ∀ {b} -> (u : Sub< b > Sg E' Q) (e∘u≡m : ∀ S x -> (u ∘s toSub e') S x ≡d ⟦ m ⟧ S x) → ∀ S x -> u S x ≡d universal' S x
    universal-unique' {b} u₁ u∘e'≡m ._ zero    = ren-injd {b1 = b} {b2 = buni} (ieu ∘i Pullback.p₁ pull0) _ _
          (begin
           ↓↓ (u₁ ⋆ ((ieu ∘i Pullback.p₁ pull0) / zero)) ≡⟨ cong ↓↓ (sym (cong (_⋆_ u₁) e'[u]≡p₁/zero)) ⟩
           ↓↓ (u₁ ⋆ e' _ u)                              ≡⟨ u∘e'≡m _ u ⟩
           ↓↓ (⟦ m ⟧ _ u)                                ≡⟨ sym (e∘uni≡m _ u) ⟩
           ↓↓ (uni ⋆ e _ u)                              ≡⟨ cong ↓↓ (cong (_⋆_ uni) (sym (promote eu≈e[u]))) ⟩
           ↓↓ (uni ⋆ (ieu / eu))                         ≡⟨ cong ↓↓ (sym (trans (ren-∘ _) (cong (ren ieu) ren[p₁,z]≡uni[eu]))) ⟩ 
           ↓↓ (ren (ieu ∘i Pullback.p₁ pull0) z)         ∎) 

    universal-unique' u₁ u∘e'≡m  S (suc x) = trans (cong ↓↓ u₁∘suc≡u₂∘thin) ([]eq (universal-unique (ι u₂) (ES u₂∘e≡m)) S (thin[ eu , ev ] x))
      where
        u₂ : Sub< _ > Sg E Q
        u₂ S x with thick[ eu , ev ] x
        u₂ .(τ <<- _) x₁ | one⊎other (one eq) = ren (Pullback.p₁ pull0) (u₁ _ zero)
        u₂ .(τ <<- _) x₁ | one⊎other (other neq eq) = ren (Pullback.p₂ pull0) (u₁ _ zero)
        u₂ S₁ x₁ | neither w eq = u₁ S₁ (suc w)

        u₁∘suc≡u₂∘thin : u₁ S (suc x) ≡ u₂ S (thin[ eu , ev ] x)
        u₁∘suc≡u₂∘thin rewrite thick[ eu , ev ]-thin x = refl

        u₂∘e≡m : (S₁ : MTy) (x₁ : X ∋ S₁) → (u₂ ∘s toSub e) S₁ x₁ ≡d ⟦ m ⟧ S₁ x₁
        u₂∘e≡m _ x        with e _ x    | thick[ eu , ev ] (body (e _ x)) | u∘e'≡m _ x
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (one eq)              | qq = trans (cong ↓↓ (sym (ren-∘ (u₁ _ zero)))) qq
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (other neq eq)        | qq = trans (cong ↓↓ (sym (ren-∘ (u₁ _ zero)))) qq
        u₂∘e≡m S₁ x₁         | jex / ex | neither w eq                    | qq rewrite right-id jex = qq

coequalizer : ∀ {Z X} → (f : All (VarClosure X) Z)(g : All (VarClosure X) Z) → ∀ {Sg} -> 
              Mixed.Coequalizer {Sg} (eval f) (eval g)
coequalizer []          []          = Mixed.Equ _ , idmr , 
     (record {
        commutes = ES λ S x → refl;
        universal = λ m commutes → m;
        universal-unique = λ u e∘u≡m → ES (λ S x → trans (sym (cong ↓↓ (ren-id (⟦ u ⟧ S x)))) ([]eq e∘u≡m S x));
        e∘universal≡m = \ {Q} {m} -> ES λ S x → cong ↓↓ (ren-id (⟦ m ⟧ S x)) })
coequalizer (i / u ∷ f) (j / v ∷ g) = coequalizer-step f g coequ (i / u) (j / v) (e _ u) (e _ v) (to-vc refl) (to-vc refl)
  where 
    coequ = coequalizer f g 
    open Mixed.Coequalizer coequ


coproduct : ∀ {A B Sg} -> Mixed.Coproduct {Sg} A B
coproduct {A} {B} {Sg} = Mixed.Prod (A ++ B) inl inr ⟨_,_⟩ 
          (λ {_} {f} {g} → ES
                             (λ S x →
                                trans (ren-id _)
                                (cong (helper (down ⟦ f ⟧) (down ⟦ g ⟧))
                                 (split∘glue≡id {_} {A} (inj₁ x)))))
          (λ {_} {f} {g} → ES
                             (λ S x →
                                trans (ren-id _)
                                (cong (helper (down ⟦ f ⟧) (down ⟦ g ⟧))
                                 (split∘glue≡id {_} {A} (inj₂ x)))))
          (\ x y -> ES (universal x y))
 where
  inj : ∀ {S} -> A ∋ S ⊎ B ∋ S -> VarClosure (A ++ B) S
  inj x = idmr _ (glue x)

  inl : ∀ S -> A ∋ S  -> VarClosure (A ++ B) S
  inl S x = inj (inj₁ x)

  inr : ∀ S -> B ∋ S  -> VarClosure (A ++ B) S
  inr S x = inj (inj₂ x)

  helper : ∀ {C b} → Sub< b > Sg A C → Sub< b > Sg B C → ∀ {T} -> (A ∋ T ⊎ B ∋ T) -> Tm< b > Sg C (ctx T) (! (type T))
  helper f g {type <<- ctx} (inj₁ x) = f _ x
  helper f g {type <<- ctx} (inj₂ y) = g _ y

  ⟨_,_⟩ : ∀ {C} → (ESub Sg A C) → (ESub Sg B C) → (ESub Sg (A ++ B) C)
  ⟨ f , g ⟩ = ι (λ S u → helper (down ⟦ f ⟧) (down ⟦ g ⟧) (split# A u))
 
  universal : ∀ {C} {f : ESub Sg A C} {g : ESub Sg B C} {i : ESub Sg (A ++ B) C}
               → (i ∘e toESub inl) ≡e f → (i ∘e toESub inr) ≡e g  → down ⟦ ⟨ f , g ⟩ ⟧ ≡s down ⟦ i ⟧ 
  universal (i∘inl≡f) (i∘inr≡g) S x with split# A x | glue∘split≡id {_} {A} x 
  universal {i = ι i} (i∘inl≡f) (i∘inr≡g) S .(glue# A (inj₁ x)) | inj₁ x | refl = sym (trans (sym (cong ↓↓ (ren-id (i S _)))) ([]eq i∘inl≡f S x))
  universal {i = ι i} (i∘inl≡f) (i∘inr≡g) S .(glue# A (inj₂ y)) | inj₂ y | refl = sym (trans (sym (cong ↓↓ (ren-id (i S _)))) ([]eq i∘inr≡g S y))

pushout' : ∀ {Z Y X Sg} → (f : MetaRen Z X)(g : MetaRen Z Y) → ESubop.Pullback {Sg} (toESub f) (toESub g)
pushout' {Z} {Y} {X} {Sg} f g = ESubopProps.convert (toESub f) (toESub g) (Mixed.Coproduct.to-sub coprod) 
                           (ESubopProps.Equalizer-ext (ES λ S u → cong ↓↓ (cong eta (proj₂ (reify (π₁ ∘mr f)) S u))) 
                                                     (ES λ S u →  cong ↓↓ (cong eta (proj₂ (reify (π₂ ∘mr g)) S u)))
                              (Mixed.Coequalizer.to-sub
                               (coequalizer (proj₁ (reify (π₁ ∘mr f)))
                                (proj₁ (reify (π₂ ∘mr g))))))
   where
    coprod = coproduct {X} {Y}
    open Mixed.Coproduct {Sg} coprod

abstract
  pushout : ∀ {Z Y X Sg} → (f : MetaRen Z X)(g : MetaRen Z Y) → Mixed.Pushout {Sg} f g
  pushout f g = Mixed.Pull P , _ , _ , isPullback
    where
      open ESubop.Pullback (pushout' f g)



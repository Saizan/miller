module Colimits.Sub where

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
open import Vars.SumIso

open import Injection
open import Limits.Injection
open import Data.List.Extras
open import Vars2 

open import Syntax
open import Equality
open import MetaRens hiding (_⋆_)
open import RenOrn

module Mixed {Sg : Ctx} where
  module X = Subop {Sg}
  record Pushout {X Y Z}(f : MetaRen Z X)(g : MetaRen Z Y) : Set where
    constructor Pull_,_,_,_
    field
      P  : MCtx
      p₁ : MetaRen X P
      p₂ : MetaRen Y P
      isPullback : X.IsPullback (toSub f) (toSub g) P (toSub p₁) (toSub p₂)

    open X.IsPullback isPullback public
    
    to-sub : X.Pullback (toSub f) (toSub g)
    to-sub = X.Pull P , toSub p₁ , toSub p₂ , isPullback

  record Coequalizer {X Y}(f g : MetaRen Y X) : Set where
    constructor Equ_,_,_
    field
      E  : MCtx
      e : MetaRen X E
      isEqualizer : X.IsEqualizer (toSub f) (toSub g) E (toSub e)

    open X.IsEqualizer isEqualizer public

    to-sub : X.Equalizer (toSub f) (toSub g)
    to-sub = X.Equ E , toSub e , isEqualizer

  record Coproduct (A B : MCtx) : Set where
    constructor Prod
    field
      A×B : MCtx
      π₁ : MetaRen A A×B
      π₂ : MetaRen B A×B
      ⟨_,_⟩ : ∀ {C} → (Sub Sg A C) → (Sub Sg B C) → (Sub Sg A×B C)

      commute₁ : ∀ {C} {f : Sub Sg A C} {g : Sub Sg B C} → (⟨ f , g ⟩ ∘s toSub π₁) ≡s f
      commute₂ : ∀ {C} {f : Sub Sg A C} {g : Sub Sg B C} → (⟨ f , g ⟩ ∘s toSub π₂) ≡s g
      universal : ∀ {C} {f : Sub Sg A C} {g : Sub Sg B C} {i : Sub Sg A×B C}
               → (i ∘s toSub π₁) ≡s f → (i ∘s toSub π₂) ≡s g → ⟨ f , g ⟩ ≡s i

    to-sub : X.Product A B
    to-sub = X.Prod A×B (toSub π₁) (toSub π₂) ⟨_,_⟩ commute₁ commute₂ universal


eta : ∀ {Sg G S} -> VarClosure G S -> Tm Sg G (ctx S) (! type S)
eta cl = mvar (body cl) (ρ-env cl)

eta-inj : ∀ {Sg G S} -> (c1 c2 : VarClosure G S) -> eta {Sg} c1 ≡ eta c2 -> c1 ≡ c2
eta-inj (i / v) (.i / .v) refl = refl

_⋆_ : ∀ {Sg G D} → Sub Sg G D → ∀ {S} → VarClosure G S → Tm Sg D (ctx S) (! type S)
f ⋆ (i / u) = ren i (f _ u)

epic-from-sub : ∀ {X Y Sg} -> (f : MetaRen X Y) -> Subop.Monic {Sg} (toSub f) -> MRop.Monic f
epic-from-sub f f-epic {C} {g1} {g2} eq S u = eta-inj _ _
     (f-epic {C} {toSub g1} {toSub g2} (λ S₁ u₁ → cong eta (eq S₁ u₁)) S u)

epic-to-sub : ∀ {X Y Sg} -> (f : MetaRen X Y) -> MRop.Monic f -> Subop.Monic {Sg} (toSub f)
epic-to-sub f f-epic {C} {g1} {g2} eq S u with epic-inv f f-epic S u 
... | (_ , y , j , eq') with f _ y | eq _ y 
epic-to-sub f f-epic eq S u | _ , y , j , refl | .(j / u) | z = ren-inj j _ _ z

mutual
  lift-equalizer : ∀ {Sg G X Y S} {i j : Inj X Y} (equ : Equalizer i j) (t : Tm Sg G X S) →
                   let open Equalizer equ in ren i t ≡T ren j t → e ⁻¹ t
  lift-equalizer equ (con c ts) (con refl eq) = con c (lifts-equalizer equ ts eq)
  lift-equalizer equ (mvar u j₁) (mvar refl eq) = mvar u (universal j₁ eq , e∘universal≡m)
    where open Equalizer equ
  lift-equalizer equ (var x ts) (var eqv eqts) = var (proj₁ r) (sym (proj₂ r)) (lifts-equalizer equ ts eqts)
    where r = e$u≡m equ _ x eqv
  lift-equalizer equ (lam t) (lam eq) = lam (lift-equalizer (cons-equalizer _ _ equ) t eq)

  lifts-equalizer : ∀ {Sg G X Y S} {i j : Inj X Y} (equ : Equalizer i j) (t : Tms Sg G X S) → 
                    let open Equalizer equ in rens i t ≡T rens j t → e ⁻¹ t
  lifts-equalizer equ [] eq = []
  lifts-equalizer equ (t ∷ ts) (eqt ∷ eqts) = lift-equalizer equ t eqt ∷ lifts-equalizer equ ts eqts

mutual
  lift-pullback : ∀ {X Y Z} {i : Inj X Z}{j : Inj Y Z} (pull : Pullback i j) → let open Pullback pull in 
                  ∀ {Sg G T} (t : Tm Sg G _ T) s → ren i t ≡T ren j s → p₂ ⁻¹ s
  lift-pullback pull (con c ts) (mvar u j₁) ()
  lift-pullback pull (con c ts) (var x ts₁) ()
  lift-pullback pull (mvar u j₁) (con c ts) ()
  lift-pullback pull (mvar u j₁) (var x ts) ()
  lift-pullback pull (var x ts) (con c ts₁) ()
  lift-pullback pull (var x ts) (mvar u j₁) ()

  lift-pullback pull (con c ts) (con .c ts₁) (con refl eq) = con c (lifts-pullback pull ts ts₁ eq)
  lift-pullback pull (lam t)    (lam s)      (lam eq)      = lam (lift-pullback (cons-pullback _ _ pull) t s eq)
  lift-pullback pull (mvar u q₁) (mvar .u q₂)  (mvar refl i∘q₁≡j∘q₂) = mvar u (universal q₁ q₂ i∘q₁≡j∘q₂ , p₂∘universal≡q₂)
    where open Pullback pull
  lift-pullback pull (var x ts) (var x₁ ts₁) (var i$x≡j$x₁ eqts) = var (proj₁ r) (proj₂ (proj₂ r)) (lifts-pullback pull ts ts₁ eqts)
    where r = p$u≡q _ _ pull _ x₁ x i$x≡j$x₁ 

  lifts-pullback : ∀ {X Y Z} {i : Inj X Z}{j : Inj Y Z} (pull : Pullback i j) → let open Pullback pull in 
                  ∀ {Sg G T} (t : Tms Sg G _ T) s → rens i t ≡T rens j s → p₂ ⁻¹ s
  lifts-pullback pull []       []         eq           = []
  lifts-pullback pull (t ∷ ts) (t₁ ∷ ts₁) (eqt ∷ eqts) = (lift-pullback pull t t₁ eqt) ∷ (lifts-pullback pull ts ts₁ eqts)

lift-pullback-other : ∀ {X Y Z} {i : Inj X Z}{j : Inj Y Z} (pull : Pullback i j) → let open Pullback pull in 
                      ∀ {Sg G T} (t : Tm Sg G _ T) s → ren i t ≡ ren j s → (p₂⁻¹s : p₂ ⁻¹ s) 
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
                 (equ : Mixed.Coequalizer (eval f) (eval g)) → let open Mixed.Coequalizer equ in 
                 ∀ (u v : VarClosure X τ) (eu : VarClosure E (type τ <<- Ψ u)) (ev : VarClosure E (type τ <<- Ψ v))
                 → eu ≈vc e _ (body u) → ev ≈vc e _ (body v)
                 → Mixed.Coequalizer {Sg} (eval (u ∷ f)) (eval (v ∷ g))
coequalizer-step {τ <<- Ss} {Z} {X} f g {Sg} equ (i / u) (j / v) (ieu / eu) (jev / ev) eu≈e[u] ev≈e[v] with thick[ eu , ev ]-refl₂ 
coequalizer-step {τ <<- Ss} {Z} {X} f g {Sg} equ (i / u) (j / v) (ieu / eu) (jev / .eu) (vc refl eq2 eq3) (vc eq4 eq5 eq6) | one refl , eq₁ 
  = Mixed.Equ E' , e' , 
    (record {
       commutes = ∋-case (cong eta commz) (λ a y → cong eta (comms a y));
       universal = Universal.universal';
       universal-unique = Universal.universal-unique' _ _;
       e∘universal≡m = Universal.universal∘e'≡m _ _ }) 
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
   commutes-mr S y = (eta-inj (bind e ((eval f S y))) (bind e ((eval g S y))) (commutes S y))

   commz' : map-Vc i (bind e'' (ieu / eu)) ≡ map-Vc j (bind e'' (jev / eu))
   commz' rewrite thick[ eu , eu ]-refl = cong₂ _/_ (trans assoc-∘i (trans (Equalizer.commutes equ0) (sym assoc-∘i))) refl

   commz : map-Vc i (bind e'' (e _ u)) ≡ map-Vc j (bind e'' (e _ v))
   commz = subst₂ (λ eu ev → map-Vc i (bind e'' eu) ≡ map-Vc j (bind e'' ev)) (promote eu≈e[u]) (promote ev≈e[v]) commz'

   comms : (e' ∘mr eval f) ≡mr (e' ∘mr eval g)
   comms S y with e _ (body (eval f S y))  | e _ (body (eval g S y)) | to-vc (commutes-mr S y)
   comms S y    | _ / .w                   | _ / w                   | vc refl eq7 refl 
     = cong₂ _/_ (trans assoc-∘i (trans (cong (λ j₁ → j₁ ∘i ρ-env (e'' _ w)) (≅-to-≡ eq7)) (sym assoc-∘i))) refl

   module Universal {Q : List MTy} (m : Sub Sg X Q)
      (m-comm : (m ∘s toSub (eval ((i / u) ∷ f))) ≡s (m ∘s toSub (eval ((j / v) ∷ g)))) where 

    uni = universal m (λ S₁ x₁ → m-comm S₁ (suc x₁))
    e∘uni≡m = e∘universal≡m {_} {m} {(λ S₁ x₁ → m-comm S₁ (suc x₁))}

    abstract
      uni⋆e[u],uni⋆e[v]⇒i,j : ren i (uni ⋆ (ieu / eu)) ≡
                              ren j (uni ⋆ (jev / eu))
      uni⋆e[u],uni⋆e[v]⇒i,j = 
        subst₂ (\ a b → ren i (uni ⋆ a) ≡ ren j (uni ⋆ b)) (sym (promote eu≈e[u])) (sym (promote ev≈e[v])) 
                 (trans (cong (ren i) (e∘uni≡m _ u)) 
                   (trans (m-comm _ zero) 
                   (sym (cong (ren j) (e∘uni≡m _ v)))))
      uni[eu]⇒i∘ieu,j∘jev : ren (i ∘i ieu) (uni _ eu) ≡ ren (j ∘i jev) (uni _ eu)
      uni[eu]⇒i∘ieu,j∘jev = trans (ren-∘ (uni _ eu)) (trans uni⋆e[u],uni⋆e[v]⇒i,j (sym (ren-∘ (uni _ eu))))
    
    equ0⁻¹uni[eu] = forget (lift-equalizer equ0 (uni _ eu) (≡-T uni[eu]⇒i∘ieu,j∘jev))

    universal' : Sub Sg E' Q
    universal' ._ zero = proj₁ equ0⁻¹uni[eu]
    universal' S (suc x) = uni S (thin[ eu , eu ] x)

    universal∘e'≡m : ∀ S (x : X ∋ S) → universal' ⋆ (e' _ x) ≡ m _ x
    universal∘e'≡m S x       with e _ x     | thick[ eu , eu ] (body (e _ x)) | e∘uni≡m _ x
    universal∘e'≡m S x          | jex / ex  | neither w eq                    | pr rewrite eq | right-id jex = pr
    universal∘e'≡m (.τ <<- _) x | jex / ex  | one⊎other (other neq eq)        | pr = ⊥-elim (neq refl eq)
    universal∘e'≡m (.τ <<- _) x | jex / .eu | one⊎other (one refl)            | pr = trans (trans (ren-∘ _) (cong (ren _) (proj₂ equ0⁻¹uni[eu]))) pr

    universal-unique' : (u : Sub Sg E' Q) (e∘u≡m : (u ∘s toSub e') ≡s m) → u ≡s universal'
    universal-unique' u₁ u∘e'≡m ._ zero    
      = ren-inj (ieu ∘i Equalizer.e equ0) _ _ 
                (begin
                   u₁ ⋆ ((ieu ∘i Equalizer.e equ0) / zero) ≡⟨ sym (cong (_⋆_ u₁) e'[u]≡e/zero) ⟩
                   u₁ ⋆ e' _ u                             ≡⟨ u∘e'≡m _ u ⟩
                   m _ u                                   ≡⟨ sym (e∘uni≡m _ u) ⟩
                   uni ⋆ e _ u                             ≡⟨ cong (_⋆_ uni) (sym (promote eu≈e[u])) ⟩
                   uni ⋆ (ieu / eu)                        ≡⟨ sym (trans (ren-∘ _) (cong (ren _) (proj₂ equ0⁻¹uni[eu]))) ⟩ 
                   _                                       ∎)
    universal-unique' u₁ u∘e'≡m  S (suc x) = trans u₁∘suc≡u₂∘thin (universal-unique u₂ u₂∘e≡m S (thin[ eu , eu ] x))
      where
        u₂ : Sub Sg E Q
        u₂ S x with thick[ eu , eu ] x
        u₂ .(τ <<- _) x₁ | one⊎other (one eq) = ren (Equalizer.e equ0) (u₁ _ zero)
        u₂ .(τ <<- _) x₁ | one⊎other (other neq eq) = ⊥-elim (neq refl eq)
        u₂ S₁ x₁ | neither w eq = u₁ S₁ (suc w)

        u₁∘suc≡u₂∘thin : u₁ S (suc x) ≡ u₂ S (thin[ eu , eu ] x)
        u₁∘suc≡u₂∘thin rewrite thick[ eu , eu ]-thin x = refl

        u₂∘e≡m : (u₂ ∘s toSub e) ≡s m
        u₂∘e≡m _ x with        e _ x    | thick[ eu , eu ] (body (e _ x)) | u∘e'≡m _ x
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (one eq)              | qq = trans (sym (ren-∘ _)) qq
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (other neq eq)        | qq = ⊥-elim (neq refl eq)
        u₂∘e≡m S₁ x₁         | jex / ex | neither w eq                    | qq rewrite right-id jex = qq

... | other neq eq , eq₁ 
 = Mixed.Equ E' , e' , 
    (record {
       commutes = ∋-case (cong eta commz) (λ a y → cong eta (comms a y));
       universal = Universal.universal';
       universal-unique = Universal.universal-unique' _ _;
       e∘universal≡m = Universal.universal∘e'≡m _ _})
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
   commutes-mr S y = (eta-inj (bind e ((eval f S y))) (bind e ((eval g S y))) (commutes S y))

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

   module Universal {Q : List MTy} (m : Sub Sg X Q)
      (m-comm : (m ∘s toSub (eval ((i / u) ∷ f))) ≡s (m ∘s toSub (eval ((j / v) ∷ g)))) where

    uni = universal m (λ S₁ x₁ → m-comm S₁ (suc x₁))
    e∘uni≡m = e∘universal≡m {_} {m} {(λ S₁ x₁ → m-comm S₁ (suc x₁))}

    abstract
      uni⋆e[u],uni⋆e[v]⇒i,j : ren i (uni ⋆ (ieu / eu)) ≡
                              ren j (uni ⋆ (jev / ev))
      uni⋆e[u],uni⋆e[v]⇒i,j = 
        (subst₂ (\ a b → ren i (uni ⋆ a) ≡ ren j (uni ⋆ b)) (sym (promote eu≈e[u])) (sym (promote ev≈e[v])) 
                        (trans (cong (ren i) (e∘uni≡m _ u)) 
                        (trans (m-comm _ zero) 
                        (sym (cong (ren j) (e∘uni≡m _ v))))))

      uni[eu],uni[ev]⇒i∘ieu,j∘jev : ren (i ∘i ieu) (uni _ eu) ≡ 
                                    ren (j ∘i jev) (uni _ ev)
      uni[eu],uni[ev]⇒i∘ieu,j∘jev = trans (ren-∘ _) (trans uni⋆e[u],uni⋆e[v]⇒i,j (sym (ren-∘ _)))

    p₂⁻¹uni[ev] = lift-pullback pull0 (uni _ eu) (uni _ ev) (≡-T uni[eu],uni[ev]⇒i∘ieu,j∘jev)

    z = proj₁ (forget p₂⁻¹uni[ev])

    ren[p₂,z]≡uni[ev] = proj₂ (forget p₂⁻¹uni[ev])
    ren[p₁,z]≡uni[eu] = lift-pullback-other pull0 (uni _ eu) (uni _ ev) uni[eu],uni[ev]⇒i∘ieu,j∘jev p₂⁻¹uni[ev] 
                     
    universal' : Sub Sg E' Q
    universal' ._ zero    = z
    universal'  S (suc x) = uni S (thin[ eu , ev ] x)

    universal∘e'≡m : ∀ S (x : X ∋ S) → universal' ⋆ (e' _ x) ≡ m _ x
    universal∘e'≡m S x       with e _ x     | thick[ eu , ev ] (body (e _ x)) | e∘uni≡m _ x
    universal∘e'≡m S x          | ex        | neither w eq₂                   | eq₃ rewrite eq₂ | right-id (ρ-env ex) = eq₃
    universal∘e'≡m (.τ <<- _) x | jex / .eu | one⊎other (one refl)            | eq₃
      = trans (trans (ren-∘ _) (cong (ren jex) ren[p₁,z]≡uni[eu])) eq₃
    universal∘e'≡m (.τ <<- _) x | jex / .ev | one⊎other (other neq₁ refl)     | eq₃
      = trans (trans (ren-∘ _) (cong (ren jex) ren[p₂,z]≡uni[ev])) eq₃

    universal-unique' : (u : Sub Sg E' Q) (e∘u≡m : (u ∘s toSub e') ≡s m) → u ≡s universal'
    universal-unique' u₁ u∘e'≡m ._ zero    = ren-inj (ieu ∘i Pullback.p₁ pull0) _ _
         (begin
            u₁ ⋆ ((ieu ∘i Pullback.p₁ pull0) / zero) ≡⟨ sym (cong (_⋆_ u₁) e'[u]≡p₁/zero) ⟩
            u₁ ⋆ e' _ u                              ≡⟨ u∘e'≡m _ u ⟩
            m _ u                                    ≡⟨ sym (e∘uni≡m _ u) ⟩
            uni ⋆ e _ u                              ≡⟨ cong (_⋆_ uni) (sym (promote eu≈e[u])) ⟩
            uni ⋆ (ieu / eu)                         ≡⟨ sym (trans (ren-∘ _) (cong (ren ieu) ren[p₁,z]≡uni[eu])) ⟩ 
            _                                        ∎)

    universal-unique' u₁ u∘e'≡m  S (suc x) = trans u₁∘suc≡u₂∘thin (universal-unique u₂ u₂∘e≡m S (thin[ eu , ev ] x))
      where
        u₂ : Sub Sg E Q
        u₂ S x with thick[ eu , ev ] x
        u₂ .(τ <<- _) x₁ | one⊎other (one eq) = ren (Pullback.p₁ pull0) (u₁ _ zero)
        u₂ .(τ <<- _) x₁ | one⊎other (other neq eq) = ren (Pullback.p₂ pull0) (u₁ _ zero)
        u₂ S₁ x₁ | neither w eq = u₁ S₁ (suc w)

        u₁∘suc≡u₂∘thin : u₁ S (suc x) ≡ u₂ S (thin[ eu , ev ] x)
        u₁∘suc≡u₂∘thin rewrite thick[ eu , ev ]-thin x = refl

        u₂∘e≡m : (S₁ : MTy) (x₁ : X ∋ S₁) → (u₂ ∘s toSub e) S₁ x₁ ≡ m S₁ x₁
        u₂∘e≡m _ x        with e _ x    | thick[ eu , ev ] (body (e _ x)) | u∘e'≡m _ x
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (one eq)              | qq = trans (sym (ren-∘ _)) qq
        u₂∘e≡m (._ <<- _) x₁ | jex / ex | one⊎other (other neq eq)        | qq = trans (sym (ren-∘ _)) qq
        u₂∘e≡m S₁ x₁         | jex / ex | neither w eq                    | qq rewrite right-id jex = qq

coequalizer : ∀ {Z X} → (f : All (VarClosure X) Z)(g : All (VarClosure X) Z) → ∀ {Sg} -> 
              Mixed.Coequalizer {Sg} (eval f) (eval g)
coequalizer []          []          = Mixed.Equ _ , idmr , 
     (record {
        commutes = λ S x → refl;
        universal = λ m commutes → m;
        universal-unique = λ u e∘u≡m S x → trans (sym (ren-id _)) (e∘u≡m S x);
        e∘universal≡m = λ S x → ren-id _ })
coequalizer (i / u ∷ f) (j / v ∷ g) = coequalizer-step f g coequ (i / u) (j / v) (e _ u) (e _ v) (to-vc refl) (to-vc refl)
  where 
    coequ = coequalizer f g 
    open Mixed.Coequalizer coequ


coproduct : ∀ {A B Sg} -> Mixed.Coproduct {Sg} A B
coproduct {A} {B} {Sg} = Mixed.Prod (A ++ B) inl inr ⟨_,_⟩ 
          (λ {_} {f} {g} S x → trans (ren-id _)
            (cong [ f S , g S ]′ (split∘glue≡id (inj₁ x)))) 
          (λ {_} {f} {g} S x → trans (ren-id _)
            (cong [ f S , g S ]′ (split∘glue≡id (inj₂ x)))) 
          universal
 where
  inj : ∀ {S} -> A ∋ S ⊎ B ∋ S -> VarClosure (A ++ B) S
  inj x = idmr _ (glue x)

  inl : ∀ S -> A ∋ S  -> VarClosure (A ++ B) S
  inl S x = inj (inj₁ x)

  inr : ∀ S -> B ∋ S  -> VarClosure (A ++ B) S
  inr S x = inj (inj₂ x)

  ⟨_,_⟩ : ∀ {C} → (Sub Sg A C) → (Sub Sg B C) → (Sub Sg (A ++ B) C)
  ⟨ f , g ⟩ S x = [ f S , g S ]′ (split x)
  
  universal : ∀ {C} {f : Sub Sg A C} {g : Sub Sg B C} {i : Sub Sg (A ++ B) C}
               → (i ∘s toSub inl) ≡s f → (i ∘s toSub inr) ≡s g  → ⟨ f , g ⟩ ≡s i
  universal {C} {f} {g} {i} i∘inl≡f i∘inr≡g S x with split# A x | glue∘split≡id {_} {A} x 
  universal i∘inl≡f i∘inr≡g S .(glue# A (inj₁ x))  | inj₁ x     | refl = sym (trans (sym (ren-id _)) (i∘inl≡f S x))
  universal i∘inl≡f i∘inr≡g S .(glue# A (inj₂ y))  | inj₂ y     | refl = sym (trans (sym (ren-id _)) (i∘inr≡g S y))

pushout' : ∀ {Z Y X Sg} → (f : MetaRen Z X)(g : MetaRen Z Y) → Subop.Pullback {Sg} (toSub f) (toSub g)
pushout' {Z} {Y} {X} {Sg} f g = SubopProps.convert (toSub f) (toSub g) (Mixed.Coproduct.to-sub coprod) 
                           (SubopProps.Equalizer-ext (λ S u → cong eta (proj₂ (reify (π₁ ∘mr f)) S u)) 
                                                     (λ S u → cong eta (proj₂ (reify (π₂ ∘mr g)) S u))
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
      open Subop.Pullback (pushout' f g)

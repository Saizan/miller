module Syntax.NbEC where
 open import Relation.Nullary
 import Relation.Nullary.Decidable as Dec
 open import Relation.Binary.PropositionalEquality
 open import EqReasoning
 import Relation.Binary.HeterogeneousEquality as Het
 open Het using (_≅_ ; _≇_ ; refl; ≅-to-≡; ≡-to-≅)
 open import Data.Empty
 open import Data.Unit hiding (_≤_)
 open import Data.Sum
 open import Data.Bool
 open import Data.Product
 open import Data.List.All renaming (map to mapAll)
 open import Function using (_∘_)
 open import Injection
 open import Data.List.Extras public

 open import Syntax.Type
 open import Syntax.NbE

 mutual
   eval-tri : ∀ {b Sg G D K D1 T} → (t : Tm< b > Sg G D T) → (i : Inj D K) {g1 : All (Dom Sg G D1) D} {g2 : All (Dom Sg G D1) K} →
            g1 ≤[ i ] g2 → T ∋ eval (ren i t) g2 ≡d eval t g1
   eval-tri (con c ts) i g1≤g2 = cong (con c) (reifys-ext (evals-tri ts i g1≤g2))
   eval-tri (mvar u j) i g1≤g2 = cong (mvar u) (reifys-ext (evalAs-tri j i g1≤g2))
   eval-tri (var x ts) i {g1} {g2} g1≤g2 = $$-ext {x = get g2 (i $ x)} {get g1 x} (symd _ (g1≤g2 x))
                                           {evals (rens i ts) g2} {evals ts g1} (evals-tri ts i g1≤g2)
   eval-tri (lam t)    i {g1} {g2} g1≤g2 = λ D i₁ {s1} {s2} s → eval-tri t (cons i) 
    (λ { {._} zero → symd _ s;
         (suc v)   → begin[ dom ]
          get (mapEnv i₁ g1) v                          ≈⟨ get-nat reflA v i₁ ⟩
          mapDom i₁ (get g1 v)                          ≈⟨ mapDom-ext i₁ (g1≤g2 v) ⟩
          mapDom i₁ (get g2 (i $ v))                    ≈⟨ symd _ (get-nat reflA (i $ v) i₁) ⟩
          get (s1 ∷ mapEnv i₁ g2) (thin zero _ (i $ v)) ≡⟨ cong (get (s1 ∷ mapEnv i₁ g2)) (sym (iso2 _ _ v)) ⟩
          get (s1 ∷ mapEnv i₁ g2) (weak i $ v)          ∎})

   evals-tri : ∀ {b Sg G D K D1 T} → (t : Tms< b > Sg G D T) → (i : Inj D K) {g1 : All (Dom Sg G D1) D} {g2 : All (Dom Sg G D1) K} →
            g1 ≤[ i ] g2 → evals (rens i t) g2 ≡A evals t g1
   evals-tri (t ∷ ts) i le zero    = eval-tri t i le
   evals-tri (t ∷ ts) i le (suc v) = evals-tri ts i le v

   evalAs-tri : ∀ {b Sg G D K D1 T} → (t : Args b Sg G D T) → (i : Inj D K) {g1 : All (Dom Sg G D1) D} {g2 : All (Dom Sg G D1) K} →
            g1 ≤[ i ] g2 → evalAs (renArgs i t) g2 ≡A evalAs t g1
   evalAs-tri {true}  j  i {g1} {g2} le v 
     rewrite get-build (λ x₁ → get g2 ((i ∘i j) $ x₁)) v 
           | get-build (λ x₁ → get g1 (j $ x₁)) v = transd _ (≡-d (cong (get g2) (apply-∘ i j))) (symd _ (le (j $ v)))
   evalAs-tri {false} ts i           le v = evals-tri ts i le v

 -- flip eval maps the square  Dom(j) . g1 = g2 . i  to  Dom(j) . flip eval g1 = flip eval g2 . Tm(i)
 -- which makes it a functor from the comma category  _∋_ / Dom Sg G  of environments to  Tm Sg G / Dom Sg G .
 eval-square : ∀ {b Sg G D K D1 H T} (t : Tm< b > Sg G D T) (i : Inj D K) (j : Inj D1 H) {g1 : All (Dom Sg G D1) D} {g2 : All (Dom Sg G H) K} →
               mapEnv j g1 ≤[ i ] g2 → T ∋ eval (ren i t) g2 ≡d mapDom j (eval t g1)
 eval-square t i j {g1} {g2} sq = begin[ dom ] 
   eval (ren i t) g2    ≈⟨ eval-tri t i sq ⟩ 
   eval t (mapEnv j g1) ≈⟨ eval-nat t reflA j ⟩ 
   mapDom j (eval t g1) ∎

 evals-square : ∀ {b Sg G D K D1 H T} (ts : Tms< b > Sg G D T) (i : Inj D K) (j : Inj D1 H) {g1 : All (Dom Sg G D1) D} {g2 : All (Dom Sg G H) K} →
               mapEnv j g1 ≤[ i ] g2 → evals (rens i ts) g2 ≡A mapEnv j (evals ts g1)
 evals-square t i j {g1} {g2} sq v = begin[ dom ] 
   get (evals (rens i t) g2) v   ≈⟨ evals-tri t i sq v ⟩
   get (evals t (mapEnv j g1)) v ≈⟨ evals-nat t reflA j v ⟩
   get (mapEnv j (evals t g1)) v ∎

  
 mutual
   Rel : ∀ {Sg G B C} T → (f : All (Dom Sg G C) B) → (g : Dom Sg G B T) → (h : Dom Sg G C T) → Set
   Rel ([]       ->> B) f g h = (! B) ∋ eval g f ≡d h
   Rel ((T ∷ Ts) ->> B) f g h = 
       (∀ D i K j {s1 s2} f' (ex : mapEnv j f ≤[ i ] f') → Rel T f' s1 s2 → Rel (Ts ->> B) f' (proj₁ g D i s1) (proj₁ h K j s2))

   RelA : ∀ {Sg G A B C} → (f : All (Dom Sg G C) B)
          (g : All (Dom Sg G B) A)(h : All (Dom Sg G C) A) → Set 
   RelA f g h = (∀ {S} (x : _ ∋ S) → Rel S f (get g x) (get h x))

 transR : ∀ {Sg G B C} T {f : All (Dom Sg G C) B} {g : Dom Sg G B T} {h : Dom Sg G C T} →
          Rel T f g h → ∀ {d} → T ∋ h ≡d d → Rel T f g d
 transR ([]       ->> B) r eq = trans r eq
 transR ((T ∷ Ts) ->> B) r eq = (λ D i K j f' ex x → transR (Ts ->> B) (r D i K j f' ex x) (eq K j (refld _)))

 mapRel : ∀ {Sg G B C} T → (f : All (Dom Sg G C) B) {g : Dom Sg G B T} {h : Dom Sg G C T} → Rel T f g h → 
          ∀ {D} (i : Inj B D) {K} (j : Inj C K) (f' : All (Dom Sg G K) D)
          → mapEnv j f ≤[ i ] f' → Rel T f' (mapDom i g) (mapDom j h)
 mapRel ([]      ->> _) f {g} r i j f' ex = trans (eval-square g i j ex) (cong (ren j) r)
 mapRel ((_ ∷ _) ->> _) f     r i j f' ex = (λ D i₁ K j₁ f'' ex₁ x₃ → 
                r D (i₁ ∘i i) K (j₁ ∘i j) f'' (≤[]-∘ f i j f' ex i₁ j₁ f'' ex₁) x₃)

 mapRelA : ∀ {Sg G B C T} (f : All (Dom Sg G C) B) {g : All (Dom Sg G B) T} {h : All (Dom Sg G C) T} → RelA f g h → 
           ∀ {D} (i : Inj B D) {K} (j : Inj C K) (f' : All (Dom Sg G K) D)
           → mapEnv j f ≤[ i ] f' → RelA f' (mapEnv i g) (mapEnv j h)
 mapRelA f {g} {h} r i j f' ex {S} x = subst₂ (Rel S f') (sym (get-nat-≡ {f = mapDom i} g x)) (sym (get-nat-≡ {f = mapDom j} h x)) 
                                                         (mapRel S f (r x) i j f' ex)
   
 mutual

   expand-∘ : ∀ {Sg G D0 D} Ss {B} (f : All (Dom Sg G D) D0) (d : Dom Sg G D (Ss ->> B)) {e e-nat} → 
             (∀ D i K (j : Inj _ K) {xs1 xs2} f' (ex : mapEnv j f ≤[ i ] f') → RelA f' xs1 xs2 → Rel (! B) f' (e D i xs1) (mapDom j d $$ xs2))
             → Rel (Ss ->> B) f (expand Ss e e-nat) d
   expand-∘ []       f d eq = trans (eq _ id-i _ id-i {[]} {[]} f (λ x → 
                              transd _ (mapEnv-id x) (≡-d (cong (get f) (sym (id-i$ x))))) (λ ())) (ren-id _)
   expand-∘ (S ∷ Ss) f (d , d-nat) {e} eq = (λ D i K j {x1} {x2} f' ex x₁ → 
    expand-∘ Ss f' (d K j x2) (λ D₁ i₁ K₁ j₁ {xs1} {xs2} f'' ex₁ x₂ → begin[ dom ]
     eval (e D₁ (i₁ ∘i i) (mapDom i₁ x1 ∷ xs1)) f'' ≈⟨ eq _ (i₁ ∘i i) _ (j₁ ∘i j) {mapDom i₁ x1 ∷ xs1} {mapDom j₁ x2 ∷ xs2}
                                                        f'' (≤[]-∘ f i j f' ex i₁ j₁ f'' ex₁)
                                                        (λ { {._} zero → mapRel S f' x₁ i₁ j₁ f'' ex₁; (suc v) → x₂ v}) ⟩
     d K₁ (id-i ∘i (j₁ ∘i j)) (mapDom j₁ x2) $$ xs2 ≈⟨ $$-ext (≡-d (cong₂ (d K₁) (left-id (j₁ ∘i j)) refl))
                                                              {xs2} {xs2} reflA ⟩
     d K₁ (j₁ ∘i j) (mapDom j₁ x2) $$ xs2           ≈⟨ $$-ext (d-nat _ j (refld _) _ j₁) 
                                                              {xs2} {xs2} reflA ⟩
     mapDom j₁ (d K j x2) $$ xs2                    ∎))
                 
   injv-∘ : ∀ {Sg G D0 D} T (f : All (Dom Sg G D) D0) (v : _ ∋ T) (d : Dom Sg G D T)
            → T ∋ get f v ≡d d → Rel T f (injv v) d
   injv-∘ (Ss ->> B) f v d eq = expand-∘ Ss f d (λ D i K j {xs} {ys} f' ex x → 
          $$-ext {x = get f' (i $ v)} {mapDom j d} (transd _ (transd _ (symd _ (ex v)) (get-nat reflA v j)) (mapDom-ext j eq)) 
                 {evals (reifys xs) f'} {ys} (RelA-unfold f' x))

   precompose-∘ : ∀ {Sg G Z A B C} → (f : All (Dom Sg G C) B) {g : All (Dom Sg G B) A}{h : All (Dom Sg G C) A} 
                  → RelA f g h → (j : Inj Z A) → RelA f (build (\ z -> get g (j $ z))) (build (\ z -> get h (j $ z)))
   precompose-∘ f {g} {h} ar j {S} x = subst₂ (Rel S f) (sym (get-build (λ z → get g (j $ z)) x)) 
                                                        (sym (get-build (λ z → get h (j $ z)) x)) 
                                              (ar (j $ x))

   idEnv-∘ : ∀ {Sg G D T} (g : All (Dom Sg G D) T) -> RelA g idEnv g
   idEnv-∘ {Sg} {G} {D} g x rewrite get-build (injv {Sg} {G}) x = injv-∘ _ g x (get g x) (refld _)

   nf-∘ : ∀ {b Sg G A B C T} → (t : Tm< b > Sg G A T) → (f : All (Dom Sg G C) B){g : All (Dom Sg G B) A}{h : All (Dom Sg G C) A} 
          → RelA f g h → nf (nf t g) f ≡ nf t h
   nf-∘ t f ar = reify-ext _ (Rel-unfold _ f (eval-∘ f ar t))

   nfs-∘ : ∀ {b Sg G A B C T} → (t : Tms< b > Sg G A T) → (f : All (Dom Sg G C) B){g : All (Dom Sg G B) A}{h : All (Dom Sg G C) A} →
           RelA f g h → nfs (nfs t g) f ≡ nfs t h
   nfs-∘ []       f ar = refl
   nfs-∘ (x ∷ xs) f ar = cong₂ _∷_ (nf-∘ x f ar) (nfs-∘ xs f ar)

   nfAs-∘ : ∀ {b Sg G A B C T} → (t : Args b Sg G A T) → (f : All (Dom Sg G C) B){g : All (Dom Sg G B) A}{h : All (Dom Sg G C) A} →
            RelA f g h → nfs (nfAs t g) f ≡ nfAs t h
   nfAs-∘ {true}  []             f ar = refl
   nfAs-∘ {true}  (i ∷ t [ pf ]) f ar = cong₂ _∷_ (reify-ext _ (Rel-unfold _ f (ar i))) 
                                                  (nfAs-∘ t f ar)
   nfAs-∘ {false} t              f ar = nfs-∘ t f ar
   
   eval-∘ : ∀ {b Sg G A B C T} → (f : All (Dom Sg G C) B)
          {g : All (Dom Sg G B) A}{h : All (Dom Sg G C) A} → RelA f g h → (t : Tm< b > Sg G A T) → Rel T f (eval t g) (eval t h)
   eval-∘ f ar (con c ts) = cong (con c) (nfs-∘ ts f ar)
   eval-∘ f ar (mvar u j) = cong (mvar u) (nfAs-∘ j f ar)
   eval-∘ f ar (var x ts) = $$-∘ f (evals-∘ f ar ts) (ar x)
   eval-∘ f {g} {h} ar (lam t) =  
     (λ D i K j f' ex x → 
      eval-∘ f' 
       (λ { {._} zero   → x; 
            {S} (suc v) → subst₂ (Rel S f') (sym (get-nat-≡ {f = mapDom i} g v)) (sym (get-nat-≡ {f = mapDom j} h v))
                           (mapRel S f (ar v) i j f' ex)}) 
       t)

   evals-∘ : ∀ {b Sg G A B C T} → (f : All (Dom Sg G C) B){g : All (Dom Sg G B) A}{h : All (Dom Sg G C) A} → RelA f g h → 
             (t : Tms< b > Sg G A T) → RelA f (evals t g) (evals t h)
   evals-∘ f ar (t ∷ t₁) zero    = eval-∘ f ar t
   evals-∘ f ar (t ∷ t₁) (suc x) = evals-∘ f ar t₁ x

   $$-∘ : ∀ {Sg G A B C} → (f : All (Dom Sg G C) B) {g : All (Dom Sg G B) A}{h : All (Dom Sg G C) A} → RelA f g h →
          ∀ {X} {gx : Dom _ _ _ (_ ->> X)} {hx} → Rel _ f gx hx → _ ∋ eval (gx $$ g) f ≡d (hx $$ h)
   $$-∘ f {[]}     {[]}      ar r = r
   $$-∘ f {px ∷ g} {px₁ ∷ h} ar r = $$-∘ f (ar ∘ suc)
     (r _ id-i _ id-i f (\ x → transd _ (mapEnv-id x) (≡-d (cong (get f) (sym (id-i$ x))))) (ar zero))

   Rel-unfold : ∀ {Sg G} A {B C} → (f : All (Dom Sg G C) B)
          {g : (Dom Sg G B) A}{h : (Dom Sg G C) A} → Rel A f g h → _ ∋ eval (reify A g) f ≡d h
   Rel-unfold ([]       ->> _) f r = r
   Rel-unfold ((T ∷ Ts) ->> _) f r = λ D i s → 
     Rel-unfold (Ts ->> _) (_ ∷ mapEnv i f) 
            (r (T ∷ _) (weak id-i) D i (_ ∷ mapEnv i f) 
               (λ x → ≡-d (sym (cong (get (_ ∷ mapEnv i f)) (apply-weakid x))))
               (injv-∘ T (_ ∷ mapEnv i f) zero _ s))

   RelA-unfold : ∀ {Sg G A B C} → (f : All (Dom Sg G C) B)
             {g : All (Dom Sg G B) A}{h : All (Dom Sg G C) A} → RelA f g h → evals (reifys g) f ≡A h
   RelA-unfold f {gx ∷ g} {hx ∷ h} r zero    = Rel-unfold _ f (r zero)
   RelA-unfold f {gx ∷ g} {hx ∷ h} r (suc v) = RelA-unfold f (r ∘ suc) v


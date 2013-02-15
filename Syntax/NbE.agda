module Syntax.NbE where

 open import Relation.Binary.PropositionalEquality
 open import Relation.Binary
 open import Data.Sum
 open import Data.Product
 open import Function using (_∘_)

 open import Data.List.All public renaming (map to mapAll)

 open import Support.EqReasoning

 open import Injection

 open import Syntax.Type

 mutual
   Dom : (Sg : Ctx)(G : MCtx)(D : Ctx) → Ty → Set
   Dom Sg G D ([] ->> B) = Tm< false > Sg G D (! B)
   Dom Sg G D ((S ∷ Ss) ->> B) = Σ ((D1 : Ctx) → Inj D D1 → Dom Sg G D1 S → Dom Sg G D1 (Ss ->> B))
     \ x → (D1 : Ctx) → (i : Inj D D1) → {s1 s2 : Dom Sg G D1 S} (s : S ∋ s1 ≡d s2) 
                → (∀ K k → (Ss ->> B) ∋ x K (k ∘i i) (mapDom k s1) ≡d mapDom k (x D1 i s2))

   _∋_≡d_ : ∀ {Sg G D} T → (x y : Dom Sg G D T) → Set
   ([]       ->> _) ∋ x ≡d y = x ≡ y
   ((T ∷ Ts) ->> B) ∋ x ≡d y = ∀ D i {s1 s2} (s : T ∋ s1 ≡d s2) → (Ts ->> B) ∋ proj₁ x D i s1 ≡d proj₁ y D i s2

 
   symd : ∀ {Sg G D} T → {x y : Dom Sg G D T} → T ∋ x ≡d y → T ∋ y ≡d x
   symd ([]       ->> B) eq = sym eq
   symd ((T ∷ Ts) ->> B) eq = λ D i s → symd (Ts ->> B) (eq D i (symd T s))

   transd : ∀ {Sg G D} T → {x y z : Dom Sg G D T} → T ∋ x ≡d y → T ∋ y ≡d z → T ∋ x ≡d z
   transd ([] ->> B)       eq1 eq2 = trans eq1 eq2
   transd ((T ∷ Ts) ->> B) eq1 eq2 = λ D i s → transd (Ts ->> B) (eq1 D i s) (eq2 D i (transd _ (symd _ s) s))

   mapDom : ∀ {Sg G D D1 T} → Inj D D1 → Dom Sg G D T → Dom Sg G D1 T
   mapDom {T = [] ->>       _} i t           = ren i t
   mapDom {T = (_ ∷ Ts) ->> _} i (t , t-nat) = (λ D2 j s → t D2 (j ∘i i) s) , 
     (λ D1 i₁ {s1} {s2} s K k →
      subst (λ r → Ts ->> _ ∋ t K r (mapDom k s1) ≡d mapDom k (t D1 (i₁ ∘i i) s2))
             assoc-∘i (t-nat _ (i₁ ∘i i) s K k))

   mapDom-id : ∀ {Sg G D T} → (d : Dom Sg G D T) → T ∋ mapDom id-i d ≡d d
   mapDom-id {T = []       ->> _} d           = ren-id d
   mapDom-id {T = (T ∷ Ts) ->> _} (d , d-nat) = 
     λ D i s →
         transd _ (≡-d (cong (λ r → d D r _) (right-id i)))
        (transd _ (symd _ (mapDom-id (d D i _))) 
        (transd _ (symd _ (d-nat D i (refld T) _ id-i))
        (transd _ (d-nat D i s _ id-i) 
                  (mapDom-id (d D i _)))))

   refld : ∀ {Sg G D} T → {x : Dom Sg G D T} → T ∋ x ≡d x
   refld T {x} = transd T (symd T (mapDom-id x)) (mapDom-id x)

   ≡-d : ∀ {Sg G D T} → {x y : Dom Sg G D T} → x ≡ y → T ∋ x ≡d y
   ≡-d refl = refld _ 

   mapDom-∘ : ∀ {Sg G D D1 D2 T} → (j : Inj D1 D2)(i : Inj D D1) → (d : Dom Sg G D T) → T ∋ mapDom j (mapDom i d) ≡d mapDom (j ∘i i) d
   mapDom-∘ {T = [] ->>       _} j i d = sym (ren-∘ d)
   mapDom-∘ {T = (S ∷ Ss) ->> _} j i d = λ D i₁ {s1} s → transd (Ss ->> _) (≡-d (cong (λ r → proj₁ d D r s1) (sym assoc-∘i))) 
                                                                           (refld ((S ∷ Ss) ->> _) {d} D (i₁ ∘i (j ∘i i)) s)

 dom : ∀ {Sg G D T} -> Setoid _ _
 dom {Sg} {G} {D} {T} = 
     record { Carrier = Dom Sg G D T; _≈_ = _∋_≡d_ T; isEquivalence = record { refl = refld _; sym = symd _; trans = transd _ } }

 get : ∀ {A : Set} {P : A → Set} {xs : List A} → All P xs → (∀ {x : A} → xs ∋ x → P x)
 get (t ∷ ts) zero    = t
 get (_ ∷ ts) (suc u) = get ts u

 get-nat-≡ : ∀ {A : Set}{P Q : A → Set}{xs : List A} → {f : ∀ {x} → P x → Q x} → (as : All P xs) → 
             ∀ {T} (v : _ ∋ T) → get (mapAll f as) v ≡ f (get as v)
 get-nat-≡         (a ∷ as) zero    = refl
 get-nat-≡ {f = f} (a ∷ as) (suc v) = get-nat-≡ {f = f} as v

 _≡A_ : ∀ {Sg G D T} → (x y : All (Dom Sg G D) T) → Set
 xs ≡A ys = ∀ {S} (x : _ ∋ S) → S ∋ get xs x ≡d get ys x

 reflA : ∀ {Sg G D T} → {x : All (Dom Sg G D) T} → x ≡A x
 reflA {x = x} = \ {S} x -> refld S

 mapDom-ext : ∀ {Sg G D D1 T} → (i : Inj D D1) {x y : Dom Sg G D T} → T ∋ x ≡d y → T ∋ mapDom i x ≡d mapDom i y
 mapDom-ext {T = []      ->> _} i eq = cong (ren i) eq
 mapDom-ext {T = (_ ∷ _) ->> _} i eq = λ D₁ i₁ s → eq D₁ (i₁ ∘i i) s

 mapEnv : ∀ {Sg G D D1 T} → Inj D D1 → All (Dom Sg G D) T → All (Dom Sg G D1) T
 mapEnv i = mapAll (mapDom i)

 mapEnv-id : ∀ {Sg G D T} → {xs : All (Dom Sg G D) T} → mapEnv id-i xs ≡A xs
 mapEnv-id {xs = x ∷ xs} zero    = mapDom-id x
 mapEnv-id {xs = x ∷ xs} (suc v) = mapEnv-id v

 mapEnv-ext : ∀ {Sg G D D1 T} → (i : Inj D D1) → {xs ys : All (Dom Sg G D) T} → xs ≡A ys → mapEnv i xs ≡A mapEnv i ys
 mapEnv-ext i {_ ∷ _} {_ ∷ _} eq zero    = mapDom-ext i (eq zero)
 mapEnv-ext i {_ ∷ _} {_ ∷ _} eq (suc x) = mapEnv-ext i (eq ∘ suc) x

 mapEnv-∘ : ∀ {Sg G D D1 D2 T} → (j : Inj D1 D2)(i : Inj D D1) → (xs : All (Dom Sg G D) T) 
               → mapEnv j (mapEnv i xs) ≡A mapEnv (j ∘i i) xs
 mapEnv-∘ j i (x ∷ xs) zero    = mapDom-∘ j i x
 mapEnv-∘ j i (x ∷ xs) (suc v) = mapEnv-∘ j i xs v


 cons-ext : ∀ {Sg G D T Ts} → {x y : Dom Sg G D T} → T ∋ x ≡d y 
            → {xs ys : All (Dom Sg G D) Ts} → xs ≡A ys → (x ∷ xs) ≡A (y ∷ ys)
 cons-ext x xs zero    = x
 cons-ext x xs (suc v) = xs v

 DomN : (Sg : Ctx)(G : MCtx)(D : Ctx) → List Ty → Base -> Set
 DomN Sg G D Ss B = Σ (∀ D1 → (i : Inj D D1) → (xs : All (Dom Sg G D1) Ss) → Tm< false > Sg G D1 (! B))
                   \ f -> ∀ D i {xs ys} (eq : xs ≡A ys) K k → f K (k ∘i i) (mapEnv k xs) ≡ ren k (f D i ys)
 _∋_≡N_ : ∀ {Sg G D T} Ts (f g : DomN Sg G D Ts T) → Set
 _∋_≡N_ {Sg} {G} {D} {T} Ts f g = (∀ D1 (i : Inj D D1) {xs ys} -> xs ≡A ys -> proj₁ f D1 i xs ≡ proj₁ g D1 i ys)

 reflN : ∀ {Sg G D T Ts} (f : DomN Sg G D Ts T) -> Ts ∋ f ≡N f
 reflN (f , f-nat) D i {xs} {ys} eq = begin 
   f D i xs                         ≡⟨ sym (ren-id _) ⟩
   ren id-i (f D i xs)              ≡⟨ sym (f-nat D i reflA D id-i) ⟩ 
   f D (id-i ∘i i) (mapEnv id-i xs) ≡⟨ f-nat D i eq D id-i ⟩
   ren id-i (f D i ys)              ≡⟨ ren-id _ ⟩
   f D i ys                         ∎

 mapDomN : ∀ {Sg G D Ts T K} (i : Inj D K) -> DomN Sg G D Ts T -> DomN Sg G K Ts T  
 mapDomN i (f , f-nat) = (λ D1 j xs → f D1 (j ∘i i) xs) 
   , (λ D i₁ {xs} {ys} eq K k → begin[ dom ] 
        f K ((k ∘i i₁) ∘i i) (mapEnv k xs) ≈⟨ cong₂ (f K) (sym assoc-∘i) refl ⟩ 
        f K (k ∘i (i₁ ∘i i)) (mapEnv k xs) ≈⟨ f-nat _ (i₁ ∘i i) eq K k ⟩ 
        ren k (f D (i₁ ∘i i) ys) ∎)

 applyN : ∀ {Sg G D S Ss T K} -> DomN Sg G D (S ∷ Ss) T -> Inj D K -> Dom Sg G K S -> DomN Sg G K Ss T
 applyN (f , f-nat) i s = (λ D2 j xs → f D2 (j ∘i i) (mapDom j s ∷ xs)) , 
  (λ D₁ i₁ {xs} {ys} eq K k → begin[ dom ]
   f K ((k ∘i i₁) ∘i i) (mapDom (k ∘i i₁) s ∷ mapEnv k xs) ≈⟨ reflN (f , f-nat) K ((k ∘i i₁) ∘i i)
                                                               (cons-ext (symd _ (mapDom-∘ k i₁ s)) (mapEnv-ext k reflA)) ⟩
   f K ((k ∘i i₁) ∘i i) (mapEnv k (mapDom i₁ s ∷ xs))      ≈⟨ cong₂ (f K) (sym assoc-∘i) refl ⟩
   f K (k ∘i (i₁ ∘i i)) (mapEnv k (mapDom i₁ s ∷ xs))      ≈⟨ f-nat _ (i₁ ∘i i) {mapDom i₁ s ∷ xs} {mapDom i₁ s ∷ ys}
                                                               (cons-ext (mapDom-ext i₁ (refld _)) eq) _ k ⟩ 
   ren k (f D₁ (i₁ ∘i i) (mapDom i₁ s ∷ ys)) ∎)

 applyN-nat : ∀ {Sg G D S Ss T D1} (f : DomN Sg G D (S ∷ Ss) T) (i : Inj D D1) -> 
              ∀ {s1 s2 : Dom Sg G D1 S} (_ : S ∋ s1 ≡d s2) -> 
              ∀ {K} (k : Inj D1 K) -> Ss ∋ applyN f (k ∘i i) (mapDom k s1) ≡N mapDomN k (applyN f i s2)
 applyN-nat (f , f-nat) i {s1} {s2} s {K} k D i₁ {xs} {ys} xs≡ys = begin 
   f D (i₁ ∘i (k ∘i i)) (mapDom i₁ (mapDom k s1) ∷ xs) ≈⟨ cong₂ (f D) assoc-∘i refl ⟩ 
   f D ((i₁ ∘i k) ∘i i) (mapDom i₁ (mapDom k s1) ∷ xs) ≈⟨ (reflN (f , f-nat) D ((i₁ ∘i k) ∘i i) 
                                                           (cons-ext (transd _ (mapDom-∘ i₁ k s1) (mapDom-ext (i₁ ∘i k) s)) xs≡ys)) ⟩ 
   f D ((i₁ ∘i k) ∘i i) (mapDom (i₁ ∘i k) s2 ∷ ys)     ∎


 mutual

  expand : ∀ {Sg G D T} Ts → DomN Sg G D Ts T → Dom Sg G D (Ts ->> T)
  expand []       (f , f-nat) = f _ id-i []
  expand (S ∷ Ts) (f , f-nat) = (λ D1 i s → expand Ts (applyN (f , f-nat) i s)) , 
    (λ D1 i {s1} {s2} s K k → begin[ dom ] 
      expand Ts (applyN (f , f-nat) (k ∘i i) (mapDom k s1)) ≈⟨ expand-ext Ts (applyN-nat (f , f-nat) i s k) ⟩
      expand Ts (mapDomN k (applyN (f , f-nat) i s2))       ≈⟨ expand-nat Ts (applyN (f , f-nat) i s2) (applyN (f , f-nat) i s2) 
                                                                                 (reflN (applyN (f , f-nat) i s2)) K k ⟩ 
      mapDom k (expand Ts (applyN (f , f-nat) i s2)) ∎)

  injv : ∀ {Sg G D T} → D ∋ T → Dom Sg G D T
  injv {T = Ss ->> B} v = expand Ss ((λ D1 i xs → var (i $ v) (reifys xs)) ,
                                    (λ D₁ i eq K k → cong₂ var (apply-∘ k i) 
                                                               (reifys-nat eq k)))

  reify : ∀ {Sg G D}(T : Ty) → Dom Sg G D T → Tm< false > Sg G D T
  reify ([]       ->> B) x = x
  reify ((S ∷ Ss) ->> B) f = lam (reify (Ss ->> B) (proj₁ f _ (weak id-i) (injv zero)))

  reifys : ∀ {Sg G D Ts} → All (Dom Sg G D) Ts → Tms< false > Sg G D Ts
  reifys []       = []
  reifys (t ∷ ts) = reify _ t ∷ reifys ts

  expand-nat : ∀ {Sg G D T} Ts (f g : DomN Sg G D Ts T) → (∀ D1 (i : Inj D D1) {xs ys} -> xs ≡A ys -> proj₁ f D1 i xs ≡ proj₁ g D1 i ys) ->
                ∀ (K : List Ty) (k : Inj D K) → (Ts ->> T) ∋ expand Ts (mapDomN k f) ≡d mapDom k (expand Ts g)
  expand-nat []       (f , f-nat) (g , g-nat) eq K k = begin 
    f K (id-i ∘i k) []  ≡⟨ eq K (id-i ∘i k) reflA ⟩ 
    g K (id-i ∘i k) []  ≡⟨ cong₂ (g K) (trans (left-id k) (sym (right-id k))) refl ⟩ 
    g K (k ∘i id-i) []  ≡⟨ g-nat _ id-i reflA _ k ⟩ 
    ren k (g _ id-i []) ∎
  expand-nat (T ∷ Ts) (f , _) (g , _) eq K k = λ D i {s1} {s2} s → expand-ext Ts 
    (λ D₁ i₁ {xs} {ys} xs≡ys → begin[ dom ] 
      f D₁ ((i₁ ∘i i) ∘i k) (mapDom i₁ s1 ∷ xs) ≈⟨ eq D₁ ((i₁ ∘i i) ∘i k) (cons-ext (mapDom-ext i₁ s) xs≡ys) ⟩ 
      g D₁ ((i₁ ∘i i) ∘i k) (mapDom i₁ s2 ∷ ys) ≈⟨ cong₂ (g D₁) (sym assoc-∘i) refl ⟩ 
      g D₁ (i₁ ∘i (i ∘i k)) (mapDom i₁ s2 ∷ ys) ∎)

  expand-ext : ∀ {Sg G D T} Ts {f g : DomN Sg G D Ts T}
               → (Ts ∋ f ≡N g) → (Ts ->> T) ∋ expand Ts f ≡d expand Ts g
  expand-ext []       eq = eq _ id-i {[]} {[]} (λ ()) 
  expand-ext (S ∷ Ts) eq = λ D1 i s → expand-ext Ts (λ D i₁ x → eq D (i₁ ∘i i) (cons-ext (mapDom-ext i₁ s) x))


  injv-nat : ∀ {Sg G D D1}(i : Inj D D1){T}(v : D ∋ T) → T ∋ mapDom i (injv v) ≡d (injv {Sg} {G} (i $ v))
  injv-nat i {[]       ->> B} v = cong (\ v -> var v []) (begin 
       i $ (id-i $ v) ≡⟨ cong (_$_ i) (id-i$ v) ⟩
       i $ v          ≡⟨ sym (id-i$ (i $ v)) ⟩ 
       id-i $ (i $ v) ∎)
  injv-nat i {(S ∷ Ss) ->> B} v = λ D i₁ s → expand-ext Ss (λ D₁ i₂ x → 
    cong₂ var (begin (i₂ ∘i (i₁ ∘i i)) $ v ≡⟨ cong (λ i₃ → i₃ $ v) assoc-∘i ⟩ 
                     ((i₂ ∘i i₁) ∘i i) $ v ≡⟨ apply-∘ (i₂ ∘i i₁) i ⟩ 
                     (i₂ ∘i i₁) $ (i $ v)  ∎) 
              (reifys-ext (cons-ext (mapDom-ext i₂ s) x)))

  injv-ext : ∀ {Sg G D T} → (v : D ∋ T) → T ∋ injv {Sg} {G} v ≡d injv v
  injv-ext {Sg} {G} {D} {Ss ->> B} v = expand-ext Ss (λ D₁ i x → cong (var _) (reifys-ext x))

  reify-nat : ∀ {Sg G D} T {x y : Dom Sg G D T} → T ∋ x ≡d y → ∀ {K} (k : Inj _ K) → reify T (mapDom k x) ≡ ren k (reify T y)
  reify-nat ([]       ->> _)                         eq k = cong (ren k) eq
  reify-nat ((S ∷ Ss) ->> _) {x , x-nat} {y , y-nat} eq k 
    = cong lam (begin
       reify (Ss ->> _) (x _ (weak id-i ∘i k) (injv (cons k $ zero)))         ≡⟨ reify-ext (Ss ->> _) lemma ⟩
       reify (Ss ->> _) (mapDom (cons k) (y (S ∷ _) (weak id-i) (injv zero))) ≡⟨ reify-nat (Ss ->> _) (refld (Ss ->> _)) (cons k) ⟩
       ren (cons k) (reify (Ss ->> _) (y (S ∷ _) (weak id-i) (injv zero)))    ∎)
   where
    lemma = begin[ dom ] 
     x _ (weak id-i ∘i k) (injv (cons k $ zero))
       ≡⟨ cong (λ r → x _ r (injv (cons k $ zero))) (ext-∘ (λ _ v → begin
          weak id-i $ (k $ v)             ≡⟨ iso2 _ _ (k $ v) ⟩
          suc (id-i $ (k $ v))            ≡⟨ cong suc (id-i$ (k $ v)) ⟩
          thin zero _ (k $ v)             ≡⟨ sym (iso2 _ _ v) ⟩
          weak k $ v                      ≡⟨ cong (_$_ (weak k)) (sym (id-i$ v)) ⟩
          cons k $ thin zero _ (id-i $ v) ≡⟨ cong (_$_ (cons k)) (sym (iso2 _ _ v)) ⟩
          cons k $ (weak id-i $ v)        ∎)) ⟩
     x _ (cons k ∘i weak id-i) (injv (cons k $ zero))        ≈⟨ eq _ (cons k ∘i weak id-i) (symd _ (injv-nat (cons k) zero)) ⟩
     y _ (cons k ∘i weak id-i) (mapDom (cons k) (injv zero)) ≈⟨ y-nat (S ∷ _) (weak id-i) (injv-ext zero) (_ <: S) (cons k) ⟩
     mapDom (cons k) (y _ (weak id-i) (injv zero))           ∎

  reify-ext : ∀ {Sg G D} T → {xs ys : Dom Sg G D T} → T ∋ xs ≡d ys → reify T xs ≡ reify T ys
  reify-ext ([]       ->> _) eq = eq
  reify-ext ((S ∷ Ss) ->> B) eq = cong lam (reify-ext (Ss ->> B) (eq _ (weak id-i) (injv-ext zero)))
  
  reifys-nat : ∀ {Sg G D T} {x y : All (Dom Sg G D) T} → x ≡A y → ∀ {K} (k : Inj _ K) → reifys (mapEnv k x) ≡ rens k (reifys y)
  reifys-nat {x = []}     {[]}     eq k = refl
  reifys-nat {x = x ∷ xs} {y ∷ ys} eq k = cong₂ _∷_ (reify-nat _ (eq zero) k) (reifys-nat (eq ∘ suc) k)
    
  reifys-ext : ∀ {Sg G D Ts} → {xs ys : All (Dom Sg G D) Ts} → xs ≡A ys → reifys xs ≡ reifys ys
  reifys-ext {xs = []}     {[]}     eq = refl
  reifys-ext {xs = x ∷ xs} {y ∷ ys} eq = cong₂ _∷_ (reify-ext _ (eq zero)) (reifys-ext (eq ∘ suc))


 build : ∀ {A : Set} {P : A → Set} {xs : List A} → (∀ {x : A} → xs ∋ x → P x) → All P xs
 build {A} {P} {[]}     f = []
 build {A} {P} {x ∷ xs} f = f zero ∷ build (λ x₁ → f (suc x₁)) 

 build-ext : ∀ {A : Set} {P : A → Set} {xs : List A}
         → {f g : ∀ {x : A} → xs ∋ x → P x} → (∀ {x : A} (v : xs ∋ x) → f v ≡ g v) → build f ≡ build g
 build-ext {xs = []}     eq = refl
 build-ext {xs = x ∷ xs} eq = cong₂ _∷_ (eq zero) (build-ext (\ v → eq (suc v)))

 get-build : ∀ {A : Set} {P : A → Set} {xs : List A} → (f : ∀ {x : A} → xs ∋ x → P x) →
             ∀ {T} (x : _ ∋ T) → get (build f) x ≡ f x
 get-build f zero    = refl
 get-build f (suc u) = get-build (λ u₁ → f (suc u₁)) u

 build-get : ∀ {A : Set} {P : A → Set} {xs : List A} → (f : All P xs)
             → (build (\ x → get f x)) ≡ f
 build-get []       = refl
 build-get (x ∷ xs) = cong₂ _∷_ refl (build-get xs)

 mapAll-build : ∀ {A} xs {P Q : A → Set} (f : (∀ {x : A} → xs ∋ x → P x)) (g : ∀ {x} → P x → Q x) → mapAll g (build f) ≡ build (g ∘ f)
 mapAll-build []       f g = refl
 mapAll-build (x ∷ xs) f g = cong₂ _∷_ refl (mapAll-build xs (f ∘ suc) g)

 _$$_ : ∀ {Sg G D Ts B} → Dom Sg G D (Ts ->> B) → All (Dom Sg G D) Ts → Dom Sg G D (! B)
 f $$ []         = f
 f $$ (px ∷ xs₁) = proj₁ f _ id-i px $$ xs₁

 $$-ext : ∀ {Sg G D Ts B} → {x y : Dom Sg G D (Ts ->> B)} → _ ∋ x ≡d y → 
          ∀ {xs ys : All (Dom Sg G D) Ts} → xs ≡A ys → (! B) ∋ (x $$ xs) ≡d (y $$ ys)
 $$-ext f {[]}     {[]}     eq = f
 $$-ext f {x ∷ xs} {y ∷ ys} eq = $$-ext (f _ id-i (eq zero)) (eq ∘ suc)

 $$-nat : ∀ {Sg G D Ts B} → {x y : Dom Sg G D (Ts ->> B)} → _ ∋ x ≡d y → 
          ∀ {xs ys : All (Dom Sg G D) Ts} → xs ≡A ys → ∀ {K} (k : Inj _ K) → (! B) ∋ (mapDom k x $$ mapEnv k xs) ≡d ren k (y $$ ys)
 $$-nat                                           f≡g {[]}     {[]}     eq k = cong (ren k) f≡g
 $$-nat {Ts = T ∷ Ts} {B} {x = f , _} {g , g-nat} f≡g {x ∷ xs} {y ∷ ys} eq k = begin
   f _ (id-i ∘i k) (mapDom k x) $$ mapEnv k xs ≡⟨ $$-ext {Ts = Ts} {B = B} {x = f _ (id-i ∘i k) (mapDom k x)}
                                                    {mapDom k (g _ id-i y)} lemma
                                                    {xs = mapEnv k xs} {ys = mapEnv k ys}
                                                    (λ x₁ → mapEnv-ext k (eq ∘ suc) x₁) ⟩
   mapDom k (g _ id-i y) $$ mapEnv k ys        ≡⟨ $$-nat {Ts = Ts} {B = B} (refld _) {ys} {ys} reflA k ⟩
   ren k (g _ id-i y $$ ys)                    ∎
  where
   lemma = begin[ dom ]
     f _ (id-i ∘i k) (mapDom k x) ≡⟨ cong₂ (f _) (trans (left-id k) (sym (right-id k))) refl ⟩
     f _ (k ∘i id-i) (mapDom k x) ≈⟨ f≡g _ (k ∘i id-i) (mapDom-ext k (eq zero)) ⟩
     g _ (k ∘i id-i) (mapDom k y) ≈⟨ g-nat _ id-i (refld T) _ k ⟩
     mapDom k (g _ id-i y)        ∎

 idEnv : ∀ {Sg G D} → All (Dom Sg G D) D
 idEnv = build injv 

 get-nat : ∀ {Sg G D D1 T} {xs ys : All (Dom Sg G D1) D} → xs ≡A ys → (v : _ ∋ T) →
           ∀ {K} (k : Inj D1 K) → T ∋ get (mapEnv k xs) v ≡d mapDom k (get ys v)
 get-nat {xs = x ∷ xs} {y ∷ ys} eq zero    k = mapDom-ext k (eq zero)
 get-nat {xs = x ∷ xs} {y ∷ ys} eq (suc v) k = get-nat (eq ∘ suc) v k

 mutual
  nf : ∀ {b Sg G D D1 T} → Tm< b > Sg G D T → All (Dom Sg G D1) D → Tm< false > Sg G D1 T
  nf t g = reify _ (eval t g)

  nfs : ∀ {b Sg G D D1 T} → Tms< b > Sg G D T → All (Dom Sg G D1) D → Tms< false > Sg G D1 T
  nfs ts g = reifys (evals ts g)

  nfAs : ∀ {b Sg G D D1 T} → Args b Sg G D T → All (Dom Sg G D1) D → Tms< false > Sg G D1 T
  nfAs as g = reifys (evalAs as g)

  eval : ∀ {b Sg G D D1 T} → Tm< b > Sg G D T → All (Dom Sg G D1) D → Dom Sg G D1 T
  eval (con c ts) g = con c (nfs ts g)
  eval (mvar u j) g = mvar u (nfAs j g)
  eval (var x ts) g = get g x $$ evals ts g
  eval (lam t)    g = (λ D2 i s → eval t (s ∷ mapEnv i g)) , 
    (λ D1 i {s1} {s2} s K k → begin[ dom ]
       eval t (mapDom k s1 ∷ mapEnv (k ∘i i) g)     ≈⟨ eval-ext t (cons-ext (mapDom-ext k s) (λ x → symd _ (mapEnv-∘ k i _ x))) ⟩
       eval t (mapDom k s2 ∷ mapEnv k (mapEnv i g)) ≈⟨ eval-nat t reflA k ⟩
       mapDom k (eval t (s2 ∷ mapEnv i g))          ∎)

  evals : ∀ {b Sg G D D1 Ts} → Tms< b > Sg G D Ts → All (Dom Sg G D1) D → All (Dom Sg G D1) Ts
  evals []       g = []
  evals (t ∷ ts) g = eval t g ∷ evals ts g
  
  evalAs : ∀ {b Sg G D D1 Ts} → Args b Sg G D Ts → All (Dom Sg G D1) D → All (Dom Sg G D1) Ts
  evalAs {true}  i  g = build (λ x₁ → get g (i $ x₁))
  evalAs {false} xs g = evals xs g

  eval-nat : ∀ {b Sg G D D1 T} (t : Tm< b > Sg G D T) {xs ys : All (Dom Sg G D1) D} → xs ≡A ys ->
               {K : List Ty} (k : Inj D1 K) → T ∋ eval t (mapEnv k xs) ≡d mapDom k (eval t ys)
  eval-nat (con c ts) {xs} {ys} eq k = cong (con c) (nfs-nat ts eq k)
  eval-nat (mvar u j) {xs} {ys} eq k = cong (mvar u) (nfAs-nat j eq k)
  eval-nat (var x ts) {xs} {ys} eq k = begin[ dom ]
    get (mapEnv k xs) x $$ evals ts (mapEnv k xs) ≈⟨ $$-ext {x = get (mapEnv k xs) x} {mapDom k (get ys x)} (get-nat eq x k)
                                                       {evals ts (mapEnv k xs)} {mapEnv k (evals ts ys)} (evals-nat ts eq k) ⟩ 
    mapDom k (get ys x) $$ mapEnv k (evals ts ys) ≈⟨ $$-nat {x = get ys x} (refld _) {evals ts ys} reflA k ⟩
    ren k (get ys x $$ evals ts ys)               ∎
  eval-nat (lam t)    eq k = λ D i₁ s₁ → eval-ext t (cons-ext s₁ (λ x → transd _ (mapEnv-∘ i₁ k _ x) (mapEnv-ext (i₁ ∘i k) eq x)))

  evals-nat : ∀ {b Sg G D D1 T} (t : Tms< b > Sg G D T) {xs ys : All (Dom Sg G D1) D} → xs ≡A ys ->
               {K : List Ty} (k : Inj D1 K) → evals t (mapEnv k xs) ≡A mapEnv k (evals t ys)
  evals-nat (t ∷ ts) eq k zero    = eval-nat t eq k
  evals-nat (t ∷ ts) eq k (suc v) = evals-nat ts eq k v

  evalAs-nat : ∀ {b Sg G D D1 T} (t : Args b Sg G D T) {xs ys : All (Dom Sg G D1) D} → xs ≡A ys ->
               {K : List Ty} (k : Inj D1 K) → evalAs t (mapEnv k xs) ≡A mapEnv k (evalAs t ys)
  evalAs-nat {true}  (u ∷ i [ _ ]) eq k zero    = get-nat eq u k
  evalAs-nat {true}  (u ∷ i [ _ ]) eq k (suc v) = evalAs-nat i eq k v
  evalAs-nat {false} ts            eq k v       = evals-nat ts eq k v

  nfs-nat : ∀ {b Sg G D D1 T} → (ts : Tms< b > Sg G D T) → {g1 g2 : All (Dom Sg G D1) D} → g1 ≡A g2 → 
            ∀ {K} (k : Inj _ K) → nfs ts (mapEnv k g1) ≡ rens k (nfs ts g2)
  nfs-nat ts {xs} {ys} eq k = begin
    reifys (evals ts (mapEnv k xs)) ≡⟨ reifys-ext (evals-nat ts eq k) ⟩
    reifys (mapEnv k (evals ts ys)) ≡⟨ reifys-nat reflA k ⟩ 
    rens k (reifys (evals ts ys))   ∎

  nfAs-nat : ∀ {b Sg G D D1 T} → (ts : Args b Sg G D T) → {g1 g2 : All (Dom Sg G D1) D} → g1 ≡A g2 → 
            ∀ {K} (k : Inj _ K) → nfAs ts (mapEnv k g1) ≡ rens k (nfAs ts g2)
  nfAs-nat j {xs} {ys} eq k = begin
    reifys (evalAs j (mapEnv k xs)) ≡⟨ reifys-ext (evalAs-nat j eq k) ⟩
    reifys (mapEnv k (evalAs j ys)) ≡⟨ reifys-nat reflA k ⟩
    rens k (reifys (evalAs j ys))   ∎

  eval-ext : ∀ {b Sg G D D1 T} → (t : Tm< b > Sg G D T) → {g1 g2 : All (Dom Sg G D1) D} →
             g1 ≡A g2 → T ∋ eval t g1 ≡d eval t g2
  eval-ext (con c ts) eq = cong (con c) (nfs-ext ts eq)
  eval-ext (mvar u j) eq = cong (mvar u) (nfAs-ext j eq)
  eval-ext (var x ts) eq = $$-ext (eq x) (evals-ext ts eq)
  eval-ext (lam t)    eq = λ D i {s1} {s2} s → eval-ext t (cons-ext s (mapEnv-ext i eq))

  evals-ext : ∀ {b Sg G D D1 T} → (t : Tms< b > Sg G D T) → {g1 g2 : All (Dom Sg G D1) D} →
             g1 ≡A g2 → evals t g1 ≡A evals t g2
  evals-ext (t ∷ ts) eq zero    = eval-ext t eq
  evals-ext (t ∷ ts) eq (suc x) = evals-ext ts eq x

  evalAs-ext : ∀ {b Sg G D D1 T} → (t : Args b Sg G D T) → {g1 g2 : All (Dom Sg G D1) D} → g1 ≡A g2 → evalAs t g1 ≡A evalAs t g2
  evalAs-ext {true}  (i ∷ t [ pf ]) eq zero    = eq i
  evalAs-ext {true}  (i ∷ t [ pf ]) eq (suc x) = evalAs-ext t eq x
  evalAs-ext {false} t              eq x       = evals-ext t eq x
 
  nf-ext : ∀ {b Sg G D D1 T} → (t : Tm< b > Sg G D T) → {g1 g2 : All (Dom Sg G D1) D} → g1 ≡A g2 → nf t g1 ≡ nf t g2
  nf-ext t g = reify-ext _ (eval-ext t g)

  nfs-ext : ∀ {b Sg G D D1 T} → (t : Tms< b > Sg G D T) → {g1 g2 : All (Dom Sg G D1) D} → g1 ≡A g2 → nfs t g1 ≡ nfs t g2
  nfs-ext t g = reifys-ext (evals-ext t g)

  nfAs-ext : ∀ {b Sg G D D1 T} → (t : Args b Sg G D T) → {g1 g2 : All (Dom Sg G D1) D} → g1 ≡A g2 → nfAs t g1 ≡ nfAs t g2
  nfAs-ext t g = reifys-ext (evalAs-ext t g)

 _≤[_]_ : ∀ {Sg G D D1 D2} (g : All (Dom Sg G D1) D) (j : Inj D D2) (g1 : All (Dom Sg G D1) D2) → Set
 g ≤[ j ] g2 = ∀ {S} (x : _ ∋ S) → S ∋ get g x ≡d get g2 (j $ x)

 ≤[]-∘ : ∀ {Sg G B C} → (f : All (Dom Sg G C) B) ->
              ∀ {D} (i : Inj B D) {K} (j : Inj C K) → ∀ (f' : All (Dom Sg G K) D)
              → mapEnv j f ≤[ i ] f' → ∀ {D'} (i' : Inj D D') {K'} (j' : Inj K K') → ∀ (f'' : All (Dom Sg G K') D')
              → mapEnv j' f' ≤[ i' ] f'' → mapEnv (j' ∘i j) f ≤[ (i' ∘i i) ] f'' 
 ≤[]-∘ f i j f' ex i' j' f'' ex' {S} x = begin[ dom ]
  get (mapEnv (j' ∘i j) f) x     ≈⟨ symd S (mapEnv-∘ j' j f x) ⟩
  get (mapEnv j' (mapEnv j f)) x ≈⟨ get-nat reflA x j' ⟩
  mapDom j' (get (mapEnv j f) x) ≈⟨ mapDom-ext j' (ex x) ⟩
  mapDom j' (get f' (i $ x))     ≈⟨ symd _ (get-nat reflA (i $ x) j') ⟩
  get (mapEnv j' f') (i $ x)     ≈⟨ ex' (i $ x) ⟩
  get f'' (i' $ (i $ x))         ≡⟨ cong (get f'') (sym (apply-∘ i' i)) ⟩
  get f'' ((i' ∘i i) $ x)        ∎

 idEnv-≤[] : ∀ {Sg G D} {D1} (i : Inj D D1) → mapEnv i (idEnv {Sg} {G}) ≤[ i ] idEnv 
 idEnv-≤[] i {S} x = begin[ dom ] 
   get (mapEnv i idEnv) x                  ≡⟨ cong (λ g → get g x) (mapAll-build _ injv (mapDom i)) ⟩
   get (build (λ v → mapDom i (injv v))) x ≡⟨ get-build (λ x₁ → mapDom i (injv x₁)) x ⟩
   mapDom i (injv x)                       ≈⟨ injv-nat i x ⟩ 
   injv (i $ x)                            ≡⟨ sym (get-build injv (i $ x)) ⟩
   get idEnv (i $ x)                       ∎


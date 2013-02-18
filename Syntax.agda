module Syntax where

open import Data.Nat hiding (_≤_)
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Sum

open import Support.Equality
open import Support.EqReasoning
open import Support.Product public

open import Injections

open import Syntax.Type public
open import Syntax.NbE
open import Syntax.NbE.Properties
open import Syntax.Sub public
open import Syntax.Equality public
open import Syntax.RenOrn public


congTm : ∀ {b1 b2 Sg G D T G1 D1 T1} -> b1 ≡ b2 -> (f : ∀ {b} -> Term< b > Sg G D T -> Term< b > Sg G1 D1 T1) -> 
         {x : Term< b1 > Sg G D T}{y : Term< b2 > Sg G D T} -> x ≅ y -> f x ≅ f y
congTm refl f refl = refl

cong-∷ : ∀ {b1 b2 Sg G D T Ts} -> b1 ≡ b2 -> {x : Tm< b1 > Sg G D T}{y : Tm< b2 > Sg G D T}
         {xs : Tms< b1 > Sg G D Ts} {ys : Tms< b2 > Sg G D Ts} -> x ≅ y -> xs ≅ ys -> Tms._∷_ x xs ≅ Tms._∷_ y ys
cong-∷ refl refl refl = refl

cong-[] : ∀ {b1 b2 Sg G D} -> b1 ≡ b2 -> 
          let xs : Tms< b1 > Sg G D []; xs = []; ys : Tms< b2 > Sg G D []; ys = [] in xs ≅ ys
cong-[] refl = refl


module Subid where

 open import Function using (_∘_)

 x∧true≡x : ∀ {x} -> x ∧ true ≡ x
 x∧true≡x {false} = refl
 x∧true≡x {true}  = refl

 mutual
  sub-id : ∀ {b Sg G D T} (t : Tm< b > Sg G D T) → sub id-s t ≅ t
  sub-id {b}     (con c ts) = congTm (x∧true≡x {b}) (con c) (subs-id ts)
  sub-id {b}     (var x ts) = congTm (x∧true≡x {b}) (var x) (subs-id ts)
  sub-id {b}     (lam t)    = congTm (x∧true≡x {b}) lam     (sub-id t)
  sub-id {true}  (mvar u j) = ≡-to-≅ (cong (mvar u) (right-id j))
  sub-id {false} (mvar u ts) rewrite ≅-to-≡ (subs-id ts) = ≡-to-≅ (cong (mvar u) (begin 
   reifys (build (λ z → get (evals ts idEnv) (id-i $ z))) 
     ≡⟨ cong reifys (begin 
          build (λ z → get (evals ts idEnv) (id-i $ z)) ≡⟨ build-ext (λ v → cong (get (evals ts idEnv)) (id-i$ v)) ⟩
          build (get (evals ts idEnv))                  ≡⟨ build-get (evals ts idEnv) ⟩
          evals ts idEnv                                ∎) ⟩
   nfs ts idEnv ≡⟨ nfs-id ts ⟩
   ts           ∎))
  
  subs-id : ∀ {b Sg G D T} (t : Tms< b > Sg G D T) → subs id-s t ≅ t
  subs-id {b} []       = cong-[] (x∧true≡x {b})
  subs-id {b} (t ∷ ts) = cong-∷  (x∧true≡x {b}) (sub-id t) (subs-id ts)

sub-id : ∀ {Sg G D T} (t : Tm Sg G D T) → sub id-s t ≡ t
sub-id t = ≅-to-≡ (Subid.sub-id t)

subs-id : ∀ {Sg G D T} (t : Tms Sg G D T) → subs id-s t ≡ t
subs-id ts = ≅-to-≡ (Subid.subs-id ts)

left-ids : ∀ {b Sg G G1} -> (f : Sub< b > Sg G G1) -> (f ∘s id-s) ≡s f
left-ids f S u = ren-id _

∧-assoc : ∀ {a b c} -> (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
∧-assoc {true} = refl
∧-assoc {false} = refl

module Sub∘ where
 mutual
  sub-∘ : ∀ {b3 b1 b2 Sg G1 G2 G3 D T} {f : Sub< b1 > Sg G2 G3}{g : Sub< b2 > _ _ _} (t : Tm< b3 > Sg G1 D T) → sub f (sub g t) ≅ sub (f ∘s g) t
  sub-∘ {b3} (con c ts) = congTm (∧-assoc {b3}) (con c) (subs-∘ ts)
  sub-∘ {b3} (var x ts) = congTm (∧-assoc {b3}) (var x) (subs-∘ ts)
  sub-∘ {b3} (lam t)    = congTm (∧-assoc {b3}) lam     (sub-∘ t)
  sub-∘ {true}          {g = g} (mvar u j)  = ≡-to-≅ (sub-nat (g _ u))
  sub-∘ {false} {f = f} {g = g} (mvar u ts) = 
   Het.trans (≡-to-≅ (nf-nats {f = f} (evals-nats idEnv-nats (idEnv-∘ idEnv) (subs g ts)) (evals-∘ _ (idEnv-∘ idEnv) _) (g _ u))) 
             (Het.cong (replace ((f ∘s g) _ u)) (subs-∘ {f = f} {g = g} ts))
  
  subs-∘ : ∀ {b3 b1 b2 Sg G1 G2 G3 D T} {f : Sub< b1 > Sg G2 G3}{g : Sub< b2 > _ _ _} (t : Tms< b3 > Sg G1 D T) → subs f (subs g t) ≅ subs (f ∘s g) t
  subs-∘ {b3} []       = cong-[] (∧-assoc {b3})
  subs-∘ {b3} (t ∷ t₁) = cong-∷ (∧-assoc {b3}) (sub-∘ t) (subs-∘ t₁)

 subT-∘ : ∀ {Sg G1 G2 G3 D T} {f : Sub< false > Sg G2 G3} {g : Sub< true > Sg _ _} (t : Term< true > Sg G1 D T) 
                              → subT f (subT g t) ≡ subT (f ∘s g) t
 subT-∘ {Sg} {G1} {G2} {G3} {D} {inj₁ x} t = ≅-to-≡ (sub-∘ {true} {false} {true} t)
 subT-∘ {Sg} {G1} {G2} {G3} {D} {inj₂ y} t = ≅-to-≡ (subs-∘ {true} {false} {true} t)
 
sub-∘ : ∀ {Sg G1 G2 G3 D T} {f : Sub Sg G2 G3}{g : Sub _ _ _} (t : Tm Sg G1 D T) → sub f (sub g t) ≡ sub (f ∘s g) t
sub-∘ t = ≅-to-≡ (Sub∘.sub-∘ {true} {true} {true} t)

subs-∘ : ∀ {Sg G1 G2 G3 D T} {f : Sub Sg G2 G3}{g : Sub _ _ _} (t : Tms Sg G1 D T) → subs f (subs g t) ≡ subs (f ∘s g) t
subs-∘ t = ≅-to-≡ (Sub∘.subs-∘ {true} {true} {true} t)


-- Substitution respects pointwise equality.
mutual
  sub-ext : ∀ {b2 b1 Sg G1 G2 D T} {f g : Sub< b1 > Sg G1 G2} → f ≡s g → (t : Tm< b2 > Sg G1 D T) → sub f t ≡ sub g t
  sub-ext         q (con c ts) = cong (con c) (subs-ext q ts)
  sub-ext {true}  q (mvar u j) = cong (ren j) (q _ u)
  sub-ext {false} q (mvar u j) = cong₂ replace (q _ u) (subs-ext q j)
  sub-ext         q (var x ts) = cong (var x) (subs-ext q ts)
  sub-ext         q (lam t)    = cong lam (sub-ext q t)

  subs-ext : ∀ {b1 b2 Sg G1 G2 D T} {f g : Sub< b1 > Sg G1 G2} → f ≡s g → (t : Tms< b2 > Sg G1 D T) → subs f t ≡ subs g t
  subs-ext q []       = refl
  subs-ext q (t ∷ ts) = cong₂ _∷_ (sub-ext q t) (subs-ext q ts)



subT-id : ∀ {Sg G D T} (t : Term Sg G D T) → subT id-s t ≡ t
subT-id {Sg} {G} {D} {inj₁ x} t = ≅-to-≡ (Subid.sub-id t)
subT-id {Sg} {G} {D} {inj₂ y} t = ≅-to-≡ (Subid.subs-id t)

subT-ext : ∀ {b1 b2 Sg G1 G2 D T} {f g : Sub< b1 > Sg G1 G2} → f ≡s g → (t : Term< b2 > Sg G1 D T) → subT f t ≡ subT g t
subT-ext {T = inj₁ x} eq t = sub-ext eq t
subT-ext {T = inj₂ y} eq t = subs-ext eq t

subT-∘ : ∀ {Sg G1 G2 G3 D T} {f : Sub Sg G2 G3}{g : Sub Sg _ _} (t : Term Sg G1 D T) → subT f (subT g t) ≡ subT (f ∘s g) t
subT-∘ {T = inj₁ _} t = sub-∘ t
subT-∘ {T = inj₂ _} t = subs-∘ t



left-idf : ∀ {Sg G G1} -> (f : Sub< false > Sg G G1) -> (f ∘s id-f) ≡s f
left-idf f S u = begin
  eval (f S u) (evals (subs f (reifys idEnv)) idEnv) ≡⟨ eval-ext (f S u) (λ {S} x → begin[ dom ]
           get (evals (subs f (reifys idEnv)) idEnv) x ≡⟨ cong (λ ts → get (evals ts idEnv) x) (reifys-nats idEnv-nats) ⟩ 
           get (evals (reifys idEnv) idEnv) x          ≈⟨ RelA-unfold idEnv (idEnv-∘ idEnv) x ⟩
           get idEnv x                                 ∎) ⟩
  nf (f S u) idEnv                                   ≡⟨ nf-id (f S u) ⟩
  f S u                                              ∎

mutual
  right-idf : ∀ {Sg G D T} -> (t : Tm< false > Sg G D T) -> sub id-f t ≡ t
  right-idf (con c ts) = cong (con c) (rights-idf ts)
  right-idf (var x ts) = cong (var x) (rights-idf ts)
  right-idf (lam t)    = cong lam (right-idf t)
  right-idf (mvar u ts) rewrite rights-idf ts = cong (mvar u) 
    (begin reifys (evals (reifys idEnv) (evals ts idEnv)) ≡⟨ reifys-ext (RelA-unfold _ (idEnv-∘ (evals ts idEnv))) ⟩
           reifys (evals ts idEnv)                        ≡⟨ refl ⟩
           nfs ts idEnv                                   ≡⟨ nfs-id ts ⟩
           ts                                             ∎)

  rights-idf : ∀ {Sg G D T} -> (t : Tms< false > Sg G D T) -> subs id-f t ≡ t
  rights-idf []       = refl
  rights-idf (x ∷ xs) = cong₂ _∷_ (right-idf x) (rights-idf xs)

↓↓ : ∀ {b Sg G D T } -> Tm< b > Sg G D T -> Tm< false > Sg G D T
↓↓ {true}  t = sub id-f t
↓↓ {false} t = t

_≡d_ : ∀ {b1 b2 Sg G D T } -> (t1 : Tm< b1 > Sg G D T)(t2 : Tm< b2 > Sg G D T) -> Set
t1 ≡d t2 = ↓↓ t1 ≡ ↓↓ t2

down : ∀ {b Sg G G1} -> Sub< b > Sg G G1 -> Sub< false > Sg G G1
down {b} s = \ S u -> ↓↓ (s S u) 

↓↓-nat : ∀ {b Sg G D D1 T } -> (i : Inj D D1) (t : Tm< b > Sg G D T) -> ↓↓ (ren i t) ≡ ren i (↓↓ t)
↓↓-nat {true} i t = sub-nat t
↓↓-nat {false} i t = refl

↓↓-comm : ∀ {b b1 Sg G G1 D T} -> (s : Sub< b > Sg G G1) -> (t : Tm< b1 > Sg G D T) -> sub (down s) t ≅ ↓↓ (sub s t)
↓↓-comm {true}  {true}  s t = Het.sym (Sub∘.sub-∘ {f = id-f} {g = s} t)
↓↓-comm {true}  {false} s t = Het.trans (Het.sym (Sub∘.sub-∘ {f = id-f} {g = s} t)) (≡-to-≅ (right-idf (sub s t)))
↓↓-comm {false} {true}  s t = refl
↓↓-comm {false} {false} s t = refl 

↓↓-nat₂ : ∀ {b b1 Sg G G1 D T } -> (s : Sub< b1 > Sg G G1) (t : Tm< b > Sg G D T) -> ↓↓ (sub s t) ≡ sub s (↓↓ t)
↓↓-nat₂ {true}  {true}  s t = begin 
  sub id-f (sub s t)          ≡⟨ ≅-to-≡ (Sub∘.sub-∘ {f = id-f} {g = s} t) ⟩
  sub (id-f ∘s s) t           ≡⟨ sym (sub-ext (left-idf (id-f ∘s s)) t) ⟩
  sub ((id-f ∘s s) ∘s id-f) t ≡⟨ sym (≅-to-≡ (Sub∘.sub-∘ {f = id-f ∘s s} {g = id-f} t)) ⟩
  sub (id-f ∘s s) (↓↓ t)      ≡⟨ ≅-to-≡ (↓↓-comm s (↓↓ t)) ⟩
  ↓↓ (sub s (↓↓ t))           ∎
↓↓-nat₂ {true}  {false} s t = begin 
  sub s t            ≡⟨ sym (sub-ext (left-idf s) t) ⟩
  sub (s ∘s id-f) t  ≡⟨ ≅-to-≡ (Het.sym (Sub∘.sub-∘ {f = s} {g = id-f} t)) ⟩
  sub s (sub id-f t) ∎
↓↓-nat₂ {false} {true}  s t = refl
↓↓-nat₂ {false} {false} s t = refl 

sub-extd : ∀ {b1 b2 b3 Sg G D G1 T } -> (s1 : Sub< b1 > Sg G G1)(s2 : Sub< b2 > Sg G G1) -> (t : Tm< b3 > Sg G D T) ->
            (∀ S x -> s1 S x ≡d s2 S x) -> sub s1 t ≡d sub s2 t
sub-extd s1 s2 t eq = ≅-to-≡ (Het.trans (Het.sym (↓↓-comm s1 t)) (Het.trans (≡-to-≅ (sub-ext eq t)) (↓↓-comm s2 t)))

cong-ren : ∀ {b1 b2 Sg G D D1 T } -> (i : Inj D D1) -> {t1 : Tm< b1 > Sg G D T}{t2 : Tm< b2 > Sg G D T} ->
           t1 ≡d t2 -> ren i t1 ≡d ren i t2
cong-ren i {t1} {t2} eq = begin
  ↓↓ (ren i t1) ≡⟨ ↓↓-nat i t1 ⟩
  ren i (↓↓ t1) ≡⟨ cong (ren i) eq ⟩ 
  ren i (↓↓ t2) ≡⟨ sym (↓↓-nat i t2) ⟩
  ↓↓ (ren i t2) ∎

ren-injd : ∀ {b1 b2 Sg G D D0}{T : Ty} → (i : Inj D D0) → (s : Tm< b1 > Sg G D T) (t : Tm< b2 > Sg G D T) 
             -> ren i s ≡d ren i t -> s ≡d t
ren-injd i s t eq = ren-inj i (↓↓ s) (↓↓ t) (begin
  ren i (↓↓ s) ≡⟨ sym (↓↓-nat i s) ⟩
  ↓↓ (ren i s) ≡⟨ eq ⟩
  ↓↓ (ren i t) ≡⟨ ↓↓-nat i t ⟩
  ren i (↓↓ t) ∎)

cong-↓↓ : ∀ {b1 b2 Sg G D T} -> {t1 : Tm< b1 > Sg G D T}{t2 : Tm< b2 > Sg G D T} ->
            b1 ≡ b2 -> t1 ≅ t2 -> t1 ≡d t2
cong-↓↓ {b} refl eq = cong ↓↓ (≅-to-≡ eq)

cong-sub : ∀ {b1 b2 b3 Sg G D G1 T } -> (s : Sub< b3 > Sg G G1) -> {t1 : Tm< b1 > Sg G D T}{t2 : Tm< b2 > Sg G D T} ->
           t1 ≡d t2 -> sub s t1 ≡d sub s t2
cong-sub s {t1} {t2} eq = begin
  ↓↓ (sub s t1) ≡⟨ ↓↓-nat₂ s t1 ⟩
  sub s (↓↓ t1) ≡⟨ cong (sub s) eq ⟩
  sub s (↓↓ t2) ≡⟨ sym (↓↓-nat₂ s t2) ⟩
  ↓↓ (sub s t2) ∎

mutual
  sub-idf-inj : ∀ {Sg G D T} -> (s t : Tm< true > Sg G D T) -> ↓↓ s ≡T ↓↓ t -> s ≡ t
  sub-idf-inj (con c ts) (con c₁ ts₁) (con ceq eq) = cong₂ con ceq (subs-idf-inj ts ts₁ eq)
  sub-idf-inj (con c ts) (mvar u j)   ()
  sub-idf-inj (con c ts) (var x ts₁)  ()
  sub-idf-inj (mvar u j) (con c ts)   ()
  sub-idf-inj {Sg} {G} (mvar u j) (mvar u₁ j₁) (mvar ueq x₁) = cong₂ mvar ueq 
    (ext-$ j j₁
     λ {(Ss ->> B) v → 
     injective (right# Ss) _ _
      (var-inj₀ (≡-T (begin 
       var (right# Ss $ (j $ v)) (reifys (mapEnv (left# Ss) idEnv)) ≡⟨ sym (apply-injv Ss B v j) ⟩
       eval (reify (Ss ->> B) (injv (right# Ss $ (j $ v)))) idEnv $$ 
         mapEnv (left# Ss) idEnv ≡⟨ (cong (λ t → eval t idEnv $$ mapEnv (left# Ss) idEnv) (hip v)) ⟩
       eval (reify (Ss ->> B) (injv (right# Ss $ (j₁ $ v)))) idEnv $$
         mapEnv (left# Ss) idEnv ≡⟨ apply-injv Ss B v j₁ ⟩
       var (right# Ss $ (j₁ $ v)) (reifys (mapEnv (left# Ss) idEnv)) ∎)))})
   where
    open import Injections.Sum
    pointwise : ∀ {Sg G D T} -> {f g : ∀ {S} (x : T ∋ S) -> Dom Sg G D S} 
           -> ∀ {S} x -> reifys (build f) ≡T reifys (build g) -> reify S (f x) ≡ reify S (g x)
    pointwise zero    (t ∷ ts) = T-≡ t
    pointwise (suc x) (t ∷ ts) = pointwise x ts
    apply-injv : ∀ Ss B v j -> 
                eval (reify (Ss ->> B) (injv (right# Ss $ (j $ v)))) idEnv $$ mapEnv (left# Ss) idEnv
              ≡ var (right# Ss $ (j $ v)) (reifys (mapEnv (left# Ss) idEnv))
    apply-injv Ss B v j = begin
      eval (reify (Ss ->> B) (injv (right# Ss $ (j $ v)))) idEnv $$
        mapEnv (left# Ss) idEnv ≡⟨ $$-ext
                                     (Rel-unfold (Ss ->> B) idEnv
                                      (injv-∘ (Ss ->> B) idEnv _ _
                                       (≡-d (get-build (injv {Sg} {G}) (right# Ss $ (j $ v))))))
                                     {xs = mapEnv (left# Ss) idEnv} {ys = mapEnv (left# Ss) idEnv} reflA ⟩
      injv (right# Ss $ (j $ v)) $$ mapEnv (left# Ss) idEnv ≡⟨ injv-id (right# Ss $ (j $ v)) (mapEnv (left# Ss) idEnv) ⟩
      var (right# Ss $ (j $ v)) (reifys (mapEnv (left# Ss) idEnv)) ∎

    hip : ∀ {Ss B} (v : _ ∋ (Ss ->> B)) -> reify _ (injv (right# Ss $ (j $ v))) ≡ reify _ (injv (right# Ss $ (j₁ $ v)))
    hip {Ss} v = pointwise {f = \ x -> injv (right# Ss $ (j $ x))} {g = \ x -> injv (right# Ss $ (j₁ $ x))} v
      (≡-T (begin 
       reifys (build (λ x → injv (right# Ss $ (j $ x))))    ≡⟨ reifys∘build∘injv-nat j ⟩ 
       rens (right# Ss) (rens j  (reifys idEnv))            ≡⟨ cong (rens (right# Ss)) x₁ ⟩ 
       rens (right# Ss) (rens j₁ (reifys idEnv))            ≡⟨ sym (reifys∘build∘injv-nat j₁) ⟩ 
       reifys (build (λ x₂ → injv (right# Ss $ (j₁ $ x₂)))) ∎))
     where
      build∘injv-nat : ∀ j -> build (λ x → injv (right# Ss $ (j $ x))) ≡A mapEnv (right# Ss ∘i j) (build injv)
      build∘injv-nat j {S} x = begin[ dom ] 
       get (build (λ v₁ → injv (right# Ss $ (j $ v₁)))) x ≡⟨ get-build (λ x₂ → injv (right# Ss $ (j $ x₂))) x ⟩
       injv (right# Ss $ (j $ x)) ≡⟨ cong injv (sym (apply-∘ (right# Ss) j)) ⟩
       injv ((right# Ss ∘i j) $ x) ≈⟨ symd S (injv-nat (right# Ss ∘i j) x) ⟩
       mapDom (right# Ss ∘i j) (injv x) ≡⟨ sym (cong (mapDom _) (get-build injv x)) ⟩
       mapDom (right# Ss ∘i j) (get idEnv x) ≡⟨ sym (get-nat-≡ {f = mapDom (right# Ss ∘i j)} idEnv x) ⟩
       get (mapEnv (right# Ss ∘i j) idEnv) x ∎
      reifys∘build∘injv-nat : ∀ j -> reifys (build (λ x → injv (right# Ss $ (j $ x)))) ≡ rens (right# Ss) (rens j (reifys (build injv)))
      reifys∘build∘injv-nat j = begin 
        reifys (build (λ x → injv (right# Ss $ (j $ x)))) ≡⟨ reifys-ext (build∘injv-nat j) ⟩
        reifys (mapEnv (right# Ss ∘i j) idEnv)            ≡⟨ reifys-nat reflA (right# Ss ∘i j) ⟩
        rens (right# Ss ∘i j) (reifys idEnv)              ≡⟨ rens-∘ (reifys idEnv) ⟩
        rens (right# Ss) (rens j (reifys idEnv))          ∎
  sub-idf-inj (mvar u j) (var x ts)   ()
  sub-idf-inj (var x ts) (con c ts₁)  ()
  sub-idf-inj (var x ts) (mvar u j)   ()
  sub-idf-inj (var x ts) (var x₁ ts₁) (var xeq eq) = cong₂ var xeq (subs-idf-inj ts ts₁ eq)
  sub-idf-inj (lam s)    (lam t)      (lam eq)     = cong lam (sub-idf-inj s t eq)

  subs-idf-inj : ∀ {Sg G D T} -> (s t : Tms< true > Sg G D T) -> subs id-f s ≡T subs id-f t -> s ≡ t
  subs-idf-inj []       []       _            = refl
  subs-idf-inj (s ∷ ss) (t ∷ ts) (teq ∷ tseq) = cong₂ _∷_ (sub-idf-inj s t teq) (subs-idf-inj ss ts tseq)

↓↓-inj : ∀ {b Sg G D T } -> {s t : Tm< b > Sg G D T} -> s ≡d t -> s ≡ t
↓↓-inj {true} eq = sub-idf-inj _ _ (≡-T eq)
↓↓-inj {false} eq = eq

open import Syntax.Height public
open import Syntax.OneHoleContext public

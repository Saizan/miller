module Syntax.Sub where

open import Data.Unit using (⊤)
open import Data.Sum

open import Support.Equality
open ≡-Reasoning
open import Support.Product

open import Injection

open import Syntax.Type
open import Syntax.NbE
open import Syntax.NbEC

replace : ∀ {b Sg G D D1 T} → Tm< b > Sg G D T → Tms< false > Sg G D1 D → Tm< false > Sg G D1 T
replace t ts = nf t (evals ts idEnv)

toFalse : ∀ {b Sg G D T} → Tm< b > Sg G D T → Tm< false > Sg G D T
toFalse {false} t = t 
toFalse {true}  t = nf t idEnv

-- The type of meta-substitutions
Sub<_> : ∀ b → Ctx → MCtx → MCtx → Set
Sub< b > Sg G1 G2 = ∀ S → G1 ∋ S → Tm< b > Sg G2 (ctx S) (! type S)

Sub : Ctx → MCtx → MCtx → Set
Sub = Sub< true >

_≡s_ : ∀ {b Sg G G1}(s s₁ : Sub< b > Sg G G1) → Set
s ≡s s₁ = ∀ S u → s S u ≡ s₁ S u
 
thin-s : ∀ {Sg}{G T} → (u : G ∋ T) → Sub Sg (G - u) G
thin-s u = \ S v → mvar (thin u S v) id-i

mutual
  sub : ∀ {b1 b2 Sg G1 G2 D T} → Sub< b1 > Sg G1 G2 → Tm< b2 > Sg G1 D T → Tm< b2 ∧ b1 > Sg G2 D T
  sub              s (con x x₁)  = con x (subs s x₁)
  sub {b1} {true}  s (mvar u i)  = ren i (s _ u)
  sub {b1} {false} s (mvar u xs) = replace (s _ u) (subs s xs)
  sub              s (var x xs)  = var x (subs s xs)
  sub              s (lam t)     = lam (sub s t)

  subs : ∀ {b1 b2 Sg G1 G2 D Ss} → Sub< b1 > Sg G1 G2 → Tms< b2 > Sg G1 D Ss → Tms< b2 ∧ b1 > Sg G2 D Ss
  subs s []       = []
  subs s (x ∷ ts) = sub s x ∷ subs s ts

id-s : ∀ {Sg G} → Sub Sg G G
id-s = \ S x → mvar x id-i

id-f : ∀ {Sg G} → Sub< false > Sg G G
id-f = \ S u → mvar u (reifys idEnv)

_∘s_ : ∀ {b1 b2 Sg G1 G2 G3} → Sub< b1 > Sg G2 G3 → Sub< b2 > Sg G1 G2 → Sub< b2 ∧ b1 > Sg G1 G3
r ∘s s = λ S x → sub r (s S x)

-- f ≤ g iff g can be specialized to f 
_≤_ : ∀ {Sg G G1 G2 b} → Sub< b > Sg G G1 → Sub Sg G G2 → Set
f ≤ g = ∃ \ r → ∀ S u → f S u ≡ (r ∘s g) S u

subT : ∀ {b1 b2 T Sg G1 G2 D} → (Sub< b1 > Sg G1 G2) → Term< b2 > Sg G1 D T → Term< b2 ∧ b1 > Sg G2 D T
subT {T = inj₁ _} i t = sub i t
subT {T = inj₂ _} i ts = subs i ts

mutual
  Dom-nats : ∀ {Sg G1 G2 D b} T → (f : Sub< b > Sg G1 G2) (x : Dom Sg G1 D T)(y : Dom Sg G2 D T) → Set
  Dom-nats ([]       ->> _) f x y = sub f x ≡ y
  Dom-nats ((S ∷ Ss) ->> B) f x y = ∀ D1 r {s1 s2} → Rel S idEnv s2 s2 →
                                     Dom-nats S f s1 s2 → Dom-nats (Ss ->> B) f (proj₁ x D1 r s1) (proj₁ y D1 r s2)

  Env-nats : ∀ {Sg G1 G2 D Ts b} → (f : Sub< b > Sg G1 G2) (x : All (Dom Sg G1 D) Ts)(y : All (Dom Sg G2 D) Ts) → Set
  Env-nats f []       []       = ⊤
  Env-nats f (x ∷ xs) (y ∷ ys) = Dom-nats _ f x y × Env-nats f xs ys

RelId : ∀ {Sg G D Ts} → (y : All (Dom Sg G D) Ts) → Set
RelId f = RelA idEnv f f

get-nats : ∀ {b1 Sg G1 G2 D1 D2} {f : Sub< b1 > Sg G1 G2} {g1 : All (Dom Sg G1 D1) D2}{g2 : All (Dom Sg G2 D1) D2} 
           → Env-nats f g1 g2 → ∀ {T} x → Dom-nats T f (get g1 x) (get g2 x)
get-nats {g1 = _ ∷ _} {_ ∷ _} (dnat , _) zero = dnat
get-nats {g1 = _ ∷ _} {_ ∷ _} (_ , enat) (suc x) = get-nats enat x
 

mutual
  sub-nat : ∀ {b1 b2 Sg G1 G2 D1 D2 T} {f : Sub< b1 > Sg G1 G2} {i : Inj D1 D2} (t : Tm< b2 > Sg G1 D1 T) → sub f (ren i t) ≡ ren i (sub f t)
  sub-nat                          (con c ts)  = cong (con c) (subs-nat ts)
  sub-nat                          (var x ts)  = cong (var _) (subs-nat ts)
  sub-nat                          (lam t)     = cong lam (sub-nat t)
  sub-nat {b1} {true}              (mvar u j)  = ren-∘ _
  sub-nat {b1} {false} {f = f} {i} (mvar u xs) = begin 
    replace (f _ u) (subs f (rens i xs))              ≡⟨ cong (replace (f _ u)) (subs-nat xs) ⟩ 
    replace (f _ u) (rens i (subs f xs))              ≡⟨ eval-ext (f _ u) (evals-square (subs f xs) i i (idEnv-≤[] i)) ⟩
    eval (f _ u) (mapEnv i (evals (subs f xs) idEnv)) ≡⟨ eval-nat (f _ u) reflA i ⟩ 
    ren i (sub f (mvar u xs))                         ∎
  
  subs-nat : ∀ {b1 b2 Sg G1 G2 D1 D2 T} {f : Sub< b1 > Sg G1 G2} {i : Inj D1 D2} (t : Tms< b2 > Sg G1 D1 T) → subs f (rens i t) ≡ rens i (subs f t)
  subs-nat []       = refl
  subs-nat (t ∷ ts) = cong₂ _∷_ (sub-nat t) (subs-nat ts)

mutual
  eval-nats : ∀ {b1 b2 Sg G1 G2 D1 D2 T} {f : Sub< b1 > Sg G1 G2} {g1 : All (Dom Sg G1 D1) D2}{g2 : All (Dom Sg G2 D1) D2} 
              → Env-nats f g1 g2 → RelId g2 → (t : Tm< b2 > Sg G1 D2 T) → Dom-nats T f (eval t g1) (eval (sub f t) g2)
  eval-nats g gr (con c ts) = cong (con c) (nfs-nats g gr ts)
  eval-nats g gr (var x ts) = $$-nats _ (get-nats g x) (evals-nats g gr ts) (evals-∘ idEnv gr _)
  eval-nats g gr (lam t)    = λ D1 r sr x → eval-nats (x , mapEnv-nats _ _ r g) 
       (λ { {._} zero → sr; {S} (suc v) → mapRelA idEnv gr r r idEnv (idEnv-≤[] r) v }) t
  eval-nats {_} {true}  {f = f} {g1} {g2} g gr (mvar u j)  = begin 
    eval (f _ u) (evals (subs f (reifys (build (λ x₁ → get g1 (j $ x₁))))) idEnv) 
        ≡⟨ cong (λ ts → eval (f _ u) (evals ts idEnv)) (reifys-nats {f = f} (evalAs-nats g j)) ⟩ 
    eval (f _ u) (evals (reifys (build (λ z → get g2 (j $ z)))) idEnv)
        ≡⟨ eval-ext (f _ u) (RelA-unfold idEnv (precompose-∘ idEnv gr j)) ⟩
    eval (f _ u) (build (λ z → get g2 (j $ z))) 
        ≡⟨ sym (eval-tri (f _ u) j (λ x → ≡-d (get-build (λ v → get g2 (j $ v)) x))) ⟩
    eval (ren j (f _ u)) g2 ∎  
 
  eval-nats {_} {false} {f = f} {g1} {g2} g gr (mvar u ts) = begin
    replace (f _ u) (subs f (reifys (evals ts g1)))          ≡⟨ cong (replace (f _ u)) (reifys-nats {f = f} (evals-nats g gr ts)) ⟩
    nf (f _ u) (evals (reifys (evals (subs f ts) g2)) idEnv) ≡⟨ sym
                                                                  (nf-∘ (f _ u) g2
                                                                   (λ {S} x →
                                                                      transR S (evals-∘ g2 (idEnv-∘ g2) (subs f ts) x)
                                                                      (symd _ (RelA-unfold idEnv (evals-∘ idEnv gr (subs f ts)) x)))) ⟩
    nf (nf (f _ u) (evals (subs f ts) idEnv)) g2             ∎


  evals-nats : ∀ {b1 b2 Sg G1 G2 D1 D2 T} {f : Sub< b1 > Sg G1 G2} {g1 : All (Dom Sg G1 D1) D2}{g2 : All (Dom Sg G2 D1) D2} 
               → Env-nats f g1 g2 → RelId g2 → (t : Tms< b2 > Sg G1 D2 T) → Env-nats f (evals t g1) (evals (subs f t) g2)
  evals-nats enat gr []       = _
  evals-nats enat gr (x ∷ xs) = eval-nats enat gr x , evals-nats enat gr xs

  evalAs-nats : ∀ {b1 Sg G1 G2 D1 D2 T} {f : Sub< b1 > Sg G1 G2} {g1 : All (Dom Sg G1 D1) D2}{g2 : All (Dom Sg G2 D1) D2} 
                → Env-nats f g1 g2 → (t : Args true Sg G1 D2 T) → Env-nats f (evalAs t g1) (evalAs t g2)
  evalAs-nats g []             = _
  evalAs-nats g (i ∷ t [ pf ]) = get-nats g i , evalAs-nats g t
  
  expand-nats : ∀ {b1 Sg G1 G2 D B} Ss {f : Sub< b1 > Sg G1 G2}{c1 c2} 
                → (∀ D r {xs ys} → Env-nats f xs ys → sub f (proj₁ c1 D r xs) ≡ proj₁ c2 D r ys) 
                → Dom-nats {D = D} (Ss ->> B) f (expand Ss c1) (expand Ss c2)
  expand-nats []       h = h _ id-i _
  expand-nats (S ∷ Ss) h = λ D1 r sr x₁ → expand-nats Ss (λ D r₁ eq → h D (r₁ ∘i r) (mapDom-nats S r₁ x₁ , eq))

  injv-nats : ∀ {b1 Sg G1 G2 D T} {f : Sub< b1 > Sg G1 G2} → (v : D ∋ T) → Dom-nats T f (injv v) (injv v)
  injv-nats {T = _ ->> _} v = expand-nats _ (λ D r x → cong (var _) (reifys-nats x))
   
  reify-nats : ∀ {b1 Sg G1 G2 D1} T {f : Sub< b1 > Sg G1 G2} {t1 : (Dom Sg G1 D1) T}{t2 : (Dom Sg G2 D1) T} 
               → Dom-nats T f t1 t2 → sub f (reify T t1) ≡ reify T t2
  reify-nats ([]       ->> _) t = t
  reify-nats ((S ∷ Ss) ->> _) t = cong lam (reify-nats (Ss ->> _) (t _ (weak id-i) (injv-∘ S idEnv zero (injv zero) (refld _)) (injv-nats zero)))

  reifys-nats : ∀ {b1 Sg G1 G2 D1 D2} {f : Sub< b1 > Sg G1 G2} {g1 : All (Dom Sg G1 D1) D2}{g2 : All (Dom Sg G2 D1) D2}
                → Env-nats f g1 g2 → subs f (reifys g1) ≡ reifys g2
  reifys-nats {g1 = []}     {[]}     eq = refl
  reifys-nats {g1 = x ∷ xs} {y ∷ ys} eq = cong₂ _∷_ (reify-nats _ (proj₁ eq)) (reifys-nats (proj₂ eq))

  nf-nats : ∀ {b1 b2 Sg G1 G2 D1 D2 T} {f : Sub< b1 > Sg G1 G2} {g1 : All (Dom Sg G1 D1) D2}{g2 : All (Dom Sg G2 D1) D2} 
            → Env-nats f g1 g2 → RelId g2 → (t : Tm< b2 > Sg G1 D2 T) → sub f (nf t g1) ≡ nf (sub f t) g2
  nf-nats enat gr t = reify-nats _ (eval-nats enat gr t)

  nfs-nats : ∀ {b1 b2 Sg G1 G2 D1 D2 T} {f : Sub< b1 > Sg G1 G2} {g1 : All (Dom Sg G1 D1) D2}{g2 : All (Dom Sg G2 D1) D2} 
           →  Env-nats f g1 g2 → RelId g2 → (t : Tms< b2 > Sg G1 D2 T) → subs f (nfs t g1) ≡ nfs (subs f t) g2
  nfs-nats g gr []       = refl
  nfs-nats g gr (x ∷ xs) = cong₂ _∷_ (nf-nats g gr x) (nfs-nats g gr xs)

  mapDom-nats : ∀ {Sg G1 G2 D D1 b} Ts → {f : Sub< b > Sg G1 G2} {x : (Dom Sg G1 D) Ts}{y : (Dom Sg G2 D) Ts}
                → (i : Inj D D1) → Dom-nats Ts f x y → Dom-nats Ts f (mapDom i x) (mapDom i y)
  mapDom-nats ([]       ->> _) {x = x} i d = trans (sub-nat x) (cong (ren i) d)
  mapDom-nats ((S ∷ Ss) ->> _)         i d = λ D1 r x₁ → d D1 (r ∘i i) x₁

  mapEnv-nats : ∀ {Sg G1 G2 D D1 Ts b} → {f : Sub< b > Sg G1 G2} (x : All (Dom Sg G1 D) Ts)(y : All (Dom Sg G2 D) Ts)
                → (i : Inj D D1) → Env-nats f x y → Env-nats f (mapEnv i x) (mapEnv i y)
  mapEnv-nats [] [] i e = _
  mapEnv-nats (x ∷ xs) (y ∷ ys) i (s , e) = mapDom-nats _ i s , mapEnv-nats xs ys i e

  $$-nats : ∀ {Sg G G1 D Ts B b} (s : Sub< b > Sg G G1) 
             {f1 : Dom Sg G D (Ts ->> B)} {f2 : Dom Sg G1 D (Ts ->> B)} {xs : All (Dom Sg G D) Ts} {xs1 : All (Dom Sg G1 D) Ts} →  
             Dom-nats (Ts ->> B) s f1 f2 → Env-nats s xs xs1 → RelId xs1 → Dom-nats (! B) s (f1 $$ xs) (f2 $$ xs1)
  $$-nats s {xs = []}      {[]}      dnat enat gr = dnat
  $$-nats s {xs = px ∷ xs} {py ∷ ys} dnat enat gr = $$-nats s (dnat _ id-i (gr zero) (proj₁ enat)) (proj₂ enat) (\ x → gr (suc x))

  build-nats : ∀ {b Sg G G1 D} Ts (s : Sub< b > Sg G G1) (f : ∀ {S} (x : Ts ∋ S) → Dom Sg G D S) ->
              (g : ∀ {S} (x : Ts ∋ S) → Dom Sg G1 D S) ->
              (∀ {S} (x : Ts ∋ S) → Dom-nats S s (f x) (g x)) → Env-nats s (build f) (build g)
  build-nats []       s f g fg-nats = _
  build-nats (x ∷ Ts) s f g fg-nats = fg-nats zero , build-nats Ts s (λ x₁ → f (suc x₁)) (λ x₁ → g (suc x₁)) (λ x₁ → fg-nats (suc x₁))

  idEnv-nats : ∀ {D b Sg G1 G2} {f : Sub< b > Sg G1 G2} → Env-nats f (idEnv {D = D}) idEnv
  idEnv-nats = build-nats _ _ injv injv injv-nats


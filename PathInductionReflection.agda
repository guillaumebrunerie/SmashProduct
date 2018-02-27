{-# OPTIONS --without-K --type-in-type --caching #-}

data ℕ : Set where
  O : ℕ
  S : ℕ → ℕ

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

record Unit : Set where
  constructor tt

data Empty : Set where

data _==_ {A : Set} (a : A) : A → Set where
  idp : a == a

PathOver : {A : Set} (B : A → Set) {x y : A} (p : x == y) → B x → B y → Set
PathOver B idp u v = (u == v)

postulate
  A : Set

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

coe : {A B : Set} → (A == B) → A → B
coe idp a = a

PathOverCoe : {x y : Set} {p : x == y} {u : x} → PathOver (λ x → x) p u (coe p u)
PathOverCoe {p = idp} = idp

eq-PathOver : {X Y : Set} {p : X == Y} {u v : X} {u' v' : Y}
            → PathOver (λ x → x) p u u'
            → PathOver (λ x → x) p v v'
            → (u == v) == (u' == v')
eq-PathOver {p = idp} idp idp = idp

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A



data Context : Set
data Type (Γ : Context) : Set
data Term (Γ : Context) (T : Type Γ) : Set
data vars : (Γ : Context) → Set
get-type : (Γ : Context) → vars Γ → Type Γ

record Coherence : Set where
  constructor coh
  inductive
  field
    Γ : Context
    T : Type Γ

infixl 10 _,_

data Context where
  ⟨⟩ : Context
  _,_ : (Γ : Context) (T : Type Γ) → Context

weaken : {Γ : Context} {T : Type Γ} → Type Γ → Type (Γ , T)
weaken-tm : {Γ : Context} {T : Type Γ} {A : Type Γ} → Term Γ A → Term (Γ , T) (weaken A)

data vars where
  last : {Γ : Context} {T : Type Γ} → vars (Γ , T)
  before : {Γ : Context} {T : Type Γ} → vars Γ → vars (Γ , T)

data Type Γ where
  * : Type Γ
  Id : {T : Type Γ} → Term Γ T → Term Γ T → Type Γ

data Term Γ T where
  Var : (n : vars Γ) (eq : T == get-type Γ n) → Term Γ T

weaken * = *
weaken (Id u v) = Id (weaken-tm u) (weaken-tm v)

get-type (Γ , T) last = weaken T
get-type (Γ , T) (before n) = weaken (get-type Γ n)

weaken-tm (Var n idp) = Var (before n) idp

{-# TERMINATING #-}
[_]ctx : Context → Set
[_]ty : {Γ : Context} → Type Γ → [ Γ ]ctx → Set
[_]tm : {Γ : Context} {T : Type Γ} → Term Γ T → (γ : [ Γ ]ctx) → [ T ]ty γ

[ ⟨⟩ ]ctx = Unit
[ Γ , T ]ctx = Σ [ Γ ]ctx [ T ]ty

[ * ]ty _ = A
[ Id x y ]ty γ = ([ x ]tm γ) == ([ y ]tm γ)

eq-weaken : {Γ : Context} {T : Type Γ} {γ : [ Γ ]ctx} {U : Type Γ} {u : [ U ]ty γ} → [ T ]ty γ == [ weaken T ]ty (γ , u)
eq-weaken-tm : {Γ : Context} {T : Type Γ} {γ : [ Γ ]ctx} {t : Term Γ T} {U : Type Γ} {u : [ U ]ty γ} → PathOver (λ x → x) eq-weaken ([ t ]tm γ) ([ weaken-tm t ]tm (γ , u))

eq-weaken {T = *} = idp
eq-weaken {T = Id x y} = eq-PathOver (eq-weaken-tm {t = x}) (eq-weaken-tm {t = y})

[ Var last idp ]tm (a , b) = coe eq-weaken b
[ Var (before n) idp ]tm (a , b) = coe eq-weaken ([ Var n idp ]tm a)

eq-weaken-tm {t = Var n idp} = PathOverCoe

[[_]] : Coherence → Set
[[ coh Γ U ]] = (γ : [ Γ ]ctx) → [ U ]ty γ

test : Coherence
test = coh (⟨⟩ , * , * , Id (Var (before last) idp) (Var last idp)) (Id (Var (before last) idp) (Var (before (before last)) idp))

subst-ty : {Γ : Context} {U : Type Γ} (T : Type (Γ , U)) (a : Term Γ U) → Type Γ
subst-tm : {Γ : Context} {U : Type Γ} {T : Type (Γ , U)} (u : Term (Γ , U) T) (a : Term Γ U) → Term Γ (subst-ty T a)

subst-ty * a = *
subst-ty (Id u v) a = Id (subst-tm u a) (subst-tm v a)

subst-tm (Var last idp) a = {!a!}
subst-tm (Var (before n) idp) a = Var {!n!} idp

postulate
  inv : [[ test ]]

paf : {a b : A} → a == b → b == a
paf p = inv (_ , _ , _ , p)

thing : {Γ : Context} {T : Type Γ} {U : Type Γ} {T' : Type (Γ , U)} {γ : [ Γ ]ctx} {u : [ U ]ty γ} → (T' == weaken T) → [ T ]ty γ == [ T' ]ty (γ , u)
thing idp = eq-weaken

-- Here is the problem:
-- In [lemma], the right-hand side of [eq'] depends on [a] (because we weaken by [a]), so we cannot use J on it

solve : (Γ : Context) (T : Type Γ) → Maybe [[ coh Γ T ]]
solve ⟨⟩ _ = nothing
solve (⟨⟩ , *) * = just (λ γ → snd γ)
solve (⟨⟩ , *) (Id (Var last idp) (Var last idp)) = just (λ γ → idp)
solve (⟨⟩ , *) (Id (Var last idp) (Var (before ()) eq))
solve (⟨⟩ , *) (Id (Var (before ()) idp) x₁)
solve (⟨⟩ , Id (Var () idp) x₁) U 
solve (Γ , * , *) U = nothing
solve (Γ , * , Id (Var last idp) (Var last eq)) U = nothing
solve (Γ , * , Id (Var last idp) (Var (before n) eq)) U  with solve Γ (subst-ty (subst-ty U {!!}) (Var n {!eq!}))
... | nothing = nothing
... | just res = just {!!} where
  lemma : (γ : [ Γ ]ctx)
          (a : A)
          (eq' : a == coe (thing {u = a} eq) ([ Var n idp ]tm γ)) →
            [ U ]ty (γ , a , {!!})
  lemma = {!!}
solve (Γ , * , Id (Var (before n) idp) x₁) U = nothing
solve (Γ , Id x x₁ , T') U = nothing

-- ctx : Context
-- ctx = (⟨⟩ , * , * , Id (Var (before last)) (Var last))

-- _→Set : Context → Set
-- _→/_ : (Γ : Context) (A : Γ →Set) → Set
-- [_]ty+ : {Γ : Context} (T : Type Γ) → Γ →Set
-- that : (Γ : Context) (T : Γ →Set) → Γ →Set

-- Pi/ : (Γ : Context) (T : Type Γ) (A : Γ →Set) (B : Γ →/ that Γ A) → Γ →Set

-- ⟨⟩ →Set = Set
-- (Γ , T) →Set = Γ →/ [ T ]ty+

-- that ⟨⟩ T = T → Set
-- that (Γ , U) T = {!!}

-- ⟨⟩ →/ A = A
-- (Γ , T) →/ A = Γ →/ (Pi/ Γ T [ T ]ty+ {!A!}) -- (Pi/ Γ T [ T ]ty+ A)

-- Pi/ ⟨⟩ T A B = (a : A) → B a
-- Pi/ (Γ , T₁) T A B = {!!}

-- [ T ]ty+ = {!!}

-- [ Γ ]ctx+ represents the type (γ : Γ) → Set
-- [ Γ ]ctxdep A represents the type (γ : Γ) → A γ

-- given T : (γ : Γ) → Set    and U : (γ : Γ) → ((t : T γ) → Set)
-- (γ : Γ) ((t : T γ) → U γ t)

--(γ : Γ) (t : T γ) → A γ t

-- [[_]] : Coherence → Set
-- [[ coh ⟨⟩ U ]] = [ U ]ty tt
-- [[ coh (Γ , T) U ]] = {!!}

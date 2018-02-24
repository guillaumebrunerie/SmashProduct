{-# OPTIONS --without-K --rewriting #-}

module PathInduction where


-- Universe levels

open import Agda.Primitive public using (lzero)
  renaming (Level to ULevel; lsuc to lsucc; _⊔_ to lmax)

Type : (i : ULevel) → Set (lsucc i)
Type i = Set i


of-type : ∀ {i} (A : Type i) (u : A) → A
of-type A u = u

infix 40 of-type
syntax of-type A u =  u :> A

-- Rewriting

postulate _↦_ : {i : ULevel} {A : Type i} → A → A → Type i
{-# BUILTIN REWRITE _↦_ #-}

-- Identity type

infix 30 _==_
data _==_ {i : ULevel} {A : Type i} (a : A) : A → Type i where
  idp : a == a

data Square {i} {A : Type i} {a : A} : {b c d : A} (p : a == b) (q : c == d) (r : a == c) (s : b == d) → Type i where
  ids : Square idp idp idp idp

data Cube {i} {A : Type i} {a : A} :
  {b c d : A}
  {p : a == b} {q : c == d}
  {r : a == c} {s : b == d}
  (sq : Square p q r s) -- left

  {a' b' c' d' : A}
  {p' : a' == b'} {q' : c' == d'}
  {r' : a' == c'} {s' : b' == d'}
  (sq' : Square p' q' r' s') -- left

  {a= : a == a'} {b= : b == b'}
  {c= : c == c'} {d= : d == d'}
  (p= : Square p p' a= b=) -- back
  (q= : Square q q' c= d=) -- top
  (r= : Square r r' a= c=) -- bottom
  (s= : Square s s' b= d=) -- front
  → Type i

  where
  idc : Cube ids ids ids ids ids ids


data HyperCube {i} {A : Type i} {a : A} :
  {b c d : A} {p : a == b} {q : c == d} {r : a == c} {s : b == d} {sq : Square p q r s}
  {a' b' c' d' : A} {p' : a' == b'} {q' : c' == d'} {r' : a' == c'} {s' : b' == d'} {sq' : Square p' q' r' s'}
  {a= : a == a'} {b= : b == b'} {c= : c == c'} {d= : d == d'}
  {p= : Square p p' a= b=} {q= : Square q q' c= d=} {r= : Square r r' a= c=} {s= : Square s s' b= d=}
  (α : Cube sq sq' p= q= r= s=)

  {a* b* c* d* : A} {p* : a* == b*} {q* : c* == d*} {r* : a* == c*} {s* : b* == d*} {sq* : Square p* q* r* s*}
  {a'* b'* c'* d'* : A} {p'* : a'* == b'*} {q'* : c'* == d'*} {r'* : a'* == c'*} {s'* : b'* == d'*} {sq'* : Square p'* q'* r'* s'*}
  {a=* : a* == a'*} {b=* : b* == b'*} {c=* : c* == c'*} {d=* : d* == d'*}
  {p=* : Square p* p'* a=* b=*} {q=* : Square q* q'* c=* d=*} {r=* : Square r* r'* a=* c=*} {s=* : Square s* s'* b=* d=*}
  (α* : Cube sq* sq'* p=* q=* r=* s=*)

  {a*= : a == a*} {b*= : b == b*} {c*= : c == c*} {d*= : d == d*} {p*= : Square p p* a*= b*=} {q*= : Square q q* c*= d*=} {r*= : Square r r* a*= c*=} {s*= : Square s s* b*= d*=} (sq*= : Cube sq sq* p*= q*= r*= s*=)
  {a'*= : a' == a'*} {b'*= : b' == b'*} {c'*= : c' == c'*} {d'*= : d' == d'*} {p'*= : Square p' p'* a'*= b'*=} {q'*= : Square q' q'* c'*= d'*=} {r'*= : Square r' r'* a'*= c'*=} {s'*= : Square s' s'* b'*= d'*=} (sq'*= : Cube sq' sq'* p'*= q'*= r'*= s'*=)
  {a=*= : Square a= a=* a*= a'*=} {b=*= : Square b= b=* b*= b'*=} {c=*= : Square c= c=* c*= c'*=} {d=*= : Square d= d=* d*= d'*=}
  (p=*= : Cube p= p=* p*= p'*= a=*= b=*=) (q=*= : Cube q= q=* q*= q'*= c=*= d=*=) (r=*= : Cube r= r=* r*= r'*= a=*= c=*=) (s=*= : Cube s= s=* s*= s'*= b=*= d=*=)
  → Type i

  where
  idhc : HyperCube idc idc idc idc idc idc idc idc



module _ {i} {A : Type i} where
  coh∙! : {a b c : A} → a == b → c == b → a == c
  coh∙! idp idp = idp

  coh!∙ : {a b c : A} → b == a → b == c → a == c
  coh!∙ idp p = p

  coh∙∙! : {a b c d : A} → a == b → b == c → d == c → a == d
  coh∙∙! idp idp idp = idp

  coh!∙∙ : {a b c d : A} → b == a → b == c → c == d → a == d
  coh!∙∙ idp idp idp = idp



record Coh {i} (A : Type i) : Type i where
  field
    & : A
open Coh public

module _ {i j} {A : Type i} {a : A} where

 instance

  J- : {B : (a' : A) → a == a' → Type j}
    → Coh (B a idp) → Coh ({a' : A} (p : a == a') → B a' p)
  & (J- d) idp = & d

  J! : {B : (a' : A) → a' == a → Type j}
    → Coh (B a idp) → Coh ({a' : A} (p : a' == a) → B a' p)
  & (J! d) idp = & d

  J□ : {B : {b c d : A} {p : a == b} {q : c == d} {r : a == c} {s : b == d} → Square p q r s → Type j}
    → Coh (B ids) → Coh ({b c d : A} {p : a == b} {q : c == d} {r : a == c} {s : b == d} (sq : Square p q r s) → B sq)
  & (J□ {B = B} d) ids = & d

  J□i : {B : {b c d : A} {p : a == b} {q : c == d} {r : a == c} {s : b == d} → Square p q r s → Type j}
    → Coh (B ids) → Coh ({b c d : A} {p : a == b} {q : c == d} {r : a == c} {s : b == d} {sq : Square p q r s} → B sq)
  & (J□i {B = B} d) {sq = ids} = & d

  J□1 : {B : (p : a == a) → Square p idp idp idp → Type j}
    → Coh (B idp ids) → Coh ({p : a == a} (sq : Square p idp idp idp) → B p sq)
  & (J□1 {B = B} d) c = aux B (& d) c  where

    e : {a b c d : A} (q : c == d) (r : a == c) (s : b == d) → Square (coh∙∙! r q s) q r s
    e idp idp idp = ids

    aux : {a b c d : A} {q : c == d} {r : a == c} {s : b == d} (B : (p : a == b) → Square p q r s → Type j)
       → B (coh∙∙! r q s) (e q r s) → {p : a == b} (sq : Square p q r s) → B p sq
    aux B d ids = d

  J□2 : {B : (p : a == a) → Square idp p idp idp → Type j}
    → Coh (B idp ids) → Coh ({p : a == a} (sq : Square idp p idp idp) → B p sq)
  & (J□2 {B = B} d) c = aux B (& d) c  where

    e : {a b c d : A} (p : a == b) (r : a == c) (s : b == d) → Square p (coh!∙∙ r p s) r s
    e idp idp idp = ids

    aux : {a b c d : A} {p : a == b} {r : a == c} {s : b == d} (B : (q : c == d) → Square p q r s → Type j)
       → B (coh!∙∙ r p s) (e p r s) → {q : c == d} (sq : Square p q r s) → B q sq
    aux B d ids = d

  J□3 : {B : (p : a == a) → Square idp idp p idp → Type j}
    → Coh (B idp ids) → Coh ({p : a == a} (sq : Square idp idp p idp) → B p sq)
  & (J□3 {B = B} d) c = aux B (& d) c  where

    e : {a b c d : A} (p : a == b) (q : c == d) (s : b == d) → Square p q (coh∙∙! p s q) s
    e idp idp idp = ids

    aux : {a b c d : A} {p : a == b} {q : c == d} {s : b == d} (B : (r : a == c) → Square p q r s → Type j)
       → B (coh∙∙! p s q) (e p q s) → {r : a == c} (sq : Square p q r s) → B r sq
    aux B d ids = d

  J□4 : {B : (p : a == a) → Square idp idp idp p → Type j}
    → Coh (B idp ids) → Coh ({p : a == a} (sq : Square idp idp idp p) → B p sq)
  & (J□4 {B = B} d) c = aux B (& d) c  where

    e : {a b c d : A} (p : a == b) (q : c == d) (r : a == c) → Square p q r (coh!∙∙ p r q)
    e idp idp idp = ids

    aux : {a b c d : A} {p : a == b} {q : c == d} {r : a == c} (B : (s : b == d) → Square p q r s → Type j)
       → B (coh!∙∙ p r q) (e p q r) → {s : b == d} (sq : Square p q r s) → B s sq
    aux B d ids = d

instance
  idp-Coh : ∀ {i} {A : Type i} {a : A} → Coh (a == a)
  & idp-Coh = idp

  ids-Coh : ∀ {i} {A : Type i} {a : A} → Coh (Square {a = a} idp idp idp idp)
  & ids-Coh = ids

  idc-Coh : ∀ {i} {A : Type i} {a : A} → Coh (Cube {a = a} ids ids ids ids ids ids)
  & idc-Coh = idc

  -- Allows us to put the initial [a] in the [Coh]
  strip-a : ∀ {i j} {A : Type i} {P : A → A → Type j} → ((a : A) → Coh ({b : A} → P a b)) → Coh ({a b : A} → P a b)
  & (strip-a z) = & (z _)

  -- Allows us to put the initial [Aa] in the [Coh]
  strip-aA : ∀ {i j} {P : (A : Type i) → A → Type j} → ((A : Type i) (a : A) → Coh (P A a)) → Coh ((A : Type i) (a : A) → P A a)
  & (strip-aA z) A a = & (z A a)

  -- Allows us to put the initial [Aa] in the [Coh]
  strip-aA' : ∀ {i j} {P : (A : Type i) → A → Type j} → ((A : Type i) (a : A) → Coh (P A a)) → Coh ((A : Type i) {a : A} → P A a)
  & (strip-aA' z) A = & (z A _)

  -- Allows us to put the initial [Aa] in the [Coh]
  strip-aA'' : ∀ {i j} {P : (A : Type i) → A → Type j} → ((A : Type i) (a : A) → Coh (P A a)) → Coh ({A : Type i} {a : A} → P A a)
  & (strip-aA'' z) = & (z _ _)

  -- Allows us to put the initial [Aa] in the [Coh]
  strip-XYf : ∀ {i j} {P : (X Y : Type i) (f : X → Y) → X → Type j} → ((X Y : Type i) (f : X → Y) (a : X) → Coh (P X Y f a)) → Coh ({X Y : Type i} {f : X → Y} (a : X) → P X Y f a)
  & (strip-XYf z) a = & (z _ _ _ _)

  -- Allows us to put the initial [Aa] in the [Coh]
  strip-XYf' : ∀ {i j} {P : (X Y : Type i) (f : X → Y) → X → Type j} → ((X Y : Type i) (f : X → Y) (a : X) → Coh (P X Y f a)) → Coh ({X Y : Type i} {f : X → Y} {a : X} → P X Y f a)
  & (strip-XYf' z) = & (z _ _ _ _)

  -- Allows us to put the initial [Aa] in the [Coh]
  strip-XYf'' : ∀ {i j} {P : (X Y : Type i) (f : X → Y) → X → Type j} → ((X Y : Type i) (f : X → Y) (a : X) → Coh (P X Y f a)) → Coh ({X Y : Type i} (f : X → Y) (a : X) → P X Y f a)
  & (strip-XYf'' z) f a = & (z _ _ _ _)

  -- Allows us to put the initial [Aa] in the [Coh]
  strip-XYf''' : ∀ {i j} {P : (X Y : Type i) (f : X → Y) → X → Type j} → ((X Y : Type i) (f : X → Y) (a : X) → Coh (P X Y f a)) → Coh ({X Y : Type i} (f : X → Y) {a : X} → P X Y f a)
  & (strip-XYf''' z) f = & (z _ _ _ _)

  -- Allows us to have implicit arguments
  implicit : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} → Coh ({a : A} (b : B a) → C a b) → Coh ({a : A} {b : B a} → C a b)
  & (implicit d) = & d _

  -- Allows us to have explicit arguments
  explicit : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} → Coh ({a : A} (b : B a) → C a b) → Coh ((a : A) (b : B a) → C a b)
  & (explicit d) a b = & d b

path-induction : ∀ {i} {A : Type i} {{a : A}} → A
path-induction {{a}} = a

module _ {i j} {A : Type i} {a : A} where
 instance
--   JCube1 : {B : (p : Square {a = a} idp idp idp idp) → Cube p ids ids ids ids ids → Type j}
--     → Coh (B ids idc) → Coh ({p : Square {a = a} idp idp idp idp} (cube : Cube p ids ids ids ids ids) → B p cube)
--   & (JCube1 {B = B} d) c = aux B (& d) c  where

--     comp : Coh ({a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
--            {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
--            {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
--            (right : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁)

--            {a₀₀₀ : A} {p₀₀₋ : a₀₀₀ == a₀₀₁}
--            {a₀₁₀ : A} {p₀₁₋ : a₀₁₀ == a₀₁₁}
--            {a₁₀₀ : A} {p₁₀₋ : a₁₀₀ == a₁₀₁}
--            {a₁₁₀ : A} {p₁₁₋ : a₁₁₀ == a₁₁₁}

--            {p₀₋₀ : a₀₀₀ == a₀₁₀}
--            (back : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁)
--            {p₋₀₀ : a₀₀₀ == a₁₀₀}
--            (top : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁)
--            {p₋₁₀ : a₀₁₀ == a₁₁₀}
--            (bottom : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁)
--            {p₁₋₀ : a₁₀₀ == a₁₁₀}
--            (front : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁)
--            → Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀)
--     comp = path-induction

--     fill : Coh ({a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
--            {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
--            {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
--            (right : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁)

--            {a₀₀₀ : A} {p₀₀₋ : a₀₀₀ == a₀₀₁}
--            {a₀₁₀ : A} {p₀₁₋ : a₀₁₀ == a₀₁₁}
--            {a₁₀₀ : A} {p₁₀₋ : a₁₀₀ == a₁₀₁}
--            {a₁₁₀ : A} {p₁₁₋ : a₁₁₀ == a₁₁₁}

--            {p₀₋₀ : a₀₀₀ == a₀₁₀}
--            (back : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁)
--            {p₋₀₀ : a₀₀₀ == a₁₀₀}
--            (top : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁)
--            {p₋₁₀ : a₀₁₀ == a₁₁₀}
--            (bottom : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁)
--            {p₁₋₀ : a₁₀₀ == a₁₁₀}
--            (front : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁)
--            → Cube (& comp right back top bottom front) right back top bottom front)
--     fill = path-induction
  
--     aux :  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
--            {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
--            {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
--            -- missing left

--            {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
--            {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
--            {right : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

--            {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
--            {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
--            {back : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
--            {top : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
--            {bottom : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
--            {front : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
--            → (B : (left : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀) → Cube left right back top bottom front → Type j)
--            → B (& comp right back top bottom front) (& fill right back top bottom front) -- uncurry B (fill-cube-left right back top bottom front)
--            → ({left : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} (cube : Cube left right back top bottom front) → B left cube)
--     aux B d idc = d

  postulate
    JCube1 : {B : (p : Square {a = a} idp idp idp idp) → Cube p ids ids ids ids ids → Type j}
      → Coh (B ids idc) → Coh ({p : Square {a = a} idp idp idp idp} (cube : Cube p ids ids ids ids ids) → B p cube)

  JCube2 : {B : (p : Square {a = a} idp idp idp idp) → Cube ids p ids ids ids ids → Type j}
    → Coh (B ids idc) → Coh ({p : Square {a = a} idp idp idp idp} (cube : Cube ids p ids ids ids ids) → B p cube)
  & (JCube2 {B = B} d) idc = & d

  postulate
    JCube3 : {B : (p : Square {a = a} idp idp idp idp) → Cube ids ids p ids ids ids → Type j}
      → Coh (B ids idc) → Coh ({p : Square {a = a} idp idp idp idp} (cube : Cube ids ids p ids ids ids) → B p cube)

    JCube4 : {B : (p : Square {a = a} idp idp idp idp) → Cube ids ids ids p ids ids → Type j}
      → Coh (B ids idc) → Coh ({p : Square {a = a} idp idp idp idp} (cube : Cube ids ids ids p ids ids) → B p cube)

    JCube5 : {B : (p : Square {a = a} idp idp idp idp) → Cube ids ids ids ids p ids → Type j}
      → Coh (B ids idc) → Coh ({p : Square {a = a} idp idp idp idp} (cube : Cube ids ids ids ids p ids) → B p cube)

  JCube6 : {B : (p : Square {a = a} idp idp idp idp) → Cube ids ids ids ids ids p → Type j}
    → Coh (B ids idc) → Coh ({p : Square {a = a} idp idp idp idp} (cube : Cube ids ids ids ids ids p) → B p cube)
  & (JCube6 d) idc = & d

{-# OPTIONS --without-K --rewriting #-}

module SmashCommon where

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
data _==_ {i : ULevel} {A : Type i} : A → A → Type i where
  idp : {a : A} → a == a


postulate
  #postulate# : ∀ {i} {A : Type i} → A

ap : ∀ {i} {A B : Type i} (f : A → B) {a b : A} (p : a == b) → f a == f b
ap f idp = idp

transport : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y) → B x → B y
transport B idp u = u

-- Dependent identity type

PathOver : ∀ {i} {A : Type i} (P : A → Type i) {a b : A} (p : a == b) (u : P a) (v : P b) → Type i
PathOver P idp u v = u == v

-- Dependent ap

apd : ∀ {i} {A : Type i} {B : A → Type i} (f : (x : A) → B x) {a b : A} (p : a == b) → PathOver B p (f a) (f b)
apd f idp = idp

-- PathOver constant family

↓-cst-in : ∀ {i} {A B : Type i} {a b : A} {p : a == b} {u v : B} → u == v → PathOver (λ _ → B) p u v
↓-cst-in {p = idp} q = q

-- Pointed types and functions

record Ptd (i : ULevel) : Type (lsucc i) where
  field
    ∣_∣ : Type i
    pt : ∣_∣

open Ptd public

record PtdMap {i} (A B : Ptd i) : Type i where
  field
    fun : ∣ A ∣ → ∣ B ∣
    ptf : fun (pt A) == pt B

open PtdMap public

infix 50 _$_

_$_ : ∀ {i} {A B : Ptd i} (f : PtdMap A B) → ∣ A ∣ → ∣ B ∣
f $ a = fun f a

id-pt : ∀ {i} (A : Ptd i) → PtdMap A A
id-pt A = record { fun = λ x → x ; ptf = idp }

-- Smash product

postulate
  _∧_ : ∀ {i} (A B : Ptd i) → Ptd i

module _ {i} {A B : Ptd i} where

  postulate
    proj : ∣ A ∣ → ∣ B ∣ → ∣ A ∧ B ∣
    basel : ∣ A ∧ B ∣
    gluel : (a : ∣ A ∣) → proj a (pt B) == basel
    baser : ∣ A ∧ B ∣
    gluer : (b : ∣ B ∣) → proj (pt A) b == baser

  module SmashElim {P : ∣ A ∧ B ∣ → Type i} (proj* : (a : ∣ A ∣) (b : ∣ B ∣) → P (proj a b))
           (basel* : P basel) (gluel* : (a : ∣ A ∣) → PathOver P (gluel a) (proj* a (pt B)) basel*)
           (baser* : P baser) (gluer* : (b : ∣ B ∣) → PathOver P (gluer b) (proj* (pt A) b) baser*)  where

    postulate
      f : (x : ∣ A ∧ B ∣) → P x
      proj-β : (a : ∣ A ∣) (b : ∣ B ∣) → f (proj a b) ↦ proj* a b
      basel-β : f basel ↦ basel*
      baser-β : f baser ↦ baser*
      {-# REWRITE proj-β #-}
      {-# REWRITE basel-β #-}
      {-# REWRITE baser-β #-}
      gluel-β : (a : ∣ A ∣) → apd f (gluel a) == gluel* a
      gluer-β : (b : ∣ B ∣) → apd f (gluer b) == gluer* b

      pt-β : pt (A ∧ B) ↦ proj (pt A) (pt B)
      {-# REWRITE pt-β #-}

  Smash-elim : {P : ∣ A ∧ B ∣ → Type i} (proj* : (a : ∣ A ∣) (b : ∣ B ∣) → P (proj a b))
               (basel* : P basel) (gluel* : (a : ∣ A ∣) → PathOver P (gluel a) (proj* a (pt B)) basel*)
               (baser* : P baser) (gluer* : (b : ∣ B ∣) → PathOver P (gluer b) (proj* (pt A) b) baser*)
             → (x : ∣ A ∧ B ∣) → P x
  Smash-elim proj* basel* gluel* baser* gluer* = SmashElim.f proj* basel* gluel* baser* gluer*

data Square {i} {A : Type i} : {a b c d : A} (p : a == b) (q : c == d) (r : a == c) (s : b == d) → Type i where
  ids : {a : A} → Square {a = a} idp idp idp idp

data Cube {i} {A : Type i} :
  {a b c d : A}
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
  idc : {a : A} → Cube {a = a} ids ids ids ids ids ids


data HyperCube {i} {A : Type i} :
  {a b c d : A} {p : a == b} {q : c == d} {r : a == c} {s : b == d} {sq : Square p q r s}
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
  idhc : {a : A} → HyperCube {a = a} idc idc idc idc idc idc idc idc

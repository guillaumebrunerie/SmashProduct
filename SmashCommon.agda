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
data _==_ {i : ULevel} {A : Type i} (a : A) : A → Type i where
  idp : a == a


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

record Pointed {i} (A : Type i) : Type i where
  field
    pt : A

open Pointed {{…}} public

record PointedFun {i} {A B : Type i} {{_ : Pointed A}} {{_ : Pointed B}} (f : A → B) : Type i where
  field
    ptf : f pt == pt

ptf : ∀ {i} {A B : Type i} {{_ : Pointed A}} {{_ : Pointed B}} (f : A → B) {{_ : PointedFun f}} → f pt == pt
ptf f {{k}} = PointedFun.ptf k

instance
  idf-ptf : ∀ {i} {A : Type i} {{_ : Pointed A}} → PointedFun (λ (x : A) → x)
  PointedFun.ptf idf-ptf = idp

-- Smash product

postulate
  _∧_ : ∀ {i} (A B : Type i) {{_ : Pointed A}} {{_ : Pointed B}} → Type i

module _ {i} {A B : Type i} {{_ : Pointed A}} {{_ : Pointed B}} where

  postulate
    proj : A → B → A ∧ B
    basel : A ∧ B
    gluel : (a : A) → proj a pt == basel
    baser : A ∧ B
    gluer : (b : B) → proj pt b == baser

  module SmashElim {P : A ∧ B → Type i} (proj* : (a : A) (b : B) → P (proj a b))
           (basel* : P basel) (gluel* : (a : A) → PathOver P (gluel a) (proj* a pt) basel*)
           (baser* : P baser) (gluer* : (b : B) → PathOver P (gluer b) (proj* pt b) baser*)  where

    postulate
      f : (x : A ∧ B) → P x
      proj-β : (a : A) (b : B) → f (proj a b) ↦ proj* a b
      basel-β : f basel ↦ basel*
      baser-β : f baser ↦ baser*
      {-# REWRITE proj-β #-}
      {-# REWRITE basel-β #-}
      {-# REWRITE baser-β #-}
      gluel-β : (a : A) → apd f (gluel a) == gluel* a
      gluer-β : (b : B) → apd f (gluer b) == gluer* b

  instance
    Smash-pt : Pointed (A ∧ B)
    Smash-pt = record { pt = proj pt pt }

  Smash-elim : {P : A ∧ B → Type i} (proj* : (a : A) (b : B) → P (proj a b))
               (basel* : P basel) (gluel* : (a : A) → PathOver P (gluel a) (proj* a pt) basel*)
               (baser* : P baser) (gluer* : (b : B) → PathOver P (gluer b) (proj* pt b) baser*)
             → (x : A ∧ B) → P x
  Smash-elim proj* basel* gluel* baser* gluer* = SmashElim.f proj* basel* gluel* baser* gluer*

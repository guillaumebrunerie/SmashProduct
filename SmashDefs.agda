{-# OPTIONS --without-K --rewriting #-}

module SmashDefs where

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

ap : {i : ULevel} {A B : Type i} (f : A → B) {a b : A} (p : a == b) → f a == f b
ap f idp = idp

-- Dependent identity type

PathOver : {i : ULevel} {A : Type i} (P : A → Type i) {a b : A} (p : a == b) (u : P a) (v : P b) → Type i
PathOver P idp u v = u == v

-- Pointed types and functions

record Pointed {i : ULevel} (A : Type i) : Type i where
  field
    pt : A

open Pointed {{…}} public

record PointedFun {i : ULevel} {A B : Type i} {{_ : Pointed A}} {{_ : Pointed B}} (f : A → B) : Type i where
  field
    ptf : f pt == pt

ptf : {i : ULevel} {A B : Type i} {{_ : Pointed A}} {{_ : Pointed B}} (f : A → B) {{_ : PointedFun f}} → f pt == pt
ptf f {{k}} = PointedFun.ptf k

instance
  idf-ptf : ∀ {i} {A : Type i} {{_ : Pointed A}} → PointedFun (λ (x : A) → x)
  PointedFun.ptf idf-ptf = idp

-- Smash product

postulate
  _∧_ : {i : ULevel} (A B : Type i) {{_ : Pointed A}} {{_ : Pointed B}} → Type i

module _ {i : ULevel} {A B : Type i} {{_ : Pointed A}} {{_ : Pointed B}} where

  postulate
    proj : A → B → A ∧ B
    basel : A ∧ B
    gluel : (a : A) → proj a pt == basel
    baser : A ∧ B
    gluer : (b : B) → proj pt b == baser

  module _ {P : A ∧ B → Type i} (proj* : (a : A) (b : B) → P (proj a b))
           (basel* : P basel) (gluel* : (a : A) → PathOver P (gluel a) (proj* a pt) basel*)
           (baser* : P baser) (gluer* : (b : B) → PathOver P (gluer b) (proj* pt b) baser*)  where

    postulate
      Smash-elim : (x : A ∧ B) → P x
      proj-β : (a : A) (b : B) → Smash-elim (proj a b) ↦ proj* a b
      basel-β : Smash-elim basel ↦ basel*
      baser-β : Smash-elim baser ↦ baser*
      {-# REWRITE proj-β #-}
      {-# REWRITE basel-β #-}
      {-# REWRITE baser-β #-}

  module _ {P : Type i} (proj* : A → B → P)
           (basel* : P) (gluel* : (a : A) → proj* a pt == basel*)
           (baser* : P) (gluer* : (b : B) → proj* pt b == baser*)  where

    postulate
      Smash-rec : A ∧ B → P  -- TODO
      proj-β' : {a : A} {b : B} → Smash-rec (proj a b) ↦ proj* a b
      basel-β' : Smash-rec basel ↦ basel*
      baser-β' : Smash-rec baser ↦ baser*
      {-# REWRITE proj-β' #-}
      {-# REWRITE basel-β' #-}
      {-# REWRITE baser-β' #-}

  instance
    Smash-pt : Pointed (A ∧ B)
    Smash-pt = record { pt = proj pt pt }

  module _ {P : Type i} {proj* : A → B → P}
           {basel* : P} {gluel* : (a : A) → proj* a pt == basel*}
           {baser* : P} {gluer* : (b : B) → proj* pt b == baser*}  where

    postulate
      gluel-β' : (a : A) → ap (Smash-rec proj* basel* gluel* baser* gluer*) (gluel a) == gluel* a
      gluer-β' : (b : B) → ap (Smash-rec proj* basel* gluel* baser* gluer*) (gluer b) == gluer* b

-- Operations

module _ {i} {A : Type i} where
  coh∙! : {a b c : A} → a == b → c == b → a == c
  coh∙! idp idp = idp

  coh∙ : {a b c : A} → a == b → b == c → a == c
  coh∙ idp p = p

  coh!∙ : {a b c : A} → b == a → b == c → a == c
  coh!∙ idp p = p

  coh∙∙! : {a b c d : A} → a == b → b == c → d == c → a == d
  coh∙∙! idp idp idp = idp

  coh!∙∙ : {a b c d : A} → b == a → b == c → c == d → a == d
  coh!∙∙ idp idp idp = idp

  coh-purple : {a b c : A} {p : b == c} (q : a == b) {r : a == c} → r == coh∙ q p → p == coh!∙ q r
  coh-purple idp idp = idp

  green-coh : {a b : A} (p : a == b) → idp == coh∙! p p
  green-coh idp = idp

module _ {i} {A B : Type i} (f : A → B) where

  apcoh∙! : {a b c : A} (p : a == b) (q : c == b) → ap f (coh∙! p q) == coh∙! (ap f p) (ap f q)
  apcoh∙! idp idp = idp

  apcoh!∙ : {a b c : A} (p : b == a) (q : b == c) → ap f (coh!∙ p q) == coh!∙ (ap f p) (ap f q)
  apcoh!∙ idp idp = idp

  apcoh∙ : {a b c : A} (p : a == b) (q : b == c) → ap f (coh∙ p q) == coh∙ (ap f p) (ap f q)
  apcoh∙ idp idp = idp

  apcoh∙∙! : {a b c d : A} (p : a == b) (q : b == c) (r : d == c) → ap f (coh∙∙! p q r) == coh∙∙! (ap f p) (ap f q) (ap f r)
  apcoh∙∙! idp idp idp = idp

  apcoh!∙∙ : {a b c d : A} (p : b == a) (q : b == c) (r : c == d) → ap f (coh!∙∙ p q r) == coh!∙∙ (ap f p) (ap f q) (ap f r)
  apcoh!∙∙ idp idp idp = idp

ap-idf : ∀ {i} {A : Type i} {a a' : A} {p : a == a'} → ap (λ (x : A) → x) p == p
ap-idf {p = idp} = idp

ap-∘ : ∀ {i} {A B C : Type i} (f : B → C) (g : A → B) {a a' : A} {p : a == a'} {gp : g a == g a'} (gp= : ap g p == gp) {fgp : f (g a) == f (g a')} (fgp= : ap f gp == fgp)
     → ap (λ x → f (g x)) p == fgp
ap-∘ f g {p = idp} idp idp = idp

∘-ap : ∀ {i} {A B C : Type i} (f : B → C) (g : A → B) {a a' : A} {p : a == a'} -- {gp : g a == g a'} (gp= : ap g p == gp) {fgp : f (g a) == f (g a')} (fgp= : ap f gp == fgp)
     → ap f (ap g p) == ap (λ x → f (g x)) p
∘-ap f g {p = idp} = idp

postulate
  ↓-=-in-eq : ∀ {i} {A B : Type i} {f g : A → B}
    {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    {gp : g x == g y} {fp : f x == f y}
    → ap g p == gp
    → ap f p == fp
    → coh∙ u gp == coh∙ fp v
    → PathOver (λ x → f x == g x) p u v

  ↓-=cst-in : ∀ {i} {A B : Type i} {f : A → B} {b : B}
    {x y : A} {p : x == y} {u : f x == b} {v : f y == b}
    → u == coh∙ (ap f p) v
    → PathOver (λ x → f x == b) p u v

complicated-coh : ∀ {i} {X : Type i} {a b : X} {p q q' : a == b} → q == q' → p == q' → p == coh∙ q idp
complicated-coh {p = idp} idp idp = idp

module _ {i} {A B : Type i} {{_ : Pointed A}} {{_ : Pointed B}} where
  purple : {b b' : B} (q : b == b') → gluer b == coh∙ (ap (proj pt) q) (gluer b') :> (_ == _ :> (A ∧ B))
  purple idp = idp

  green : {a a' : A} (p : a == a') → ap (λ x → proj x pt) p == coh∙! (gluel a) (gluel a') :> (_ == _ :> (A ∧ B))
  green idp = green-coh _

  pink-l : {a a' : A} {b b' : B} (p : a == a') (q : b == b') → ap (λ x → proj x b) p == coh∙∙! (ap (proj a) q) (ap (λ x → proj x b') p) (ap (proj a') q) :> (_ == _ :> (A ∧ B))
  pink-l idp idp = idp

  pink-r : {a a' : A} {b b' : B} (p : a == a') (q : b == b') → ap (λ x → proj x b') p == coh!∙∙ (ap (proj a) q) (ap (λ x → proj x b) p) (ap (proj a') q) :> (_ == _ :> (A ∧ B))
  pink-r idp idp = idp


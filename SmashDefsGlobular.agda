{-# OPTIONS --without-K --rewriting #-}

open import PathInduction
open import SmashCommon

module SmashDefsGlobular where


cohSq : ∀ {i} → Coh ({X : Type i} {c d : X} (q : c == d) {a : X} (r : a == c) {b : X} (s : b == d) → a == b)
cohSq = path-induction

lemmaCohSq : ∀ {i} → Coh ({X : Type i} {c d : X} {q : c == d} → & cohSq q idp idp == q)
lemmaCohSq = path-induction

lemmaCohSq' : ∀ {i} → Coh ({X : Type i} {c d : X} {q : c == d} → q == & cohSq q idp idp)
lemmaCohSq' = path-induction

↓-=-in : ∀ {i} {A B : Type i} {f g : A → B}
  {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
  → u == & cohSq v (ap f p) (ap g p)
  → PathOver (λ x → f x == g x) p u v
↓-=-in {p = idp} idp = & lemmaCohSq

ap+ : ∀ {i} {A B : Type i} {f g : A → B} (α : (x : A) → f x == g x)
      {x y : A} (p : x == y)
      → α x == & cohSq (α y) (ap f p) (ap g p)
ap+ α idp = & lemmaCohSq'

ap+-reduce : ∀ {i} {A B : Type i} {a b : A → B} {f : (x : A) → a x == b x}
  {y z : A} (p : y == z) (sq : f y == & cohSq (f z) (ap a p) (ap b p))
  → apd f p == ↓-=-in sq
  → ap+ f p == sq
ap+-reduce {i = i} idp sq q = {!q!}

cohCu : ∀ {i} → Coh ({X : Type i} {a b : X} {p : a == b} {c : X} {q q' : b == c} (α : q == q') {d : X} {r : d == c} {t : a == d} (β : t == & cohSq q p r) {t' : a == d} (β' : t' == & cohSq q' p r) → t == t')
cohCu = path-induction

↓-=2-in : ∀ {i} {A B : Type i} {f g : A → B} {α β : (x : A) → f x == g x}
  {x y : A} {p : x == y} {u : α x == β x} {v : α y == β y}
  → u == & cohCu v (ap+ α p) (ap+ β p)
  → PathOver (λ x → α x == β x) p u v
↓-=2-in {p = idp} idp = {!!}

ap++ : ∀ {i} {A B : Type i} {f g : A → B} {α β : (x : A) → f x == g x} (γ : (x : A) → α x == β x)
      {x y : A} (p : x == y)
      → γ x == & cohCu (γ y) (ap+ α p) (ap+ β p)
ap++ γ idp = {!!}

ap++-reduce : ∀ {i} {A B : Type i} {a b : A → B} {f g : (x : A) → a x == b x} {α : (x : A) → f x == g x}
  {y z : A} (p : y == z) (sq : α y == & cohCu (α z) (ap+ f p) (ap+ g p))
  → apd α p == ↓-=2-in sq
  → ap++ α p == sq
ap++-reduce {i = i} idp sq q = {!idp!}

ap= : ∀ {i} {A B : Type i} {f g : A → B} (eq : (x : A) → f x == g x) {y z : A} (p : y == z)
    → ap f p == & cohSq (ap g p) (eq y) (eq z)
ap= eq idp = {!!}


module _ {i} {A B : Type i} {{_ : Pointed A}} {{_ : Pointed B}} where

  module SmashElimId {D : Type i} {g h : A ∧ B → D} (proj* : (a : A) (b : B) → g (proj a b) == h (proj a b))
             (basel* : g basel == h basel) (gluel* : (a : A) → proj* a pt == & cohSq basel* (ap g (gluel a)) (ap h (gluel a)))
             (baser* : g baser == h baser) (gluer* : (b : B) → proj* pt b == & cohSq baser* (ap g (gluer b)) (ap h (gluer b))) where

    module M = SmashElim {P = λ x → g x == h x} proj* basel* (λ a → ↓-=-in (gluel* a)) baser* (λ b → ↓-=-in (gluer* b))

    f : (x : A ∧ B) → g x == h x
    f = M.f

    abstract
      gluel-β : (a : A) → ap+ f (gluel a) == gluel* a
      gluel-β a = ap+-reduce (gluel a) (gluel* a) (M.gluel-β a)

      gluer-β : (b : B) → ap+ f (gluer b) == gluer* b
      gluer-β b = ap+-reduce (gluer b) (gluer* b) (M.gluer-β b)



  module SmashElimId2 {D : Type i} {g h : A ∧ B → D} {α β : (x : A ∧ B) → g x == h x} (proj* : (a : A) (b : B) → α (proj a b) == β (proj a b))
             (basel* : α basel == β basel) (gluel* : (a : A) → proj* a pt == & cohCu basel* (ap+ α (gluel a)) (ap+ β (gluel a)))
             (baser* : α baser == β baser) (gluer* : (b : B) → proj* pt b == & cohCu baser* (ap+ α (gluer b)) (ap+ β (gluer b))) where

    module M = SmashElim {P = λ x → α x == β x} proj* basel* (λ a → ↓-=2-in (gluel* a)) baser* (λ b → ↓-=2-in (gluer* b))

    f : (x : A ∧ B) → α x == β x
    f = M.f

    abstract
      gluel-β : (a : A) → ap++ f (gluel a) == gluel* a
      gluel-β a = ap++-reduce (gluel a) (gluel* a) (M.gluel-β a)

      gluer-β : (b : B) → ap++ f (gluer b) == gluer* b
      gluer-β b = ap++-reduce (gluer b) (gluer* b) (M.gluer-β b)

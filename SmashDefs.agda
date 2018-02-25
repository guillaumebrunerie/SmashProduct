{-# OPTIONS --without-K --rewriting #-}

open import PathInduction

module SmashDefs where

coh∙ : ∀ {i} → Coh ({X : Type i} {a b : X} → a == b → {c : X} → b == c → a == c)
coh∙ = path-induction

coh∙□ : ∀ {i} → Coh ({X : Type i} {a b : X} {p q : a == b} (α : Square p q idp idp) {r : a == b} (β : Square q r idp idp) → Square p r idp idp)
coh∙□ = path-induction

coh!∙□ : ∀ {i} → Coh ({X : Type i} {a b : X} {q p : a == b} (α : Square q p idp idp) {r : a == b} (β : Square q r idp idp) → Square p r idp idp)
coh!∙□ = path-induction

postulate
  #ADMITTED# : ∀ {i} {A : Type i} → A

ap : ∀ {i} {A B : Type i} (f : A → B) {a b : A} (p : a == b) → f a == f b
ap f idp = idp

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

{- Non-dependent version -}

module _ {i} {A B : Type i} {{_ : Pointed A}} {{_ : Pointed B}} where
  module SmashRec {P : Type i} (proj* : A → B → P)
           (basel* : P) (gluel* : (a : A) → proj* a pt == basel*)
           (baser* : P) (gluer* : (b : B) → proj* pt b == baser*)  where

    module M = SmashElim {P = λ _ → P} proj* basel* (λ a → ↓-cst-in (gluel* a)) baser* (λ b → ↓-cst-in (gluer* b))

    f : A ∧ B → P
    f = M.f

    gluel-β : (a : A) → Square (ap f (gluel a)) (gluel* a) idp idp
    gluel-β a = #ADMITTED#

    gluer-β : (b : B) → Square (ap f (gluer b)) (gluer* b) idp idp
    gluer-β b = #ADMITTED#


hids : ∀ {i} → Coh ({X : Type i} {a b : X} (p : a == b) → Square p p idp idp)
hids = path-induction

vids : ∀ {i} → Coh ({X : Type i} {a b : X} (p : a == b) → Square idp idp p p)
vids = path-induction

hidc : ∀ {i} → Coh ({X : Type i} {a b c d : X} {p : a == b} {q : c == d} {r : a == c} {s : b == d} {sq : Square p q r s} → Cube sq sq (& hids p) (& hids q) (& hids r) (& hids s))
hidc = path-induction

vidc : ∀ {i} → Coh ({X : Type i} {a b : X} (p : a == b) → Cube ids ids (& vids p) (& vids p) (& vids p) (& vids p))
vidc = path-induction

ap-idf : ∀ {i} {A : Type i} {a a' : A} (p : a == a') → Square (ap (λ (x : A) → x) p) p idp idp
ap-idf idp = ids

-- ap-∘-eq : ∀ {i} {A B C : Type i} (f : B → C) (g : A → B) {a a' : A} {p : a == a'} {gp : g a == g a'} (gp= : ap g p == gp)
--      → ap (λ x → f (g x)) p == ap f gp
-- ap-∘-eq f g {p = idp} idp = idp

ap-∘ : ∀ {i} {A B C : Type i} (f : B → C) (g : A → B) {a a' : A} (p : a == a')
     → Square (ap (λ x → f (g x)) p) (ap f (ap g p)) idp idp
ap-∘ f g idp = ids

inv : ∀ {i} → Coh ({A : Type i} {a b : A} (p : a == b) → b == a)
inv = path-induction
 
ap-∘-idfl : ∀ {i} {A B : Type i} (g : A → B) {a a' : A} (p : a == a')
     → Cube (ap-∘ (λ x → x) g p) (& hids (ap g p)) (& hids (ap g p)) (ap-idf (ap g p)) ids ids
ap-∘-idfl g idp = idc

ap-cst : ∀ {i} {A B : Type i} (b : B) {a a' : A} (p : a == a') → Square (ap (λ _ → b) p) idp idp idp
ap-cst b idp = ids

-- ap-∘-cst : ∀ {i} {A B C : Type i} (f : B → C) (b : B) {a a' : A} (p : a == a')
--      → Square (ap-∘ f (λ _ → b) p) (ap-cst (f b) p) (ap (ap f) (ap-cst b p)) idp
-- ap-∘-cst f b idp = ids

-- ↓-=-in-eq : ∀ {i} {A B : Type i} {f g : A → B}
--   {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
--   {gp : g x == g y} {fp : f x == f y}
--   → ap g p == gp
--   → ap f p == fp
--   → & coh∙ u gp == & coh∙ fp v
--   → PathOver (λ x → f x == g x) p u v
-- ↓-=-in-eq {p = idp} idp idp α = coh α  where

--   coh : ∀ {i} {X : Type i} {a b : X} {u v : a == b} → coh∙ u idp == v → u == v
--   coh {u = idp} idp = idp

antidegen : ∀ {i} → Coh ({X : Type i} {a b : X} {u v : a == b} → Square u v idp idp → u == v)
antidegen = path-induction

antidegen-cube : ∀ {i} → Coh ({X : Type i} {a b c d : X} {p : a == b} {q : c == d} {r : a == c} {s : b == d} {sq1 sq2 : Square p q r s} → Cube sq1 sq2 (& hids _) (& hids _) (& hids _) (& hids _) → sq1 == sq2)
antidegen-cube = path-induction

↓-=-in□ : ∀ {i} {A B : Type i} {f g : A → B}
  {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
  → Square u v (ap f p) (ap g p)
  → PathOver (λ x → f x == g x) p u v
↓-=-in□ {p = idp} α = & antidegen α

degen : ∀ {i} → Coh ({A : Type i} {a b : A} {p q : a == b} → p == q → Square p q idp idp)
degen = path-induction

degen! : ∀ {i} → Coh ({A : Type i} {a b : A} {p q : a == b} → p == q → Square q p idp idp)
degen! = path-induction

ap□ : ∀ {i} {A B : Type i} {f g : A → B} (α : (x : A) → f x == g x)
      {x y : A} (p : x == y)
      → Square (α x) (α y) (ap f p) (ap g p)
ap□ α idp = & hids (α _)

ap□-idp : ∀ {i} {A B : Type i} (f : A → B)
      {x y : A} (p : x == y)
      → Cube (ap□ (λ x → idp {a = f x}) p) (& vids (ap f p)) ids ids (& hids (ap f p)) (& hids (ap f p))
ap□-idp f idp = idc

ap++ : ∀ {i} {A B : Type i} {a b c d : A → B} {p : (x : A) → a x == b x} {q : (x : A) → c x == d x} {r : (x : A) → a x == c x} {s : (x : A) → b x == d x} (α : (x : A) → Square (p x) (q x) (r x) (s x))
      {x y : A} (k : x == y)
      → Cube (α x) (α y) (ap□ p k) (ap□ q k) (ap□ r k) (ap□ s k)
ap++ α idp = & hidc

ap-square : ∀ {i} {A B : Type i} (f : A → B)
  {a b c d : A} {p : a == b} {q : c == d} {r : a == c} {s : b == d}
  → Square p q r s
  → Square (ap f p) (ap f q) (ap f r) (ap f s)
ap-square f ids = ids

aphids : ∀ {i} → Coh ({X Y : Type i} (f : X → Y) {a b : X} (p : a == b) → Cube (ap-square f (& hids p)) (& hids (ap f p)) (& hids _) (& hids _) ids ids)
aphids = path-induction

ap-∘3 : ∀ {i} {A B C D : Type i} (f : C → D) (g : B → C) (h : A → B) {a a' : A} (p : a == a')
      → Cube (ap-∘ (λ x → f (g x)) h p) (ap-square f (ap-∘ g h p)) (ap-∘ f (λ y → g (h y)) p) (ap-∘ f g (ap h p)) ids ids
ap-∘3 f g h idp = idc

ap-∘3-cst : ∀ {i} {A B C D : Type i} (f : C → D) (c : C) (h : A → B) {a a' : A} (p : a == a')
      → Cube (ap-square f (ap-∘ (λ _ → c) h p)) (ap-square f (ap-cst c p)) (& hids (ap f (ap (λ (_ : A) → c) p))) (ap-square f (ap-cst c (ap h p))) (ids {a = f c}) (ids {a = f c})
ap-∘3-cst f c h idp = idc

ap□+ : ∀ {i} {A B : Type i} {f g : A → B} (α : (x : A) → f x == g x)
      {a b c d : A} {p : a == b} {q : c == d} {r : a == c} {s : b == d}
      (sq : Square p q r s)
      → Cube (ap□ α p) (ap□ α q) (ap□ α r) (ap□ α s) (ap-square f sq) (ap-square g sq)
ap□+ α ids = & hidc

ap□-reduce : ∀ {i} {A B : Type i} {a b : A → B} {f : (x : A) → a x == b x}
  {y z : A} (p : y == z) (sq : Square (f y) (f z) (ap a p) (ap b p))
  → apd f p == ↓-=-in□ sq
  → Cube (ap□ f p) sq (& hids _) (& hids _) (& hids _) (& hids _)
ap□-reduce {i = i} idp sq q = & coh2 (& coh q)  where

  coh : Coh ({X : Type i} {x y : X} {p q : x == y} {sq : Square p q idp idp} {r : p == q} (s : r == & antidegen sq) → & degen r == sq)
  coh = path-induction

  coh2 : Coh ({X : Type i} {x y : X} {p : x == y} {sq : Square p p idp idp} (e : & degen idp == sq) → Cube (& hids _) sq (& hids _) (& hids _) (& hids _) (& hids _))
  coh2 = path-induction

ap-square-∘ : ∀ {i} {A B C : Type i} (g : B → C) (f : A → B)
  {a b c d : A} {p : a == b} {q : c == d} {r : a == c} {s : b == d}
  (α : Square p q r s)
  → Cube (ap-square (λ x → g (f x)) α) (ap-square g (ap-square f α)) (ap-∘ g f p) (ap-∘ g f q) (ap-∘ g f r) (ap-∘ g f s)
ap-square-∘ g f ids = idc

ap-square-idf : ∀ {i} {A : Type i}
  {a b c d : A} {p : a == b} {q : c == d} {r : a == c} {s : b == d}
  (α : Square p q r s)
  → Cube (ap-square (λ x → x) α) α (ap-idf p) (ap-idf q) (ap-idf r) (ap-idf s)
ap-square-idf ids = idc

ap-cube : ∀ {i} {A B : Type i} (f : A → B)
  {a b c d : A}
  {p : a == b} {q : c == d}
  {r : a == c} {s : b == d}
  {sq : Square p q r s}

  {a' b' c' d' : A}
  {p' : a' == b'} {q' : c' == d'}
  {r' : a' == c'} {s' : b' == d'}
  {sq' : Square p' q' r' s'}

  {a= : a == a'} {b= : b == b'}
  {c= : c == c'} {d= : d == d'}
  {p= : Square p p' a= b=}
  {q= : Square q q' c= d=}
  {r= : Square r r' a= c=}
  {s= : Square s s' b= d=}
  → Cube sq sq' p= q= r= s=
  → Cube (ap-square f sq) (ap-square f sq') (ap-square f p=) (ap-square f q=) (ap-square f r=) (ap-square f s=)
ap-cube f idc = idc

ap-cube-∘ : ∀ {i} {A B C : Type i} (g : B → C) (f : A → B)
  {a b c d : A} {p : a == b} {q : c == d} {r : a == c} {s : b == d} {sq : Square p q r s}
  {a' b' c' d' : A} {p' : a' == b'} {q' : c' == d'} {r' : a' == c'} {s' : b' == d'} {sq' : Square p' q' r' s'}
  {a= : a == a'} {b= : b == b'} {c= : c == c'} {d= : d == d'}
  {p= : Square p p' a= b=} {q= : Square q q' c= d=} {r= : Square r r' a= c=} {s= : Square s s' b= d=}
  (α : Cube sq sq' p= q= r= s=)
  → HyperCube (ap-cube (λ x → g (f x)) α) (ap-cube g (ap-cube f α)) (ap-square-∘ g f sq) (ap-square-∘ g f sq') (ap-square-∘ g f p=) (ap-square-∘ g f q=) (ap-square-∘ g f r=) (ap-square-∘ g f s=)
ap-cube-∘ g f idc = idhc

hinv : ∀ {i} → Coh ({X : Type i} {a b : X} {p q : a == b} (sq : Square p q idp idp) → Square q p idp idp)
hinv = path-induction

aphinv : ∀ {i} → Coh ({X Y : Type i} (f : X → Y) {a b : X} {p q : a == b} (sq : Square p q idp idp) → Cube (ap-square f (& hinv sq)) (& hinv (ap-square f sq)) (& hids (ap f q)) (& hids (ap f p)) ids ids)
aphinv = path-induction

postulate
  ap□-∘-eq : ∀ {i} {A B C : Type i} {a b : A → B} (g : (x : A) → a x == b x) (f : B → C)
           {y z : A} (p : y == z) {res : (x : A) → f (a x) == f (b x)} (eq : (x : A) → Square (ap f (g x)) (res x) idp idp)
           → Cube (ap□ res p)
                  (ap-square f (ap□ g p))
                  (& hinv (eq y))
                  (& hinv (eq z))
                  (ap-∘ f a p)
                  (ap-∘ f b p)

  ap□-∘3 : ∀ {i} {X A B C : Type i} (f : B → C) {a b : A → B} (g : (x : A) → a x == b x) (h : X → A)
           {y z : X} (p : y == z)
           → Cube (ap□ (λ x → ap f (g (h x))) p)
                  (ap□ (λ x → ap f (g x)) (ap h p))
                  (& hids (ap f (g (h y))))
                  (& hids (ap f (g (h z))))
                  (ap-∘ (λ x → f (a x)) h p)
                  (ap-∘ (λ x → f (b x)) h p)

  ap□-∘-idf : ∀ {i} {A B : Type i} {a b : A → B} (g : (x : A) → a x == b x)
         {y z : A} (p : y == z)
         → Cube (ap□ (λ y → ap (λ x → x) (g y)) p)
                (ap□ g p)
                (ap-idf (g y))
                (ap-idf (g z))
                (& hids _)
                (& hids _)

  ap□-∘2 : ∀ {i} {A B C : Type i} {a b : B → C} (f : (x : B) → a x == b x) (g : A → B)
           {y z : A} (p : y == z)
           → Cube (ap□ (λ x → f (g x)) p) (ap□ f (ap g p)) (& hids (f (g y))) (& hids (f (g z))) (ap-∘ a g p) (ap-∘ b g p)

  ap□-= : ∀ {i} {A B : Type i} {a b : A → B} {f g : (x : A) → a x == b x} (α : (x : A) → Square (f x) (g x) idp idp)
            {x y : A} (p : x == y)
          → Cube (ap□ f p) (ap□ g p) (α x) (α y) (& hids (ap a p)) (& hids (ap b p))


  -- ∘-ap□-eq : ∀ {i} {A B C : Type i} {a b : A → B} (g : (x : A) → a x == b x) (f : B → C)
  --            {y z : A} (p : y == z) {res : (x : A) → f (a x) == f (b x)} (eq : (x : A) → ap f (g x) == res x)
  --        → Cube (ap-square f (ap□ g p))
  --               (ap□ res p)
  --               (& degen (eq y))
  --               (& degen (∘-ap f a p))
  --               (& degen (∘-ap f b p))
  --               (& degen (eq z))


ap□-cst : ∀ {i} {A B : Type i} {b b' : B} (q : b == b')
      {x y : A} (p : x == y)
      → Cube (ap□ (λ _ → q) p) (& hids q) (& hids q) (& hids q) (ap-cst b p) (ap-cst b' p)
ap□-cst idp idp = idc

ap-∘-cst : ∀ {i} {A B C : Type i} (f : B → C) (b : B) {a a' : A} (p : a == a')
  → Cube (ap-cst (f b) p) (ap-square f (ap-cst b p)) (ap-∘ f (λ _ → b) p) ids ids ids
ap-∘-cst f b idp = idc

ap-∘-cst2 : ∀ {i} {A B C : Type i} (c : C) (f : A → B) {a a' : A} (p : a == a')
  → Cube (ap-∘ (λ _ → c) f p) ids (ap-cst c p) (ap-cst c (ap f p)) ids ids
ap-∘-cst2 c f idp = idc

apdegen : ∀ {i} → Coh ({A B : Type i} (f : A → B) {a : A} {b : A} {p q : a == b} (r : p == q) → Cube (ap-square f (& degen r)) (& degen (ap (ap f) r)) (& degen idp) (& degen idp) (& degen idp) (& degen idp))
apdegen = path-induction

apdegen! : ∀ {i} → Coh ({A B : Type i} (f : A → B) {a : A} {b : A} {p q : a == b} (r : p == q) → Cube (ap-square f (& degen! r)) (& degen! (ap (ap f) r)) (& degen idp) (& degen idp) (& degen idp) (& degen idp))
apdegen! = path-induction


↓-Square-in : ∀ {i} {A B : Type i} {a b c d : A → B}
  {p : (x : A) → a x == b x} {q : (x : A) → c x == d x}
  {r : (x : A) → a x == c x} {s : (x : A) → b x == d x}
  {y z : A} {α : y == z}
  {u : Square (p y) (q y) (r y) (s y)}
  {v : Square (p z) (q z) (r z) (s z)}
  → Cube u v (ap□ p α) (ap□ q α) (ap□ r α) (ap□ s α)
  → PathOver (λ x → Square (p x) (q x) (r x) (s x)) α u v
↓-Square-in {α = idp} c = & antidegen-cube c

↓-Cube-in : ∀ {i} {A B : Type i}
  {a b c d : A → B}
  {p : (x : A) → a x == b x} {q : (x : A) → c x == d x}
  {r : (x : A) → a x == c x} {s : (x : A) → b x == d x}
  {sq : (x : A) → Square (p x) (q x) (r x) (s x)}
  {a' b' c' d' : A → B}
  {p' : (x : A) → a' x == b' x} {q' : (x : A) → c' x == d' x}
  {r' : (x : A) → a' x == c' x} {s' : (x : A) → b' x == d' x}
  {sq' : (x : A) → Square (p' x) (q' x) (r' x) (s' x)}
  {a= : (x : A) → a x == a' x}
  {b= : (x : A) → b x == b' x}
  {c= : (x : A) → c x == c' x}
  {d= : (x : A) → d x == d' x}
  {p= : (x : A) → Square (p x) (p' x) (a= x) (b= x)}
  {q= : (x : A) → Square (q x) (q' x) (c= x) (d= x)}
  {r= : (x : A) → Square (r x) (r' x) (a= x) (c= x)}
  {s= : (x : A) → Square (s x) (s' x) (b= x) (d= x)}
  {y z : A} {α : y == z}
  {u : Cube (sq y) (sq' y) (p= y) (q= y) (r= y) (s= y)}
  {v : Cube (sq z) (sq' z) (p= z) (q= z) (r= z) (s= z)}
  → HyperCube u v (ap++ sq α) (ap++ sq' α) (ap++ p= α) (ap++ q= α) (ap++ r= α) (ap++ s= α)
  → PathOver (λ x → Cube (sq x) (sq' x) (p= x) (q= x) (r= x) (s= x)) α u v
↓-Cube-in {α = idp} c = {!!}


module _ {i} {A B : Type i} {{_ : Pointed A}} {{_ : Pointed B}} where
  module SmashElimId {D : Type i} {g h : A ∧ B → D} (proj* : (a : A) (b : B) → g (proj a b) == h (proj a b))
             (basel* : g basel == h basel) (gluel* : (a : A) → Square (proj* a pt) basel* (ap g (gluel a)) (ap h (gluel a)))
             (baser* : g baser == h baser) (gluer* : (b : B) → Square (proj* pt b) baser* (ap g (gluer b)) (ap h (gluer b))) where

    module M = SmashElim {P = λ x → g x == h x} proj* basel* (λ a → ↓-=-in□ (gluel* a)) baser* (λ b → ↓-=-in□ (gluer* b))

    f : (x : A ∧ B) → g x == h x
    f = M.f

    abstract
      gluel-β : (a : A) → Cube (ap□ f (gluel a)) (gluel* a) (& hids _) (& hids _) (& hids _) (& hids _)
      gluel-β a = ap□-reduce (gluel a) (gluel* a) (M.gluel-β a)

      gluer-β : (b : B) → Cube (ap□ f (gluer b)) (gluer* b) (& hids _) (& hids _) (& hids _) (& hids _)
      gluer-β b = ap□-reduce (gluer b) (gluer* b) (M.gluer-β b)

  -- module SmashElimSquare {D : Type i} {a b c d : A ∧ B → D} {p : (x : A ∧ B) → a x == b x} {q : (x : A ∧ B) → a x == c x} {r : (x : A ∧ B) → b x == d x} {s : (x : A ∧ B) → c x == d x}
  --            (proj* : (a : A) (b : B) → g (proj a b) == h (proj a b))
  --            (basel* : g basel == h basel) (gluel* : (a : A) → Square (proj* a pt) (ap g (gluel a)) (ap h (gluel a)) basel*)
  --            (baser* : g baser == h baser) (gluer* : (b : B) → Square (proj* pt b) (ap g (gluer b)) (ap h (gluer b)) baser*) where

  --   module M = SmashElim proj* basel* (λ a → ↓-=-in□ (gluel* a)) baser* (λ b → ↓-=-in□ (gluer* b))

  --   f : (x : A ∧ B) → g x == h x
  --   f = M.f

  --   gluel-β : (a : A) → ap□ f (gluel a) == gluel* a
  --   gluel-β a = coh∙ (ap ↓-=-out□ (M.gluel-β a)) ↓-=-β□

  --   gluer-β : (b : B) → ap□ f (gluer b) == gluer* b
  --   gluer-β b = coh∙ (ap ↓-=-out□ (M.gluer-β b)) ↓-=-β□



-- ↓-=-out□ : ∀ {i} {A B : Type i} {f g : A → B}
--   {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
--   → PathOver (λ x → f x == g x) p u v
--   → Square u (ap f p) (ap g p) v
-- ↓-=-out□ {p = idp} α = & degen α

-- postulate
--   ↓-=-β□ : ∀ {i} {A B : Type i} {f g : A → B}
--     {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
--     {sq : Square u (ap f p) (ap g p) v}
--     → ↓-=-out□ (↓-=-in□ sq) == sq

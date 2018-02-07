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

-- Dependent ap

apd : {i : ULevel} {A : Type i} {B : A → Type i} (f : (x : A) → B x) {a b : A} (p : a == b) → PathOver B p (f a) (f b)
apd f idp = idp

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

∘-ap : ∀ {i} {A B C : Type i} (f : B → C) (g : A → B) {a a' : A} {p : a == a'}
     → ap f (ap g p) == ap (λ x → f (g x)) p
∘-ap f g {p = idp} = idp

∘-ap-eq : ∀ {i} {A B C : Type i} (f : B → C) (g : A → B) {a a' : A} {p : a == a'} {fgp : f (g a) == f (g a')} (fgp= : ap (λ x → f (g x)) p == fgp)
     → ap f (ap g p) == fgp
∘-ap-eq f g {p = idp} idp = idp

ap-cst : ∀ {i} {A B : Type i} {b : B} {a a' : A} {p : a == a'} → ap (λ _ → b) p == idp
ap-cst {p = idp} = idp

data Square {i} {A : Type i} {a : A} : {b c d : A} (p : a == b) (q : a == c) (r : b == d) (s : c == d) → Type i where
  ids : Square idp idp idp idp

data SquareLine {i} {A : Type i} {a : A} : {b c d : A} {p p' : a == b} (p= : p == p') {q : a == c} {r : b == d} {s s' : c == d} (s= : s == s') → Square p q r s → Square p' q r s' → Type i where
  idps : SquareLine idp idp ids ids

data Cube {i} {A : Type i} {a₀₀₀ : A} :
  {a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  (sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀) -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  (sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  (sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁) -- back
  (sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁) -- top
  (sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁) -- bottom
  (sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁) -- front
  → Type i

  where
  idc : Cube ids ids ids ids ids ids

↓-=-in-eq : ∀ {i} {A B : Type i} {f g : A → B}
  {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
  {gp : g x == g y} {fp : f x == f y}
  → ap g p == gp
  → ap f p == fp
  → coh∙ u gp == coh∙ fp v
  → PathOver (λ x → f x == g x) p u v
↓-=-in-eq {p = idp} idp idp α = coh α  where

  coh : ∀ {i} {X : Type i} {a b : X} {u v : a == b} → coh∙ u idp == v → u == v
  coh {u = idp} idp = idp

postulate
  ↓-=-in□ : ∀ {i} {A B : Type i} {f g : A → B}
    {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    {gp : g x == g y} {fp : f x == f y}
    → ap g p == gp
    → ap f p == fp
    → Square u fp gp v
    → PathOver (λ x → f x == g x) p u v

  ↓-=-out□ : ∀ {i} {A B : Type i} {f g : A → B}
    {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → PathOver (λ x → f x == g x) p u v
    → Square u (ap f p) (ap g p) v

degen : ∀ {i} {A : Type i} {a b : A} {p q : a == b} → p == q → Square p idp idp q
degen {p = idp} idp = ids

ap□ : ∀ {i} {A B : Type i} {f g : A → B} (α : (x : A) → f x == g x)
      {x y : A} (p : x == y) -- {fp : f x == f y} (fp= : ap f p == fp) {gp : g x == g y} (gp= : ap g p == gp)
      → Square (α x) (ap f p) (ap g p) (α y)
ap□ α p = ↓-=-out□ (apd α p)

ap-square : ∀ {i} {A B : Type i} (f : A → B)
  {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  → Square p₀₋ p₋₀ p₋₁ p₁₋
  → Square (ap f p₀₋) (ap f p₋₀) (ap f p₋₁) (ap f p₁₋)
ap-square f ids = ids

postulate
  ap□-ap : ∀ {i} {A B C : Type i} {a b : A → B} (g : (x : A) → a x == b x) (f : B → C)
         {y z : A} (p : y == z)
         → Cube (ap□ (λ z → ap f (g z)) p) (ap-square f (ap□ g p)) (degen idp) (degen (ap-∘ f a idp idp)) (degen (ap-∘ f b idp idp)) (degen idp)

postulate
  ↓-=-in-eq-dep : ∀ {i} {A B : Type i} {f g : A → B} {α β : (x : A) → f x == g x}
    {x y : A} {p : x == y} {u : α x == β x} {v : α y == β y}
    {gp : g x == g y} {fp : f x == f y}
    {gp= : ap g p == gp} {fp= : ap f p == fp}
    {βp : Square (β x) fp gp (β y)}
    {αp : Square (α x) fp gp (α y)}
    → apd β p == ↓-=-in□ gp= fp= βp
    → apd α p == ↓-=-in□ gp= fp= αp
    → SquareLine u v αp βp
    → PathOver (λ x → α x == β x) p u v

  ↓-Square-in : ∀ {i} {A B : Type i} {a b c d : A → B}
    {p : (x : A) → a x == b x} {q : (x : A) → a x == c x}
    {r : (x : A) → b x == d x} {s : (x : A) → c x == d x}
    {y z : A} {α : y == z}
    {aα : a y == a z} (aα= : ap a α == aα) {bα : b y == b z} (bα= : ap b α == bα)
    {cα : c y == c z} (cα= : ap c α == cα) {dα : d y == d z} (dα= : ap d α == dα)
    {u : Square (p y) (q y) (r y) (s y)}
    {v : Square (p z) (q z) (r z) (s z)}
    {pα : Square (p y) aα bα (p z)} (pα= : Cube (ap□ p α) pα (degen idp) (degen aα=) (degen bα=) (degen idp))
    {qα : Square (q y) aα cα (q z)} (qα= : Cube (ap□ q α) qα (degen idp) (degen aα=) (degen cα=) (degen idp))
    {rα : Square (r y) bα dα (r z)} (rα= : Cube (ap□ r α) rα (degen idp) (degen bα=) (degen dα=) (degen idp))
    {sα : Square (s y) cα dα (s z)} (sα= : Cube (ap□ s α) sα (degen idp) (degen cα=) (degen dα=) (degen idp))
    → Cube u v pα qα rα sα
    → PathOver (λ x → Square (p x) (q x) (r x) (s x)) α u v

  ↓-Square-in-simpl : ∀ {i} {A B : Type i} {a b c d : A → B}
    {p : (x : A) → a x == b x} {q : (x : A) → a x == c x}
    {r : (x : A) → b x == d x} {s : (x : A) → c x == d x}
    {y z : A} {α : y == z}
    {u : Square (p y) (q y) (r y) (s y)}
    {v : Square (p z) (q z) (r z) (s z)}
    → Cube u v (ap□ p α) (ap□ q α) (ap□ r α) (ap□ s α)
    → PathOver (λ x → Square (p x) (q x) (r x) (s x)) α u v

-- apdcoh∙ : ∀ {i} {A B : Type i} {a b c : A → B} {p : (x : A) → a x == b x} {q : (x : A) → b x == c x}
--   {x y : A} (r : x == y)
--   {ar : a x == a y} (ar= : ap a r == ar)
--   {cr : c x == c y} (cr= : ap c r == cr)
--   → apd (λ v → coh∙ (p v) (q v)) r == ↓-=-in-eq cr= ar= {!apd p r!}
-- apdcoh∙ = {!!}

-- J□1 : ∀ {i} {A : Type i} {a : A} {B : (p : a == a) → Square idp idp idp p → Type i}
--   → B idp ids → {p : a == a} (sq : Square idp idp idp p) → B p sq
-- J□1 α ids = {!!}

module _ {i} {A B : Type i} {{_ : Pointed A}} {{_ : Pointed B}} where
  purple : {b b' : B} (q : b == b') → gluer b == coh∙ (ap (proj pt) q) (gluer b') :> (_ == _ :> (A ∧ B))
  purple idp = idp

  green : {a a' : A} (p : a == a') → ap (λ x → proj x pt) p == coh∙! (gluel a) (gluel a') :> (_ == _ :> (A ∧ B))
  green idp = green-coh _

  pink-l : {a a' : A} {b b' : B} (p : a == a') (q : b == b') → ap (λ x → proj x b) p == coh∙∙! (ap (proj a) q) (ap (λ x → proj x b') p) (ap (proj a') q) :> (_ == _ :> (A ∧ B))
  pink-l idp idp = idp

  pink-r : {a a' : A} {b b' : B} (p : a == a') (q : b == b') → ap (λ x → proj x b') p == coh!∙∙ (ap (proj a) q) (ap (λ x → proj x b) p) (ap (proj a') q) :> (_ == _ :> (A ∧ B))
  pink-r idp idp = idp


  purple□ : {b b' : B} (q : b == b') → Square (gluer b) (ap (proj pt) q) (ap (λ _ → baser) q) (gluer b')
  purple□ q = ap□ (gluer {A = A}) q

  green□ : {a a' : A} (p : a == a') → Square (gluel a) (ap (λ x → proj x pt) p) (ap (λ _ → basel) p) (gluel a')
  green□ p = ap□ (gluel {B = B}) p

  pink□ : {a a' : A} {b b' : B} (p : a == a') (q : b == b') → Square (ap (λ x → proj x b) p) (ap (proj a) q) (ap (proj a') q) (ap (λ x → proj x b') p)
  pink□ p q = ap□ (λ y → ap (λ x → proj x y) p) q

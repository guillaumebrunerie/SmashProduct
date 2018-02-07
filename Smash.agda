{-# OPTIONS --without-K --rewriting #-}

open import SmashDefs

module Smash {i : ULevel} where

-- idsmash-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) → x2 == a
-- idsmash-coh1 X a _ idp _ idp = idp

-- idsmash-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x2 : X) (p2 : x2 == x0) → x2 == a
-- idsmash-coh2 X a _ idp _ idp = idp

-- apidsmash-coh1 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x1 : X} {p1 : a == x1} {fp1 : f a == f x1} (fp1= : ap f p1 == fp1) {x2 : X} {p2 : x2 == x1} {fp2 : f x2 == f x1} (fp2= : ap f p2 == fp2) → ap f (idsmash-coh1 X a x1 p1 x2 p2) == idsmash-coh1 Y (f a) (f x1) fp1 (f x2) fp2
-- apidsmash-coh1 {p1 = idp} idp {p2 = idp} idp = idp

-- apidsmash-coh2 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x0 : X} {p0 : a == x0} {fp0 : f a == f x0} (fp0= : ap f p0 == fp0) {x2 : X} {p2 : x2 == x0} {fp2 : f x2 == f x0} (fp2= : ap f p2 == fp2) → ap f (idsmash-coh2 X a x0 p0 x2 p2) == idsmash-coh2 Y (f a) (f x0) fp0 (f x2) fp2
-- apidsmash-coh2 {p0 = idp} idp {p2 = idp} idp = idp

-- idsmash : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → A ∧ B
-- idsmash A B =
--   Smash-rec (λ a b → proj a b)
--             pt
--             (λ a → idsmash-coh1 (A ∧ B) (proj pt pt) basel (gluel pt) (proj a pt) (gluel a))
--             pt
--             (λ b → idsmash-coh2 (A ∧ B) (proj pt pt) baser (gluer pt) (proj pt b) (gluer b))


σ-coh1 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x2 : X) (p2 : x2 == x0) → x2 == a
σ-coh1 X a _ idp _ idp = idp

σ-coh2 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) → x2 == a
σ-coh2 X a _ idp _ idp = idp

apσ-coh1 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x0 : X} {p0 : a == x0} {fp0 : f a == f x0} (fp0= : ap f p0 == fp0) {x2 : X} {p2 : x2 == x0} {fp2 : f x2 == f x0} (fp2= : ap f p2 == fp2) → ap f (σ-coh1 X a x0 p0 x2 p2) == σ-coh1 Y (f a) (f x0) fp0 (f x2) fp2
apσ-coh1 {p0 = idp} idp {p2 = idp} idp = idp

apσ-coh2 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x1 : X} {p1 : a == x1} {fp1 : f a == f x1} (fp1= : ap f p1 == fp1) {x2 : X} {p2 : x2 == x1} {fp2 : f x2 == f x1} (fp2= : ap f p2 == fp2) → ap f (σ-coh2 X a x1 p1 x2 p2) == σ-coh2 Y (f a) (f x1) fp1 (f x2) fp2
apσ-coh2 {p1 = idp} idp {p2 = idp} idp = idp

σ : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → B ∧ A
σ A B =
  Smash-rec (λ a b → proj b a)
            pt
            (λ a → σ-coh1 (B ∧ A) (proj pt pt) baser (gluer pt) (proj pt a) (gluer a))
            pt
            (λ b → σ-coh2 (B ∧ A) (proj pt pt) basel (gluel pt) (proj b pt) (gluel b))


-- ∧-map-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x5 : X) (p5 : x5 == x1) (x6 : X) (p6 : x6 == x5) → x6 == a
-- ∧-map-coh1 X a _ idp _ idp _ idp = idp

-- ∧-map-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x8 : X) (p8 : x8 == x0) (x9 : X) (p9 : x9 == x8) → x9 == a
-- ∧-map-coh2 X a _ idp _ idp _ idp = idp

-- ap∧-map-coh1 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x1 : X} {p1 : a == x1} {fp1 : f a == f x1} (fp1= : ap f p1 == fp1) {x5 : X} {p5 : x5 == x1} {fp5 : f x5 == f x1} (fp5= : ap f p5 == fp5) {x6 : X} {p6 : x6 == x5} {fp6 : f x6 == f x5} (fp6= : ap f p6 == fp6) → ap f (∧-map-coh1 X a x1 p1 x5 p5 x6 p6) == ∧-map-coh1 Y (f a) (f x1) fp1 (f x5) fp5 (f x6) fp6
-- ap∧-map-coh1 {p1 = idp} idp {p5 = idp} idp {p6 = idp} idp = idp

-- ap∧-map-coh2 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x0 : X} {p0 : a == x0} {fp0 : f a == f x0} (fp0= : ap f p0 == fp0) {x8 : X} {p8 : x8 == x0} {fp8 : f x8 == f x0} (fp8= : ap f p8 == fp8) {x9 : X} {p9 : x9 == x8} {fp9 : f x9 == f x8} (fp9= : ap f p9 == fp9) → ap f (∧-map-coh2 X a x0 p0 x8 p8 x9 p9) == ∧-map-coh2 Y (f a) (f x0) fp0 (f x8) fp8 (f x9) fp9
-- ap∧-map-coh2 {p0 = idp} idp {p8 = idp} idp {p9 = idp} idp = idp

-- ∧-map : (A : Type i) {{_ : Pointed A}} (A' : Type i) {{_ : Pointed A'}} (B : Type i) {{_ : Pointed B}} (B' : Type i) {{_ : Pointed B'}} (f : A → A') {{_ : PointedFun f}} (g : B → B') {{_ : PointedFun g}} (x : A ∧ B) → A' ∧ B'
-- ∧-map A A' B B' f g =
--   Smash-rec (λ a b → proj (f a) (g b))
--             pt
--             (λ a → ∧-map-coh1 (A' ∧ B') (proj pt pt) basel (gluel pt) (proj (f a) pt) (gluel (f a)) (proj (f a) (g pt)) (ap (λ z → proj (f a) z) (ptf g)))
--             pt
--             (λ b → ∧-map-coh2 (A' ∧ B') (proj pt pt) baser (gluer pt) (proj pt (g b)) (gluer (g b)) (proj (f pt) (g b)) (ap (λ z → proj z (g b)) (ptf f)))


-- α-aux-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x5 : X) (p5 : x5 == x1) (x6 : X) (p6 : x5 == x6) (x8 : X) (p8 : x8 == x6) → x8 == a
-- α-aux-coh1 X a _ idp _ idp _ idp _ idp = idp

-- α-aux-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x6 : X) (p6 : x6 == x0) → x6 == a
-- α-aux-coh2 X a _ idp _ idp = idp

-- apα-aux-coh1 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x1 : X} {p1 : a == x1} {fp1 : f a == f x1} (fp1= : ap f p1 == fp1) {x5 : X} {p5 : x5 == x1} {fp5 : f x5 == f x1} (fp5= : ap f p5 == fp5) {x6 : X} {p6 : x5 == x6} {fp6 : f x5 == f x6} (fp6= : ap f p6 == fp6) {x8 : X} {p8 : x8 == x6} {fp8 : f x8 == f x6} (fp8= : ap f p8 == fp8) → ap f (α-aux-coh1 X a x1 p1 x5 p5 x6 p6 x8 p8) == α-aux-coh1 Y (f a) (f x1) fp1 (f x5) fp5 (f x6) fp6 (f x8) fp8
-- apα-aux-coh1 {p1 = idp} idp {p5 = idp} idp {p6 = idp} idp {p8 = idp} idp = idp

-- apα-aux-coh2 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x0 : X} {p0 : a == x0} {fp0 : f a == f x0} (fp0= : ap f p0 == fp0) {x6 : X} {p6 : x6 == x0} {fp6 : f x6 == f x0} (fp6= : ap f p6 == fp6) → ap f (α-aux-coh2 X a x0 p0 x6 p6) == α-aux-coh2 Y (f a) (f x0) fp0 (f x6) fp6
-- apα-aux-coh2 {p0 = idp} idp {p6 = idp} idp = idp

-- α-aux : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (c : C) (x : A ∧ B) → A ∧ (B ∧ C)
-- α-aux A B C c =
--   Smash-rec (λ a b → proj a (proj b c))
--             pt
--             (λ a → α-aux-coh1 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) basel (gluel pt) (proj a (proj pt pt)) (gluel a) (proj a baser) (ap (λ z → proj a z) (gluer pt)) (proj a (proj pt c)) (ap (λ z → proj a z) (gluer c)))
--             pt
--             (λ b → α-aux-coh2 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) baser (gluer (proj pt pt)) (proj pt (proj b c)) (gluer (proj b c)))

-- α-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x5 : X) (p5 : x5 == x1) (x7 : X) (p7 : x5 == x7) (x8 : X) (p8 : x8 == x7) → x8 == a
-- α-coh1 X a _ idp _ idp _ idp _ idp = idp

-- α-auxcoh-coh1 : (X : Type i) (a : X) → a == a
-- α-auxcoh-coh1 X a = idp

-- α-auxcoh-coh2 : (X : Type i) (a : X) → a == a
-- α-auxcoh-coh2 X a = idp

-- α-auxcoh-coh3 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x4 : X) (p4 : x4 == x1) (x5 : X) (p5 : x4 == x5) (x6 : X) (p6 : x4 == x6) → coh∙ (α-coh1 X a x1 p1 x4 p4 x6 p6 x4 p6) idp == coh∙ (α-aux-coh1 X a x1 p1 x4 p4 x5 p5 x4 p5) (α-auxcoh-coh1 X a)
-- α-auxcoh-coh3 X a _ idp _ idp _ idp _ idp = idp

-- α-auxcoh-coh4 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x1 : X) (p1 : a == x1) (x3 : X) (p3 : a == x3) (x4 : X) (p4 : x4 == x3) (x6 : x3 == x0) (p6 : x6 == coh!∙ p3 p0) (x7 : x4 == x0) (p7 : x7 == coh∙ p4 x6) → coh∙ (α-coh1 X a x1 p1 a p1 x3 p3 x4 p4) idp == coh∙ (α-aux-coh2 X a x0 p0 x4 x7) (α-auxcoh-coh2 X a)
-- α-auxcoh-coh4 X a _ idp _ idp _ idp _ idp _ idp _ idp = idp

-- α-auxcoh : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : A ∧ B) → α-aux A B C pt x == proj pt (proj pt pt)
-- α-auxcoh A B C =
--   Smash-elim (λ a b → α-coh1 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) basel (gluel pt) (proj a (proj pt pt)) (gluel a) (proj a basel) (ap (λ z → proj a z) (gluel pt)) (proj a (proj b pt)) (ap (λ z → proj a z) (gluel b)))
--              (α-auxcoh-coh1 (A ∧ (B ∧ C)) (proj pt (proj pt pt)))
--              (λ a → ↓-=-in-eq (ap-cst) (gluel-β' a) (α-auxcoh-coh3 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) basel (gluel pt) (proj a (proj pt pt)) (gluel a) (proj a baser) (ap (λ z → proj a z) (gluer pt)) (proj a basel) (ap (λ z → proj a z) (gluel pt))))
--              (α-auxcoh-coh2 (A ∧ (B ∧ C)) (proj pt (proj pt pt)))
--              (λ b → ↓-=-in-eq (ap-cst) (gluer-β' b) (α-auxcoh-coh4 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) baser (gluer (proj pt pt)) basel (gluel pt) (proj pt basel) (ap (λ z → proj pt z) (gluel pt)) (proj pt (proj b pt)) (ap (λ z → proj pt z) (gluel b)) (gluer basel) (coh-purple (ap (λ x → proj pt x) (gluel pt)) (purple (gluel pt))) (gluer (proj b pt)) (purple (gluel b))))

-- α-coh2 : (X : Type i) (a : X) (x2 : X) (p2 : a == x2) (x4 : X) (p4 : x4 == x2) → x4 == a
-- α-coh2 X a _ idp _ idp = idp

-- α : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : (A ∧ B) ∧ C) → A ∧ (B ∧ C)
-- α A B C =
--   Smash-rec (λ x c → α-aux A B C c x)
--             pt
--             (α-auxcoh A B C)
--             pt
--             (λ c → α-coh2 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) (proj pt baser) (ap (λ z → proj pt z) (gluer pt)) (proj pt (proj pt c)) (ap (λ z → proj pt z) (gluer c)))


-- α⁻¹-aux-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x4 : X) (p4 : x4 == x1) → x4 == a
-- α⁻¹-aux-coh1 X a _ idp _ idp = idp

-- α⁻¹-aux-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x8 : X) (p8 : x8 == x0) (x10 : X) (p10 : x8 == x10) (x11 : X) (p11 : x11 == x10) → x11 == a
-- α⁻¹-aux-coh2 X a _ idp _ idp _ idp _ idp = idp

-- apα⁻¹-aux-coh1 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x1 : X} {p1 : a == x1} {fp1 : f a == f x1} (fp1= : ap f p1 == fp1) {x4 : X} {p4 : x4 == x1} {fp4 : f x4 == f x1} (fp4= : ap f p4 == fp4) → ap f (α⁻¹-aux-coh1 X a x1 p1 x4 p4) == α⁻¹-aux-coh1 Y (f a) (f x1) fp1 (f x4) fp4
-- apα⁻¹-aux-coh1 {p1 = idp} idp {p4 = idp} idp = idp

-- apα⁻¹-aux-coh2 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x0 : X} {p0 : a == x0} {fp0 : f a == f x0} (fp0= : ap f p0 == fp0) {x8 : X} {p8 : x8 == x0} {fp8 : f x8 == f x0} (fp8= : ap f p8 == fp8) {x10 : X} {p10 : x8 == x10} {fp10 : f x8 == f x10} (fp10= : ap f p10 == fp10) {x11 : X} {p11 : x11 == x10} {fp11 : f x11 == f x10} (fp11= : ap f p11 == fp11) → ap f (α⁻¹-aux-coh2 X a x0 p0 x8 p8 x10 p10 x11 p11) == α⁻¹-aux-coh2 Y (f a) (f x0) fp0 (f x8) fp8 (f x10) fp10 (f x11) fp11
-- apα⁻¹-aux-coh2 {p0 = idp} idp {p8 = idp} idp {p10 = idp} idp {p11 = idp} idp = idp

-- α⁻¹-aux : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (a : A) (x : B ∧ C) → (A ∧ B) ∧ C
-- α⁻¹-aux A B C a =
--   Smash-rec (λ b c → proj (proj a b) c)
--             pt
--             (λ b → α⁻¹-aux-coh1 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj (proj a b) pt) (gluel (proj a b)))
--             pt
--             (λ c → α⁻¹-aux-coh2 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) baser (gluer pt) (proj (proj pt pt) c) (gluer c) (proj basel c) (ap (λ z → proj z c) (gluel pt)) (proj (proj a pt) c) (ap (λ z → proj z c) (gluel a)))

-- α⁻¹-coh1 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x8 : X) (p8 : x8 == x0) (x9 : X) (p9 : x8 == x9) (x11 : X) (p11 : x11 == x9) → x11 == a
-- α⁻¹-coh1 X a _ idp _ idp _ idp _ idp = idp

-- α⁻¹-auxcoh-coh1 : (X : Type i) (a : X) → a == a
-- α⁻¹-auxcoh-coh1 X a = idp

-- α⁻¹-auxcoh-coh2 : (X : Type i) (a : X) → a == a
-- α⁻¹-auxcoh-coh2 X a = idp

-- α⁻¹-auxcoh-coh3 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) (x4 : X) (p4 : x4 == x1) (x5 : a == x2) (p5 : x5 == coh∙! p1 p2) (x7 : x4 == x2) (p7 : x7 == coh∙! p4 p2) → coh∙ (α⁻¹-coh1 X a x0 p0 a p0 x2 x5 x4 x7) idp == coh∙ (α⁻¹-aux-coh1 X a x1 p1 x4 p4) (α⁻¹-auxcoh-coh1 X a)
-- α⁻¹-auxcoh-coh3 X a _ idp _ idp _ idp _ idp _ idp _ idp = idp

-- α⁻¹-auxcoh-coh4 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x6 : X) (p6 : x6 == x0) (x7 : X) (p7 : x6 == x7) (x8 : X) (p8 : x6 == x8) → coh∙ (α⁻¹-coh1 X a x0 p0 x6 p6 x7 p7 x6 p7) idp == coh∙ (α⁻¹-aux-coh2 X a x0 p0 x6 p6 x8 p8 x6 p8) (α⁻¹-auxcoh-coh2 X a)
-- α⁻¹-auxcoh-coh4 X a _ idp _ idp _ idp _ idp = idp

-- α⁻¹-auxcoh : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : B ∧ C) → α⁻¹-aux A B C pt x == proj (proj pt pt) pt
-- α⁻¹-auxcoh A B C =
--   Smash-elim (λ b c → α⁻¹-coh1 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) baser (gluer pt) (proj (proj pt pt) c) (gluer c) (proj baser c) (ap (λ z → proj z c) (gluer pt)) (proj (proj pt b) c) (ap (λ z → proj z c) (gluer b)))
--              (α⁻¹-auxcoh-coh1 ((A ∧ B) ∧ C) (proj (proj pt pt) pt))
--              (λ b → ↓-=-in-eq (ap-cst) (gluel-β' b) (α⁻¹-auxcoh-coh3 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) baser (gluer pt) basel (gluel (proj pt pt)) (proj baser pt) (gluel baser) (proj (proj pt b) pt) (gluel (proj pt b)) (ap (λ z → proj z pt) (gluer pt)) (green (gluer pt)) (ap (λ z → proj z pt) (gluer b)) (green (gluer b))))
--              (α⁻¹-auxcoh-coh2 ((A ∧ B) ∧ C) (proj (proj pt pt) pt))
--              (λ c → ↓-=-in-eq (ap-cst) (gluer-β' c) (α⁻¹-auxcoh-coh4 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) baser (gluer pt) (proj (proj pt pt) c) (gluer c) (proj baser c) (ap (λ z → proj z c) (gluer pt)) (proj basel c) (ap (λ z → proj z c) (gluel pt))))

-- α⁻¹-coh2 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x4 : X) (p4 : x4 == x1) → x4 == a
-- α⁻¹-coh2 X a _ idp _ idp = idp

-- α⁻¹ : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : A ∧ (B ∧ C)) → (A ∧ B) ∧ C
-- α⁻¹ A B C =
--   Smash-rec (α⁻¹-aux A B C)
--             pt
--             (λ a → α⁻¹-coh2 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj (proj a pt) pt) (gluel (proj a pt)))
--             pt
--             (α⁻¹-auxcoh A B C)


-- β-aux-coh1 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x8 : X) (p8 : x8 == x0) (x10 : X) (p10 : x8 == x10) (x11 : X) (p11 : x11 == x10) → x11 == a
-- β-aux-coh1 X a _ idp _ idp _ idp _ idp = idp

-- β-aux-coh2 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x4 : X) (p4 : x4 == x1) → x4 == a
-- β-aux-coh2 X a _ idp _ idp = idp

-- apβ-aux-coh1 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x0 : X} {p0 : a == x0} {fp0 : f a == f x0} (fp0= : ap f p0 == fp0) {x8 : X} {p8 : x8 == x0} {fp8 : f x8 == f x0} (fp8= : ap f p8 == fp8) {x10 : X} {p10 : x8 == x10} {fp10 : f x8 == f x10} (fp10= : ap f p10 == fp10) {x11 : X} {p11 : x11 == x10} {fp11 : f x11 == f x10} (fp11= : ap f p11 == fp11) → ap f (β-aux-coh1 X a x0 p0 x8 p8 x10 p10 x11 p11) == β-aux-coh1 Y (f a) (f x0) fp0 (f x8) fp8 (f x10) fp10 (f x11) fp11
-- apβ-aux-coh1 {p0 = idp} idp {p8 = idp} idp {p10 = idp} idp {p11 = idp} idp = idp

-- apβ-aux-coh2 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x1 : X} {p1 : a == x1} {fp1 : f a == f x1} (fp1= : ap f p1 == fp1) {x4 : X} {p4 : x4 == x1} {fp4 : f x4 == f x1} (fp4= : ap f p4 == fp4) → ap f (β-aux-coh2 X a x1 p1 x4 p4) == β-aux-coh2 Y (f a) (f x1) fp1 (f x4) fp4
-- apβ-aux-coh2 {p1 = idp} idp {p4 = idp} idp = idp

-- β-aux : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (c : C) (x : A ∧ B) → (C ∧ B) ∧ A
-- β-aux A B C c =
--   Smash-rec (λ a b → proj (proj c b) a)
--             pt
--             (λ a → β-aux-coh1 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) baser (gluer pt) (proj (proj pt pt) a) (gluer a) (proj basel a) (ap (λ z → proj z a) (gluel pt)) (proj (proj c pt) a) (ap (λ z → proj z a) (gluel c)))
--             pt
--             (λ b → β-aux-coh2 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj (proj c b) pt) (gluel (proj c b)))

-- β-coh1 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x8 : X) (p8 : x8 == x0) (x9 : X) (p9 : x8 == x9) (x11 : X) (p11 : x11 == x9) → x11 == a
-- β-coh1 X a _ idp _ idp _ idp _ idp = idp

-- β-auxcoh-coh1 : (X : Type i) (a : X) → a == a
-- β-auxcoh-coh1 X a = idp

-- β-auxcoh-coh2 : (X : Type i) (a : X) → a == a
-- β-auxcoh-coh2 X a = idp

-- β-auxcoh-coh3 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x6 : X) (p6 : x6 == x0) (x7 : X) (p7 : x6 == x7) (x8 : X) (p8 : x6 == x8) → coh∙ (β-coh1 X a x0 p0 x6 p6 x7 p7 x6 p7) idp == coh∙ (β-aux-coh1 X a x0 p0 x6 p6 x8 p8 x6 p8) (β-auxcoh-coh1 X a)
-- β-auxcoh-coh3 X a _ idp _ idp _ idp _ idp = idp

-- β-auxcoh-coh4 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) (x4 : X) (p4 : x4 == x1) (x5 : a == x2) (p5 : x5 == coh∙! p1 p2) (x7 : x4 == x2) (p7 : x7 == coh∙! p4 p2) → coh∙ (β-coh1 X a x0 p0 a p0 x2 x5 x4 x7) idp == coh∙ (β-aux-coh2 X a x1 p1 x4 p4) (β-auxcoh-coh2 X a)
-- β-auxcoh-coh4 X a _ idp _ idp _ idp _ idp _ idp _ idp = idp

-- β-auxcoh : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : A ∧ B) → β-aux A B C pt x == proj (proj pt pt) pt
-- β-auxcoh A B C =
--   Smash-elim (λ a b → β-coh1 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) baser (gluer pt) (proj (proj pt pt) a) (gluer a) (proj baser a) (ap (λ z → proj z a) (gluer pt)) (proj (proj pt b) a) (ap (λ z → proj z a) (gluer b)))
--              (β-auxcoh-coh1 ((C ∧ B) ∧ A) (proj (proj pt pt) pt))
--              (λ a → ↓-=-in-eq (ap-cst) (gluel-β' a) (β-auxcoh-coh3 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) baser (gluer pt) (proj (proj pt pt) a) (gluer a) (proj baser a) (ap (λ z → proj z a) (gluer pt)) (proj basel a) (ap (λ z → proj z a) (gluel pt))))
--              (β-auxcoh-coh2 ((C ∧ B) ∧ A) (proj (proj pt pt) pt))
--              (λ b → ↓-=-in-eq (ap-cst) (gluer-β' b) (β-auxcoh-coh4 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) baser (gluer pt) basel (gluel (proj pt pt)) (proj baser pt) (gluel baser) (proj (proj pt b) pt) (gluel (proj pt b)) (ap (λ z → proj z pt) (gluer pt)) (green (gluer pt)) (ap (λ z → proj z pt) (gluer b)) (green (gluer b))))

-- β-coh2 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x4 : X) (p4 : x4 == x1) → x4 == a
-- β-coh2 X a _ idp _ idp = idp

-- β : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : (A ∧ B) ∧ C) → (C ∧ B) ∧ A
-- β A B C =
--   Smash-rec (λ x c → β-aux A B C c x)
--             pt
--             (β-auxcoh A B C)
--             pt
--             (λ c → β-coh2 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj (proj c pt) pt) (gluel (proj c pt)))


-- ∧-map-id-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) → a == x1
-- ∧-map-id-coh1 X a _ idp = idp

-- ∧-map-id-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) → a == x0
-- ∧-map-id-coh2 X a _ idp = idp

-- ∧-map-id-coh3 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) → coh∙ idp p2 == coh∙ (∧-map-coh1 X a x1 p1 x2 p2 x2 idp) (∧-map-id-coh1 X a x1 p1)
-- ∧-map-id-coh3 X a _ idp _ idp = idp

-- ∧-map-id-coh4 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x3 : X) (p3 : x3 == x0) → coh∙ idp p3 == coh∙ (∧-map-coh2 X a x0 p0 x3 p3 x3 idp) (∧-map-id-coh2 X a x0 p0)
-- ∧-map-id-coh4 X a _ idp _ idp = idp

-- ∧-map-id : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → ∧-map A A B B (λ y → y) (λ z → z) x == x
-- ∧-map-id A B =
--   Smash-elim (λ a b → idp)
--              (∧-map-id-coh1 (A ∧ B) (proj pt pt) basel (gluel pt))
--              (λ a → ↓-=-in-eq (ap-idf) (gluel-β' a) (∧-map-id-coh3 (A ∧ B) (proj pt pt) basel (gluel pt) (proj a pt) (gluel a)))
--              (∧-map-id-coh2 (A ∧ B) (proj pt pt) baser (gluer pt))
--              (λ b → ↓-=-in-eq (ap-idf) (gluer-β' b) (∧-map-id-coh4 (A ∧ B) (proj pt pt) baser (gluer pt) (proj pt b) (gluer b)))


-- σ-triangle-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) → a == x1
-- σ-triangle-coh1 X a _ idp = idp

-- σ-triangle-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) → a == x0
-- σ-triangle-coh2 X a _ idp = idp

-- σ-triangle-coh3 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) → Square idp (σ-coh1 X a a (σ-coh2 X a x1 p1 a p1) x2 (σ-coh2 X a x1 p1 x2 p2)) p2 (σ-triangle-coh1 X a x1 p1)
-- σ-triangle-coh3 X a _ idp _ idp = ids

-- σ-triangle-coh4 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x2 : X) (p2 : x2 == x0) → coh∙ idp p2 == coh∙ (σ-coh2 X a a (σ-coh1 X a x0 p0 a p0) x2 (σ-coh1 X a x0 p0 x2 p2)) (σ-triangle-coh2 X a x0 p0)
-- σ-triangle-coh4 X a _ idp _ idp = idp

-- σ-triangle : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → σ B A (σ A B x) == x
-- σ-triangle A B =
--   Smash-elim (λ a b → idp)
--              (σ-triangle-coh1 (A ∧ B) (proj pt pt) basel (gluel pt))
--              (λ a → ↓-=-in□ (ap-idf) (ap-∘ (λ x → σ B A x) (σ A B) (gluel-β' a) (apσ-coh1 (gluer-β' pt) (gluer-β' a))) (σ-triangle-coh3 (A ∧ B) (proj pt pt) basel (gluel pt) (proj a pt) (gluel a)))
--              (σ-triangle-coh2 (A ∧ B) (proj pt pt) baser (gluer pt))
--              (λ b → {!↓-=-in-eq (ap-idf) (ap-∘ (λ x → σ B A x) (σ A B) (gluer-β' b) (apσ-coh2 (gluel-β' pt) (gluel-β' b))) (σ-triangle-coh4 (A ∧ B) (proj pt pt) baser (gluer pt) (proj pt b) (gluer b))!})


σ-2triangle-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) → a == x1
σ-2triangle-coh1 X a _ idp = idp

σ-2triangle-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) → a == x0
σ-2triangle-coh2 X a _ idp = idp

σ-2triangle-coh3 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) → Square idp (σ-coh1 X a a (σ-coh2 X a a (σ-coh1 X a a (σ-coh2 X a x1 p1 a p1) a (σ-coh2 X a x1 p1 a p1)) a (σ-coh1 X a a (σ-coh2 X a x1 p1 a p1) a (σ-coh2 X a x1 p1 a p1))) x2 (σ-coh2 X a a (σ-coh1 X a a (σ-coh2 X a x1 p1 a p1) a (σ-coh2 X a x1 p1 a p1)) x2 (σ-coh1 X a a (σ-coh2 X a x1 p1 a p1) x2 (σ-coh2 X a x1 p1 x2 p2)))) p2 (σ-2triangle-coh1 X a x1 p1)
σ-2triangle-coh3 X a _ idp _ idp = ids

σ-2triangle-coh4 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x2 : X) (p2 : x2 == x0) → Square idp (σ-coh2 X a a (σ-coh1 X a a (σ-coh2 X a a (σ-coh1 X a x0 p0 a p0) a (σ-coh1 X a x0 p0 a p0)) a (σ-coh2 X a a (σ-coh1 X a x0 p0 a p0) a (σ-coh1 X a x0 p0 a p0))) x2 (σ-coh1 X a a (σ-coh2 X a a (σ-coh1 X a x0 p0 a p0) a (σ-coh1 X a x0 p0 a p0)) x2 (σ-coh2 X a a (σ-coh1 X a x0 p0 a p0) x2 (σ-coh1 X a x0 p0 x2 p2)))) p2 (σ-2triangle-coh2 X a x0 p0)
σ-2triangle-coh4 X a _ idp _ idp = ids

σ-2triangle : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → σ B A (σ A B (σ B A (σ A B x))) == x
σ-2triangle A B =
  Smash-elim (λ a b → idp)
             (σ-2triangle-coh1 (A ∧ B) (proj pt pt) basel (gluel pt))
             (λ a → ↓-=-in□ (ap-idf) (ap-∘ (λ x → σ B A (σ A B (σ B A x))) (σ A B) (gluel-β' a) (apσ-coh1 (ap-∘ (λ x → σ B A (σ A B x)) (σ B A) (gluer-β' pt) (apσ-coh2 (ap-∘ (λ x → σ B A x) (σ A B) (gluel-β' pt) (apσ-coh1 (gluer-β' pt) (gluer-β' pt))) (ap-∘ (λ x → σ B A x) (σ A B) (gluel-β' pt) (apσ-coh1 (gluer-β' pt) (gluer-β' pt))))) (ap-∘ (λ x → σ B A (σ A B x)) (σ B A) (gluer-β' a) (apσ-coh2 (ap-∘ (λ x → σ B A x) (σ A B) (gluel-β' pt) (apσ-coh1 (gluer-β' pt) (gluer-β' pt))) (ap-∘ (λ x → σ B A x) (σ A B) (gluel-β' a) (apσ-coh1 (gluer-β' pt) (gluer-β' a))))))) (σ-2triangle-coh3 (A ∧ B) (proj pt pt) basel (gluel pt) (proj a pt) (gluel a)))
             (σ-2triangle-coh2 (A ∧ B) (proj pt pt) baser (gluer pt))
             (λ b → ↓-=-in□ idp idp ?) -- ↓-=-in□ (ap-idf) (ap-∘ (λ x → σ B A (σ A B (σ B A x))) (σ A B) (gluer-β' b) (apσ-coh2 (ap-∘ (λ x → σ B A (σ A B x)) (σ B A) (gluel-β' pt) (apσ-coh1 (ap-∘ (λ x → σ B A x) (σ A B) (gluer-β' pt) (apσ-coh2 (gluel-β' pt) (gluel-β' pt))) (ap-∘ (λ x → σ B A x) (σ A B) (gluer-β' pt) (apσ-coh2 (gluel-β' pt) (gluel-β' pt))))) (ap-∘ (λ x → σ B A (σ A B x)) (σ B A) (gluel-β' b) (apσ-coh1 (ap-∘ (λ x → σ B A x) (σ A B) (gluer-β' pt) (apσ-coh2 (gluel-β' pt) (gluel-β' pt))) (ap-∘ (λ x → σ B A x) (σ A B) (gluer-β' b) (apσ-coh2 (gluel-β' pt) (gluel-β' b))))))) (σ-2triangle-coh4 (A ∧ B) (proj pt pt) baser (gluer pt) (proj pt b) (gluer b)))


-- σ-nat-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x3 : X) (p3 : x3 == x1) (x4 : X) (p4 : x4 == x3) → a == x4
-- σ-nat-coh1 X a _ idp _ idp _ idp = idp

-- σ-nat-coh2 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x3 : X) (p3 : x3 == x1) (x4 : X) (p4 : x4 == x3) → a == x4
-- σ-nat-coh2 X a _ idp _ idp _ idp = idp

-- σ-nat-coh3 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == a) (x3 : X) (p3 : x3 == x1) (x4 : X) (p4 : x4 == x3) (x5 : x3 == a) (p5 : x5 == coh∙! p3 p1) (x6 : x2 == x0) (p6 : x6 == coh∙ p2 p0) (x7 : x4 == x2) (p7 : x7 == coh∙∙! p4 x5 p2) (x8 : X) (p8 : x8 == x0) (x9 : X) (p9 : x9 == x8) → coh∙ idp (σ-coh1 X x4 a (∧-map-coh2 X a x0 p0 x2 x6 x4 x7) x9 (∧-map-coh2 X a x0 p0 x8 p8 x9 p9)) == coh∙ (∧-map-coh1 X a a (σ-coh1 X a x0 p0 a p0) x8 (σ-coh1 X a x0 p0 x8 p8) x9 p9) (σ-nat-coh1 X a x1 p1 x3 p3 x4 p4)
-- σ-nat-coh3 X a _ idp _ idp _ idp _ idp _ idp _ idp _ idp _ idp _ idp _ idp = idp

-- σ-nat-coh4 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x3 : X) (p3 : x3 == x1) (x4 : X) (p4 : x4 == x3) (x5 : X) (p5 : x5 == x1) (x6 : X) (p6 : x6 == x5) → coh∙ idp (σ-coh2 X x4 a (∧-map-coh1 X a x1 p1 x3 p3 x4 p4) x6 (∧-map-coh1 X a x1 p1 x5 p5 x6 p6)) == coh∙ (∧-map-coh2 X a a (σ-coh2 X a x1 p1 a p1) x5 (σ-coh2 X a x1 p1 x5 p5) x6 p6) (σ-nat-coh2 X a x1 p1 x3 p3 x4 p4)
-- σ-nat-coh4 X a _ idp _ idp _ idp _ idp _ idp = idp

-- σ-nat : (A : Type i) {{_ : Pointed A}} (A' : Type i) {{_ : Pointed A'}} (B : Type i) {{_ : Pointed B}} (B' : Type i) {{_ : Pointed B'}} (f : A → A') {{_ : PointedFun f}} (g : B → B') {{_ : PointedFun g}} (x : A ∧ B) → σ A' B' (∧-map A A' B B' f g x) == ∧-map B B' A A' g f (σ A B x)
-- σ-nat A A' B B' f g =
--   Smash-elim (λ a b → idp)
--              (σ-nat-coh1 (B' ∧ A') (proj pt pt) basel (gluel pt) (proj (g pt) pt) (gluel (g pt)) (proj (g pt) (f pt)) (ap (λ z → proj (g pt) z) (ptf f)))
--              (λ a → ↓-=-in-eq (ap-∘ (λ x → ∧-map B B' A A' g f x) (σ A B) (gluel-β' a) (apσ-coh1 (gluer-β' pt) (gluer-β' a))) (ap-∘ (λ x → σ A' B' x) (∧-map A A' B B' f g) (gluel-β' a) (ap∧-map-coh1 (gluel-β' pt) (gluel-β' (f a)) (∘-ap-eq (λ x → σ A' B' x) (λ z → proj (f a) z) idp))) (σ-nat-coh3 (B' ∧ A') (proj pt pt) baser (gluer pt) basel (gluel pt) (proj pt (f pt)) (ap (λ z → proj pt z) (ptf f)) (proj (g pt) pt) (gluel (g pt)) (proj (g pt) (f pt)) (ap (λ z → proj (g pt) z) (ptf f)) (ap (λ z → proj z pt) (ptf g)) (green (ptf g)) (gluer (f pt)) (purple (ptf f)) (ap (λ z → proj z (f pt)) (ptf g)) (pink-l (ptf g) (ptf f)) (proj pt (f a)) (gluer (f a)) (proj (g pt) (f a)) (ap (λ z → proj z (f a)) (ptf g))))
--              (σ-nat-coh2 (B' ∧ A') (proj pt pt) basel (gluel pt) (proj (g pt) pt) (gluel (g pt)) (proj (g pt) (f pt)) (ap (λ z → proj (g pt) z) (ptf f)))
--              (λ b → ↓-=-in-eq (ap-∘ (λ x → ∧-map B B' A A' g f x) (σ A B) (gluer-β' b) (apσ-coh2 (gluel-β' pt) (gluel-β' b))) (ap-∘ (λ x → σ A' B' x) (∧-map A A' B B' f g) (gluer-β' b) (ap∧-map-coh2 (gluer-β' pt) (gluer-β' (g b)) (∘-ap-eq (λ x → σ A' B' x) (λ z → proj z (g b)) idp))) (σ-nat-coh4 (B' ∧ A') (proj pt pt) basel (gluel pt) (proj (g pt) pt) (gluel (g pt)) (proj (g pt) (f pt)) (ap (λ z → proj (g pt) z) (ptf f)) (proj (g b) pt) (gluel (g b)) (proj (g b) (f pt)) (ap (λ z → proj (g b) z) (ptf f))))

-- α-rinv-aux-coh1 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x6 : X) (p6 : x6 == x0) (x8 : X) (p8 : x6 == x8) → a == x8
-- α-rinv-aux-coh1 X a _ idp _ idp _ idp = idp

-- α-rinv-aux-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x6 : X) (p6 : x6 == x0) (x7 : X) (p7 : x6 == x7) → a == x7
-- α-rinv-aux-coh2 X a _ idp _ idp _ idp = idp

-- α-rinv-aux-coh3 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x1 : X) (p1 : a == x1) (x3 : X) (p3 : x3 == x1) (x4 : X) (p4 : x4 == x1) (x6 : a == x3) (p6 : x6 == coh∙! p1 p3) (x7 : x4 == x3) (p7 : x7 == coh∙! p4 p3) (x8 : X) (p8 : x8 == x0) (x10 : X) (p10 : x8 == x10) (x11 : X) (p11 : x11 == x10) → Square idp (α-aux-coh1 X a a (α⁻¹-coh2 X a x1 p1 a p1) x4 (α⁻¹-coh2 X a x1 p1 x4 p4) a (α⁻¹-aux-coh2 X a x0 p0 a p0 x3 x6 x4 x7) x11 (α⁻¹-aux-coh2 X a x0 p0 x8 p8 x10 p10 x11 p11)) p11 (α-rinv-aux-coh1 X a x0 p0 x8 p8 x10 p10)
-- α-rinv-aux-coh3 X a _ idp _ idp _ idp _ idp _ idp _ idp _ idp _ idp _ idp = ids

-- α-rinv-aux-coh4 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) (x5 : a == x2) (p5 : x5 == coh∙! p1 p2) (x8 : X) (p8 : x8 == x0) (x9 : X) (p9 : x8 == x9) (x11 : X) (p11 : x11 == x9) → Square idp (α-aux-coh2 X a a (α⁻¹-coh1 X a x0 p0 a p0 x2 x5 a x5) x11 (α⁻¹-coh1 X a x0 p0 x8 p8 x9 p9 x11 p11)) p11 (α-rinv-aux-coh2 X a x0 p0 x8 p8 x9 p9)
-- α-rinv-aux-coh4 X a _ idp _ idp _ idp _ idp _ idp _ idp _ idp = ids

-- α-rinv-aux : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (c : C) (x : A ∧ B) → α⁻¹ A B C (α-aux A B C c x) == proj x c
-- α-rinv-aux A B C c =
--   Smash-elim (λ a b → idp)
--              (α-rinv-aux-coh1 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) baser (gluer pt) (proj (proj pt pt) c) (gluer c) (proj basel c) (ap (λ z → proj z c) (gluel pt)))
--              (λ a → ↓-=-in□ idp (ap-∘ (λ x → α⁻¹ A B C x) (α-aux A B C c) (gluel-β' a) (apα-aux-coh1 (gluel-β' pt) (gluel-β' a) (∘-ap-eq (λ x → α⁻¹ A B C x) (λ z → proj a z) (gluer-β' pt)) (∘-ap-eq (λ x → α⁻¹ A B C x) (λ z → proj a z) (gluer-β' c)))) (α-rinv-aux-coh3 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) baser (gluer pt) basel (gluel (proj pt pt)) (proj basel pt) (gluel basel) (proj (proj a pt) pt) (gluel (proj a pt)) (ap (λ z → proj z pt) (gluel pt)) (green (gluel pt)) (ap (λ z → proj z pt) (gluel a)) (green (gluel a)) (proj (proj pt pt) c) (gluer c) (proj basel c) (ap (λ z → proj z c) (gluel pt)) (proj (proj a pt) c) (ap (λ z → proj z c) (gluel a))))
--              (α-rinv-aux-coh2 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) baser (gluer pt) (proj (proj pt pt) c) (gluer c) (proj baser c) (ap (λ z → proj z c) (gluer pt)))
--              (λ b → ↓-=-in□ idp (ap-∘ (λ x → α⁻¹ A B C x) (α-aux A B C c) (gluer-β' b) (apα-aux-coh2 (gluer-β' (proj pt pt)) (gluer-β' (proj b c)))) (α-rinv-aux-coh4 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) baser (gluer pt) basel (gluel (proj pt pt)) (proj baser pt) (gluel baser) (ap (λ z → proj z pt) (gluer pt)) (green (gluer pt)) (proj (proj pt pt) c) (gluer c) (proj baser c) (ap (λ z → proj z c) (gluer pt)) (proj (proj pt b) c) (ap (λ z → proj z c) (gluer b))))

-- α-rinv-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) → a == x1
-- α-rinv-coh1 X a _ idp = idp

-- α-rinv-cohdef : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x4 : X) (p4 : x4 == x1) → coh∙ idp p4 == coh∙ (ap {!ERROR (asubst α⁻¹ A B C)!} (α-coh1 {!ERROR (asubst A ∧ (B ∧ C))!} {!ERROR (asubst proj pt (proj pt pt))!} {!ERROR (asubst basel)!} {!ERROR (asubst gluel pt)!} {!ERROR (asubst proj a (proj pt pt))!} {!ERROR (asubst gluel a)!} {!ERROR (asubst proj a basel)!} (ap {!ERROR (asubst λ z → proj a z)!} {!ERROR (asubst gluel pt)!}) {!ERROR (asubst proj a (proj b pt))!} (ap {!ERROR (asubst λ z → proj a z)!} {!ERROR (asubst gluel b)!}))) (α-rinv-coh1 X a x1 p1)
-- α-rinv-cohdef X a _ idp _ idp = idp

-- α-rinv-auxcoh-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x3 : X) (p3 : x3 == x1) → coh∙ {!ERROR (asubst {!ERROR (TODO1)!})!} p3 == coh∙ (ap {!ERROR (asubst α⁻¹ A B C)!} {!ERROR (asubst {!ERROR (TODO1)!})!}) (α-rinv-coh1 X a x1 p1)
-- α-rinv-auxcoh-coh1 X a _ idp _ idp = idp

-- α-rinv-auxcoh-coh2 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) → coh∙ {!ERROR (asubst {!ERROR (TODO2)!})!} p2 == coh∙ (ap {!ERROR (asubst α⁻¹ A B C)!} {!ERROR (asubst {!ERROR (TODO2)!})!}) (α-rinv-coh1 X a x1 p1)
-- α-rinv-auxcoh-coh2 X a _ idp _ idp = idp

-- α-rinv-auxcoh : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : A ∧ B) → Square (α-rinv-aux A B C pt x) (ap (α⁻¹ A B C) (α-auxcoh A B C x)) (gluel x) (α-rinv-coh1 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) basel (gluel (proj pt pt)))
-- α-rinv-auxcoh A B C =
--   Smash-elim (λ a b → {!α-rinv-cohdef ((A ∧ B) ∧ C) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj (proj a b) pt) (gluel (proj a b))!})
--              {!.α-rinv-auxcoh-coh1 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj basel pt) (gluel basel)!}
--              (λ a → ↓-Square-in-simpl {!!})
--              {!α-rinv-auxcoh-coh2 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj baser pt) (gluel baser)!}
--              (λ b → ↓-Square-in {!!} idp ap-cst ap-cst {!!} {!!} {!!} {!!} {!!})

-- α-rinv-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) → a == x0
-- α-rinv-coh2 X a _ idp = idp

-- α-rinv : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : (A ∧ B) ∧ C) → α⁻¹ A B C (α A B C x) == x
-- α-rinv A B C =
--   Smash-elim (λ x c → α-rinv-aux A B C c x)
--              (α-rinv-coh1 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) basel (gluel (proj pt pt)))
--              (λ x → ↓-=-in□ (ap-idf) (ap-∘ (λ x → α⁻¹ A B C x) (α A B C) (gluel-β' x) (idp)) (α-rinv-auxcoh A B C x))
--              (α-rinv-coh2 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) baser (gluer pt))
--              (λ c → ↓-=-in-eq ({!gluer-βrhs!}) ({!gluer-βlhs!}) ({!coh3app!}))



-- test : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : A ∧ B) → Square (α-rinv-aux A B C pt x) (ap (α⁻¹ A B C) (α-auxcoh A B C x)) (gluel x) (α-rinv-coh1 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) basel (gluel (proj pt pt)))
-- test A B C =
--   Smash-elim (λ a b → {!!}) {!!}
--              (λ a → ↓-Square-in {!!} {!!} {!!} {!!} {!!}) {!!} {!!}
  -- Smash-elim (λ a b → α-rinv-cohdef ((A ∧ B) ∧ C) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj (proj a b) pt) (gluel (proj a b)))
  --            (α-rinv-auxcoh-coh1 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj basel pt) (gluel basel))
  --            (λ a → ↓-=-in-eq-dep {!apd gluel (gluel a)!} {!!} {!!})
  --            (α-rinv-auxcoh-coh2 ((A ∧ B) ∧ C) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj baser pt) (gluel baser))
  --            {!!}

{-# OPTIONS --without-K --rewriting #-}

open import PathInduction
open import SmashDefs

module Smash {i : ULevel} where


σ-cohl : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → x1 == a)
σ-cohl = path-induction

{- For all coherences, does not change the level -}
apσ-cohl : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Square (ap (λ z → f z) (& σ-cohl X p0 p1)) (& σ-cohl Y (ap (λ z → f z) p0) (ap (λ z → f z) p1)) idp idp)
apσ-cohl = path-induction

{- Only for coherences of level 1, because of ap+ -}
σ-cohl□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) → Square (& σ-cohl X up0 up1) (& σ-cohl X vp0 vp1) x1 a)
σ-cohl□ = path-induction

ap/σ-cohl : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) → Cube (ap□ (λ x → & σ-cohl Y (p0 x) (p1 x)) r) (& σ-cohl□ Y (ap□ p0 r) (ap□ p1 r)) (& hids (& σ-cohl Y (p0 y) (p1 y))) (& hids (& σ-cohl Y (p0 z) (p1 z))) (& hids (ap (λ x → x1 x) r)) (& hids (ap (λ x → a x) r))
ap/σ-cohl {y = y} idp p0 p1 = & lemma (p0 y) (p1 y)  where

  lemma : Coh ({X : Type i} {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0)
        → Cube (& hids (& σ-cohl X p0 p1)) (& σ-cohl□ X (& hids p0) (& hids p1)) (& hids (& σ-cohl X p0 p1)) (& hids (& σ-cohl X p0 p1)) ids ids)
  lemma = path-induction


σ-cohl□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) → Square x1 a (& σ-cohl X up0 up1) (& σ-cohl X vp0 vp1))
σ-cohl□' = path-induction

ap□σ-cohl : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (ap□ α (& σ-cohl X p0 p1))
          {!& σ-cohl□' Y {f a} {g a} {α a}
                      {f x0} {ap (λ z → f z) p0} {g x0} {ap (λ z → g z) p0} {α x0} (ap□ α p0)
                      {f x1} {ap (λ z → f z) p1} {g x1} {ap (λ z → g z) p1} {α x1} (ap□ α p1)!} (& hids (α x1)) (& hids (α a)) (& apσ-cohl f p0 p1) (& apσ-cohl g p0 p1)
ap□σ-cohl = {!!}

-- {- For all coherences, increases the level by 1 -}
-- σ-cohl□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) → Square x1 a (& σ-cohl X up0 up1) (& σ-cohl X vp0 vp1))
-- σ-cohl□' = path-induction

-- ap□σ-cohl : {X : Type i} {Y : Type i} {f g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0)
--           → Cube (ap□ α (& σ-cohl X p0 p1))
--                  (& σ-cohl□' Y (ap□ α p0) (ap□ α p1))
--                  (& hids (α x1))
--                  (& hids (α a))
--                  (& apσ-cohl f p0 p1)
--                  (& apσ-cohl g p0 p1)
-- ap□σ-cohl α {a} idp idp = & lemma (α a)  where

--   lemma : Coh ({X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& σ-cohl□' X (& hids p) (& hids p)) (& hids p) (& hids p) ids ids)
--   lemma = path-induction

-- σ-cohr : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → x1 == a)
-- σ-cohr = path-induction

-- apσ-cohr : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Square (ap (λ z → f z) (& σ-cohr X p0 p1)) (& σ-cohr Y (ap (λ z → f z) p0) (ap (λ z → f z) p1)) idp idp)
-- apσ-cohr = path-induction

-- σ-cohr□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) → Square (& σ-cohr X up0 up1) (& σ-cohr X vp0 vp1) x1 a)
-- σ-cohr□ = path-induction

-- σ : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → B ∧ A
-- σ A B = σ.f  module _ where

--   module σ =
--     SmashRec (λ a b → proj b a)
--              pt
--              (λ a → & σ-cohl (B ∧ A) (gluer pt) (gluer a))
--              pt
--              (λ b → & σ-cohr (B ∧ A) (gluel pt) (gluel b))



-- ∧-map-cohl : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → x2 == a)
-- ∧-map-cohl = path-induction

-- ap∧-map-cohl : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → Square (ap (λ z → f z) (& ∧-map-cohl X p0 p1 p2)) (& ∧-map-cohl Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2)) idp idp)
-- ap∧-map-cohl = path-induction

-- ∧-map-cohl□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) {ux2 : X} {up2 : ux2 == ux1} {vx2 : X} {vp2 : vx2 == vx1} {x2 : ux2 == vx2} (p2 : Square up2 vp2 x2 x1) → Square (& ∧-map-cohl X up0 up1 up2) (& ∧-map-cohl X vp0 vp1 vp2) x2 a)
-- ∧-map-cohl□ = path-induction

-- ∧-map-cohr : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → x2 == a)
-- ∧-map-cohr = path-induction

-- ap∧-map-cohr : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → Square (ap (λ z → f z) (& ∧-map-cohr X p0 p1 p2)) (& ∧-map-cohr Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2)) idp idp)
-- ap∧-map-cohr = path-induction

-- ∧-map-cohr□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) {ux2 : X} {up2 : ux2 == ux1} {vx2 : X} {vp2 : vx2 == vx1} {x2 : ux2 == vx2} (p2 : Square up2 vp2 x2 x1) → Square (& ∧-map-cohr X up0 up1 up2) (& ∧-map-cohr X vp0 vp1 vp2) x2 a)
-- ∧-map-cohr□ = path-induction

-- ∧-map : (A : Type i) {{_ : Pointed A}} (A' : Type i) {{_ : Pointed A'}} (B : Type i) {{_ : Pointed B}} (B' : Type i) {{_ : Pointed B'}} (f : A → A') {{_ : PointedFun f}} (g : B → B') {{_ : PointedFun g}} (x : A ∧ B) → A' ∧ B'
-- ∧-map A A' B B' f g = ∧-map.f  module _ where

--   module ∧-map =
--     SmashRec (λ a b → proj (f a) (g b))
--              pt
--              (λ a → & ∧-map-cohl (A' ∧ B') (gluel pt) (gluel (f a)) (ap (λ z → proj (f a) z) (ptf g)))
--              pt
--              (λ b → & ∧-map-cohr (A' ∧ B') (gluer pt) (gluer (g b)) (ap (λ z → proj z (g b)) (ptf f)))







-- ∧-map-id-cohl : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : x1 == a} (p2 : Square (& ∧-map-cohl X p0 p1 idp) x2 idp idp) {x3 : x1 == x0} (p3 : Square x3 p1 idp idp) → Square idp p0 x2 x3)
-- ∧-map-id-cohl = path-induction

-- ap∧-map-id-cohl : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : x1 == a} (p2 : Square (& ∧-map-cohl X p0 p1 idp) x2 idp idp) {x3 : x1 == x0} (p3 : Square x3 p1 idp idp) → Cube (ap-square f (& ∧-map-id-cohl X p0 p2 p3)) (& ∧-map-id-cohl Y (ap (λ z → f z) p0) (& coh!∙□ (& ap∧-map-cohl f p0 p1 idp) (ap-square (λ z → f z) p2)) (ap-square (λ z → f z) p3)) ids (& hids (ap f p0)) (& hids (ap f x2)) (& hids (ap f x3)))
-- ap∧-map-id-cohl = path-induction







-- ∧-map-id-cohr : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : x1 == a} (p2 : Square (& ∧-map-cohr X p0 p1 idp) x2 idp idp) {x3 : x1 == x0} (p3 : Square x3 p1 idp idp) → Square idp p0 x2 x3)
-- ∧-map-id-cohr = path-induction

-- ap∧-map-id-cohr : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : x1 == a} (p2 : Square (& ∧-map-cohr X p0 p1 idp) x2 idp idp) {x3 : x1 == x0} (p3 : Square x3 p1 idp idp) → Cube (ap-square f (& ∧-map-id-cohr X p0 p2 p3)) (& ∧-map-id-cohr Y (ap (λ z → f z) p0) (& coh!∙□ (& ap∧-map-cohr f p0 p1 idp) (ap-square (λ z → f z) p2)) (ap-square (λ z → f z) p3)) ids (& hids (ap f p0)) (& hids (ap f x2)) (& hids (ap f x3)))
-- ap∧-map-id-cohr = path-induction





-- ∧-map-id : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → ∧-map A A B B (λ y → y) (λ z → z) x == x
-- ∧-map-id A B = ∧-map-id.f  module _ where

--   module ∧-map-id =
--     SmashElimId {g = λ x → ∧-map A A B B (λ y → y) (λ z → z) x}
--                 {h = λ x → x}
--                 (λ a b → idp)
--                 (gluel pt)
--                 (λ a → & ∧-map-id-cohl (A ∧ B) (gluel pt) (∧-map.gluel-β A A B B (λ y → y) (λ z → z) a) (ap-idf (gluel a)))
--                 (gluer pt)
--                 (λ b → & ∧-map-id-cohr (A ∧ B) (gluer pt) (∧-map.gluer-β A A B B (λ y → y) (λ z → z) b) (ap-idf (gluer b)))







-- σ-triangle-cohl : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : a == a} (p2 : Square (& σ-cohr X p0 p0) x2 idp idp) {x3 : x1 == a} (p3 : Square (& σ-cohr X p0 p1) x3 idp idp) {x4 : x1 == a} (p4 : Square x4 (& σ-cohl X x2 x3) idp idp) {x5 : x1 == a} (p5 : Square x4 x5 idp idp) {x6 : x1 == a} (p6 : Square x6 x5 idp idp) {x7 : x1 == x0} (p7 : Square x7 p1 idp idp) → Square idp p0 x6 x7)
-- σ-triangle-cohl = path-induction

-- apσ-triangle-cohl : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : a == a} (p2 : Square (& σ-cohr X p0 p0) x2 idp idp) {x3 : x1 == a} (p3 : Square (& σ-cohr X p0 p1) x3 idp idp) {x4 : x1 == a} (p4 : Square x4 (& σ-cohl X x2 x3) idp idp) {x5 : x1 == a} (p5 : Square x4 x5 idp idp) {x6 : x1 == a} (p6 : Square x6 x5 idp idp) {x7 : x1 == x0} (p7 : Square x7 p1 idp idp) → Cube (ap-square f (& σ-triangle-cohl X p0 p2 p3 p4 p5 p6 p7)) (& σ-triangle-cohl Y (ap (λ z → f z) p0) (& coh!∙□ (& apσ-cohr f p0 p0) (ap-square (λ z → f z) p2)) (& coh!∙□ (& apσ-cohr f p0 p1) (ap-square (λ z → f z) p3)) (& coh∙□ (ap-square (λ z → f z) p4) (& apσ-cohl f x2 x3)) (ap-square (λ z → f z) p5) (ap-square (λ z → f z) p6) (ap-square (λ z → f z) p7)) ids (& hids (ap f p0)) (& hids (ap f x6)) (& hids (ap f x7)))
-- apσ-triangle-cohl = path-induction







-- σ-triangle-cohr : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : a == a} (p2 : Square (& σ-cohl X p0 p0) x2 idp idp) {x3 : x1 == a} (p3 : Square (& σ-cohl X p0 p1) x3 idp idp) {x4 : x1 == a} (p4 : Square x4 (& σ-cohr X x2 x3) idp idp) {x5 : x1 == a} (p5 : Square x4 x5 idp idp) {x6 : x1 == a} (p6 : Square x6 x5 idp idp) {x7 : x1 == x0} (p7 : Square x7 p1 idp idp) → Square idp p0 x6 x7)
-- σ-triangle-cohr = path-induction

-- apσ-triangle-cohr : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : a == a} (p2 : Square (& σ-cohl X p0 p0) x2 idp idp) {x3 : x1 == a} (p3 : Square (& σ-cohl X p0 p1) x3 idp idp) {x4 : x1 == a} (p4 : Square x4 (& σ-cohr X x2 x3) idp idp) {x5 : x1 == a} (p5 : Square x4 x5 idp idp) {x6 : x1 == a} (p6 : Square x6 x5 idp idp) {x7 : x1 == x0} (p7 : Square x7 p1 idp idp) → Cube (ap-square f (& σ-triangle-cohr X p0 p2 p3 p4 p5 p6 p7)) (& σ-triangle-cohr Y (ap (λ z → f z) p0) (& coh!∙□ (& apσ-cohl f p0 p0) (ap-square (λ z → f z) p2)) (& coh!∙□ (& apσ-cohl f p0 p1) (ap-square (λ z → f z) p3)) (& coh∙□ (ap-square (λ z → f z) p4) (& apσ-cohr f x2 x3)) (ap-square (λ z → f z) p5) (ap-square (λ z → f z) p6) (ap-square (λ z → f z) p7)) ids (& hids (ap f p0)) (& hids (ap f x6)) (& hids (ap f x7)))
-- apσ-triangle-cohr = path-induction





-- σ-triangle : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → σ B A (σ A B x) == x
-- σ-triangle A B = σ-triangle.f  module _ where

--   module σ-triangle =
--     SmashElimId {g = λ x → σ B A (σ A B x)}
--                 {h = λ x → x}
--                 (λ a b → idp)
--                 (gluel pt)
--                 (λ a → & σ-triangle-cohl (A ∧ B) (gluel pt) (σ.gluer-β B A pt) (σ.gluer-β B A a) (& apσ-cohl (λ x → σ B A x) (gluer pt) (gluer a)) (ap-square (λ x → σ B A x) (σ.gluel-β A B a)) (ap-∘ (λ x → σ B A x) (λ x → σ A B x) (gluel a)) (ap-idf (gluel a)))
--                 (gluer pt)
--                 (λ b → & σ-triangle-cohr (A ∧ B) (gluer pt) (σ.gluel-β B A pt) (σ.gluel-β B A b) (& apσ-cohr (λ x → σ B A x) (gluel pt) (gluel b)) (ap-square (λ x → σ B A x) (σ.gluer-β A B b)) (ap-∘ (λ x → σ B A x) (λ x → σ A B x) (gluer b)) (ap-idf (gluer b)))







-- σ-2triangle-cohl : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : a == a} (p2 : Square (& σ-cohr X p0 p0) x2 idp idp) {x3 : a == a} (p3 : Square x3 (& σ-cohl X x2 x2) idp idp) {x4 : a == a} (p4 : Square x3 x4 idp idp) {x5 : a == a} (p5 : Square x5 x4 idp idp) {x6 : a == a} (p6 : Square x6 (& σ-cohr X x5 x5) idp idp) {x7 : a == a} (p7 : Square x6 x7 idp idp) {x8 : a == a} (p8 : Square x8 x7 idp idp) {x9 : x1 == a} (p9 : Square (& σ-cohr X p0 p1) x9 idp idp) {x10 : x1 == a} (p10 : Square x10 (& σ-cohl X x2 x9) idp idp) {x11 : x1 == a} (p11 : Square x10 x11 idp idp) {x12 : x1 == a} (p12 : Square x12 x11 idp idp) {x13 : x1 == a} (p13 : Square x13 (& σ-cohr X x5 x12) idp idp) {x14 : x1 == a} (p14 : Square x13 x14 idp idp) {x15 : x1 == a} (p15 : Square x15 x14 idp idp) {x16 : x1 == a} (p16 : Square x16 (& σ-cohl X x8 x15) idp idp) {x17 : x1 == a} (p17 : Square x16 x17 idp idp) {x18 : x1 == a} (p18 : Square x18 x17 idp idp) {x19 : x1 == x0} (p19 : Square x19 p1 idp idp) → Square idp p0 x18 x19)
-- σ-2triangle-cohl = path-induction

-- apσ-2triangle-cohl : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : a == a} (p2 : Square (& σ-cohr X p0 p0) x2 idp idp) {x3 : a == a} (p3 : Square x3 (& σ-cohl X x2 x2) idp idp) {x4 : a == a} (p4 : Square x3 x4 idp idp) {x5 : a == a} (p5 : Square x5 x4 idp idp) {x6 : a == a} (p6 : Square x6 (& σ-cohr X x5 x5) idp idp) {x7 : a == a} (p7 : Square x6 x7 idp idp) {x8 : a == a} (p8 : Square x8 x7 idp idp) {x9 : x1 == a} (p9 : Square (& σ-cohr X p0 p1) x9 idp idp) {x10 : x1 == a} (p10 : Square x10 (& σ-cohl X x2 x9) idp idp) {x11 : x1 == a} (p11 : Square x10 x11 idp idp) {x12 : x1 == a} (p12 : Square x12 x11 idp idp) {x13 : x1 == a} (p13 : Square x13 (& σ-cohr X x5 x12) idp idp) {x14 : x1 == a} (p14 : Square x13 x14 idp idp) {x15 : x1 == a} (p15 : Square x15 x14 idp idp) {x16 : x1 == a} (p16 : Square x16 (& σ-cohl X x8 x15) idp idp) {x17 : x1 == a} (p17 : Square x16 x17 idp idp) {x18 : x1 == a} (p18 : Square x18 x17 idp idp) {x19 : x1 == x0} (p19 : Square x19 p1 idp idp) → Cube (ap-square f (& σ-2triangle-cohl X p0 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19)) (& σ-2triangle-cohl Y (ap (λ z → f z) p0) (& coh!∙□ (& apσ-cohr f p0 p0) (ap-square (λ z → f z) p2)) (& coh∙□ (ap-square (λ z → f z) p3) (& apσ-cohl f x2 x2)) (ap-square (λ z → f z) p4) (ap-square (λ z → f z) p5) (& coh∙□ (ap-square (λ z → f z) p6) (& apσ-cohr f x5 x5)) (ap-square (λ z → f z) p7) (ap-square (λ z → f z) p8) (& coh!∙□ (& apσ-cohr f p0 p1) (ap-square (λ z → f z) p9)) (& coh∙□ (ap-square (λ z → f z) p10) (& apσ-cohl f x2 x9)) (ap-square (λ z → f z) p11) (ap-square (λ z → f z) p12) (& coh∙□ (ap-square (λ z → f z) p13) (& apσ-cohr f x5 x12)) (ap-square (λ z → f z) p14) (ap-square (λ z → f z) p15) (& coh∙□ (ap-square (λ z → f z) p16) (& apσ-cohl f x8 x15)) (ap-square (λ z → f z) p17) (ap-square (λ z → f z) p18) (ap-square (λ z → f z) p19)) ids (& hids (ap f p0)) (& hids (ap f x18)) (& hids (ap f x19)))
-- apσ-2triangle-cohl = path-induction







-- σ-2triangle-cohr : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : a == a} (p2 : Square (& σ-cohl X p0 p0) x2 idp idp) {x3 : a == a} (p3 : Square x3 (& σ-cohr X x2 x2) idp idp) {x4 : a == a} (p4 : Square x3 x4 idp idp) {x5 : a == a} (p5 : Square x5 x4 idp idp) {x6 : a == a} (p6 : Square x6 (& σ-cohl X x5 x5) idp idp) {x7 : a == a} (p7 : Square x6 x7 idp idp) {x8 : a == a} (p8 : Square x8 x7 idp idp) {x9 : x1 == a} (p9 : Square (& σ-cohl X p0 p1) x9 idp idp) {x10 : x1 == a} (p10 : Square x10 (& σ-cohr X x2 x9) idp idp) {x11 : x1 == a} (p11 : Square x10 x11 idp idp) {x12 : x1 == a} (p12 : Square x12 x11 idp idp) {x13 : x1 == a} (p13 : Square x13 (& σ-cohl X x5 x12) idp idp) {x14 : x1 == a} (p14 : Square x13 x14 idp idp) {x15 : x1 == a} (p15 : Square x15 x14 idp idp) {x16 : x1 == a} (p16 : Square x16 (& σ-cohr X x8 x15) idp idp) {x17 : x1 == a} (p17 : Square x16 x17 idp idp) {x18 : x1 == a} (p18 : Square x18 x17 idp idp) {x19 : x1 == x0} (p19 : Square x19 p1 idp idp) → Square idp p0 x18 x19)
-- σ-2triangle-cohr = path-induction

-- apσ-2triangle-cohr : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} {p1 : x1 == x0} {x2 : a == a} (p2 : Square (& σ-cohl X p0 p0) x2 idp idp) {x3 : a == a} (p3 : Square x3 (& σ-cohr X x2 x2) idp idp) {x4 : a == a} (p4 : Square x3 x4 idp idp) {x5 : a == a} (p5 : Square x5 x4 idp idp) {x6 : a == a} (p6 : Square x6 (& σ-cohl X x5 x5) idp idp) {x7 : a == a} (p7 : Square x6 x7 idp idp) {x8 : a == a} (p8 : Square x8 x7 idp idp) {x9 : x1 == a} (p9 : Square (& σ-cohl X p0 p1) x9 idp idp) {x10 : x1 == a} (p10 : Square x10 (& σ-cohr X x2 x9) idp idp) {x11 : x1 == a} (p11 : Square x10 x11 idp idp) {x12 : x1 == a} (p12 : Square x12 x11 idp idp) {x13 : x1 == a} (p13 : Square x13 (& σ-cohl X x5 x12) idp idp) {x14 : x1 == a} (p14 : Square x13 x14 idp idp) {x15 : x1 == a} (p15 : Square x15 x14 idp idp) {x16 : x1 == a} (p16 : Square x16 (& σ-cohr X x8 x15) idp idp) {x17 : x1 == a} (p17 : Square x16 x17 idp idp) {x18 : x1 == a} (p18 : Square x18 x17 idp idp) {x19 : x1 == x0} (p19 : Square x19 p1 idp idp) → Cube (ap-square f (& σ-2triangle-cohr X p0 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19)) (& σ-2triangle-cohr Y (ap (λ z → f z) p0) (& coh!∙□ (& apσ-cohl f p0 p0) (ap-square (λ z → f z) p2)) (& coh∙□ (ap-square (λ z → f z) p3) (& apσ-cohr f x2 x2)) (ap-square (λ z → f z) p4) (ap-square (λ z → f z) p5) (& coh∙□ (ap-square (λ z → f z) p6) (& apσ-cohl f x5 x5)) (ap-square (λ z → f z) p7) (ap-square (λ z → f z) p8) (& coh!∙□ (& apσ-cohl f p0 p1) (ap-square (λ z → f z) p9)) (& coh∙□ (ap-square (λ z → f z) p10) (& apσ-cohr f x2 x9)) (ap-square (λ z → f z) p11) (ap-square (λ z → f z) p12) (& coh∙□ (ap-square (λ z → f z) p13) (& apσ-cohl f x5 x12)) (ap-square (λ z → f z) p14) (ap-square (λ z → f z) p15) (& coh∙□ (ap-square (λ z → f z) p16) (& apσ-cohr f x8 x15)) (ap-square (λ z → f z) p17) (ap-square (λ z → f z) p18) (ap-square (λ z → f z) p19)) ids (& hids (ap f p0)) (& hids (ap f x18)) (& hids (ap f x19)))
-- apσ-2triangle-cohr = path-induction





-- σ-2triangle : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → σ B A (σ A B (σ B A (σ A B x))) == x
-- σ-2triangle A B = σ-2triangle.f  module _ where

--   module σ-2triangle =
--     SmashElimId {g = λ x → σ B A (σ A B (σ B A (σ A B x)))}
--                 {h = λ x → x}
--                 (λ a b → idp)
--                 (gluel pt)
--                 (λ a → & σ-2triangle-cohl (A ∧ B) (gluel pt) (σ.gluer-β B A pt) (& apσ-cohl (λ z → σ B A z) (gluer pt) (gluer pt)) (ap-square (λ z → σ B A z) (σ.gluel-β A B pt)) (ap-∘ (λ z → σ B A z) (λ x → σ A B x) (gluel pt)) (& apσ-cohr (λ z → σ B A (σ A B z)) (gluel pt) (gluel pt)) (ap-square (λ z → σ B A (σ A B z)) (σ.gluer-β B A pt)) (ap-∘ (λ z → σ B A (σ A B z)) (λ x → σ B A x) (gluer pt)) (σ.gluer-β B A a) (& apσ-cohl (λ z → σ B A z) (gluer pt) (gluer a)) (ap-square (λ z → σ B A z) (σ.gluel-β A B a)) (ap-∘ (λ z → σ B A z) (λ x → σ A B x) (gluel a)) (& apσ-cohr (λ z → σ B A (σ A B z)) (gluel pt) (gluel a)) (ap-square (λ z → σ B A (σ A B z)) (σ.gluer-β B A a)) (ap-∘ (λ z → σ B A (σ A B z)) (λ x → σ B A x) (gluer a)) (& apσ-cohl (λ x → σ B A (σ A B (σ B A x))) (gluer pt) (gluer a)) (ap-square (λ x → σ B A (σ A B (σ B A x))) (σ.gluel-β A B a)) (ap-∘ (λ x → σ B A (σ A B (σ B A x))) (λ x → σ A B x) (gluel a)) (ap-idf (gluel a)))
--                 (gluer pt)
--                 (λ b → & σ-2triangle-cohr (A ∧ B) (gluer pt) (σ.gluel-β B A pt) (& apσ-cohr (λ z → σ B A z) (gluel pt) (gluel pt)) (ap-square (λ z → σ B A z) (σ.gluer-β A B pt)) (ap-∘ (λ z → σ B A z) (λ x → σ A B x) (gluer pt)) (& apσ-cohl (λ z → σ B A (σ A B z)) (gluer pt) (gluer pt)) (ap-square (λ z → σ B A (σ A B z)) (σ.gluel-β B A pt)) (ap-∘ (λ z → σ B A (σ A B z)) (λ x → σ B A x) (gluel pt)) (σ.gluel-β B A b) (& apσ-cohr (λ z → σ B A z) (gluel pt) (gluel b)) (ap-square (λ z → σ B A z) (σ.gluer-β A B b)) (ap-∘ (λ z → σ B A z) (λ x → σ A B x) (gluer b)) (& apσ-cohl (λ z → σ B A (σ A B z)) (gluer pt) (gluer b)) (ap-square (λ z → σ B A (σ A B z)) (σ.gluel-β B A b)) (ap-∘ (λ z → σ B A (σ A B z)) (λ x → σ B A x) (gluel b)) (& apσ-cohr (λ x → σ B A (σ A B (σ B A x))) (gluel pt) (gluel b)) (ap-square (λ x → σ B A (σ A B (σ B A x))) (σ.gluer-β A B b)) (ap-∘ (λ x → σ B A (σ A B (σ B A x))) (λ x → σ A B x) (gluer b)) (ap-idf (gluer b)))



-- α-aux-cohl : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → x3 == a)
-- α-aux-cohl = path-induction

-- apα-aux-cohl : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Square (ap (λ z → f z) (& α-aux-cohl X p0 p1 p2 p3)) (& α-aux-cohl Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2) (ap (λ z → f z) p3)) idp idp)
-- apα-aux-cohl = path-induction

-- α-aux-cohl□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) {ux2 : X} {up2 : ux1 == ux2} {vx2 : X} {vp2 : vx1 == vx2} {x2 : ux2 == vx2} (p2 : Square up2 vp2 x1 x2) {ux3 : X} {up3 : ux3 == ux2} {vx3 : X} {vp3 : vx3 == vx2} {x3 : ux3 == vx3} (p3 : Square up3 vp3 x3 x2) → Square (& α-aux-cohl X up0 up1 up2 up3) (& α-aux-cohl X vp0 vp1 vp2 vp3) x3 a)
-- α-aux-cohl□ = path-induction

-- α-aux-cohr : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → x1 == a)
-- α-aux-cohr = path-induction

-- apα-aux-cohr : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Square (ap (λ z → f z) (& α-aux-cohr X p0 p1)) (& α-aux-cohr Y (ap (λ z → f z) p0) (ap (λ z → f z) p1)) idp idp)
-- apα-aux-cohr = path-induction

-- α-aux-cohr□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) → Square (& α-aux-cohr X up0 up1) (& α-aux-cohr X vp0 vp1) x1 a)
-- α-aux-cohr□ = path-induction

-- α-aux : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (c : C) (x : A ∧ B) → A ∧ (B ∧ C)
-- α-aux A B C c = α-aux.f  module _ where

--   module α-aux =
--     SmashRec (λ a b → proj a (proj b c))
--              pt
--              (λ a → & α-aux-cohl (A ∧ (B ∧ C)) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluer pt)) (ap (λ z → proj a z) (gluer c)))
--              pt
--              (λ b → & α-aux-cohr (A ∧ (B ∧ C)) (gluer (proj pt pt)) (gluer (proj b c)))


-- α-coh1 : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → x3 == a)
-- α-coh1 = path-induction

-- apα-coh1 : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Square (ap (λ z → f z) (& α-coh1 X p0 p1 p2 p3)) (& α-coh1 Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2) (ap (λ z → f z) p3)) idp idp)
-- apα-coh1 = path-induction

-- α-coh1□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) {ux2 : X} {up2 : ux1 == ux2} {vx2 : X} {vp2 : vx1 == vx2} {x2 : ux2 == vx2} (p2 : Square up2 vp2 x1 x2) {ux3 : X} {up3 : ux3 == ux2} {vx3 : X} {vp3 : vx3 == vx2} {x3 : ux3 == vx3} (p3 : Square up3 vp3 x3 x2) → Square (& α-coh1 X up0 up1 up2 up3) (& α-coh1 X vp0 vp1 vp2 vp3) x3 a)
-- α-coh1□ = path-induction





-- α-auxcoh-cohl : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x1 == x3) {x4 : x1 == a} (p4 : Square (& α-aux-cohl X p0 p1 p3 p3) x4 idp idp) {x5 : a == a} (p5 : Square x5 idp idp idp) → Square (& α-coh1 X p0 p1 p2 p2) idp x4 x5)
-- α-auxcoh-cohl = path-induction

-- apα-auxcoh-cohl : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x1 == x3) {x4 : x1 == a} (p4 : Square (& α-aux-cohl X p0 p1 p3 p3) x4 idp idp) {x5 : a == a} (p5 : Square x5 idp idp idp) → Cube (ap-square f (& α-auxcoh-cohl X p0 p1 p2 p3 p4 p5)) (& α-auxcoh-cohl Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2) (ap (λ z → f z) p3) (& coh!∙□ (& apα-aux-cohl f p0 p1 p3 p3) (ap-square (λ z → f z) p4)) (ap-square (λ z → f z) p5)) (& apα-coh1 f p0 p1 p2 p2) ids (& hids (ap f x4)) (& hids (ap f x5)))
-- apα-auxcoh-cohl = path-induction







-- α-auxcoh-cohr : Coh ((X : Type i) {a : X} {x0 : X} {p0 : a == x0} {x1 : X} {p1 : x1 == x0} {x2 : X} (p2 : a == x2) {x3 : X} {p3 : x3 == x0} {x4 : x0 == x0} (p4 : Square x4 idp idp idp) {x5 : a == x3} (p5 : Square p0 p3 x5 x4) {x6 : x0 == x0} (p6 : Square x6 idp idp idp) {x7 : x1 == x3} (p7 : Square p1 p3 x7 x6) {x8 : x1 == a} (p8 : Square (& α-aux-cohr X p0 p1) x8 idp idp) {x9 : a == a} (p9 : Square x9 idp idp idp) → Square (& α-coh1 X p2 p2 x5 x7) idp x8 x9)
-- α-auxcoh-cohr = path-induction

-- apα-auxcoh-cohr : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} {p0 : a == x0} {x1 : X} {p1 : x1 == x0} {x2 : X} (p2 : a == x2) {x3 : X} {p3 : x3 == x0} {x4 : x0 == x0} (p4 : Square x4 idp idp idp) {x5 : a == x3} (p5 : Square p0 p3 x5 x4) {x6 : x0 == x0} (p6 : Square x6 idp idp idp) {x7 : x1 == x3} (p7 : Square p1 p3 x7 x6) {x8 : x1 == a} (p8 : Square (& α-aux-cohr X p0 p1) x8 idp idp) {x9 : a == a} (p9 : Square x9 idp idp idp) → Cube (ap-square f (& α-auxcoh-cohr X p2 p4 p5 p6 p7 p8 p9)) (& α-auxcoh-cohr Y (ap (λ z → f z) p2) (ap-square (λ z → f z) p4) (ap-square (λ z → f z) p5) (ap-square (λ z → f z) p6) (ap-square (λ z → f z) p7) (& coh!∙□ (& apα-aux-cohr f p0 p1) (ap-square (λ z → f z) p8)) (ap-square (λ z → f z) p9)) (& apα-coh1 f p2 p2 x5 x7) ids (& hids (ap f x8)) (& hids (ap f x9)))
-- apα-auxcoh-cohr = path-induction





-- α-auxcoh : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : A ∧ B) → α-aux A B C pt x == proj pt (proj pt pt)
-- α-auxcoh A B C = α-auxcoh.f  module _ where

--   module α-auxcoh =
--     SmashElimId {g = λ x → α-aux A B C pt x}
--                 {h = λ x → proj pt (proj pt pt)}
--                 (λ a b → & α-coh1 (A ∧ (B ∧ C)) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluel pt)) (ap (λ z → proj a z) (gluel b)))
--                 (idp)
--                 (λ a → & α-auxcoh-cohl (A ∧ (B ∧ C)) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluel pt)) (ap (λ z → proj a z) (gluer pt)) (α-aux.gluel-β A B C pt a) (ap-cst (proj pt (proj pt pt)) (gluel a)))
--                 (idp)
--                 (λ b → & α-auxcoh-cohr (A ∧ (B ∧ C)) (gluel pt) (ap-cst baser (gluel pt)) (ap□ (λ y → gluer y) (gluel pt)) (ap-cst baser (gluel b)) (ap□ (λ y → gluer y) (gluel b)) (α-aux.gluer-β A B C pt b) (ap-cst (proj pt (proj pt pt)) (gluer b)))



-- α-coh2 : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → x1 == a)
-- α-coh2 = path-induction

-- apα-coh2 : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Square (ap (λ z → f z) (& α-coh2 X p0 p1)) (& α-coh2 Y (ap (λ z → f z) p0) (ap (λ z → f z) p1)) idp idp)
-- apα-coh2 = path-induction

-- α-coh2□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) → Square (& α-coh2 X up0 up1) (& α-coh2 X vp0 vp1) x1 a)
-- α-coh2□ = path-induction

-- α : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : (A ∧ B) ∧ C) → A ∧ (B ∧ C)
-- α A B C = α.f  module _ where

--   module α =
--     SmashRec (λ x c → α-aux A B C c x) 
--              pt
--              (α-auxcoh A B C)
--              pt
--              (λ c → & α-coh2 (A ∧ (B ∧ C)) (gluer (proj pt pt)) (gluer (proj pt c)))


-- -- -- coh∙ : ∀ {i} → Coh ({X : Type i} {a : X} {b : X} (p : a == b) {c : X} (q : b == c) → a == c)
-- -- -- coh∙ = path-induction

-- -- coh∙□ : ∀ {i} → Coh ({X : Type i} {ua va : X} {a : ua == va}
-- --                                   {ub : X} {uab : ua == ub} {vb : X} {vab : va == vb} {b : ub == vb} (p : Square uab a b vab)
-- --                                   {uc : X} {ubc : ub == uc} {vc : X} {vbc : vb == vc} {c : uc == vc} (q : Square ubc b c vbc)
-- --               → Square (& coh∙ uab ubc) a c (& coh∙ vab vbc))
-- -- coh∙□ = path-induction

-- -- coh∙□-plum : ∀ {i} → Coh ({X : Type i} {ua : X}
-- --                                        {ub : X} {uab : ua == ub} {vab : ua == ub} (p : Square uab idp idp vab)
-- --                                        {uc : X} {ubc : ub == uc} {vbc : ub == uc} (q : Square ubc idp idp vbc)
-- --                    → & degen idp == & coh∙□ (& degen (idp {a = uab})) (& degen (idp {a = ubc})))
-- -- coh∙□-plum = path-induction

-- -- ap□ : ∀ {i} {A B : Type i} {f g : A → B} (α : (x : A) → f x == g x)
-- --       {x y : A} (p : x == y)
-- --       → Square (α x) (ap f p) (ap g p) (α y)
-- -- ap□ α idp = & degen idp


-- -- test : {A B : Type i} {a b c : A → B} (p : (x : A) → a x == b x) (q : (x : A) → b x == c x)
-- --        {y z : A} (r : y == z)
-- --        → ap□ (λ x → & coh∙ (p x) (q x)) r == & coh∙□ (ap□ p r) (ap□ q r)
-- -- test p q idp = & coh∙□-plum (ap□ p idp) (ap□ q idp)

-- -- Δ ⊢ args : Γ
-- -- e : δ == δ'
-- -- ------------------
-- -- Δ ⊢ args [e / Δ] : args [δ / Δ] == args [δ' / Δ]


-- -- x_i [e / Δ] = e_i

-- -- () == () :> ()
-- --   := ()
-- -- (δ, a) == (δ', a') :> (Δ, NCube n args)
-- --   := (e : δ == δ' :> Δ, c : NCube (n + 1) a a' (args [e / Δ]))

-- -- NBoundary 0 A = ()
-- -- NBoundary (n + 1) A =
-- --   {leftb : NBoundary n A}  (left  : NCube n leftb A)
-- --   {rightb : NBoundary n A} (right : NCube n rightb A)
-- --   (tube : leftb == rightb :> NBoundary n A)

-- -- NCube n : {A : Type} (args : NBoundary n A) → Type

-- -- NCube 0 A () = A

-- -- IDP : (δ : Δ) : δ == δ :> Δ
-- -- IDP () = ()
-- -- IDP (δ , a) = (IDP δ , ???)

-- -- idb (n + 1) = (idb n , idc n , idb n , idc n , IDP (idb n))
-- -- idc n : NCube n (idb n)


-- -- AP (f : NCube n A → NCube n B) {δ δ' : Δ} (p : δ == δ' :> Δ) : 

-- -- ∂ap : (f : A → B) {∂a : NBoundary n A} (a : NCube n A ∂a) → NBoundary n B
-- -- ap  : (f : A → B) {∂a : NBoundary n A} (a : NCube n A ∂a) → NCube n B (∂ap f a)

-- -- ∂ap {n = 0} f a = ()
-- -- ∂ap {n = n+1} f {∂a = (left , right , tube)} a = (ap f left , ap f right , AP (ap f) tube)


-- -- ∂ap□ : {A B : Type}
-- --        {∂f : A → NBoundary n B} (f : (x : A) → NCube n (∂f x))
-- --        {∂p : NBoundary m A} (p : NCube m ∂p)
-- --        → NBoundary (n + m) B

-- -- ap□ : {A B : Type}
-- --       {∂f : A → NBoundary n B} (f : (x : A) → NCube n (∂f x))
-- --       {∂p : NBoundary m A} (p : NCube m ∂p)
-- --       → NCube (n + m) (∂ap□ f p)

-- -- ap□ {m = 0} f p = f p

-- -- ∂ap□ {m = 0} f p = ∂f
-- -- ∂ap□ {m = m+1} f {left, right, tube} p = (ap□ f left, ap□ f right, ?)

-- -- tube : leftb == rightb
-- -- ---------------------------------
-- -- ? : ∂ap□ f leftb == ∂ap□ f rightb

-- -- ap-total : (f : A → B) (a : NCubeTotal n A) → NCubeTotal n B

-- -- ap□-total : (f : A → NCubeTotal n B) (p : NCubeTotal m A) → NCubeTotal (n + m) B
-- -- ap□-total f p {m = 0} = f p
-- -- ap□-total f p {m = m+1} = 'ap' (ap□-total f) p
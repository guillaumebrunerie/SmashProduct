{-# OPTIONS --without-K --rewriting #-}

open import SmashCommon
open import PathInduction
open import SmashDefs

module BasicsGenerated {i : ULevel} where

σ-gluel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → x1 == a)
σ-gluel = path-induction

apσ-gluel : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Square (ap (λ z → f z) (& σ-gluel X p0 p1)) (& σ-gluel Y (ap (λ z → f z) p0) (ap (λ z → f z) p1)) idp idp)
apσ-gluel = path-induction

σ-gluel□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) → Square (& σ-gluel X up0 up1) (& σ-gluel X vp0 vp1) x1 a)
σ-gluel□ = path-induction

ap/σ-gluel : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) → Cube (ap+ (λ x → & σ-gluel Y (p0 x) (p1 x)) r) (& σ-gluel□ Y (ap+ p0 r) (ap+ p1 r)) (& hids (& σ-gluel Y (p0 y) (p1 y))) (& hids (& σ-gluel Y (p0 z) (p1 z))) (& hids (ap x1 r)) (& hids (ap a r))
ap/σ-gluel {Y = Y} {y = y} idp p0 p1 = & ap/σ-gluel-lemma Y (p0 y) (p1 y)  where
  ap/σ-gluel-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& hids (& σ-gluel X p0 p1)) (& σ-gluel□ X (& hids p0) (& hids p1)) (& hids (& σ-gluel X p0 p1)) (& hids (& σ-gluel X p0 p1)) ids ids)
  ap/σ-gluel-lemma = path-induction

σ-gluel□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) → Square x1 a (& σ-gluel X up0 up1) (& σ-gluel X vp0 vp1))
σ-gluel□' = path-induction

ap+σ-gluel : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (ap+ α (& σ-gluel X p0 p1)) (& σ-gluel□' Y (ap+ α p0) (ap+ α p1)) (& hids (α x1)) (& hids (α a)) (& apσ-gluel f p0 p1) (& apσ-gluel g p0 p1)
ap+σ-gluel α {a = a} idp idp = ap+σ-gluel-lemma (α a)  where
  ap+σ-gluel-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& σ-gluel□' X (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+σ-gluel-lemma idp = idc

apσ-gluel-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& apσ-gluel (λ _ → y) p0 p1) ids (ap-cst y (& σ-gluel X p0 p1)) (& σ-gluel□ Y (ap-cst y p0) (ap-cst y p1)) ids ids)
apσ-gluel-cst = path-induction

σ-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → x1 == a)
σ-gluer = path-induction

apσ-gluer : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Square (ap (λ z → f z) (& σ-gluer X p0 p1)) (& σ-gluer Y (ap (λ z → f z) p0) (ap (λ z → f z) p1)) idp idp)
apσ-gluer = path-induction

σ-gluer□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) → Square (& σ-gluer X up0 up1) (& σ-gluer X vp0 vp1) x1 a)
σ-gluer□ = path-induction

ap/σ-gluer : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) → Cube (ap+ (λ x → & σ-gluer Y (p0 x) (p1 x)) r) (& σ-gluer□ Y (ap+ p0 r) (ap+ p1 r)) (& hids (& σ-gluer Y (p0 y) (p1 y))) (& hids (& σ-gluer Y (p0 z) (p1 z))) (& hids (ap x1 r)) (& hids (ap a r))
ap/σ-gluer {Y = Y} {y = y} idp p0 p1 = & ap/σ-gluer-lemma Y (p0 y) (p1 y)  where
  ap/σ-gluer-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& hids (& σ-gluer X p0 p1)) (& σ-gluer□ X (& hids p0) (& hids p1)) (& hids (& σ-gluer X p0 p1)) (& hids (& σ-gluer X p0 p1)) ids ids)
  ap/σ-gluer-lemma = path-induction

σ-gluer□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) → Square x1 a (& σ-gluer X up0 up1) (& σ-gluer X vp0 vp1))
σ-gluer□' = path-induction

ap+σ-gluer : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (ap+ α (& σ-gluer X p0 p1)) (& σ-gluer□' Y (ap+ α p0) (ap+ α p1)) (& hids (α x1)) (& hids (α a)) (& apσ-gluer f p0 p1) (& apσ-gluer g p0 p1)
ap+σ-gluer α {a = a} idp idp = ap+σ-gluer-lemma (α a)  where
  ap+σ-gluer-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& σ-gluer□' X (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+σ-gluer-lemma idp = idc

apσ-gluer-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& apσ-gluer (λ _ → y) p0 p1) ids (ap-cst y (& σ-gluer X p0 p1)) (& σ-gluer□ Y (ap-cst y p0) (ap-cst y p1)) ids ids)
apσ-gluer-cst = path-induction

σ : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → B ∧ A
σ A B = σ.f  module _ where

  module σ =
    SmashRec (λ a b → proj b a)
             pt
             (λ a → & σ-gluel (B ∧ A) (gluer pt) (gluer a))
             pt
             (λ b → & σ-gluer (B ∧ A) (gluel pt) (gluel b))



∧-map-gluel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → x2 == a)
∧-map-gluel = path-induction

ap∧-map-gluel : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → Square (ap (λ z → f z) (& ∧-map-gluel X p0 p1 p2)) (& ∧-map-gluel Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2)) idp idp)
ap∧-map-gluel = path-induction

∧-map-gluel□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) {ux2 : X} {up2 : ux2 == ux1} {vx2 : X} {vp2 : vx2 == vx1} {x2 : ux2 == vx2} (p2 : Square up2 vp2 x2 x1) → Square (& ∧-map-gluel X up0 up1 up2) (& ∧-map-gluel X vp0 vp1 vp2) x2 a)
∧-map-gluel□ = path-induction

ap/∧-map-gluel : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) {x2 : X → Y} (p2 : (x : X) → x2 x == x1 x) → Cube (ap+ (λ x → & ∧-map-gluel Y (p0 x) (p1 x) (p2 x)) r) (& ∧-map-gluel□ Y (ap+ p0 r) (ap+ p1 r) (ap+ p2 r)) (& hids (& ∧-map-gluel Y (p0 y) (p1 y) (p2 y))) (& hids (& ∧-map-gluel Y (p0 z) (p1 z) (p2 z))) (& hids (ap x2 r)) (& hids (ap a r))
ap/∧-map-gluel {Y = Y} {y = y} idp p0 p1 p2 = & ap/∧-map-gluel-lemma Y (p0 y) (p1 y) (p2 y)  where
  ap/∧-map-gluel-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → Cube (& hids (& ∧-map-gluel X p0 p1 p2)) (& ∧-map-gluel□ X (& hids p0) (& hids p1) (& hids p2)) (& hids (& ∧-map-gluel X p0 p1 p2)) (& hids (& ∧-map-gluel X p0 p1 p2)) ids ids)
  ap/∧-map-gluel-lemma = path-induction

∧-map-gluel□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) {ux2 : X} {up2 : ux2 == ux1} {vx2 : X} {vp2 : vx2 == vx1} {x2 : ux2 == vx2} (p2 : Square x2 x1 up2 vp2) → Square x2 a (& ∧-map-gluel X up0 up1 up2) (& ∧-map-gluel X vp0 vp1 vp2))
∧-map-gluel□' = path-induction

ap+∧-map-gluel : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → Cube (ap+ α (& ∧-map-gluel X p0 p1 p2)) (& ∧-map-gluel□' Y (ap+ α p0) (ap+ α p1) (ap+ α p2)) (& hids (α x2)) (& hids (α a)) (& ap∧-map-gluel f p0 p1 p2) (& ap∧-map-gluel g p0 p1 p2)
ap+∧-map-gluel α {a = a} idp idp idp = ap+∧-map-gluel-lemma (α a)  where
  ap+∧-map-gluel-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& ∧-map-gluel□' X (& hids p) (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+∧-map-gluel-lemma idp = idc

ap∧-map-gluel-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → Cube (& ap∧-map-gluel (λ _ → y) p0 p1 p2) ids (ap-cst y (& ∧-map-gluel X p0 p1 p2)) (& ∧-map-gluel□ Y (ap-cst y p0) (ap-cst y p1) (ap-cst y p2)) ids ids)
ap∧-map-gluel-cst = path-induction

∧-map-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → x2 == a)
∧-map-gluer = path-induction

ap∧-map-gluer : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → Square (ap (λ z → f z) (& ∧-map-gluer X p0 p1 p2)) (& ∧-map-gluer Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2)) idp idp)
ap∧-map-gluer = path-induction

∧-map-gluer□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) {ux2 : X} {up2 : ux2 == ux1} {vx2 : X} {vp2 : vx2 == vx1} {x2 : ux2 == vx2} (p2 : Square up2 vp2 x2 x1) → Square (& ∧-map-gluer X up0 up1 up2) (& ∧-map-gluer X vp0 vp1 vp2) x2 a)
∧-map-gluer□ = path-induction

ap/∧-map-gluer : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) {x2 : X → Y} (p2 : (x : X) → x2 x == x1 x) → Cube (ap+ (λ x → & ∧-map-gluer Y (p0 x) (p1 x) (p2 x)) r) (& ∧-map-gluer□ Y (ap+ p0 r) (ap+ p1 r) (ap+ p2 r)) (& hids (& ∧-map-gluer Y (p0 y) (p1 y) (p2 y))) (& hids (& ∧-map-gluer Y (p0 z) (p1 z) (p2 z))) (& hids (ap x2 r)) (& hids (ap a r))
ap/∧-map-gluer {Y = Y} {y = y} idp p0 p1 p2 = & ap/∧-map-gluer-lemma Y (p0 y) (p1 y) (p2 y)  where
  ap/∧-map-gluer-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → Cube (& hids (& ∧-map-gluer X p0 p1 p2)) (& ∧-map-gluer□ X (& hids p0) (& hids p1) (& hids p2)) (& hids (& ∧-map-gluer X p0 p1 p2)) (& hids (& ∧-map-gluer X p0 p1 p2)) ids ids)
  ap/∧-map-gluer-lemma = path-induction

∧-map-gluer□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) {ux2 : X} {up2 : ux2 == ux1} {vx2 : X} {vp2 : vx2 == vx1} {x2 : ux2 == vx2} (p2 : Square x2 x1 up2 vp2) → Square x2 a (& ∧-map-gluer X up0 up1 up2) (& ∧-map-gluer X vp0 vp1 vp2))
∧-map-gluer□' = path-induction

ap+∧-map-gluer : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → Cube (ap+ α (& ∧-map-gluer X p0 p1 p2)) (& ∧-map-gluer□' Y (ap+ α p0) (ap+ α p1) (ap+ α p2)) (& hids (α x2)) (& hids (α a)) (& ap∧-map-gluer f p0 p1 p2) (& ap∧-map-gluer g p0 p1 p2)
ap+∧-map-gluer α {a = a} idp idp idp = ap+∧-map-gluer-lemma (α a)  where
  ap+∧-map-gluer-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& ∧-map-gluer□' X (& hids p) (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+∧-map-gluer-lemma idp = idc

ap∧-map-gluer-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x2 == x1) → Cube (& ap∧-map-gluer (λ _ → y) p0 p1 p2) ids (ap-cst y (& ∧-map-gluer X p0 p1 p2)) (& ∧-map-gluer□ Y (ap-cst y p0) (ap-cst y p1) (ap-cst y p2)) ids ids)
ap∧-map-gluer-cst = path-induction

∧-map : (A : Type i) {{_ : Pointed A}} (A' : Type i) {{_ : Pointed A'}} (B : Type i) {{_ : Pointed B}} (B' : Type i) {{_ : Pointed B'}} (f : A → A') {{_ : PointedFun f}} (g : B → B') {{_ : PointedFun g}} (x : A ∧ B) → A' ∧ B'
∧-map A A' B B' f g = ∧-map.f  module _ where

  module ∧-map =
    SmashRec (λ a b → proj (f a) (g b))
             pt
             (λ a → & ∧-map-gluel (A' ∧ B') (gluel pt) (gluel (f a)) (ap (λ z → proj (f a) z) (ptf g)))
             pt
             (λ b → & ∧-map-gluer (A' ∧ B') (gluer pt) (gluer (g b)) (ap (λ z → proj z (g b)) (ptf f)))







∧-map-id-gluel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : x1 == a} (p2 : Square x2 (& ∧-map-gluel X p0 p1 idp) idp idp) {x3 : x1 == x0} (p3 : Square x3 p1 idp idp) → Square idp p0 x2 x3)
∧-map-id-gluel = path-induction

ap∧-map-id-gluel : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : x1 == a} (p2 : Square x2 (& ∧-map-gluel X p0 p1 idp) idp idp) {x3 : x1 == x0} (p3 : Square x3 p1 idp idp) → Cube (ap² f (& ∧-map-id-gluel X p0 p1 p2 p3)) (& ∧-map-id-gluel Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (& coh∙□ (ap² (λ z → f z) p2) (& ap∧-map-gluel f p0 p1 idp)) (ap² (λ z → f z) p3)) ids (& hids (ap f p0)) (& hids (ap f x2)) (& hids (ap f x3)))
ap∧-map-id-gluel = path-induction



∧-map-id-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : x1 == a} (p2 : Square x2 (& ∧-map-gluer X p0 p1 idp) idp idp) {x3 : x1 == x0} (p3 : Square x3 p1 idp idp) → Square idp p0 x2 x3)
∧-map-id-gluer = path-induction

ap∧-map-id-gluer : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : x1 == a} (p2 : Square x2 (& ∧-map-gluer X p0 p1 idp) idp idp) {x3 : x1 == x0} (p3 : Square x3 p1 idp idp) → Cube (ap² f (& ∧-map-id-gluer X p0 p1 p2 p3)) (& ∧-map-id-gluer Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (& coh∙□ (ap² (λ z → f z) p2) (& ap∧-map-gluer f p0 p1 idp)) (ap² (λ z → f z) p3)) ids (& hids (ap f p0)) (& hids (ap f x2)) (& hids (ap f x3)))
ap∧-map-id-gluer = path-induction

∧-map-id : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → ∧-map A A B B (λ y → y) (λ z → z) x == x
∧-map-id A B = ∧-map-id.f  module _ where

  module ∧-map-id =
    SmashElimId {g = λ x → ∧-map A A B B (λ y → y) (λ z → z) x}
                {h = λ x → x}
                (λ a b → idp)
                (gluel pt)
                (λ a → & ∧-map-id-gluel (A ∧ B) (gluel pt) (gluel a) (∧-map.gluel-β A A B B (λ y → y) (λ z → z) a) (ap-idf (gluel a)))
                (gluer pt)
                (λ b → & ∧-map-id-gluer (A ∧ B) (gluer pt) (gluer b) (∧-map.gluer-β A A B B (λ y → y) (λ z → z) b) (ap-idf (gluer b)))







σ-triangle-gluel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : a == a} (p2 : Square x2 (& σ-gluer X p0 p0) idp idp) {x3 : x1 == a} (p3 : Square x3 (& σ-gluer X p0 p1) idp idp) {x4 : x1 == a} (p4 : Square x4 (& σ-gluel X x2 x3) idp idp) {x5 : x1 == a} (p5 : Square x5 x4 idp idp) {x6 : x1 == a} (p6 : Square x6 x5 idp idp) {x7 : x1 == x0} (p7 : Square x7 p1 idp idp) → Square idp p0 x6 x7)
σ-triangle-gluel = path-induction

apσ-triangle-gluel : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : a == a} (p2 : Square x2 (& σ-gluer X p0 p0) idp idp) {x3 : x1 == a} (p3 : Square x3 (& σ-gluer X p0 p1) idp idp) {x4 : x1 == a} (p4 : Square x4 (& σ-gluel X x2 x3) idp idp) {x5 : x1 == a} (p5 : Square x5 x4 idp idp) {x6 : x1 == a} (p6 : Square x6 x5 idp idp) {x7 : x1 == x0} (p7 : Square x7 p1 idp idp) → Cube (ap² f (& σ-triangle-gluel X p0 p1 p2 p3 p4 p5 p6 p7)) (& σ-triangle-gluel Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (& coh∙□ (ap² (λ z → f z) p2) (& apσ-gluer f p0 p0)) (& coh∙□ (ap² (λ z → f z) p3) (& apσ-gluer f p0 p1)) (& coh∙□ (ap² (λ z → f z) p4) (& apσ-gluel f x2 x3)) (ap² (λ z → f z) p5) (ap² (λ z → f z) p6) (ap² (λ z → f z) p7)) ids (& hids (ap f p0)) (& hids (ap f x6)) (& hids (ap f x7)))
apσ-triangle-gluel = path-induction



σ-triangle-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : a == a} (p2 : Square x2 (& σ-gluel X p0 p0) idp idp) {x3 : x1 == a} (p3 : Square x3 (& σ-gluel X p0 p1) idp idp) {x4 : x1 == a} (p4 : Square x4 (& σ-gluer X x2 x3) idp idp) {x5 : x1 == a} (p5 : Square x5 x4 idp idp) {x6 : x1 == a} (p6 : Square x6 x5 idp idp) {x7 : x1 == x0} (p7 : Square x7 p1 idp idp) → Square idp p0 x6 x7)
σ-triangle-gluer = path-induction

apσ-triangle-gluer : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : a == a} (p2 : Square x2 (& σ-gluel X p0 p0) idp idp) {x3 : x1 == a} (p3 : Square x3 (& σ-gluel X p0 p1) idp idp) {x4 : x1 == a} (p4 : Square x4 (& σ-gluer X x2 x3) idp idp) {x5 : x1 == a} (p5 : Square x5 x4 idp idp) {x6 : x1 == a} (p6 : Square x6 x5 idp idp) {x7 : x1 == x0} (p7 : Square x7 p1 idp idp) → Cube (ap² f (& σ-triangle-gluer X p0 p1 p2 p3 p4 p5 p6 p7)) (& σ-triangle-gluer Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (& coh∙□ (ap² (λ z → f z) p2) (& apσ-gluel f p0 p0)) (& coh∙□ (ap² (λ z → f z) p3) (& apσ-gluel f p0 p1)) (& coh∙□ (ap² (λ z → f z) p4) (& apσ-gluer f x2 x3)) (ap² (λ z → f z) p5) (ap² (λ z → f z) p6) (ap² (λ z → f z) p7)) ids (& hids (ap f p0)) (& hids (ap f x6)) (& hids (ap f x7)))
apσ-triangle-gluer = path-induction

σ-triangle : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → σ B A (σ A B x) == x
σ-triangle A B = σ-triangle.f  module _ where

  module σ-triangle =
    SmashElimId {g = λ x → σ B A (σ A B x)}
                {h = λ x → x}
                (λ a b → idp)
                (gluel pt)
                (λ a → & σ-triangle-gluel (A ∧ B) (gluel pt) (gluel a) (σ.gluer-β B A pt) (σ.gluer-β B A a) (& apσ-gluel (λ x → σ B A x) (gluer pt) (gluer a)) (ap² (λ x → σ B A x) (σ.gluel-β A B a)) (ap-∘ (λ x → σ B A x) (σ A B) (gluel a)) (ap-idf (gluel a)))
                (gluer pt)
                (λ b → & σ-triangle-gluer (A ∧ B) (gluer pt) (gluer b) (σ.gluel-β B A pt) (σ.gluel-β B A b) (& apσ-gluer (λ x → σ B A x) (gluel pt) (gluel b)) (ap² (λ x → σ B A x) (σ.gluer-β A B b)) (ap-∘ (λ x → σ B A x) (σ A B) (gluer b)) (ap-idf (gluer b)))



α-proj-gluel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → x3 == a)
α-proj-gluel = path-induction

apα-proj-gluel : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Square (ap (λ z → f z) (& α-proj-gluel X p0 p1 p2 p3)) (& α-proj-gluel Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2) (ap (λ z → f z) p3)) idp idp)
apα-proj-gluel = path-induction

α-proj-gluel□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) {ux2 : X} {up2 : ux1 == ux2} {vx2 : X} {vp2 : vx1 == vx2} {x2 : ux2 == vx2} (p2 : Square up2 vp2 x1 x2) {ux3 : X} {up3 : ux3 == ux2} {vx3 : X} {vp3 : vx3 == vx2} {x3 : ux3 == vx3} (p3 : Square up3 vp3 x3 x2) → Square (& α-proj-gluel X up0 up1 up2 up3) (& α-proj-gluel X vp0 vp1 vp2 vp3) x3 a)
α-proj-gluel□ = path-induction

ap/α-proj-gluel : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) {x2 : X → Y} (p2 : (x : X) → x1 x == x2 x) {x3 : X → Y} (p3 : (x : X) → x3 x == x2 x) → Cube (ap+ (λ x → & α-proj-gluel Y (p0 x) (p1 x) (p2 x) (p3 x)) r) (& α-proj-gluel□ Y (ap+ p0 r) (ap+ p1 r) (ap+ p2 r) (ap+ p3 r)) (& hids (& α-proj-gluel Y (p0 y) (p1 y) (p2 y) (p3 y))) (& hids (& α-proj-gluel Y (p0 z) (p1 z) (p2 z) (p3 z))) (& hids (ap x3 r)) (& hids (ap a r))
ap/α-proj-gluel {Y = Y} {y = y} idp p0 p1 p2 p3 = & ap/α-proj-gluel-lemma Y (p0 y) (p1 y) (p2 y) (p3 y)  where
  ap/α-proj-gluel-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (& hids (& α-proj-gluel X p0 p1 p2 p3)) (& α-proj-gluel□ X (& hids p0) (& hids p1) (& hids p2) (& hids p3)) (& hids (& α-proj-gluel X p0 p1 p2 p3)) (& hids (& α-proj-gluel X p0 p1 p2 p3)) ids ids)
  ap/α-proj-gluel-lemma = path-induction

α-proj-gluel□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) {ux2 : X} {up2 : ux1 == ux2} {vx2 : X} {vp2 : vx1 == vx2} {x2 : ux2 == vx2} (p2 : Square x1 x2 up2 vp2) {ux3 : X} {up3 : ux3 == ux2} {vx3 : X} {vp3 : vx3 == vx2} {x3 : ux3 == vx3} (p3 : Square x3 x2 up3 vp3) → Square x3 a (& α-proj-gluel X up0 up1 up2 up3) (& α-proj-gluel X vp0 vp1 vp2 vp3))
α-proj-gluel□' = path-induction

ap+α-proj-gluel : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (ap+ α (& α-proj-gluel X p0 p1 p2 p3)) (& α-proj-gluel□' Y (ap+ α p0) (ap+ α p1) (ap+ α p2) (ap+ α p3)) (& hids (α x3)) (& hids (α a)) (& apα-proj-gluel f p0 p1 p2 p3) (& apα-proj-gluel g p0 p1 p2 p3)
ap+α-proj-gluel α {a = a} idp idp idp idp = ap+α-proj-gluel-lemma (α a)  where
  ap+α-proj-gluel-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& α-proj-gluel□' X (& hids p) (& hids p) (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+α-proj-gluel-lemma idp = idc

apα-proj-gluel-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (& apα-proj-gluel (λ _ → y) p0 p1 p2 p3) ids (ap-cst y (& α-proj-gluel X p0 p1 p2 p3)) (& α-proj-gluel□ Y (ap-cst y p0) (ap-cst y p1) (ap-cst y p2) (ap-cst y p3)) ids ids)
apα-proj-gluel-cst = path-induction

α-proj-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → x1 == a)
α-proj-gluer = path-induction

apα-proj-gluer : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Square (ap (λ z → f z) (& α-proj-gluer X p0 p1)) (& α-proj-gluer Y (ap (λ z → f z) p0) (ap (λ z → f z) p1)) idp idp)
apα-proj-gluer = path-induction

α-proj-gluer□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) → Square (& α-proj-gluer X up0 up1) (& α-proj-gluer X vp0 vp1) x1 a)
α-proj-gluer□ = path-induction

ap/α-proj-gluer : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) → Cube (ap+ (λ x → & α-proj-gluer Y (p0 x) (p1 x)) r) (& α-proj-gluer□ Y (ap+ p0 r) (ap+ p1 r)) (& hids (& α-proj-gluer Y (p0 y) (p1 y))) (& hids (& α-proj-gluer Y (p0 z) (p1 z))) (& hids (ap x1 r)) (& hids (ap a r))
ap/α-proj-gluer {Y = Y} {y = y} idp p0 p1 = & ap/α-proj-gluer-lemma Y (p0 y) (p1 y)  where
  ap/α-proj-gluer-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& hids (& α-proj-gluer X p0 p1)) (& α-proj-gluer□ X (& hids p0) (& hids p1)) (& hids (& α-proj-gluer X p0 p1)) (& hids (& α-proj-gluer X p0 p1)) ids ids)
  ap/α-proj-gluer-lemma = path-induction

α-proj-gluer□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) → Square x1 a (& α-proj-gluer X up0 up1) (& α-proj-gluer X vp0 vp1))
α-proj-gluer□' = path-induction

ap+α-proj-gluer : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (ap+ α (& α-proj-gluer X p0 p1)) (& α-proj-gluer□' Y (ap+ α p0) (ap+ α p1)) (& hids (α x1)) (& hids (α a)) (& apα-proj-gluer f p0 p1) (& apα-proj-gluer g p0 p1)
ap+α-proj-gluer α {a = a} idp idp = ap+α-proj-gluer-lemma (α a)  where
  ap+α-proj-gluer-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& α-proj-gluer□' X (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+α-proj-gluer-lemma idp = idc

apα-proj-gluer-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& apα-proj-gluer (λ _ → y) p0 p1) ids (ap-cst y (& α-proj-gluer X p0 p1)) (& α-proj-gluer□ Y (ap-cst y p0) (ap-cst y p1)) ids ids)
apα-proj-gluer-cst = path-induction

α-proj : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (c : C) (x : A ∧ B) → A ∧ (B ∧ C)
α-proj A B C c = α-proj.f  module _ where

  module α-proj =
    SmashRec (λ a b → proj a (proj b c))
             pt
             (λ a → & α-proj-gluel (A ∧ (B ∧ C)) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluer pt)) (ap (λ z → proj a z) (gluer c)))
             pt
             (λ b → & α-proj-gluer (A ∧ (B ∧ C)) (gluer (proj pt pt)) (gluer (proj b c)))


α-gluel-proj : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → x3 == a)
α-gluel-proj = path-induction

apα-gluel-proj : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Square (ap (λ z → f z) (& α-gluel-proj X p0 p1 p2 p3)) (& α-gluel-proj Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2) (ap (λ z → f z) p3)) idp idp)
apα-gluel-proj = path-induction

α-gluel-proj□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) {ux2 : X} {up2 : ux1 == ux2} {vx2 : X} {vp2 : vx1 == vx2} {x2 : ux2 == vx2} (p2 : Square up2 vp2 x1 x2) {ux3 : X} {up3 : ux3 == ux2} {vx3 : X} {vp3 : vx3 == vx2} {x3 : ux3 == vx3} (p3 : Square up3 vp3 x3 x2) → Square (& α-gluel-proj X up0 up1 up2 up3) (& α-gluel-proj X vp0 vp1 vp2 vp3) x3 a)
α-gluel-proj□ = path-induction

ap/α-gluel-proj : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) {x2 : X → Y} (p2 : (x : X) → x1 x == x2 x) {x3 : X → Y} (p3 : (x : X) → x3 x == x2 x) → Cube (ap+ (λ x → & α-gluel-proj Y (p0 x) (p1 x) (p2 x) (p3 x)) r) (& α-gluel-proj□ Y (ap+ p0 r) (ap+ p1 r) (ap+ p2 r) (ap+ p3 r)) (& hids (& α-gluel-proj Y (p0 y) (p1 y) (p2 y) (p3 y))) (& hids (& α-gluel-proj Y (p0 z) (p1 z) (p2 z) (p3 z))) (& hids (ap x3 r)) (& hids (ap a r))
ap/α-gluel-proj {Y = Y} {y = y} idp p0 p1 p2 p3 = & ap/α-gluel-proj-lemma Y (p0 y) (p1 y) (p2 y) (p3 y)  where
  ap/α-gluel-proj-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (& hids (& α-gluel-proj X p0 p1 p2 p3)) (& α-gluel-proj□ X (& hids p0) (& hids p1) (& hids p2) (& hids p3)) (& hids (& α-gluel-proj X p0 p1 p2 p3)) (& hids (& α-gluel-proj X p0 p1 p2 p3)) ids ids)
  ap/α-gluel-proj-lemma = path-induction

α-gluel-proj□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) {ux2 : X} {up2 : ux1 == ux2} {vx2 : X} {vp2 : vx1 == vx2} {x2 : ux2 == vx2} (p2 : Square x1 x2 up2 vp2) {ux3 : X} {up3 : ux3 == ux2} {vx3 : X} {vp3 : vx3 == vx2} {x3 : ux3 == vx3} (p3 : Square x3 x2 up3 vp3) → Square x3 a (& α-gluel-proj X up0 up1 up2 up3) (& α-gluel-proj X vp0 vp1 vp2 vp3))
α-gluel-proj□' = path-induction

ap+α-gluel-proj : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (ap+ α (& α-gluel-proj X p0 p1 p2 p3)) (& α-gluel-proj□' Y (ap+ α p0) (ap+ α p1) (ap+ α p2) (ap+ α p3)) (& hids (α x3)) (& hids (α a)) (& apα-gluel-proj f p0 p1 p2 p3) (& apα-gluel-proj g p0 p1 p2 p3)
ap+α-gluel-proj α {a = a} idp idp idp idp = ap+α-gluel-proj-lemma (α a)  where
  ap+α-gluel-proj-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& α-gluel-proj□' X (& hids p) (& hids p) (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+α-gluel-proj-lemma idp = idc

apα-gluel-proj-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (& apα-gluel-proj (λ _ → y) p0 p1 p2 p3) ids (ap-cst y (& α-gluel-proj X p0 p1 p2 p3)) (& α-gluel-proj□ Y (ap-cst y p0) (ap-cst y p1) (ap-cst y p2) (ap-cst y p3)) ids ids)
apα-gluel-proj-cst = path-induction





α-gluel-gluel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x1 == x3) {x4 : x1 == a} (p4 : Square x4 (& α-proj-gluel X p0 p1 p3 p3) idp idp) {x5 : a == a} (p5 : Square x5 idp idp idp) → Square (& α-gluel-proj X p0 p1 p2 p2) idp x4 x5)
α-gluel-gluel = path-induction

apα-gluel-gluel : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x1 == x3) {x4 : x1 == a} (p4 : Square x4 (& α-proj-gluel X p0 p1 p3 p3) idp idp) {x5 : a == a} (p5 : Square x5 idp idp idp) → Cube (ap² f (& α-gluel-gluel X p0 p1 p2 p3 p4 p5)) (& α-gluel-gluel Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2) (ap (λ z → f z) p3) (& coh∙□ (ap² (λ z → f z) p4) (& apα-proj-gluel f p0 p1 p3 p3)) (ap² (λ z → f z) p5)) (& apα-gluel-proj f p0 p1 p2 p2) ids (& hids (ap f x4)) (& hids (ap f x5)))
apα-gluel-gluel = path-induction



α-gluel-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : a == x2) {x3 : X} (p3 : x3 == x0) {x4 : x0 == x0} (p4 : Square x4 idp idp idp) {x5 : a == x3} (p5 : Square p0 p3 x5 x4) {x6 : x0 == x0} (p6 : Square x6 idp idp idp) {x7 : x1 == x3} (p7 : Square p1 p3 x7 x6) {x8 : x1 == a} (p8 : Square x8 (& α-proj-gluer X p0 p1) idp idp) {x9 : a == a} (p9 : Square x9 idp idp idp) → Square (& α-gluel-proj X p2 p2 x5 x7) idp x8 x9)
α-gluel-gluer = path-induction

apα-gluel-gluer : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : a == x2) {x3 : X} (p3 : x3 == x0) {x4 : x0 == x0} (p4 : Square x4 idp idp idp) {x5 : a == x3} (p5 : Square p0 p3 x5 x4) {x6 : x0 == x0} (p6 : Square x6 idp idp idp) {x7 : x1 == x3} (p7 : Square p1 p3 x7 x6) {x8 : x1 == a} (p8 : Square x8 (& α-proj-gluer X p0 p1) idp idp) {x9 : a == a} (p9 : Square x9 idp idp idp) → Cube (ap² f (& α-gluel-gluer X p0 p1 p2 p3 p4 p5 p6 p7 p8 p9)) (& α-gluel-gluer Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2) (ap (λ z → f z) p3) (ap² (λ z → f z) p4) (ap² (λ z → f z) p5) (ap² (λ z → f z) p6) (ap² (λ z → f z) p7) (& coh∙□ (ap² (λ z → f z) p8) (& apα-proj-gluer f p0 p1)) (ap² (λ z → f z) p9)) (& apα-gluel-proj f p2 p2 x5 x7) ids (& hids (ap f x8)) (& hids (ap f x9)))
apα-gluel-gluer = path-induction

α-gluel : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : A ∧ B) → α-proj A B C pt x == proj pt (proj pt pt)
α-gluel A B C = α-gluel.f  module _ where

  module α-gluel =
    SmashElimId {g = λ x → α-proj A B C pt x}
                {h = λ x → proj pt (proj pt pt)}
                (λ a b → & α-gluel-proj (A ∧ (B ∧ C)) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluel pt)) (ap (λ z → proj a z) (gluel b)))
                (idp)
                (λ a → & α-gluel-gluel (A ∧ (B ∧ C)) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluel pt)) (ap (λ z → proj a z) (gluer pt)) (α-proj.gluel-β A B C pt a) (ap-cst (proj pt (proj pt pt)) (gluel a)))
                (idp)
                (λ b → & α-gluel-gluer (A ∧ (B ∧ C)) (gluer (proj pt pt)) (gluer (proj b pt)) (gluel pt) (gluer basel) (ap-cst baser (gluel pt)) (ap+ (λ y → gluer y) (gluel pt)) (ap-cst baser (gluel b)) (ap+ (λ y → gluer y) (gluel b)) (α-proj.gluer-β A B C pt b) (ap-cst (proj pt (proj pt pt)) (gluer b)))



α-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → x1 == a)
α-gluer = path-induction

apα-gluer : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Square (ap (λ z → f z) (& α-gluer X p0 p1)) (& α-gluer Y (ap (λ z → f z) p0) (ap (λ z → f z) p1)) idp idp)
apα-gluer = path-induction

α-gluer□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) → Square (& α-gluer X up0 up1) (& α-gluer X vp0 vp1) x1 a)
α-gluer□ = path-induction

ap/α-gluer : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) → Cube (ap+ (λ x → & α-gluer Y (p0 x) (p1 x)) r) (& α-gluer□ Y (ap+ p0 r) (ap+ p1 r)) (& hids (& α-gluer Y (p0 y) (p1 y))) (& hids (& α-gluer Y (p0 z) (p1 z))) (& hids (ap x1 r)) (& hids (ap a r))
ap/α-gluer {Y = Y} {y = y} idp p0 p1 = & ap/α-gluer-lemma Y (p0 y) (p1 y)  where
  ap/α-gluer-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& hids (& α-gluer X p0 p1)) (& α-gluer□ X (& hids p0) (& hids p1)) (& hids (& α-gluer X p0 p1)) (& hids (& α-gluer X p0 p1)) ids ids)
  ap/α-gluer-lemma = path-induction

α-gluer□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) → Square x1 a (& α-gluer X up0 up1) (& α-gluer X vp0 vp1))
α-gluer□' = path-induction

ap+α-gluer : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (ap+ α (& α-gluer X p0 p1)) (& α-gluer□' Y (ap+ α p0) (ap+ α p1)) (& hids (α x1)) (& hids (α a)) (& apα-gluer f p0 p1) (& apα-gluer g p0 p1)
ap+α-gluer α {a = a} idp idp = ap+α-gluer-lemma (α a)  where
  ap+α-gluer-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& α-gluer□' X (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+α-gluer-lemma idp = idc

apα-gluer-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& apα-gluer (λ _ → y) p0 p1) ids (ap-cst y (& α-gluer X p0 p1)) (& α-gluer□ Y (ap-cst y p0) (ap-cst y p1)) ids ids)
apα-gluer-cst = path-induction

α : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : (A ∧ B) ∧ C) → A ∧ (B ∧ C)
α A B C = α.f  module _ where

  module α =
    SmashRec (λ x c → α-proj A B C c x) 
             pt
             (α-gluel A B C)
             pt
             (λ c → & α-gluer (A ∧ (B ∧ C)) (gluer (proj pt pt)) (gluer (proj pt c)))


α⁻¹-proj-gluel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → x1 == a)
α⁻¹-proj-gluel = path-induction

apα⁻¹-proj-gluel : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Square (ap (λ z → f z) (& α⁻¹-proj-gluel X p0 p1)) (& α⁻¹-proj-gluel Y (ap (λ z → f z) p0) (ap (λ z → f z) p1)) idp idp)
apα⁻¹-proj-gluel = path-induction

α⁻¹-proj-gluel□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) → Square (& α⁻¹-proj-gluel X up0 up1) (& α⁻¹-proj-gluel X vp0 vp1) x1 a)
α⁻¹-proj-gluel□ = path-induction

ap/α⁻¹-proj-gluel : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) → Cube (ap+ (λ x → & α⁻¹-proj-gluel Y (p0 x) (p1 x)) r) (& α⁻¹-proj-gluel□ Y (ap+ p0 r) (ap+ p1 r)) (& hids (& α⁻¹-proj-gluel Y (p0 y) (p1 y))) (& hids (& α⁻¹-proj-gluel Y (p0 z) (p1 z))) (& hids (ap x1 r)) (& hids (ap a r))
ap/α⁻¹-proj-gluel {Y = Y} {y = y} idp p0 p1 = & ap/α⁻¹-proj-gluel-lemma Y (p0 y) (p1 y)  where
  ap/α⁻¹-proj-gluel-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& hids (& α⁻¹-proj-gluel X p0 p1)) (& α⁻¹-proj-gluel□ X (& hids p0) (& hids p1)) (& hids (& α⁻¹-proj-gluel X p0 p1)) (& hids (& α⁻¹-proj-gluel X p0 p1)) ids ids)
  ap/α⁻¹-proj-gluel-lemma = path-induction

α⁻¹-proj-gluel□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) → Square x1 a (& α⁻¹-proj-gluel X up0 up1) (& α⁻¹-proj-gluel X vp0 vp1))
α⁻¹-proj-gluel□' = path-induction

ap+α⁻¹-proj-gluel : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (ap+ α (& α⁻¹-proj-gluel X p0 p1)) (& α⁻¹-proj-gluel□' Y (ap+ α p0) (ap+ α p1)) (& hids (α x1)) (& hids (α a)) (& apα⁻¹-proj-gluel f p0 p1) (& apα⁻¹-proj-gluel g p0 p1)
ap+α⁻¹-proj-gluel α {a = a} idp idp = ap+α⁻¹-proj-gluel-lemma (α a)  where
  ap+α⁻¹-proj-gluel-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& α⁻¹-proj-gluel□' X (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+α⁻¹-proj-gluel-lemma idp = idc

apα⁻¹-proj-gluel-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& apα⁻¹-proj-gluel (λ _ → y) p0 p1) ids (ap-cst y (& α⁻¹-proj-gluel X p0 p1)) (& α⁻¹-proj-gluel□ Y (ap-cst y p0) (ap-cst y p1)) ids ids)
apα⁻¹-proj-gluel-cst = path-induction

α⁻¹-proj-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → x3 == a)
α⁻¹-proj-gluer = path-induction

apα⁻¹-proj-gluer : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Square (ap (λ z → f z) (& α⁻¹-proj-gluer X p0 p1 p2 p3)) (& α⁻¹-proj-gluer Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2) (ap (λ z → f z) p3)) idp idp)
apα⁻¹-proj-gluer = path-induction

α⁻¹-proj-gluer□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) {ux2 : X} {up2 : ux1 == ux2} {vx2 : X} {vp2 : vx1 == vx2} {x2 : ux2 == vx2} (p2 : Square up2 vp2 x1 x2) {ux3 : X} {up3 : ux3 == ux2} {vx3 : X} {vp3 : vx3 == vx2} {x3 : ux3 == vx3} (p3 : Square up3 vp3 x3 x2) → Square (& α⁻¹-proj-gluer X up0 up1 up2 up3) (& α⁻¹-proj-gluer X vp0 vp1 vp2 vp3) x3 a)
α⁻¹-proj-gluer□ = path-induction

ap/α⁻¹-proj-gluer : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) {x2 : X → Y} (p2 : (x : X) → x1 x == x2 x) {x3 : X → Y} (p3 : (x : X) → x3 x == x2 x) → Cube (ap+ (λ x → & α⁻¹-proj-gluer Y (p0 x) (p1 x) (p2 x) (p3 x)) r) (& α⁻¹-proj-gluer□ Y (ap+ p0 r) (ap+ p1 r) (ap+ p2 r) (ap+ p3 r)) (& hids (& α⁻¹-proj-gluer Y (p0 y) (p1 y) (p2 y) (p3 y))) (& hids (& α⁻¹-proj-gluer Y (p0 z) (p1 z) (p2 z) (p3 z))) (& hids (ap x3 r)) (& hids (ap a r))
ap/α⁻¹-proj-gluer {Y = Y} {y = y} idp p0 p1 p2 p3 = & ap/α⁻¹-proj-gluer-lemma Y (p0 y) (p1 y) (p2 y) (p3 y)  where
  ap/α⁻¹-proj-gluer-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (& hids (& α⁻¹-proj-gluer X p0 p1 p2 p3)) (& α⁻¹-proj-gluer□ X (& hids p0) (& hids p1) (& hids p2) (& hids p3)) (& hids (& α⁻¹-proj-gluer X p0 p1 p2 p3)) (& hids (& α⁻¹-proj-gluer X p0 p1 p2 p3)) ids ids)
  ap/α⁻¹-proj-gluer-lemma = path-induction

α⁻¹-proj-gluer□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) {ux2 : X} {up2 : ux1 == ux2} {vx2 : X} {vp2 : vx1 == vx2} {x2 : ux2 == vx2} (p2 : Square x1 x2 up2 vp2) {ux3 : X} {up3 : ux3 == ux2} {vx3 : X} {vp3 : vx3 == vx2} {x3 : ux3 == vx3} (p3 : Square x3 x2 up3 vp3) → Square x3 a (& α⁻¹-proj-gluer X up0 up1 up2 up3) (& α⁻¹-proj-gluer X vp0 vp1 vp2 vp3))
α⁻¹-proj-gluer□' = path-induction

ap+α⁻¹-proj-gluer : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (ap+ α (& α⁻¹-proj-gluer X p0 p1 p2 p3)) (& α⁻¹-proj-gluer□' Y (ap+ α p0) (ap+ α p1) (ap+ α p2) (ap+ α p3)) (& hids (α x3)) (& hids (α a)) (& apα⁻¹-proj-gluer f p0 p1 p2 p3) (& apα⁻¹-proj-gluer g p0 p1 p2 p3)
ap+α⁻¹-proj-gluer α {a = a} idp idp idp idp = ap+α⁻¹-proj-gluer-lemma (α a)  where
  ap+α⁻¹-proj-gluer-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& α⁻¹-proj-gluer□' X (& hids p) (& hids p) (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+α⁻¹-proj-gluer-lemma idp = idc

apα⁻¹-proj-gluer-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (& apα⁻¹-proj-gluer (λ _ → y) p0 p1 p2 p3) ids (ap-cst y (& α⁻¹-proj-gluer X p0 p1 p2 p3)) (& α⁻¹-proj-gluer□ Y (ap-cst y p0) (ap-cst y p1) (ap-cst y p2) (ap-cst y p3)) ids ids)
apα⁻¹-proj-gluer-cst = path-induction

α⁻¹-proj : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (a : A) (x : B ∧ C) → (A ∧ B) ∧ C
α⁻¹-proj A B C a = α⁻¹-proj.f  module _ where

  module α⁻¹-proj =
    SmashRec (λ b c → proj (proj a b) c)
             pt
             (λ b → & α⁻¹-proj-gluel ((A ∧ B) ∧ C) (gluel (proj pt pt)) (gluel (proj a b)))
             pt
             (λ c → & α⁻¹-proj-gluer ((A ∧ B) ∧ C) (gluer pt) (gluer c) (ap (λ z → proj z c) (gluel pt)) (ap (λ z → proj z c) (gluel a)))


α⁻¹-gluel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → x1 == a)
α⁻¹-gluel = path-induction

apα⁻¹-gluel : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Square (ap (λ z → f z) (& α⁻¹-gluel X p0 p1)) (& α⁻¹-gluel Y (ap (λ z → f z) p0) (ap (λ z → f z) p1)) idp idp)
apα⁻¹-gluel = path-induction

α⁻¹-gluel□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) → Square (& α⁻¹-gluel X up0 up1) (& α⁻¹-gluel X vp0 vp1) x1 a)
α⁻¹-gluel□ = path-induction

ap/α⁻¹-gluel : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) → Cube (ap+ (λ x → & α⁻¹-gluel Y (p0 x) (p1 x)) r) (& α⁻¹-gluel□ Y (ap+ p0 r) (ap+ p1 r)) (& hids (& α⁻¹-gluel Y (p0 y) (p1 y))) (& hids (& α⁻¹-gluel Y (p0 z) (p1 z))) (& hids (ap x1 r)) (& hids (ap a r))
ap/α⁻¹-gluel {Y = Y} {y = y} idp p0 p1 = & ap/α⁻¹-gluel-lemma Y (p0 y) (p1 y)  where
  ap/α⁻¹-gluel-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& hids (& α⁻¹-gluel X p0 p1)) (& α⁻¹-gluel□ X (& hids p0) (& hids p1)) (& hids (& α⁻¹-gluel X p0 p1)) (& hids (& α⁻¹-gluel X p0 p1)) ids ids)
  ap/α⁻¹-gluel-lemma = path-induction

α⁻¹-gluel□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) → Square x1 a (& α⁻¹-gluel X up0 up1) (& α⁻¹-gluel X vp0 vp1))
α⁻¹-gluel□' = path-induction

ap+α⁻¹-gluel : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (ap+ α (& α⁻¹-gluel X p0 p1)) (& α⁻¹-gluel□' Y (ap+ α p0) (ap+ α p1)) (& hids (α x1)) (& hids (α a)) (& apα⁻¹-gluel f p0 p1) (& apα⁻¹-gluel g p0 p1)
ap+α⁻¹-gluel α {a = a} idp idp = ap+α⁻¹-gluel-lemma (α a)  where
  ap+α⁻¹-gluel-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& α⁻¹-gluel□' X (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+α⁻¹-gluel-lemma idp = idc

apα⁻¹-gluel-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) → Cube (& apα⁻¹-gluel (λ _ → y) p0 p1) ids (ap-cst y (& α⁻¹-gluel X p0 p1)) (& α⁻¹-gluel□ Y (ap-cst y p0) (ap-cst y p1)) ids ids)
apα⁻¹-gluel-cst = path-induction

α⁻¹-gluer-proj : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → x3 == a)
α⁻¹-gluer-proj = path-induction

apα⁻¹-gluer-proj : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Square (ap (λ z → f z) (& α⁻¹-gluer-proj X p0 p1 p2 p3)) (& α⁻¹-gluer-proj Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2) (ap (λ z → f z) p3)) idp idp)
apα⁻¹-gluer-proj = path-induction

α⁻¹-gluer-proj□ : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square up0 vp0 a x0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square up1 vp1 x1 x0) {ux2 : X} {up2 : ux1 == ux2} {vx2 : X} {vp2 : vx1 == vx2} {x2 : ux2 == vx2} (p2 : Square up2 vp2 x1 x2) {ux3 : X} {up3 : ux3 == ux2} {vx3 : X} {vp3 : vx3 == vx2} {x3 : ux3 == vx3} (p3 : Square up3 vp3 x3 x2) → Square (& α⁻¹-gluer-proj X up0 up1 up2 up3) (& α⁻¹-gluer-proj X vp0 vp1 vp2 vp3) x3 a)
α⁻¹-gluer-proj□ = path-induction

ap/α⁻¹-gluer-proj : {X : Type i} {Y : Type i} {y : X} {z : X} (r : y == z) {a : X → Y} {x0 : X → Y} (p0 : (x : X) → a x == x0 x) {x1 : X → Y} (p1 : (x : X) → x1 x == x0 x) {x2 : X → Y} (p2 : (x : X) → x1 x == x2 x) {x3 : X → Y} (p3 : (x : X) → x3 x == x2 x) → Cube (ap+ (λ x → & α⁻¹-gluer-proj Y (p0 x) (p1 x) (p2 x) (p3 x)) r) (& α⁻¹-gluer-proj□ Y (ap+ p0 r) (ap+ p1 r) (ap+ p2 r) (ap+ p3 r)) (& hids (& α⁻¹-gluer-proj Y (p0 y) (p1 y) (p2 y) (p3 y))) (& hids (& α⁻¹-gluer-proj Y (p0 z) (p1 z) (p2 z) (p3 z))) (& hids (ap x3 r)) (& hids (ap a r))
ap/α⁻¹-gluer-proj {Y = Y} {y = y} idp p0 p1 p2 p3 = & ap/α⁻¹-gluer-proj-lemma Y (p0 y) (p1 y) (p2 y) (p3 y)  where
  ap/α⁻¹-gluer-proj-lemma : Coh((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (& hids (& α⁻¹-gluer-proj X p0 p1 p2 p3)) (& α⁻¹-gluer-proj□ X (& hids p0) (& hids p1) (& hids p2) (& hids p3)) (& hids (& α⁻¹-gluer-proj X p0 p1 p2 p3)) (& hids (& α⁻¹-gluer-proj X p0 p1 p2 p3)) ids ids)
  ap/α⁻¹-gluer-proj-lemma = path-induction

α⁻¹-gluer-proj□' : Coh ((X : Type i) {ua : X} {va : X} {a : ua == va} {ux0 : X} {up0 : ua == ux0} {vx0 : X} {vp0 : va == vx0} {x0 : ux0 == vx0} (p0 : Square a x0 up0 vp0) {ux1 : X} {up1 : ux1 == ux0} {vx1 : X} {vp1 : vx1 == vx0} {x1 : ux1 == vx1} (p1 : Square x1 x0 up1 vp1) {ux2 : X} {up2 : ux1 == ux2} {vx2 : X} {vp2 : vx1 == vx2} {x2 : ux2 == vx2} (p2 : Square x1 x2 up2 vp2) {ux3 : X} {up3 : ux3 == ux2} {vx3 : X} {vp3 : vx3 == vx2} {x3 : ux3 == vx3} (p3 : Square x3 x2 up3 vp3) → Square x3 a (& α⁻¹-gluer-proj X up0 up1 up2 up3) (& α⁻¹-gluer-proj X vp0 vp1 vp2 vp3))
α⁻¹-gluer-proj□' = path-induction

ap+α⁻¹-gluer-proj : {X : Type i} {Y : Type i} {f : X → Y} {g : X → Y} (α : (x : X) → f x == g x) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (ap+ α (& α⁻¹-gluer-proj X p0 p1 p2 p3)) (& α⁻¹-gluer-proj□' Y (ap+ α p0) (ap+ α p1) (ap+ α p2) (ap+ α p3)) (& hids (α x3)) (& hids (α a)) (& apα⁻¹-gluer-proj f p0 p1 p2 p3) (& apα⁻¹-gluer-proj g p0 p1 p2 p3)
ap+α⁻¹-gluer-proj α {a = a} idp idp idp idp = ap+α⁻¹-gluer-proj-lemma (α a)  where
  ap+α⁻¹-gluer-proj-lemma : {X : Type i} {a b : X} (p : a == b) → Cube (& hids p) (& α⁻¹-gluer-proj□' X (& hids p) (& hids p) (& hids p) (& hids p)) (& hids p) (& hids p) ids ids
  ap+α⁻¹-gluer-proj-lemma idp = idc

apα⁻¹-gluer-proj-cst : Coh ({X : Type i} {Y : Type i} (y : Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) → Cube (& apα⁻¹-gluer-proj (λ _ → y) p0 p1 p2 p3) ids (ap-cst y (& α⁻¹-gluer-proj X p0 p1 p2 p3)) (& α⁻¹-gluer-proj□ Y (ap-cst y p0) (ap-cst y p1) (ap-cst y p2) (ap-cst y p3)) ids ids)
apα⁻¹-gluer-proj-cst = path-induction





α⁻¹-gluer-gluel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : a == x2) {x3 : X} (p3 : x3 == x0) {x4 : x0 == x0} (p4 : Square x4 idp idp idp) {x5 : a == x3} (p5 : Square p0 p3 x5 x4) {x6 : x0 == x0} (p6 : Square x6 idp idp idp) {x7 : x1 == x3} (p7 : Square p1 p3 x7 x6) {x8 : x1 == a} (p8 : Square x8 (& α⁻¹-proj-gluel X p0 p1) idp idp) {x9 : a == a} (p9 : Square x9 idp idp idp) → Square (& α⁻¹-gluer-proj X p2 p2 x5 x7) idp x8 x9)
α⁻¹-gluer-gluel = path-induction

apα⁻¹-gluer-gluel : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : a == x2) {x3 : X} (p3 : x3 == x0) {x4 : x0 == x0} (p4 : Square x4 idp idp idp) {x5 : a == x3} (p5 : Square p0 p3 x5 x4) {x6 : x0 == x0} (p6 : Square x6 idp idp idp) {x7 : x1 == x3} (p7 : Square p1 p3 x7 x6) {x8 : x1 == a} (p8 : Square x8 (& α⁻¹-proj-gluel X p0 p1) idp idp) {x9 : a == a} (p9 : Square x9 idp idp idp) → Cube (ap² f (& α⁻¹-gluer-gluel X p0 p1 p2 p3 p4 p5 p6 p7 p8 p9)) (& α⁻¹-gluer-gluel Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2) (ap (λ z → f z) p3) (ap² (λ z → f z) p4) (ap² (λ z → f z) p5) (ap² (λ z → f z) p6) (ap² (λ z → f z) p7) (& coh∙□ (ap² (λ z → f z) p8) (& apα⁻¹-proj-gluel f p0 p1)) (ap² (λ z → f z) p9)) (& apα⁻¹-gluer-proj f p2 p2 x5 x7) ids (& hids (ap f x8)) (& hids (ap f x9)))
apα⁻¹-gluer-gluel = path-induction



α⁻¹-gluer-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x1 == x3) {x4 : x1 == a} (p4 : Square x4 (& α⁻¹-proj-gluer X p0 p1 p3 p3) idp idp) {x5 : a == a} (p5 : Square x5 idp idp idp) → Square (& α⁻¹-gluer-proj X p0 p1 p2 p2) idp x4 x5)
α⁻¹-gluer-gluer = path-induction

apα⁻¹-gluer-gluer : Coh ({X : Type i} {Y : Type i} (f : X → Y) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x1 == x3) {x4 : x1 == a} (p4 : Square x4 (& α⁻¹-proj-gluer X p0 p1 p3 p3) idp idp) {x5 : a == a} (p5 : Square x5 idp idp idp) → Cube (ap² f (& α⁻¹-gluer-gluer X p0 p1 p2 p3 p4 p5)) (& α⁻¹-gluer-gluer Y (ap (λ z → f z) p0) (ap (λ z → f z) p1) (ap (λ z → f z) p2) (ap (λ z → f z) p3) (& coh∙□ (ap² (λ z → f z) p4) (& apα⁻¹-proj-gluer f p0 p1 p3 p3)) (ap² (λ z → f z) p5)) (& apα⁻¹-gluer-proj f p0 p1 p2 p2) ids (& hids (ap f x4)) (& hids (ap f x5)))
apα⁻¹-gluer-gluer = path-induction

α⁻¹-gluer : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : B ∧ C) → α⁻¹-proj A B C pt x == proj (proj pt pt) pt
α⁻¹-gluer A B C = α⁻¹-gluer.f  module _ where

  module α⁻¹-gluer =
    SmashElimId {g = λ x → α⁻¹-proj A B C pt x}
                {h = λ x → proj (proj pt pt) pt}
                (λ b c → & α⁻¹-gluer-proj ((A ∧ B) ∧ C) (gluer pt) (gluer c) (ap (λ z → proj z c) (gluer pt)) (ap (λ z → proj z c) (gluer b)))
                (idp)
                (λ b → & α⁻¹-gluer-gluel ((A ∧ B) ∧ C) (gluel (proj pt pt)) (gluel (proj pt b)) (gluer pt) (gluel baser) (ap-cst basel (gluer pt)) (ap+ (λ x → gluel x) (gluer pt)) (ap-cst basel (gluer b)) (ap+ (λ x → gluel x) (gluer b)) (α⁻¹-proj.gluel-β A B C pt b) (ap-cst (proj (proj pt pt) pt) (gluel b)))
                (idp)
                (λ c → & α⁻¹-gluer-gluer ((A ∧ B) ∧ C) (gluer pt) (gluer c) (ap (λ z → proj z c) (gluer pt)) (ap (λ z → proj z c) (gluel pt)) (α⁻¹-proj.gluer-β A B C pt c) (ap-cst (proj (proj pt pt) pt) (gluer c)))



α⁻¹ : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : A ∧ (B ∧ C)) → (A ∧ B) ∧ C
α⁻¹ A B C = α⁻¹.f  module _ where

 module α⁻¹ =
     SmashRec (λ a → α⁻¹-proj A B C a)
             pt
             (λ a → & α⁻¹-gluel ((A ∧ B) ∧ C) (gluel (proj pt pt)) (gluel (proj a pt)))
             pt
             (α⁻¹-gluer A B C)


instance
  σ-ptf : {A : Type i} {{_ : Pointed A}} {B : Type i} {{_ : Pointed B}} → PointedFun (σ A B)
  PointedFun.ptf σ-ptf = idp

  ∧-map-ptf : {A : Type i} {{_ : Pointed A}} {A' : Type i} {{_ : Pointed A'}} {B : Type i} {{_ : Pointed B}} {B' : Type i} {{_ : Pointed B'}} {f : A → A'} {{_ : PointedFun f}} {g : B → B'} {{_ : PointedFun g}}
            → PointedFun (∧-map A A' B B' f g)
  PointedFun.ptf (∧-map-ptf {f = f} {g = g}) = & coh∙ (ap (proj (f pt)) (ptf g)) (ap (λ z → proj z pt) (ptf f))

  α-ptf : {A : Type i} {{_ : Pointed A}} {B : Type i} {{_ : Pointed B}} {C : Type i} {{_ : Pointed C}}
            → PointedFun (α A B C)
  PointedFun.ptf α-ptf = idp

  α⁻¹-ptf : {A : Type i} {{_ : Pointed A}} {B : Type i} {{_ : Pointed B}} {C : Type i} {{_ : Pointed C}}
            → PointedFun (α⁻¹ A B C)
  PointedFun.ptf α⁻¹-ptf = idp

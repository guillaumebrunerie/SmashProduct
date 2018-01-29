{-# OPTIONS --without-K --rewriting #-}

open import SmashDefs

module Smash {i : ULevel} where

idsmash-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) → x2 == a
idsmash-coh1 X a _ idp _ idp = idp

idsmash-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x2 : X) (p2 : x2 == x0) → x2 == a
idsmash-coh2 X a _ idp _ idp = idp

apidsmash-coh1 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x1 : X} {p1 : a == x1} {fp1 : f a == f x1} (fp1= : ap f p1 == fp1) {x2 : X} {p2 : x2 == x1} {fp2 : f x2 == f x1} (fp2= : ap f p2 == fp2) → ap f (idsmash-coh1 X a x1 p1 x2 p2) == idsmash-coh1 Y (f a) (f x1) fp1 (f x2) fp2
apidsmash-coh1 {p1 = idp} idp {p2 = idp} idp = idp

apidsmash-coh2 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x0 : X} {p0 : a == x0} {fp0 : f a == f x0} (fp0= : ap f p0 == fp0) {x2 : X} {p2 : x2 == x0} {fp2 : f x2 == f x0} (fp2= : ap f p2 == fp2) → ap f (idsmash-coh2 X a x0 p0 x2 p2) == idsmash-coh2 Y (f a) (f x0) fp0 (f x2) fp2
apidsmash-coh2 {p0 = idp} idp {p2 = idp} idp = idp

idsmash : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → A ∧ B
idsmash A B =
  Smash-rec (λ a b → proj a b)
            pt
            (λ a → idsmash-coh1 (A ∧ B) (proj pt pt) basel (gluel pt) (proj a pt) (gluel a))
            pt
            (λ b → idsmash-coh2 (A ∧ B) (proj pt pt) baser (gluer pt) (proj pt b) (gluer b))


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


∧-map-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x5 : X) (p5 : x5 == x1) (x6 : X) (p6 : x6 == x5) → x6 == a
∧-map-coh1 X a _ idp _ idp _ idp = idp

∧-map-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x8 : X) (p8 : x8 == x0) (x9 : X) (p9 : x9 == x8) → x9 == a
∧-map-coh2 X a _ idp _ idp _ idp = idp

ap∧-map-coh1 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x1 : X} {p1 : a == x1} {fp1 : f a == f x1} (fp1= : ap f p1 == fp1) {x5 : X} {p5 : x5 == x1} {fp5 : f x5 == f x1} (fp5= : ap f p5 == fp5) {x6 : X} {p6 : x6 == x5} {fp6 : f x6 == f x5} (fp6= : ap f p6 == fp6) → ap f (∧-map-coh1 X a x1 p1 x5 p5 x6 p6) == ∧-map-coh1 Y (f a) (f x1) fp1 (f x5) fp5 (f x6) fp6
ap∧-map-coh1 {p1 = idp} idp {p5 = idp} idp {p6 = idp} idp = idp

ap∧-map-coh2 : {X : Type i} {Y : Type i} {f : X → Y} {a : X} {x0 : X} {p0 : a == x0} {fp0 : f a == f x0} (fp0= : ap f p0 == fp0) {x8 : X} {p8 : x8 == x0} {fp8 : f x8 == f x0} (fp8= : ap f p8 == fp8) {x9 : X} {p9 : x9 == x8} {fp9 : f x9 == f x8} (fp9= : ap f p9 == fp9) → ap f (∧-map-coh2 X a x0 p0 x8 p8 x9 p9) == ∧-map-coh2 Y (f a) (f x0) fp0 (f x8) fp8 (f x9) fp9
ap∧-map-coh2 {p0 = idp} idp {p8 = idp} idp {p9 = idp} idp = idp

∧-map : (A : Type i) {{_ : Pointed A}} (A' : Type i) {{_ : Pointed A'}} (B : Type i) {{_ : Pointed B}} (B' : Type i) {{_ : Pointed B'}} (f : A → A') {{_ : PointedFun f}} (g : B → B') {{_ : PointedFun g}} (x : A ∧ B) → A' ∧ B'
∧-map A A' B B' f g =
  Smash-rec (λ a b → proj (f a) (g b))
            pt
            (λ a → ∧-map-coh1 (A' ∧ B') (proj pt pt) basel (gluel pt) (proj (f a) pt) (gluel (f a)) (proj (f a) (g pt)) (ap (λ z → proj (f a) z) (ptf g)))
            pt
            (λ b → ∧-map-coh2 (A' ∧ B') (proj pt pt) baser (gluer pt) (proj pt (g b)) (gluer (g b)) (proj (f pt) (g b)) (ap (λ z → proj z (g b)) (ptf f)))

{-
<WORKS

α-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x5 : X) (p5 : x5 == x1) (x6 : X) (p6 : x5 == x6) (x8 : X) (p8 : x8 == x6) → x8 == a
α-coh1 X a _ idp _ idp _ idp _ idp = idp

α-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x6 : X) (p6 : x6 == x0) → x6 == a
α-coh2 X a _ idp _ idp = idp

α-coh3 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x5 : X) (p5 : x5 == x1) (x7 : X) (p7 : x5 == x7) (x8 : X) (p8 : x8 == x7) → x8 == a
α-coh3 X a _ idp _ idp _ idp _ idp = idp

α-coh4 : (X : Type i) (a : X) (x2 : X) (p2 : a == x2) (x4 : X) (p4 : x4 == x2) → x4 == a
α-coh4 X a _ idp _ idp = idp

α-coh5 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x4 : X) (p4 : x4 == x1) (x5 : X) (p5 : x4 == x5) (x6 : X) (p6 : x4 == x6) → α-coh3 X a x1 p1 x4 p4 x6 p6 x4 p6 == α-coh1 X a x1 p1 x4 p4 x5 p5 x4 p5
α-coh5 X a _ idp _ idp _ idp _ idp = idp

α-coh6 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x1 : X) (p1 : a == x1) (x3 : X) (p3 : a == x3) (x4 : X) (p4 : x4 == x3) (x6 : x3 == x0) (p6 : x6 == coh!∙ p3 p0) (x7 : x4 == x0) (p7 : x7 == coh∙ p4 x6) → α-coh3 X a x1 p1 a p1 x3 p3 x4 p4 == α-coh2 X a x0 p0 x4 x7
α-coh6 X a _ idp _ idp _ idp _ idp _ idp _ idp = idp

α-aux1 : (A B C : Type i) {{_ : Pointed A}} {{_ : Pointed B}} {{_ : Pointed C}} (c : C) (x : A ∧ B) → A ∧ (B ∧ C)
α-aux1 A B C c =
  Smash-rec (λ a b → proj a (proj b c))
            pt
            (λ a → α-coh1 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) basel (gluel pt) (proj a (proj pt pt)) (gluel a) (proj a baser) (ap (λ z → proj a z) (gluer pt)) (proj a (proj pt c)) (ap (λ z → proj a z) (gluer c)))
            pt
            (λ b → α-coh2 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) baser (gluer (proj pt pt)) (proj pt (proj b c)) (gluer (proj b c)))

α-aux2 : (A B C : Type i) {{_ : Pointed A}} {{_ : Pointed B}} {{_ : Pointed C}} (x : A ∧ B) → α-aux1 A B C pt x == pt
α-aux2 A B C =
  Smash-elim (λ a b → α-coh3 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) basel (gluel pt) (proj a (proj pt pt)) (gluel a) (proj a basel) (ap (λ z → proj a z) (gluel pt)) (proj a (proj b pt)) (ap (λ z → proj a z) (gluel b)))
             idp
             (λ a → ↓-=cst-in (complicated-coh (gluel-β' a) (α-coh5 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) basel (gluel pt) (proj a (proj pt pt)) (gluel a) (proj a baser) (ap (λ z → proj a z) (gluer pt)) (proj a basel) (ap (λ z → proj a z) (gluel pt)))))
             idp
             (λ b → ↓-=cst-in (complicated-coh (gluer-β' b) (α-coh6 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) baser (gluer (proj pt pt)) basel (gluel pt) (proj pt basel) (ap (λ z → proj pt z) (gluel pt)) (proj pt (proj b pt)) (ap (λ z → proj pt z) (gluel b)) (gluer basel) (coh-purple (ap (λ x → proj pt x) (gluel pt)) (purple (gluel pt))) (gluer (proj b pt)) (purple (gluel b)))))

α : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : (A ∧ B) ∧ C) → A ∧ (B ∧ C)
α A B C =
  Smash-rec (λ x c → α-aux1 A B C c x)
            pt
            (α-aux2 A B C)
            pt
            (λ c → α-coh4 (A ∧ (B ∧ C)) (proj pt (proj pt pt)) (proj pt baser) (ap (λ z → proj pt z) (gluer pt)) (proj pt (proj pt c)) (ap (λ z → proj pt z) (gluer c)))


β-coh1 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x8 : X) (p8 : x8 == x0) (x10 : X) (p10 : x8 == x10) (x11 : X) (p11 : x11 == x10) → x11 == a
β-coh1 X a _ idp _ idp _ idp _ idp = idp

β-coh2 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x4 : X) (p4 : x4 == x1) → x4 == a
β-coh2 X a _ idp _ idp = idp

β-coh3 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x8 : X) (p8 : x8 == x0) (x9 : X) (p9 : x8 == x9) (x11 : X) (p11 : x11 == x9) → x11 == a
β-coh3 X a _ idp _ idp _ idp _ idp = idp

β-coh4 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x4 : X) (p4 : x4 == x1) → x4 == a
β-coh4 X a _ idp _ idp = idp

β-coh5 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x6 : X) (p6 : x6 == x0) (x7 : X) (p7 : x6 == x7) (x8 : X) (p8 : x6 == x8) → β-coh3 X a x0 p0 x6 p6 x7 p7 x6 p7 == β-coh1 X a x0 p0 x6 p6 x8 p8 x6 p8
β-coh5 X a _ idp _ idp _ idp _ idp = idp

β-coh6 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) (x4 : X) (p4 : x4 == x1) (x5 : a == x2) (p5 : x5 == coh∙! p1 p2) (x7 : x4 == x2) (p7 : x7 == coh∙! p4 p2) → β-coh3 X a x0 p0 a p0 x2 x5 x4 x7 == β-coh2 X a x1 p1 x4 p4
β-coh6 X a _ idp _ idp _ idp _ idp _ idp _ idp = idp

β-aux1 : (A B C : Type i) {{_ : Pointed A}} {{_ : Pointed B}} {{_ : Pointed C}} (c : C) (x : A ∧ B) → (C ∧ B) ∧ A
β-aux1 A B C c =
  Smash-rec (λ a b → proj (proj c b) a)
            pt
            (λ a → β-coh1 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) baser (gluer pt) (proj (proj pt pt) a) (gluer a) (proj basel a) (ap (λ z → proj z a) (gluel pt)) (proj (proj c pt) a) (ap (λ z → proj z a) (gluel c)))
            pt
            (λ b → β-coh2 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj (proj c b) pt) (gluel (proj c b)))

β-aux2 : (A B C : Type i) {{_ : Pointed A}} {{_ : Pointed B}} {{_ : Pointed C}} (x : A ∧ B) → β-aux1 A B C pt x == pt
β-aux2 A B C =
  Smash-elim (λ a b → β-coh3 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) baser (gluer pt) (proj (proj pt pt) a) (gluer a) (proj baser a) (ap (λ z → proj z a) (gluer pt)) (proj (proj pt b) a) (ap (λ z → proj z a) (gluer b)))
             idp
             (λ a → ↓-=cst-in (complicated-coh (gluel-β' a) (β-coh5 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) baser (gluer pt) (proj (proj pt pt) a) (gluer a) (proj baser a) (ap (λ z → proj z a) (gluer pt)) (proj basel a) (ap (λ z → proj z a) (gluel pt)))))
             idp
             (λ b → ↓-=cst-in (complicated-coh (gluer-β' b) (β-coh6 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) baser (gluer pt) basel (gluel (proj pt pt)) (proj baser pt) (gluel baser) (proj (proj pt b) pt) (gluel (proj pt b)) (ap (λ z → proj z pt) (gluer pt)) (green (gluer pt)) (ap (λ z → proj z pt) (gluer b)) (green (gluer b)))))

β : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : (A ∧ B) ∧ C) → (C ∧ B) ∧ A
β A B C =
  Smash-rec (λ x c → β-aux1 A B C c x)
            pt
            (β-aux2 A B C)
            pt
            (λ c → β-coh4 ((C ∧ B) ∧ A) (proj (proj pt pt) pt) basel (gluel (proj pt pt)) (proj (proj c pt) pt) (gluel (proj c pt)))


∧-map-id-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) → a == x1
∧-map-id-coh1 X a _ idp = idp

∧-map-id-coh2 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) → p2 == coh∙ (∧-map-coh1 X a x1 p1 x2 p2 x2 idp) (∧-map-id-coh1 X a x1 p1)
∧-map-id-coh2 X a _ idp _ idp = idp

∧-map-id-coh3 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) → a == x0
∧-map-id-coh3 X a _ idp = idp

∧-map-id-coh4 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x3 : X) (p3 : x3 == x0) → p3 == coh∙ (∧-map-coh2 X a x0 p0 x3 p3 x3 idp) (∧-map-id-coh3 X a x0 p0)
∧-map-id-coh4 X a _ idp _ idp = idp

∧-map-id : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → ∧-map A A B B (λ y → y) (λ z → z) x == x
∧-map-id A B =
  Smash-elim (λ a b → idp)
             (∧-map-id-coh1 (A ∧ B) (proj pt pt) basel (gluel pt))
             (λ a → ↓-=-in-eq ap-idf (gluel-β' a) (∧-map-id-coh2 (A ∧ B) (proj pt pt) basel (gluel pt) (proj a pt) (gluel a)))
             (∧-map-id-coh3 (A ∧ B) (proj pt pt) baser (gluer pt))
             (λ b → ↓-=-in-eq ap-idf (gluer-β' b) (∧-map-id-coh4 (A ∧ B) (proj pt pt) baser (gluer pt) (proj pt b) (gluer b)))


σ-triangle-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) → a == x1
σ-triangle-coh1 X a _ idp = idp

σ-triangle-coh2 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) → p2 == coh∙ (σ-coh1 X a a (σ-coh2 X a x1 p1 a p1) x2 (σ-coh2 X a x1 p1 x2 p2)) (σ-triangle-coh1 X a x1 p1)
σ-triangle-coh2 X a _ idp _ idp = idp

σ-triangle-coh3 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) → a == x0
σ-triangle-coh3 X a _ idp = idp

σ-triangle-coh4 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x2 : X) (p2 : x2 == x0) → p2 == coh∙ (σ-coh2 X a a (σ-coh1 X a x0 p0 a p0) x2 (σ-coh1 X a x0 p0 x2 p2)) (σ-triangle-coh3 X a x0 p0)
σ-triangle-coh4 X a _ idp _ idp = idp

σ-triangle : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → σ B A (σ A B x) == x
σ-triangle A B =
  Smash-elim (λ a b → idp)
             (σ-triangle-coh1 (A ∧ B) (proj pt pt) basel (gluel pt))
             (λ a → ↓-=-in-eq ap-idf (ap-∘ (σ B A) (σ A B) (gluel-β' a) (apσ-coh1 (gluer-β' pt) (gluer-β' a))) (σ-triangle-coh2 (A ∧ B) (proj pt pt) basel (gluel pt) (proj a pt) (gluel a)))
             (σ-triangle-coh3 (A ∧ B) (proj pt pt) baser (gluer pt))
             (λ b → ↓-=-in-eq ap-idf (ap-∘ (σ B A) (σ A B) (gluer-β' b) (apσ-coh2 (gluel-β' pt) (gluel-β' b))) (σ-triangle-coh4 (A ∧ B) (proj pt pt) baser (gluer pt) (proj pt b) (gluer b)))


σ-2triangle-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) → a == x1
σ-2triangle-coh1 X a _ idp = idp

σ-2triangle-coh2 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == x1) → p2 == coh∙ (σ-coh1 X a a (σ-coh2 X a a (σ-coh1 X a a (σ-coh2 X a x1 p1 a p1) a (σ-coh2 X a x1 p1 a p1)) a (σ-coh1 X a a (σ-coh2 X a x1 p1 a p1) a (σ-coh2 X a x1 p1 a p1))) x2 (σ-coh2 X a a (σ-coh1 X a a (σ-coh2 X a x1 p1 a p1) a (σ-coh2 X a x1 p1 a p1)) x2 (σ-coh1 X a a (σ-coh2 X a x1 p1 a p1) x2 (σ-coh2 X a x1 p1 x2 p2)))) (σ-2triangle-coh1 X a x1 p1)
σ-2triangle-coh2 X a _ idp _ idp = idp

σ-2triangle-coh3 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) → a == x0
σ-2triangle-coh3 X a _ idp = idp

σ-2triangle-coh4 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x2 : X) (p2 : x2 == x0) → p2 == coh∙ (σ-coh2 X a a (σ-coh1 X a a (σ-coh2 X a a (σ-coh1 X a x0 p0 a p0) a (σ-coh1 X a x0 p0 a p0)) a (σ-coh2 X a a (σ-coh1 X a x0 p0 a p0) a (σ-coh1 X a x0 p0 a p0))) x2 (σ-coh1 X a a (σ-coh2 X a a (σ-coh1 X a x0 p0 a p0) a (σ-coh1 X a x0 p0 a p0)) x2 (σ-coh2 X a a (σ-coh1 X a x0 p0 a p0) x2 (σ-coh1 X a x0 p0 x2 p2)))) (σ-2triangle-coh3 X a x0 p0)
σ-2triangle-coh4 X a _ idp _ idp = idp

σ-2triangle : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (x : A ∧ B) → σ B A (σ A B (σ B A (σ A B x))) == x
σ-2triangle A B =
  Smash-elim (λ a b → idp)
             (σ-2triangle-coh1 (A ∧ B) (proj pt pt) basel (gluel pt))
             (λ a → ↓-=-in-eq ap-idf (ap-∘ (λ z → σ B A (σ A B (σ B A z))) (σ A B) (gluel-β' a) (apσ-coh1 (ap-∘ (λ z → σ B A (σ A B z)) (σ B A) (gluer-β' pt) (apσ-coh2 (ap-∘ (σ B A) (σ A B) (gluel-β' pt) (apσ-coh1 (gluer-β' pt) (gluer-β' pt))) (ap-∘ (σ B A) (σ A B) (gluel-β' pt) (apσ-coh1 (gluer-β' pt) (gluer-β' pt))))) (ap-∘ (λ z → σ B A (σ A B z)) (σ B A) (gluer-β' a) (apσ-coh2 (ap-∘ (σ B A) (σ A B) (gluel-β' pt) (apσ-coh1 (gluer-β' pt) (gluer-β' pt))) (ap-∘ (σ B A) (σ A B) (gluel-β' a) (apσ-coh1 (gluer-β' pt) (gluer-β' a))))))) (σ-2triangle-coh2 (A ∧ B) (proj pt pt) basel (gluel pt) (proj a pt) (gluel a)))
             (σ-2triangle-coh3 (A ∧ B) (proj pt pt) baser (gluer pt))
             (λ b → ↓-=-in-eq ap-idf (ap-∘ (λ z → σ B A (σ A B (σ B A z))) (σ A B) (gluer-β' b) (apσ-coh2 (ap-∘ (λ z → σ B A (σ A B z)) (σ B A) (gluel-β' pt) (apσ-coh1 (ap-∘ (σ B A) (σ A B) (gluer-β' pt) (apσ-coh2 (gluel-β' pt) (gluel-β' pt))) (ap-∘ (σ B A) (σ A B) (gluer-β' pt) (apσ-coh2 (gluel-β' pt) (gluel-β' pt))))) (ap-∘ (λ z → σ B A (σ A B z)) (σ B A) (gluel-β' b) (apσ-coh1 (ap-∘ (σ B A) (σ A B) (gluer-β' pt) (apσ-coh2 (gluel-β' pt) (gluel-β' pt))) (ap-∘ (σ B A) (σ A B) (gluer-β' b) (apσ-coh2 (gluel-β' pt) (gluel-β' b))))))) (σ-2triangle-coh4 (A ∧ B) (proj pt pt) baser (gluer pt) (proj pt b) (gluer b)))


σ-nat-coh1 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x3 : X) (p3 : x3 == x1) (x4 : X) (p4 : x4 == x3) → a == x4
σ-nat-coh1 X a _ idp _ idp _ idp = idp

σ-nat-coh2 : (X : Type i) (a : X) (x0 : X) (p0 : a == x0) (x1 : X) (p1 : a == x1) (x2 : X) (p2 : x2 == a) (x3 : X) (p3 : x3 == x1) (x4 : X) (p4 : x4 == x3) (x5 : x3 == a) (p5 : x5 == coh∙! p3 p1) (x6 : x2 == x0) (p6 : x6 == coh∙ p2 p0) (x7 : x4 == x2) (p7 : x7 == coh∙∙! p4 x5 p2) (x8 : X) (p8 : x8 == x0) (x9 : X) (p9 : x9 == x8) → σ-coh1 X x4 a (∧-map-coh2 X a x0 p0 x2 x6 x4 x7) x9 (∧-map-coh2 X a x0 p0 x8 p8 x9 p9) == coh∙ (∧-map-coh1 X a a (σ-coh1 X a x0 p0 a p0) x8 (σ-coh1 X a x0 p0 x8 p8) x9 p9) (σ-nat-coh1 X a x1 p1 x3 p3 x4 p4)
σ-nat-coh2 X a _ idp _ idp _ idp _ idp _ idp _ idp _ idp _ idp _ idp _ idp = idp

σ-nat-coh3 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x3 : X) (p3 : x3 == x1) (x4 : X) (p4 : x4 == x3) → a == x4
σ-nat-coh3 X a _ idp _ idp _ idp = idp

σ-nat-coh4 : (X : Type i) (a : X) (x1 : X) (p1 : a == x1) (x3 : X) (p3 : x3 == x1) (x4 : X) (p4 : x4 == x3) (x5 : X) (p5 : x5 == x1) (x6 : X) (p6 : x6 == x5) → σ-coh2 X x4 a (∧-map-coh1 X a x1 p1 x3 p3 x4 p4) x6 (∧-map-coh1 X a x1 p1 x5 p5 x6 p6) == coh∙ (∧-map-coh2 X a a (σ-coh2 X a x1 p1 a p1) x5 (σ-coh2 X a x1 p1 x5 p5) x6 p6) (σ-nat-coh3 X a x1 p1 x3 p3 x4 p4)
σ-nat-coh4 X a _ idp _ idp _ idp _ idp _ idp = idp

σ-nat : (A : Type i) {{_ : Pointed A}} (A' : Type i) {{_ : Pointed A'}} (B : Type i) {{_ : Pointed B}} (B' : Type i) {{_ : Pointed B'}} (f : A → A') {{_ : PointedFun f}} (g : B → B') {{_ : PointedFun g}} (x : A ∧ B) → σ A' B' (∧-map A A' B B' f g x) == ∧-map B B' A A' g f (σ A B x)
σ-nat A A' B B' f g =
  Smash-elim (λ a b → idp)
             (σ-nat-coh1 (B' ∧ A') (proj pt pt) basel (gluel pt) (proj (g pt) pt) (gluel (g pt)) (proj (g pt) (f pt)) (ap (λ z → proj (g pt) z) (ptf f)))
             (λ a → ↓-=-in-eq (ap-∘ (∧-map B B' A A' g f) (σ A B) (gluel-β' a) (apσ-coh1 (gluer-β' pt) (gluer-β' a))) (ap-∘ (σ A' B') (∧-map A A' B B' f g) (gluel-β' a) (ap∧-map-coh1 (gluel-β' pt) (gluel-β' (f a)) (∘-ap (σ A' B') (λ z11 → proj (f a) z11)))) (σ-nat-coh2 (B' ∧ A') (proj pt pt) baser (gluer pt) basel (gluel pt) (proj pt (f pt)) (ap (λ z → proj pt z) (ptf f)) (proj (g pt) pt) (gluel (g pt)) (proj (g pt) (f pt)) (ap (λ z → proj (g pt) z) (ptf f)) (ap (λ z → proj z pt) (ptf g)) (green (ptf g)) (gluer (f pt)) (purple (ptf f)) (ap (λ z → proj z (f pt)) (ptf g)) (pink-l (ptf g) (ptf f)) (proj pt (f a)) (gluer (f a)) (proj (g pt) (f a)) (ap (λ z → proj z (f a)) (ptf g))))
             (σ-nat-coh3 (B' ∧ A') (proj pt pt) basel (gluel pt) (proj (g pt) pt) (gluel (g pt)) (proj (g pt) (f pt)) (ap (λ z → proj (g pt) z) (ptf f)))
             (λ b → ↓-=-in-eq (ap-∘ (∧-map B B' A A' g f) (σ A B) (gluer-β' b) (apσ-coh2 (gluel-β' pt) (gluel-β' b))) (ap-∘ (σ A' B') (∧-map A A' B B' f g) (gluer-β' b) (ap∧-map-coh2 (gluer-β' pt) (gluer-β' (g b)) (∘-ap (σ A' B') (λ z11 → proj z11 (g b))))) (σ-nat-coh4 (B' ∧ A') (proj pt pt) basel (gluel pt) (proj (g pt) pt) (gluel (g pt)) (proj (g pt) (f pt)) (ap (λ z → proj (g pt) z) (ptf f)) (proj (g b) pt) (gluel (g b)) (proj (g b) (f pt)) (ap (λ z → proj (g b) z) (ptf f))))

WORKS/>
-}


∧-map-comp : (A : Type i) {{_ : Pointed A}} (A' : Type i) {{_ : Pointed A'}} (A'' : Type i) {{_ : Pointed A''}} (B : Type i) {{_ : Pointed B}} (B' : Type i) {{_ : Pointed B'}} (B'' : Type i) {{_ : Pointed B''}} (f : A → A') {{_ : PointedFun f}} (f' : A' → A'') {{_ : PointedFun f'}} (g : B → B') {{_ : PointedFun g}} (g' : B' → B'') {{_ : PointedFun g'}} (x : A ∧ B) → ∧-map A A'' B B'' (λ z → f' (f z)) {{{!!}}} (λ z → g' (g z)) {{{!!}}} x == ∧-map A' A'' B' B'' f' g' (∧-map A A' B B' f g x)
∧-map-comp A A' A'' B B' B'' f f' g g' =
  Smash-elim (λ a b → idp)
             {!(∧-map-comp-coh1 (A'' ∧ B'') (proj pt pt) (proj (f' pt) (g' pt)) (apg' (λ y → proj (f' pt) y)))!}
             (λ a → ↓-=-in-eq (ap-∘ (∧-map A' A'' B' B'' f' g') (∧-map A A' B B' f g) (gluel-β' a) (ap∧-map-coh1 (gluel-β' pt) (gluel-β' (f a)) (∘-ap (∧-map A' A'' B' B'' f' g') (λ z11 → proj (f a) z11)))) (gluel-β' a) {!(∧-map-comp-coh2 (A'' ∧ B'') (proj pt pt) basel (gluel pt) (proj (f' pt) pt) (gluel (f' pt)) (proj (f' pt) (g' pt)) (ap (λ z → proj (f' pt) z) (ptf g')) (proj (f' pt) (g' pt)) (apg' (λ y → proj (f' pt) y)) (proj (f' (f a)) pt) (gluel (f' (f a))) (proj (f' (f a)) (g' pt)) (ap (λ z → proj (f' (f a)) z) (ptf g')) (proj (f' (f a)) (g' pt)) (apg' (λ y → proj (f' (f a)) y)) (proj (f' (f a)) (g' (g pt))) (ap (λ z → proj (f' (f a)) z) (ap g' (ptf g))))!})
             {!(∧-map-comp-coh3 (A'' ∧ B'') (proj pt pt) (proj (f' pt) (g' pt)) (apg' (λ y → proj (f' pt) y)))!}
             (λ b → ↓-=-in-eq (ap-∘ (∧-map A' A'' B' B'' f' g') (∧-map A A' B B' f g) (gluer-β' b) (ap∧-map-coh2 (gluer-β' pt) (gluer-β' (g b)) (∘-ap (∧-map A' A'' B' B'' f' g') (λ z11 → proj z11 (g b))))) (gluer-β' b) {!(∧-map-comp-coh4 (A'' ∧ B'') (proj pt pt) baser (gluer pt) basel (gluel pt) (proj pt (g' pt)) (ap (λ z → proj pt z) (ptf g')) (proj pt (g' pt)) (apg' (λ y → proj pt y)) (proj (f' pt) pt) (gluel (f' pt)) (proj (f' pt) (g' pt)) (ap (λ z → proj (f' pt) z) (ptf g')) (proj (f' pt) (g' pt)) (apg' (λ y → proj (f' pt) y)) (ap (λ z → proj z pt) (ptf f')) (green (ptf f')) (gluer (g' pt)) (purple (ptf g')) (ap (λ z → proj z (g' pt)) (ptf f')) (pink-l (ptf f') (ptf g')) (proj pt (g' (g b))) (gluer (g' (g b))) (proj (f' pt) (g' (g b))) (ap (λ z → proj z (g' (g b))) (ptf f')) (proj (f' pt) (g' (g b))) (apf' pt (λ x → proj x (g' (g b)))) (proj (f' (f pt)) (g' (g b))) (ap (λ z → proj z (g' (g b))) (ap f' (ptf f))))!})


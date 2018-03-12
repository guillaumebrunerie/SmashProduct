{-# OPTIONS --without-K --rewriting #-}

open import SmashCommon
open import PathInduction
open import SmashDefs
open import BasicsGenerated

module AlphaRinvGenerated {i : ULevel} where

α-rinv-proj-basel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) → a == x2)
α-rinv-proj-basel = path-induction

α-rinv-proj-gluel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) {x4 : X} (p4 : a == x4) {x5 : a == a} (p5 : Square x5 (& α⁻¹-gluel X p4 p4) idp idp) {x6 : X} (p6 : x6 == x4) {x7 : x6 == a} (p7 : Square x7 (& α⁻¹-gluel X p4 p6) idp idp) {x8 : X} (p8 : x8 == x4) {x9 : x4 == x4} (p9 : Square x9 idp idp idp) {x10 : a == x8} (p10 : Square p4 p8 x10 x9) {x11 : x4 == x4} (p11 : Square x11 idp idp idp) {x12 : x6 == x8} (p12 : Square p6 p8 x12 x11) {x13 : x6 == a} (p13 : Square x13 (& α⁻¹-proj-gluer X p0 p0 x10 x12) idp idp) {x14 : x6 == a} (p14 : Square x13 x14 idp idp) {x15 : x3 == a} (p15 : Square x15 (& α⁻¹-proj-gluer X p0 p1 p2 p3) idp idp) {x16 : x3 == a} (p16 : Square x15 x16 idp idp) {x17 : x3 == a} (p17 : Square x17 (& α-proj-gluel X x5 x7 x14 x16) idp idp) {x18 : x3 == a} (p18 : Square x18 x17 idp idp) {x19 : x3 == a} (p19 : Square x19 x18 idp idp) → Square idp (& α-rinv-proj-basel X p0 p1 p2) x19 p3)
α-rinv-proj-gluel = path-induction

α-rinv-proj-baser : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) → a == x2)
α-rinv-proj-baser = path-induction

α-rinv-proj-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : x1 == x2) {x3 : X} (p3 : x3 == x2) {x4 : X} (p4 : a == x4) {x5 : X} (p5 : x5 == x4) {x6 : x4 == x4} (p6 : Square x6 idp idp idp) {x7 : a == x5} (p7 : Square p4 p5 x7 x6) {x8 : a == a} (p8 : Square x8 (& α⁻¹-gluer-proj X p0 p0 x7 x7) idp idp) {x9 : x3 == a} (p9 : Square x9 (& α⁻¹-gluer-proj X p0 p1 p2 p3) idp idp) {x10 : x3 == a} (p10 : Square x10 (& α-proj-gluer X x8 x9) idp idp) {x11 : x3 == a} (p11 : Square x11 x10 idp idp) {x12 : x3 == a} (p12 : Square x12 x11 idp idp) → Square idp (& α-rinv-proj-baser X p0 p1 p2) x12 p3)
α-rinv-proj-gluer = path-induction

α-rinv-proj : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (c : C) (x : A ∧ B) → α⁻¹ A B C (α-proj A B C c x) == proj x c
α-rinv-proj A B C c = α-rinv-proj.f  module _ where

  module α-rinv-proj =
    SmashElimId {g = λ x → α⁻¹ A B C (α-proj A B C c x)}
                {h = λ x → proj x c}
                (λ a b → idp)
                (& α-rinv-proj-basel ((A ∧ B) ∧ C) (gluer pt) (gluer c) (ap (λ z → proj z c) (gluel pt)))
                (λ a → & α-rinv-proj-gluel ((A ∧ B) ∧ C) (gluer pt) (gluer c) (ap (λ z → proj z c) (gluel pt)) (ap (λ z → proj z c) (gluel a)) (gluel (proj pt pt)) (α⁻¹.gluel-β A B C pt) (gluel (proj a pt)) (α⁻¹.gluel-β A B C a) (gluel basel) (ap-cst basel (gluel pt)) (ap+ (λ x → gluel x) (gluel pt)) (ap-cst basel (gluel a)) (ap+ (λ x → gluel x) (gluel a)) (α⁻¹-proj.gluer-β A B C a pt) (ap-∘ (λ z → α⁻¹ A B C z) (λ z → proj a z) (gluer pt)) (α⁻¹-proj.gluer-β A B C a c) (ap-∘ (λ z → α⁻¹ A B C z) (λ z → proj a z) (gluer c)) (& apα-proj-gluel (λ x → α⁻¹ A B C x) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluer pt)) (ap (λ z → proj a z) (gluer c))) (ap² (λ x → α⁻¹ A B C x) (α-proj.gluel-β A B C c a)) (ap-∘ (λ x → α⁻¹ A B C x) (α-proj A B C c) (gluel a)))
                (& α-rinv-proj-baser ((A ∧ B) ∧ C) (gluer pt) (gluer c) (ap (λ z → proj z c) (gluer pt)))
                (λ b → & α-rinv-proj-gluer ((A ∧ B) ∧ C) (gluer pt) (gluer c) (ap (λ z → proj z c) (gluer pt)) (ap (λ z → proj z c) (gluer b)) (gluel (proj pt pt)) (gluel baser) (ap-cst basel (gluer pt)) (ap+ (λ x → gluel x) (gluer pt)) (α⁻¹.gluer-β A B C (proj pt pt)) (α⁻¹.gluer-β A B C (proj b c)) (& apα-proj-gluer (λ x → α⁻¹ A B C x) (gluer (proj pt pt)) (gluer (proj b c))) (ap² (λ x → α⁻¹ A B C x) (α-proj.gluer-β A B C c b)) (ap-∘ (λ x → α⁻¹ A B C x) (α-proj A B C c) (gluer b)))

α-rinv-gluel-proj : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : a == a} (p2 : Square x2 (& α⁻¹-gluel X p0 p0) idp idp) {x3 : X} (p3 : x3 == x0) {x4 : x3 == a} (p4 : Square x4 (& α⁻¹-gluel X p0 p3) idp idp) {x5 : x3 == a} (p5 : Square x5 (& α⁻¹-proj-gluel X p0 p3) idp idp) {x6 : x3 == a} (p6 : Square x5 x6 idp idp) {x7 : x1 == a} (p7 : Square x7 (& α⁻¹-proj-gluel X p0 p1) idp idp) {x8 : x1 == a} (p8 : Square x7 x8 idp idp) {x9 : x1 == a} (p9 : Square x9 (& α-gluel-proj X x2 x4 x6 x8) idp idp) {x10 : x1 == a} (p10 : Square x10 x9 idp idp) {x11 : x1 == a} (p11 : Square x11 x10 idp idp) {x12 : x1 == x0} (p12 : Square x12 p1 idp idp) → Square idp p0 x11 x12)
α-rinv-gluel-proj = path-induction

α-rinv-gluel-basel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : a == x2) {x3 : x0 == x0} (p3 : Square x3 idp idp idp) {x4 : a == x1} (p4 : Square p0 p1 x4 x3) {x5 : a == a} (p5 : Square x5 idp idp idp) {x6 : a == a} (p6 : Square x6 x5 idp idp) {x7 : x1 == x0} (p7 : Square x7 p1 idp idp) → Square (& α-rinv-proj-basel X p2 p2 x4) p0 x6 x7)
α-rinv-gluel-basel = path-induction

α-rinv-gluel-gluel : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : a == a} (p2 : Square x2 (& α⁻¹-gluel X p0 p0) idp idp) {x3 : x1 == a} (p3 : Square x3 (& α⁻¹-gluel X p0 p1) idp idp) {x4 : x1 == a} (p4 : Square x4 (& α⁻¹-proj-gluel X p0 p1) idp idp) {x5 : x1 == a} (p5 : Square x4 x5 idp idp) {x6 : x1 == a} (p6 : Square x6 (& α-gluel-proj X x2 x3 x5 x5) idp idp) {x7 : x1 == a} (p7 : Square x7 x6 idp idp) {x8 : x1 == a} (p8 : Square x8 x7 idp idp) {x9 : x1 == x0} (p9 : Square x9 p1 idp idp) {x10 : X} (p10 : x10 == x0) {x11 : X} (p11 : a == x11) {x12 : x0 == x0} (p12 : Square x12 idp idp idp) {x13 : a == x10} (p13 : Square p0 p10 x13 x12) {x14 : a == a} (p14 : Square x14 idp idp idp) {x15 : a == a} (p15 : Square x15 x14 idp idp) {x16 : x10 == x0} (p16 : Square x16 p10 idp idp) {x17 : x0 == x0} (p17 : Square x17 idp idp idp) {x18 : x1 == x10} (p18 : Square p1 p10 x18 x17) {x19 : x1 == a} (p19 : Square x19 (& α⁻¹-proj-gluer X p11 p11 x13 x18) idp idp) {x20 : x1 == a} (p20 : Square x19 x20 idp idp) {x21 : x1 == a} (p21 : Square x21 (& α-proj-gluel X x2 x3 x20 x20) idp idp) {x22 : x1 == a} (p22 : Square x22 x21 idp idp) {x23 : x1 == a} (p23 : Square x23 x22 idp idp) {x24 : Square idp (& α-rinv-proj-basel X p11 p11 x13) x23 x18} (p24 : Cube x24 (& α-rinv-proj-gluel X p11 p11 x13 x18 p0 p2 p1 p3 p10 p12 p13 p17 p18 p19 p20 p19 p20 p21 p22 p23) ids (& hids (& α-rinv-proj-basel X p11 p11 x13)) (& hids x23) (& hids x18)) {x25 : a == a} (p25 : Square x25 idp idp idp) {x26 : Square p0 p0 x25 x17} (p26 : Cube x26 (& hids p0) (& hids p0) (& hids p0) p25 p17) {x27 : a == a} (p27 : Square x25 x27 idp idp) {x28 : Square x27 idp idp idp} (p28 : Cube p25 x28 p27 ids ids ids) {x29 : Square x6 idp x22 x27} (p29 : Cube x29 (& α-gluel-gluel X x2 x3 x5 x20 (& coh∙□ p22 p21) x28) p6 ids (& hids x22) (& hids x27)) {x30 : Square x6 x6 idp idp} (p30 : Cube x30 (& hids x6) (& hids x6) (& hids x6) ids ids) {x31 : Square x22 x22 idp idp} (p31 : Cube x31 (& hids x22) (& hids x22) (& hids x22) ids ids) {x32 : Square x27 x27 idp idp} (p32 : Cube x32 (& hids x27) (& hids x27) (& hids x27) ids ids) {x33 : Square x6 idp x22 x27} (p33 : Cube x33 x29 x30 ids x31 x32) {x34 : Square x6 idp x23 x25} (p34 : Cube x34 x33 (& hids x6) ids p23 p27) {x35 : Square idp idp x23 x23} (p35 : Cube x35 (& vids x23) ids ids (& hids x23) (& hids x23)) {x36 : Square idp idp x25 x25} (p36 : Cube x36 (& vids x25) ids ids (& hids x25) (& hids x25)) {x37 : Square x7 x14 x23 x25} (p37 : Cube p7 p14 x37 x34 x35 x36) {x38 : Square x8 x15 x23 x25} (p38 : Cube p8 p15 x38 x37 x35 x36) {x39 : Square idp idp x18 x18} (p39 : Cube x39 (& vids x18) ids ids (& hids x18) (& hids x18)) {x40 : Square idp idp x17 x17} (p40 : Cube x40 (& vids x17) ids ids (& hids x17) (& hids x17)) {x41 : Square x9 x16 x18 x17} (p41 : Cube p9 p16 x41 p18 x39 x40) → Cube (& α-rinv-gluel-proj X p0 p1 p2 p1 p3 p4 p5 p4 p5 p6 p7 p8 p9) (& α-rinv-gluel-basel X p0 p10 p11 p12 p13 p14 p15 p16) x24 x26 x38 x41)
α-rinv-gluel-gluel = path-induction

α-rinv-gluel-baser : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : a == x2) {x3 : x0 == x0} (p3 : Square x3 idp idp idp) {x4 : a == x1} (p4 : Square p0 p1 x4 x3) {x5 : a == a} (p5 : Square x5 idp idp idp) {x6 : a == a} (p6 : Square x6 x5 idp idp) {x7 : x1 == x0} (p7 : Square x7 p1 idp idp) → Square (& α-rinv-proj-baser X p2 p2 x4) p0 x6 x7)
α-rinv-gluel-baser = path-induction

α-rinv-gluel-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : a == a} (p2 : Square x2 (& α⁻¹-gluel X p0 p0) idp idp) {x3 : a == a} (p3 : Square x3 (& α⁻¹-proj-gluel X p0 p0) idp idp) {x4 : a == a} (p4 : Square x3 x4 idp idp) {x5 : x1 == a} (p5 : Square x5 (& α⁻¹-proj-gluel X p0 p1) idp idp) {x6 : x1 == a} (p6 : Square x5 x6 idp idp) {x7 : x1 == a} (p7 : Square x7 (& α-gluel-proj X x2 x2 x4 x6) idp idp) {x8 : x1 == a} (p8 : Square x8 x7 idp idp) {x9 : x1 == a} (p9 : Square x9 x8 idp idp) {x10 : x1 == x0} (p10 : Square x10 p1 idp idp) {x11 : X} (p11 : x11 == x0) {x12 : X} (p12 : a == x12) {x13 : x0 == x0} (p13 : Square x13 idp idp idp) {x14 : a == x11} (p14 : Square p0 p11 x14 x13) {x15 : a == a} (p15 : Square x15 idp idp idp) {x16 : a == a} (p16 : Square x16 x15 idp idp) {x17 : x11 == x0} (p17 : Square x17 p11 idp idp) {x18 : a == a} (p18 : Square x18 (& α⁻¹-gluer-proj X p12 p12 x14 x14) idp idp) {x19 : x0 == x0} (p19 : Square x19 idp idp idp) {x20 : x1 == x11} (p20 : Square p1 p11 x20 x19) {x21 : x1 == a} (p21 : Square x21 (& α⁻¹-gluer-proj X p12 p12 x14 x20) idp idp) {x22 : x1 == a} (p22 : Square x22 (& α-proj-gluer X x18 x21) idp idp) {x23 : x1 == a} (p23 : Square x23 x22 idp idp) {x24 : x1 == a} (p24 : Square x24 x23 idp idp) {x25 : Square idp (& α-rinv-proj-baser X p12 p12 x14) x24 x20} (p25 : Cube x25 (& α-rinv-proj-gluer X p12 p12 x14 x20 p0 p11 p13 p14 p18 p21 p22 p23 p24) ids (& hids (& α-rinv-proj-baser X p12 p12 x14)) (& hids x24) (& hids x20)) {x26 : a == a} (p26 : Square x26 idp idp idp) {x27 : Square p0 p0 x26 x19} (p27 : Cube x27 (& hids p0) (& hids p0) (& hids p0) p26 p19) {x28 : a == a} (p28 : Square x26 x28 idp idp) {x29 : a == a} (p29 : Square x29 idp idp idp) {x30 : a == a} (p30 : Square x30 idp idp idp) {x31 : a == a} (p31 : Square x30 x31 idp idp) {x32 : Square x31 idp idp idp} (p32 : Cube p30 x32 p31 ids ids ids) {x33 : Square (& α⁻¹-gluer-proj X p12 p12 x14 x14) idp x3 x30} (p33 : Cube x33 (& α⁻¹-gluer-gluel X p0 p0 p12 p11 p13 p14 p13 p14 p3 p30) (& hids (& α⁻¹-gluer-proj X p12 p12 x14 x14)) ids (& hids x3) (& hids x30)) {x34 : Square idp idp x3 x3} (p34 : Cube x34 (& vids x3) ids ids (& hids x3) (& hids x3)) {x35 : Square idp idp x30 x30} (p35 : Cube x35 (& vids x30) ids ids (& hids x30) (& hids x30)) {x36 : Square x18 x29 x3 x30} (p36 : Cube p18 p29 x36 x33 x34 x35) {x37 : Square x18 x29 x4 x31} (p37 : Cube x36 x37 (& hids x18) (& hids x29) p4 p31) {x38 : a == a} (p38 : Square x38 idp idp idp) {x39 : a == a} (p39 : Square x38 x39 idp idp) {x40 : Square x39 idp idp idp} (p40 : Cube p38 x40 p39 ids ids ids) {x41 : Square (& α⁻¹-gluer-proj X p12 p12 x14 x20) idp x5 x38} (p41 : Cube x41 (& α⁻¹-gluer-gluel X p0 p1 p12 p11 p13 p14 p19 p20 p5 p38) (& hids (& α⁻¹-gluer-proj X p12 p12 x14 x20)) ids (& hids x5) (& hids x38)) {x42 : Square idp idp x5 x5} (p42 : Cube x42 (& vids x5) ids ids (& hids x5) (& hids x5)) {x43 : Square idp idp x38 x38} (p43 : Cube x43 (& vids x38) ids ids (& hids x38) (& hids x38)) {x44 : Square x21 x29 x5 x38} (p44 : Cube p21 p29 x44 x41 x42 x43) {x45 : Square x21 x29 x6 x39} (p45 : Cube x44 x45 (& hids x21) (& hids x29) p6 p39) {x46 : Square x28 idp idp idp} (p46 : Cube p26 x46 p28 ids ids ids) {x47 : Square x7 idp x23 x28} (p47 : Cube x47 (& α-gluel-gluer X x18 x21 x2 x29 x32 x37 x40 x45 (& coh∙□ p23 p22) x46) p7 ids (& hids x23) (& hids x28)) {x48 : Square x7 x7 idp idp} (p48 : Cube x48 (& hids x7) (& hids x7) (& hids x7) ids ids) {x49 : Square x23 x23 idp idp} (p49 : Cube x49 (& hids x23) (& hids x23) (& hids x23) ids ids) {x50 : Square x28 x28 idp idp} (p50 : Cube x50 (& hids x28) (& hids x28) (& hids x28) ids ids) {x51 : Square x7 idp x23 x28} (p51 : Cube x51 x47 x48 ids x49 x50) {x52 : Square x7 idp x24 x26} (p52 : Cube x52 x51 (& hids x7) ids p24 p28) {x53 : Square idp idp x24 x24} (p53 : Cube x53 (& vids x24) ids ids (& hids x24) (& hids x24)) {x54 : Square idp idp x26 x26} (p54 : Cube x54 (& vids x26) ids ids (& hids x26) (& hids x26)) {x55 : Square x8 x15 x24 x26} (p55 : Cube p8 p15 x55 x52 x53 x54) {x56 : Square x9 x16 x24 x26} (p56 : Cube p9 p16 x56 x55 x53 x54) {x57 : Square idp idp x20 x20} (p57 : Cube x57 (& vids x20) ids ids (& hids x20) (& hids x20)) {x58 : Square idp idp x19 x19} (p58 : Cube x58 (& vids x19) ids ids (& hids x19) (& hids x19)) {x59 : Square x10 x17 x20 x19} (p59 : Cube p10 p17 x59 p20 x57 x58) → Cube (& α-rinv-gluel-proj X p0 p1 p2 p0 p2 p3 p4 p5 p6 p7 p8 p9 p10) (& α-rinv-gluel-baser X p0 p11 p12 p13 p14 p15 p16 p17) x25 x27 x56 x59)
α-rinv-gluel-gluer = path-induction

α-rinv-gluel : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : A ∧ B) → Square (α-rinv-proj A B C pt x) (gluel (proj pt pt)) (ap (λ x → α⁻¹ A B C (α A B C x)) (gluel x)) (ap (λ x → x) (gluel x))
α-rinv-gluel A B C =
  Smash-elim (λ a b → & α-rinv-gluel-proj ((A ∧ B) ∧ C) (gluel (proj pt pt)) (gluel (proj a b)) (α⁻¹.gluel-β A B C pt) (gluel (proj a pt)) (α⁻¹.gluel-β A B C a) (α⁻¹-proj.gluel-β A B C a pt) (ap-∘ (λ z → α⁻¹ A B C z) (λ z → proj a z) (gluel pt)) (α⁻¹-proj.gluel-β A B C a b) (ap-∘ (λ z → α⁻¹ A B C z) (λ z → proj a z) (gluel b)) (& apα-gluel-proj (λ x → α⁻¹ A B C x) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluel pt)) (ap (λ z → proj a z) (gluel b))) (ap² (λ x → α⁻¹ A B C x) (α.gluel-β A B C (proj a b))) (ap-∘ (λ x → α⁻¹ A B C x) (α A B C) (gluel (proj a b))) (ap-idf (gluel (proj a b))))
             (& α-rinv-gluel-basel ((A ∧ B) ∧ C) (gluel (proj pt pt)) (gluel basel) (gluer pt) (ap-cst basel (gluel pt)) (ap+ (λ x → gluel x) (gluel pt)) (ap² (λ x → α⁻¹ A B C x) (α.gluel-β A B C basel)) (ap-∘ (λ x → α⁻¹ A B C x) (α A B C) (gluel basel)) (ap-idf (gluel basel)))
             (λ a → ↓-Square-in (& α-rinv-gluel-gluel ((A ∧ B) ∧ C) (gluel (proj pt pt)) (gluel (proj a pt)) (α⁻¹.gluel-β A B C pt) (α⁻¹.gluel-β A B C a) (α⁻¹-proj.gluel-β A B C a pt) (ap-∘ (λ z → α⁻¹ A B C z) (λ z → proj a z) (gluel pt)) (& apα-gluel-proj (λ x → α⁻¹ A B C x) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluel pt)) (ap (λ z → proj a z) (gluel pt))) (ap² (λ x → α⁻¹ A B C x) (α.gluel-β A B C (proj a pt))) (ap-∘ (λ x → α⁻¹ A B C x) (α A B C) (gluel (proj a pt))) (ap-idf (gluel (proj a pt))) (gluel basel) (gluer pt) (ap-cst basel (gluel pt)) (ap+ (λ x → gluel x) (gluel pt)) (ap² (λ x → α⁻¹ A B C x) (α.gluel-β A B C basel)) (ap-∘ (λ x → α⁻¹ A B C x) (α A B C) (gluel basel)) (ap-idf (gluel basel)) (ap-cst basel (gluel a)) (ap+ (λ x → gluel x) (gluel a)) (α⁻¹-proj.gluer-β A B C a pt) (ap-∘ (λ z → α⁻¹ A B C z) (λ z → proj a z) (gluer pt)) (& apα-proj-gluel (λ x → α⁻¹ A B C x) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluer pt)) (ap (λ z → proj a z) (gluer pt))) (ap² (λ x → α⁻¹ A B C x) (α-proj.gluel-β A B C pt a)) (ap-∘ (λ x → α⁻¹ A B C x) (α-proj A B C pt) (gluel a)) (α-rinv-proj.gluel-β A B C pt a) (ap-cst (proj (proj pt pt) pt) (gluel a)) (ap+-cst (gluel (proj pt pt)) (gluel a)) (ap-∘ (λ x → α⁻¹ A B C x) (λ x → proj pt (proj pt pt)) (gluel a)) (ap-∘-cst (λ z → α⁻¹ A B C z) (proj pt (proj pt pt)) (gluel a)) (& apα-gluel-gluel (λ x → α⁻¹ A B C x) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluel pt)) (ap (λ z → proj a z) (gluer pt)) (α-proj.gluel-β A B C pt a) (ap-cst (proj pt (proj pt pt)) (gluel a))) (& aphids (λ x → α⁻¹ A B C x) (& α-gluel-proj (A ∧ (B ∧ C)) (gluel pt) (gluel a) (ap (λ z → proj a z) (gluel pt)) (ap (λ z → proj a z) (gluel pt)))) (& aphids (λ x → α⁻¹ A B C x) (ap (λ x → α-proj A B C pt x) (gluel a))) (& aphids (λ x → α⁻¹ A B C x) (ap (λ x → proj pt (proj pt pt)) (gluel a))) (ap³ (λ x → α⁻¹ A B C x) (α-gluel.gluel-β A B C a)) (ap+-∘1 (λ x → α⁻¹ A B C x) (λ x → α-gluel A B C x) (gluel a)) (ap+-idp (λ x → α⁻¹ A B C (α-proj A B C pt x)) (gluel a)) (ap+-idp (λ x → proj (proj pt pt) pt) (gluel a)) (ap++ (λ x → ap² (λ x → α⁻¹ A B C x) (α.gluel-β A B C x)) (gluel a)) (ap++ (λ x → ap-∘ (λ x → α⁻¹ A B C x) (α A B C) (gluel x)) (gluel a)) (ap+-idp (λ x → proj x pt) (gluel a)) (ap+-idp (λ x → basel) (gluel a)) (ap++ (λ x → ap-idf (gluel x)) (gluel a))))
             (& α-rinv-gluel-baser ((A ∧ B) ∧ C) (gluel (proj pt pt)) (gluel baser) (gluer pt) (ap-cst basel (gluer pt)) (ap+ (λ x → gluel x) (gluer pt)) (ap² (λ x → α⁻¹ A B C x) (α.gluel-β A B C baser)) (ap-∘ (λ x → α⁻¹ A B C x) (α A B C) (gluel baser)) (ap-idf (gluel baser)))
             (λ b → ↓-Square-in (& α-rinv-gluel-gluer ((A ∧ B) ∧ C) (gluel (proj pt pt)) (gluel (proj pt b)) (α⁻¹.gluel-β A B C pt) (α⁻¹-proj.gluel-β A B C pt pt) (ap-∘ (λ z → α⁻¹ A B C z) (λ z → proj pt z) (gluel pt)) (α⁻¹-proj.gluel-β A B C pt b) (ap-∘ (λ z → α⁻¹ A B C z) (λ z → proj pt z) (gluel b)) (& apα-gluel-proj (λ x → α⁻¹ A B C x) (gluel pt) (gluel pt) (ap (λ z → proj pt z) (gluel pt)) (ap (λ z → proj pt z) (gluel b))) (ap² (λ x → α⁻¹ A B C x) (α.gluel-β A B C (proj pt b))) (ap-∘ (λ x → α⁻¹ A B C x) (α A B C) (gluel (proj pt b))) (ap-idf (gluel (proj pt b))) (gluel baser) (gluer pt) (ap-cst basel (gluer pt)) (ap+ (λ x → gluel x) (gluer pt)) (ap² (λ x → α⁻¹ A B C x) (α.gluel-β A B C baser)) (ap-∘ (λ x → α⁻¹ A B C x) (α A B C) (gluel baser)) (ap-idf (gluel baser)) (α⁻¹.gluer-β A B C (proj pt pt)) (ap-cst basel (gluer b)) (ap+ (λ x → gluel x) (gluer b)) (α⁻¹.gluer-β A B C (proj b pt)) (& apα-proj-gluer (λ x → α⁻¹ A B C x) (gluer (proj pt pt)) (gluer (proj b pt))) (ap² (λ x → α⁻¹ A B C x) (α-proj.gluer-β A B C pt b)) (ap-∘ (λ x → α⁻¹ A B C x) (α-proj A B C pt) (gluer b)) (α-rinv-proj.gluer-β A B C pt b) (ap-cst (proj (proj pt pt) pt) (gluer b)) (ap+-cst (gluel (proj pt pt)) (gluer b)) (ap-∘ (λ x → α⁻¹ A B C x) (λ x → proj pt (proj pt pt)) (gluer b)) (α⁻¹.gluer-β A B C basel) (ap-cst (proj (proj pt pt) pt) (gluel pt)) (ap-∘ (λ z → α⁻¹ A B C z) (λ y → baser) (gluel pt)) (ap-∘-cst (λ z → α⁻¹ A B C z) baser (gluel pt)) (α⁻¹-gluer.gluel-β A B C pt) (ap+-idp (λ y → α⁻¹-proj A B C pt y) (gluel pt)) (ap+-idp (λ y → proj (proj pt pt) pt) (gluel pt)) (ap++ (λ y → α⁻¹.gluer-β A B C y) (gluel pt)) (ap+-∘1 (α⁻¹ A B C) (λ y → gluer y) (gluel pt)) (ap-cst (proj (proj pt pt) pt) (gluel b)) (ap-∘ (λ z → α⁻¹ A B C z) (λ y → baser) (gluel b)) (ap-∘-cst (λ z → α⁻¹ A B C z) baser (gluel b)) (α⁻¹-gluer.gluel-β A B C b) (ap+-idp (λ y → α⁻¹-proj A B C pt y) (gluel b)) (ap+-idp (λ y → proj (proj pt pt) pt) (gluel b)) (ap++ (λ y → α⁻¹.gluer-β A B C y) (gluel b)) (ap+-∘1 (α⁻¹ A B C) (λ y → gluer y) (gluel b)) (ap-∘-cst (λ z → α⁻¹ A B C z) (proj pt (proj pt pt)) (gluer b)) (& apα-gluel-gluer (λ x → α⁻¹ A B C x) (gluer (proj pt pt)) (gluer (proj b pt)) (gluel pt) (gluer basel) (ap-cst baser (gluel pt)) (ap+ (λ y → gluer y) (gluel pt)) (ap-cst baser (gluel b)) (ap+ (λ y → gluer y) (gluel b)) (α-proj.gluer-β A B C pt b) (ap-cst (proj pt (proj pt pt)) (gluer b))) (& aphids (λ x → α⁻¹ A B C x) (& α-gluel-proj (A ∧ (B ∧ C)) (gluel pt) (gluel pt) (ap (λ z → proj pt z) (gluel pt)) (ap (λ z → proj pt z) (gluel b)))) (& aphids (λ x → α⁻¹ A B C x) (ap (λ x → α-proj A B C pt x) (gluer b))) (& aphids (λ x → α⁻¹ A B C x) (ap (λ x → proj pt (proj pt pt)) (gluer b))) (ap³ (λ x → α⁻¹ A B C x) (α-gluel.gluer-β A B C b)) (ap+-∘1 (λ x → α⁻¹ A B C x) (λ x → α-gluel A B C x) (gluer b)) (ap+-idp (λ x → α⁻¹ A B C (α-proj A B C pt x)) (gluer b)) (ap+-idp (λ x → proj (proj pt pt) pt) (gluer b)) (ap++ (λ x → ap² (λ x → α⁻¹ A B C x) (α.gluel-β A B C x)) (gluer b)) (ap++ (λ x → ap-∘ (λ x → α⁻¹ A B C x) (α A B C) (gluel x)) (gluer b)) (ap+-idp (λ x → proj x pt) (gluer b)) (ap+-idp (λ x → basel) (gluer b)) (ap++ (λ x → ap-idf (gluel x)) (gluer b))))

α-rinv-gluer : Coh ((X : Type i) {a : X} {x0 : X} (p0 : a == x0) {x1 : X} (p1 : x1 == x0) {x2 : X} (p2 : a == x2) {x3 : X} (p3 : x3 == x2) {x4 : x2 == x2} (p4 : Square x4 idp idp idp) {x5 : a == x3} (p5 : Square p2 p3 x5 x4) {x6 : a == a} (p6 : Square x6 (& α⁻¹-gluer-proj X p0 p0 x5 x5) idp idp) {x7 : X} (p7 : x1 == x7) {x8 : x1 == a} (p8 : Square x8 (& α⁻¹-gluer-proj X p0 p1 p7 p7) idp idp) {x9 : x1 == a} (p9 : Square x9 (& α-gluer X x6 x8) idp idp) {x10 : x1 == a} (p10 : Square x10 x9 idp idp) {x11 : x1 == a} (p11 : Square x11 x10 idp idp) {x12 : x1 == x0} (p12 : Square x12 p1 idp idp) → Square idp p0 x11 x12)
α-rinv-gluer = path-induction

α-rinv : (A : Type i) {{_ : Pointed A}} (B : Type i) {{_ : Pointed B}} (C : Type i) {{_ : Pointed C}} (x : (A ∧ B) ∧ C) → α⁻¹ A B C (α A B C x) == x
α-rinv A B C = α-rinv.f  module _ where

  module α-rinv =
    SmashElimId {g = λ x → α⁻¹ A B C (α A B C x)}
                {h = λ x → x}
                (λ x c → α-rinv-proj A B C c x)
                (gluel (proj pt pt))
                (α-rinv-gluel A B C)
                (gluer pt)
                (λ c → & α-rinv-gluer ((A ∧ B) ∧ C) (gluer pt) (gluer c) (gluel (proj pt pt)) (gluel baser) (ap-cst basel (gluer pt)) (ap+ (λ x → gluel x) (gluer pt)) (α⁻¹.gluer-β A B C (proj pt pt)) (ap (λ z → proj z c) (gluer pt)) (α⁻¹.gluer-β A B C (proj pt c)) (& apα-gluer (λ x → α⁻¹ A B C x) (gluer (proj pt pt)) (gluer (proj pt c))) (ap² (λ x → α⁻¹ A B C x) (α.gluer-β A B C c)) (ap-∘ (λ x → α⁻¹ A B C x) (α A B C) (gluer c)) (ap-idf (gluer c)))
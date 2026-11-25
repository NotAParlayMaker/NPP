import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_193
open PEqualNP.CircuitLowerBounds



theorem mem_kl {V : Type} [DecidableEq V] (C : PEqualNP.ProofComplexity.Clause V) (T : PEqualNP.ProofComplexity.KTerm V) :
    T ∈ PEqualNP.ProofComplexity.kLineOfClause C ↔ ∃ l ∈ C, ({l} : PEqualNP.ProofComplexity.KTerm V) = T := by
  unfold PEqualNP.ProofComplexity.kLineOfClause
  rw [Finset.mem_image]

theorem ax_card {V : Type} [DecidableEq V] (C : PEqualNP.ProofComplexity.Clause V) : ∀ T ∈ PEqualNP.ProofComplexity.kLineOfClause C, T.card ≤ 2 := by
  intro T hT
  obtain ⟨l, _, rfl⟩ := (mem_kl C T).1 hT
  simp

theorem cut_eq {V : Type} [DecidableEq V] (C D : PEqualNP.ProofComplexity.Clause V) (v : V) :
    (PEqualNP.ProofComplexity.kLineOfClause C).erase ({(v, false)} : PEqualNP.ProofComplexity.KTerm V) ∪
      (PEqualNP.ProofComplexity.kLineOfClause D \ ({(v, false)} : PEqualNP.ProofComplexity.KTerm V).image (fun l => ({(l.1, !l.2)} : PEqualNP.ProofComplexity.KTerm V)))
      = PEqualNP.ProofComplexity.kLineOfClause (C.erase (v, false) ∪ D.erase (v, true)) := by
  ext T
  rw [Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff, mem_kl, mem_kl, mem_kl]
  have him : ({(v, false)} : PEqualNP.ProofComplexity.KTerm V).image (fun l => ({(l.1, !l.2)} : PEqualNP.ProofComplexity.KTerm V)) = {({(v, true)} : PEqualNP.ProofComplexity.KTerm V)} := by
    rw [Finset.image_singleton]; rfl
  rw [him, Finset.mem_singleton]
  constructor
  · rintro (⟨hne, l, hl, rfl⟩ | ⟨⟨l, hl, rfl⟩, hni⟩)
    · exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨fun h => hne (by rw [h]), hl⟩), rfl⟩
    · exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨fun h => hni (by rw [h]), hl⟩), rfl⟩
  · rintro ⟨l, hl, rfl⟩
    rcases Finset.mem_union.1 hl with h | h
    · rw [Finset.mem_erase] at h
      exact Or.inl ⟨fun e => h.1 (Finset.singleton_injective e), l, h.2, rfl⟩
    · rw [Finset.mem_erase] at h
      exact Or.inr ⟨⟨l, h.2, rfl⟩, fun e => h.1 (Finset.singleton_injective e)⟩

theorem cutK {V : Type} [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.KLine V)) (π : List (PEqualNP.ProofComplexity.KLine V)) (C D R : PEqualNP.ProofComplexity.Clause V) (v : V)
    (hd : PEqualNP.ProofComplexity.IsResKDerivation 2 F π) (hC : PEqualNP.ProofComplexity.kLineOfClause C ∈ π) (hD : PEqualNP.ProofComplexity.kLineOfClause D ∈ π)
    (h1 : (v, false) ∈ C) (h2 : (v, true) ∈ D) (hR : R = C.erase (v, false) ∪ D.erase (v, true)) :
    PEqualNP.ProofComplexity.IsResKDerivation 2 F (PEqualNP.ProofComplexity.kLineOfClause R :: π) := by
  refine PEqualNP.ProofComplexity.IsResKDerivation.cut hd hC hD ⟨({(v, false)} : PEqualNP.ProofComplexity.KTerm V), ?_, Finset.singleton_nonempty _, ?_, ?_⟩
  · exact (mem_kl C _).2 ⟨_, h1, rfl⟩
  · intro l hl
    rw [Finset.mem_singleton.1 hl]
    exact (mem_kl D _).2 ⟨_, h2, rfl⟩
  · rw [hR, cut_eq]

theorem axK {V : Type} [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.KLine V)) (C : PEqualNP.ProofComplexity.Clause V)
    (hd : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' F) π) (h : C ∈ F) :
    PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' F) (PEqualNP.ProofComplexity.kLineOfClause C :: π) :=
  PEqualNP.ProofComplexity.IsResKDerivation.ax hd ⟨C, h, rfl⟩ (ax_card C)

theorem kl_empty {V : Type} [DecidableEq V] : PEqualNP.ProofComplexity.kLineOfClause (∅ : PEqualNP.ProofComplexity.Clause V) = ∅ := Finset.image_empty _


def K0 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((0, 1), true), ((0, 2), true)}
def K1 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 0), true), ((1, 1), true), ((1, 2), true)}
def K2 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((2, 0), true), ((2, 1), true), ((2, 2), true)}
def K3 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((3, 0), true), ((3, 1), true), ((3, 2), true)}
def K4 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), false), ((1, 0), false)}
def K5 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), false), ((2, 0), false)}
def K6 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), false), ((3, 0), false)}
def K7 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 0), false), ((2, 0), false)}
def K8 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 0), false), ((3, 0), false)}
def K9 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((2, 0), false), ((3, 0), false)}
def K10 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 1), false), ((1, 1), false)}
def K11 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 1), false), ((2, 1), false)}
def K12 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 1), false), ((3, 1), false)}
def K13 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 1), false), ((2, 1), false)}
def K14 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 1), false), ((3, 1), false)}
def K15 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((2, 1), false), ((3, 1), false)}
def K16 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), false), ((1, 2), false)}
def K17 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), false), ((2, 2), false)}
def K18 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), false), ((3, 2), false)}
def K19 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 2), false), ((2, 2), false)}
def K20 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 2), false), ((3, 2), false)}
def K21 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((2, 2), false), ((3, 2), false)}
def K22 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), false), ((2, 0), true), ((2, 1), true)}
def K23 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((0, 1), true), ((2, 0), true), ((2, 1), true)}
def K24 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((0, 1), true), ((2, 1), true), ((3, 0), false)}
def K25 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 1), true), ((2, 1), true), ((3, 0), false)}
def K26 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 1), true), ((2, 1), true), ((3, 1), true), ((3, 2), true)}
def K27 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), false), ((2, 1), true), ((2, 2), true)}
def K28 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 1), true), ((0, 2), true), ((2, 1), true), ((2, 2), true)}
def K29 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 1), true), ((2, 1), true), ((2, 2), true), ((3, 2), false)}
def K30 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 1), true), ((2, 1), true), ((3, 2), false)}
def K31 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 1), true), ((2, 1), true), ((3, 1), true)}
def K32 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 1), true), ((1, 1), false), ((3, 1), true)}
def K33 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 1), false), ((3, 1), true)}
def K34 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 1), false)}
def K35 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 0), true), ((1, 2), true)}
def K36 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 1), false), ((2, 0), true), ((2, 2), true)}
def K37 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((0, 2), true), ((2, 0), true), ((2, 2), true)}
def K38 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), true), ((2, 0), true), ((2, 2), true), ((3, 0), false)}
def K39 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), true), ((2, 2), true), ((3, 0), false)}
def K40 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), true), ((2, 2), true), ((3, 1), true), ((3, 2), true)}
def K41 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), true), ((2, 1), true), ((2, 2), true), ((3, 1), false)}
def K42 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), true), ((2, 2), true), ((3, 1), false)}
def K43 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), true), ((2, 2), true), ((3, 2), true)}
def K44 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), true), ((1, 2), false), ((2, 2), true)}
def K45 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 2), true), ((1, 2), false)}
def K46 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 2), false)}
def K47 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 0), true)}
def K48 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((0, 2), true), ((2, 0), true), ((3, 2), false)}
def K49 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((2, 0), true), ((3, 2), false)}
def K50 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((2, 0), true), ((2, 1), true), ((3, 1), false)}
def K51 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((2, 0), true), ((3, 1), false)}
def K52 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((2, 0), true), ((3, 0), true), ((3, 2), true)}
def K53 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((2, 0), true), ((3, 0), true)}
def K54 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((1, 0), false), ((2, 0), true)}
def K55 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((0, 0), true), ((1, 0), false)}
def K56 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := {((1, 0), false)}
def K57 : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3) := ∅

def p0 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := []
def p1 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K0 :: p0
def p2 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K1 :: p1
def p3 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K2 :: p2
def p4 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K3 :: p3
def p5 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K4 :: p4
def p6 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K5 :: p5
def p7 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K6 :: p6
def p8 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K7 :: p7
def p9 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K8 :: p8
def p10 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K9 :: p9
def p11 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K10 :: p10
def p12 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K11 :: p11
def p13 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K12 :: p12
def p14 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K13 :: p13
def p15 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K14 :: p14
def p16 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K15 :: p15
def p17 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K16 :: p16
def p18 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K17 :: p17
def p19 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K18 :: p18
def p20 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K19 :: p19
def p21 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K20 :: p20
def p22 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K21 :: p21
def p23 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K22 :: p22
def p24 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K23 :: p23
def p25 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K24 :: p24
def p26 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K25 :: p25
def p27 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K26 :: p26
def p28 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K27 :: p27
def p29 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K28 :: p28
def p30 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K29 :: p29
def p31 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K30 :: p30
def p32 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K31 :: p31
def p33 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K32 :: p32
def p34 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K33 :: p33
def p35 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K34 :: p34
def p36 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K35 :: p35
def p37 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K36 :: p36
def p38 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K37 :: p37
def p39 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K38 :: p38
def p40 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K39 :: p39
def p41 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K40 :: p40
def p42 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K41 :: p41
def p43 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K42 :: p42
def p44 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K43 :: p43
def p45 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K44 :: p44
def p46 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K45 :: p45
def p47 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K46 :: p46
def p48 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K47 :: p47
def p49 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K48 :: p48
def p50 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K49 :: p49
def p51 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K50 :: p50
def p52 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K51 :: p51
def p53 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K52 :: p52
def p54 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K53 :: p53
def p55 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K54 :: p54
def p56 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K55 :: p55
def p57 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K56 :: p56
def p58 : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) := PEqualNP.ProofComplexity.kLineOfClause K57 :: p57

theorem d0 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p0 := PEqualNP.ProofComplexity.IsResKDerivation.nil
theorem d1 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p1 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p0 K0 d0 (Or.inl ⟨0, by decide⟩)
theorem d2 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p2 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p1 K1 d1 (Or.inl ⟨1, by decide⟩)
theorem d3 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p3 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p2 K2 d2 (Or.inl ⟨2, by decide⟩)
theorem d4 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p4 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p3 K3 d3 (Or.inl ⟨3, by decide⟩)
theorem d5 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p5 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p4 K4 d4 (Or.inr ⟨0, 1, 0, by decide, by decide⟩)
theorem d6 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p6 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p5 K5 d5 (Or.inr ⟨0, 2, 0, by decide, by decide⟩)
theorem d7 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p7 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p6 K6 d6 (Or.inr ⟨0, 3, 0, by decide, by decide⟩)
theorem d8 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p8 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p7 K7 d7 (Or.inr ⟨1, 2, 0, by decide, by decide⟩)
theorem d9 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p9 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p8 K8 d8 (Or.inr ⟨1, 3, 0, by decide, by decide⟩)
theorem d10 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p10 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p9 K9 d9 (Or.inr ⟨2, 3, 0, by decide, by decide⟩)
theorem d11 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p11 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p10 K10 d10 (Or.inr ⟨0, 1, 1, by decide, by decide⟩)
theorem d12 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p12 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p11 K11 d11 (Or.inr ⟨0, 2, 1, by decide, by decide⟩)
theorem d13 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p13 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p12 K12 d12 (Or.inr ⟨0, 3, 1, by decide, by decide⟩)
theorem d14 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p14 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p13 K13 d13 (Or.inr ⟨1, 2, 1, by decide, by decide⟩)
theorem d15 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p15 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p14 K14 d14 (Or.inr ⟨1, 3, 1, by decide, by decide⟩)
theorem d16 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p16 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p15 K15 d15 (Or.inr ⟨2, 3, 1, by decide, by decide⟩)
theorem d17 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p17 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p16 K16 d16 (Or.inr ⟨0, 1, 2, by decide, by decide⟩)
theorem d18 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p18 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p17 K17 d17 (Or.inr ⟨0, 2, 2, by decide, by decide⟩)
theorem d19 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p19 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p18 K18 d18 (Or.inr ⟨0, 3, 2, by decide, by decide⟩)
theorem d20 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p20 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p19 K19 d19 (Or.inr ⟨1, 2, 2, by decide, by decide⟩)
theorem d21 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p21 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p20 K20 d20 (Or.inr ⟨1, 3, 2, by decide, by decide⟩)
theorem d22 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p22 :=
  axK (PEqualNP.ProofComplexity.PHP 4 3) p21 K21 d21 (Or.inr ⟨2, 3, 2, by decide, by decide⟩)
theorem d23 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p23 :=
  cutK _ p22 K17 K2 K22 ((2, 2) : (Fin 4 × Fin 3)) d22 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))) (by decide) (by decide) (by decide)
theorem d24 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p24 :=
  cutK _ p23 K22 K0 K23 ((0, 2) : (Fin 4 × Fin 3)) d23 (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))) (by decide) (by decide) (by decide)
theorem d25 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p25 :=
  cutK _ p24 K9 K23 K24 ((2, 0) : (Fin 4 × Fin 3)) d24 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d26 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p26 :=
  cutK _ p25 K6 K24 K25 ((0, 0) : (Fin 4 × Fin 3)) d25 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d27 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p27 :=
  cutK _ p26 K25 K3 K26 ((3, 0) : (Fin 4 × Fin 3)) d26 (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))) (by decide) (by decide) (by decide)
theorem d28 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p28 :=
  cutK _ p27 K5 K2 K27 ((2, 0) : (Fin 4 × Fin 3)) d27 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))) (by decide) (by decide) (by decide)
theorem d29 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p29 :=
  cutK _ p28 K27 K0 K28 ((0, 0) : (Fin 4 × Fin 3)) d28 (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))) (by decide) (by decide) (by decide)
theorem d30 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p30 :=
  cutK _ p29 K18 K28 K29 ((0, 2) : (Fin 4 × Fin 3)) d29 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d31 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p31 :=
  cutK _ p30 K21 K29 K30 ((2, 2) : (Fin 4 × Fin 3)) d30 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d32 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p32 :=
  cutK _ p31 K30 K26 K31 ((3, 2) : (Fin 4 × Fin 3)) d31 (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) (by decide) (by decide) (by decide)
theorem d33 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p33 :=
  cutK _ p32 K13 K31 K32 ((2, 1) : (Fin 4 × Fin 3)) d32 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d34 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p34 :=
  cutK _ p33 K10 K32 K33 ((0, 1) : (Fin 4 × Fin 3)) d33 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d35 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p35 :=
  cutK _ p34 K14 K33 K34 ((3, 1) : (Fin 4 × Fin 3)) d34 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d36 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p36 :=
  cutK _ p35 K34 K1 K35 ((1, 1) : (Fin 4 × Fin 3)) d35 (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))) (by decide) (by decide) (by decide)
theorem d37 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p37 :=
  cutK _ p36 K11 K2 K36 ((2, 1) : (Fin 4 × Fin 3)) d36 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))) (by decide) (by decide) (by decide)
theorem d38 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p38 :=
  cutK _ p37 K36 K0 K37 ((0, 1) : (Fin 4 × Fin 3)) d37 (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))))))))))) (by decide) (by decide) (by decide)
theorem d39 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p39 :=
  cutK _ p38 K6 K37 K38 ((0, 0) : (Fin 4 × Fin 3)) d38 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d40 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p40 :=
  cutK _ p39 K9 K38 K39 ((2, 0) : (Fin 4 × Fin 3)) d39 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d41 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p41 :=
  cutK _ p40 K39 K3 K40 ((3, 0) : (Fin 4 × Fin 3)) d40 (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))))))))))) (by decide) (by decide) (by decide)
theorem d42 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p42 :=
  cutK _ p41 K12 K28 K41 ((0, 1) : (Fin 4 × Fin 3)) d41 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))) (by decide) (by decide) (by decide)
theorem d43 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p43 :=
  cutK _ p42 K15 K41 K42 ((2, 1) : (Fin 4 × Fin 3)) d42 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d44 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p44 :=
  cutK _ p43 K42 K40 K43 ((3, 1) : (Fin 4 × Fin 3)) d43 (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (by decide) (by decide) (by decide)
theorem d45 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p45 :=
  cutK _ p44 K20 K43 K44 ((3, 2) : (Fin 4 × Fin 3)) d44 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d46 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p46 :=
  cutK _ p45 K19 K44 K45 ((2, 2) : (Fin 4 × Fin 3)) d45 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d47 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p47 :=
  cutK _ p46 K16 K45 K46 ((0, 2) : (Fin 4 × Fin 3)) d46 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d48 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p48 :=
  cutK _ p47 K46 K35 K47 ((1, 2) : (Fin 4 × Fin 3)) d47 (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))) (by decide) (by decide) (by decide)
theorem d49 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p49 :=
  cutK _ p48 K21 K37 K48 ((2, 2) : (Fin 4 × Fin 3)) d48 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))) (by decide) (by decide) (by decide)
theorem d50 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p50 :=
  cutK _ p49 K18 K48 K49 ((0, 2) : (Fin 4 × Fin 3)) d49 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d51 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p51 :=
  cutK _ p50 K12 K23 K50 ((0, 1) : (Fin 4 × Fin 3)) d50 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))) (by decide) (by decide) (by decide)
theorem d52 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p52 :=
  cutK _ p51 K15 K50 K51 ((2, 1) : (Fin 4 × Fin 3)) d51 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d53 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p53 :=
  cutK _ p52 K51 K3 K52 ((3, 1) : (Fin 4 × Fin 3)) d52 (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide) (by decide)
theorem d54 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p54 :=
  cutK _ p53 K49 K52 K53 ((3, 2) : (Fin 4 × Fin 3)) d53 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d55 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p55 :=
  cutK _ p54 K8 K53 K54 ((3, 0) : (Fin 4 × Fin 3)) d54 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d56 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p56 :=
  cutK _ p55 K7 K54 K55 ((2, 0) : (Fin 4 × Fin 3)) d55 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d57 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p57 :=
  cutK _ p56 K4 K55 K56 ((0, 0) : (Fin 4 × Fin 3)) d56 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))))))))))))))))))) (List.mem_cons_self ..) (by decide) (by decide) (by decide)
theorem d58 : PEqualNP.ProofComplexity.IsResKDerivation 2 ((fun C => PEqualNP.ProofComplexity.kLineOfClause C) '' (PEqualNP.ProofComplexity.PHP 4 3)) p58 :=
  cutK _ p57 K56 K47 K57 ((1, 0) : (Fin 4 × Fin 3)) d57 (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))) (by decide) (by decide) (by decide)
theorem fin : (∅ : PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) ∈ p58 := by
  show (∅ : PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)) ∈ PEqualNP.ProofComplexity.kLineOfClause (∅ : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)) :: p57
  rw [kl_empty]; exact List.mem_cons_self ..

end PEqualNP.Outside.L_pcx_193

open PEqualNP.Outside.L_pcx_193 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_pcx_193 : ∃ π : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsResKRefutation 2 (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 62 := by
  exact ⟨p58, ⟨d58, fin⟩, by decide⟩

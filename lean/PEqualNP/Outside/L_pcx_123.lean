import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_123
open PEqualNP.CircuitLowerBounds



def lit (i : Fin 4) (j : Fin 3) (s : Bool) : PEqualNP.ProofComplexity.LinEq (Fin 4 × Fin 3) := (({(i, j)} : Finset (Fin 4 × Fin 3)), s)

def c0 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 0 1 true, lit 0 2 true}
def c1 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 1 0 true, lit 1 1 true, lit 1 2 true}
def c2 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 2 0 true, lit 2 1 true, lit 2 2 true}
def c3 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 3 0 true, lit 3 1 true, lit 3 2 true}
def c4 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 false, lit 1 0 false}
def c5 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 false, lit 2 0 false}
def c6 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 false, lit 3 0 false}
def c7 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 1 0 false, lit 2 0 false}
def c8 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 1 0 false, lit 3 0 false}
def c9 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 2 0 false, lit 3 0 false}
def c10 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 false, lit 1 1 false}
def c11 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 false, lit 2 1 false}
def c12 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 false, lit 3 1 false}
def c13 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 1 1 false, lit 2 1 false}
def c14 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 1 1 false, lit 3 1 false}
def c15 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 2 1 false, lit 3 1 false}
def c16 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 2 false, lit 1 2 false}
def c17 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 2 false, lit 2 2 false}
def c18 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 2 false, lit 3 2 false}
def c19 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 1 2 false, lit 2 2 false}
def c20 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 1 2 false, lit 3 2 false}
def c21 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 2 2 false, lit 3 2 false}
def c22 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 0 1 true, lit 1 2 false}
def c23 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 1 2 false, lit 3 1 false}
def c24 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 1 0 true, lit 1 1 true, lit 3 1 false}
def c25 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 1 0 true, lit 3 1 false}
def c26 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 1 0 true, lit 3 0 true, lit 3 2 true}
def c27 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 0 2 true, lit 1 1 false}
def c28 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 0 2 true, lit 1 0 true, lit 1 2 true}
def c29 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 1 0 true, lit 1 2 true, lit 3 2 false}
def c30 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 1 0 true, lit 3 2 false}
def c31 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 1 0 true, lit 3 0 true}
def c32 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 1 0 true, lit 2 0 false}
def c33 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 2 0 false}
def c34 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 2 0 false}
def c35 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 true, lit 1 2 false, lit 3 0 false}
def c36 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 true, lit 1 0 true, lit 1 1 true, lit 3 0 false}
def c37 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 true, lit 1 1 true, lit 3 0 false}
def c38 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 true, lit 1 1 true, lit 3 1 true, lit 3 2 true}
def c39 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 true, lit 0 2 true, lit 1 0 false}
def c40 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 true, lit 0 2 true, lit 1 1 true, lit 1 2 true}
def c41 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 true, lit 0 2 true, lit 1 1 true, lit 3 2 false}
def c42 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 true, lit 1 1 true, lit 3 2 false}
def c43 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 true, lit 1 1 true, lit 3 1 true}
def c44 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 true, lit 2 1 false, lit 3 1 true}
def c45 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 2 1 false, lit 3 1 true}
def c46 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 2 1 false}
def c47 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 2 0 true, lit 2 2 true}
def c48 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 1 true, lit 0 2 true, lit 1 2 true, lit 3 1 false}
def c49 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 2 true, lit 1 2 true, lit 3 1 false}
def c50 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 0 true, lit 0 2 true, lit 1 2 true, lit 3 0 false}
def c51 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 2 true, lit 1 2 true, lit 3 0 false}
def c52 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 2 true, lit 1 2 true, lit 3 1 true, lit 3 2 true}
def c53 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 2 true, lit 1 2 true, lit 3 2 true}
def c54 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 0 2 true, lit 2 2 false, lit 3 2 true}
def c55 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 2 2 false, lit 3 2 true}
def c56 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 2 2 false}
def c57 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := {lit 2 0 true}
def c58 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) := ∅

def p0 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := []
def p1 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c0 :: p0
def p2 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c1 :: p1
def p3 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c2 :: p2
def p4 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c3 :: p3
def p5 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c4 :: p4
def p6 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c5 :: p5
def p7 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c6 :: p6
def p8 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c7 :: p7
def p9 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c8 :: p8
def p10 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c9 :: p9
def p11 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c10 :: p10
def p12 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c11 :: p11
def p13 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c12 :: p12
def p14 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c13 :: p13
def p15 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c14 :: p14
def p16 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c15 :: p15
def p17 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c16 :: p16
def p18 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c17 :: p17
def p19 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c18 :: p18
def p20 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c19 :: p19
def p21 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c20 :: p20
def p22 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c21 :: p21
def p23 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c22 :: p22
def p24 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c23 :: p23
def p25 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c24 :: p24
def p26 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c25 :: p25
def p27 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c26 :: p26
def p28 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c27 :: p27
def p29 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c28 :: p28
def p30 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c29 :: p29
def p31 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c30 :: p30
def p32 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c31 :: p31
def p33 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c32 :: p32
def p34 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c33 :: p33
def p35 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c34 :: p34
def p36 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c35 :: p35
def p37 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c36 :: p36
def p38 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c37 :: p37
def p39 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c38 :: p38
def p40 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c39 :: p39
def p41 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c40 :: p40
def p42 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c41 :: p41
def p43 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c42 :: p42
def p44 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c43 :: p43
def p45 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c44 :: p44
def p46 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c45 :: p45
def p47 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c46 :: p46
def p48 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c47 :: p47
def p49 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c48 :: p48
def p50 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c49 :: p49
def p51 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c50 :: p50
def p52 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c51 :: p51
def p53 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c52 :: p52
def p54 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c53 :: p53
def p55 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c54 :: p54
def p56 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c55 :: p55
def p57 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c56 :: p56
def p58 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c57 :: p57
def p59 : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)) := c58 :: p58

theorem d0 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p0 := PEqualNP.ProofComplexity.IsLinDerivation.nil
theorem d1 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p1 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d0 ⟨({((0, 0), true), ((0, 1), true), ((0, 2), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inl ⟨0, by decide⟩, by decide⟩
theorem d2 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p2 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d1 ⟨({((1, 0), true), ((1, 1), true), ((1, 2), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inl ⟨1, by decide⟩, by decide⟩
theorem d3 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p3 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d2 ⟨({((2, 0), true), ((2, 1), true), ((2, 2), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inl ⟨2, by decide⟩, by decide⟩
theorem d4 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p4 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d3 ⟨({((3, 0), true), ((3, 1), true), ((3, 2), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inl ⟨3, by decide⟩, by decide⟩
theorem d5 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p5 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d4 ⟨({((0, 0), false), ((1, 0), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨0, 1, 0, by decide, by decide⟩, by decide⟩
theorem d6 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p6 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d5 ⟨({((0, 0), false), ((2, 0), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨0, 2, 0, by decide, by decide⟩, by decide⟩
theorem d7 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p7 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d6 ⟨({((0, 0), false), ((3, 0), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨0, 3, 0, by decide, by decide⟩, by decide⟩
theorem d8 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p8 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d7 ⟨({((1, 0), false), ((2, 0), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨1, 2, 0, by decide, by decide⟩, by decide⟩
theorem d9 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p9 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d8 ⟨({((1, 0), false), ((3, 0), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨1, 3, 0, by decide, by decide⟩, by decide⟩
theorem d10 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p10 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d9 ⟨({((2, 0), false), ((3, 0), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨2, 3, 0, by decide, by decide⟩, by decide⟩
theorem d11 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p11 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d10 ⟨({((0, 1), false), ((1, 1), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨0, 1, 1, by decide, by decide⟩, by decide⟩
theorem d12 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p12 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d11 ⟨({((0, 1), false), ((2, 1), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨0, 2, 1, by decide, by decide⟩, by decide⟩
theorem d13 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p13 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d12 ⟨({((0, 1), false), ((3, 1), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨0, 3, 1, by decide, by decide⟩, by decide⟩
theorem d14 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p14 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d13 ⟨({((1, 1), false), ((2, 1), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨1, 2, 1, by decide, by decide⟩, by decide⟩
theorem d15 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p15 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d14 ⟨({((1, 1), false), ((3, 1), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨1, 3, 1, by decide, by decide⟩, by decide⟩
theorem d16 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p16 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d15 ⟨({((2, 1), false), ((3, 1), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨2, 3, 1, by decide, by decide⟩, by decide⟩
theorem d17 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p17 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d16 ⟨({((0, 2), false), ((1, 2), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨0, 1, 2, by decide, by decide⟩, by decide⟩
theorem d18 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p18 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d17 ⟨({((0, 2), false), ((2, 2), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨0, 2, 2, by decide, by decide⟩, by decide⟩
theorem d19 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p19 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d18 ⟨({((0, 2), false), ((3, 2), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨0, 3, 2, by decide, by decide⟩, by decide⟩
theorem d20 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p20 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d19 ⟨({((1, 2), false), ((2, 2), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨1, 2, 2, by decide, by decide⟩, by decide⟩
theorem d21 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p21 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d20 ⟨({((1, 2), false), ((3, 2), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨1, 3, 2, by decide, by decide⟩, by decide⟩
theorem d22 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p22 :=
  PEqualNP.ProofComplexity.IsLinDerivation.ax d21 ⟨({((2, 2), false), ((3, 2), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), Or.inr ⟨2, 3, 2, by decide, by decide⟩, by decide⟩
theorem d23 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p23 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d22 (C := c16) (D := c0) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))
    ⟨({(0, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d24 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p24 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d23 (C := c12) (D := c22) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))) (List.mem_cons_self ..)
    ⟨({(0, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d25 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p25 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d24 (C := c23) (D := c1) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))
    ⟨({(1, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d26 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p26 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d25 (C := c14) (D := c24) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))) (List.mem_cons_self ..)
    ⟨({(1, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d27 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p27 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d26 (C := c25) (D := c3) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))
    ⟨({(3, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d28 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p28 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d27 (C := c10) (D := c0) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))
    ⟨({(0, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d29 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p29 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d28 (C := c27) (D := c1) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))
    ⟨({(1, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d30 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p30 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d29 (C := c18) (D := c28) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))) (List.mem_cons_self ..)
    ⟨({(0, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d31 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p31 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d30 (C := c20) (D := c29) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))) (List.mem_cons_self ..)
    ⟨({(1, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d32 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p32 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d31 (C := c30) (D := c26) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    ⟨({(3, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d33 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p33 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d32 (C := c9) (D := c31) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(3, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d34 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p34 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d33 (C := c7) (D := c32) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(1, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d35 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p35 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d34 (C := c5) (D := c33) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(0, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d36 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p36 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d35 (C := c6) (D := c22) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))
    ⟨({(0, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d37 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p37 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d36 (C := c35) (D := c1) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))
    ⟨({(1, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d38 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p38 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d37 (C := c8) (D := c36) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(1, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d39 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p39 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d38 (C := c37) (D := c3) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))
    ⟨({(3, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d40 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p40 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d39 (C := c4) (D := c0) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))))))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))))))
    ⟨({(0, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d41 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p41 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d40 (C := c39) (D := c1) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))))))
    ⟨({(1, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d42 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p42 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d41 (C := c20) (D := c40) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(1, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d43 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p43 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d42 (C := c18) (D := c41) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(0, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d44 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p44 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d43 (C := c42) (D := c38) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    ⟨({(3, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d45 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p45 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d44 (C := c13) (D := c43) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(1, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d46 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p46 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d45 (C := c11) (D := c44) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(0, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d47 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p47 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d46 (C := c15) (D := c45) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(3, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d48 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p48 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d47 (C := c46) (D := c2) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))))))))))))
    ⟨({(2, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d49 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p49 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d48 (C := c14) (D := c40) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))
    ⟨({(1, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d50 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p50 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d49 (C := c12) (D := c48) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(0, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d51 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p51 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d50 (C := c8) (D := c28) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))))))))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))
    ⟨({(1, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d52 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p52 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d51 (C := c6) (D := c50) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(0, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d53 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p53 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d52 (C := c51) (D := c3) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))))))))))))))))
    ⟨({(3, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d54 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p54 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d53 (C := c49) (D := c52) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (List.mem_cons_self ..)
    ⟨({(3, 1)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d55 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p55 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d54 (C := c19) (D := c53) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(1, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d56 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p56 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d55 (C := c17) (D := c54) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(0, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d57 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p57 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d56 (C := c21) (D := c55) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))))))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(3, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d58 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p58 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d57 (C := c56) (D := c47) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))
    ⟨({(2, 2)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩
theorem d59 : PEqualNP.ProofComplexity.IsLinDerivation ((fun C => PEqualNP.ProofComplexity.linOfClause C) '' PEqualNP.ProofComplexity.PHP 4 3) p59 :=
  PEqualNP.ProofComplexity.IsLinDerivation.res d58 (C := c34) (D := c57) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))))))))))))))) (List.mem_cons_self ..)
    ⟨({(2, 0)} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩

end PEqualNP.Outside.L_pcx_123

open PEqualNP.Outside.L_pcx_123 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_pcx_123 : ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 59 := by
  exact ⟨p59, ⟨d59, List.mem_cons_self ..⟩, by decide⟩

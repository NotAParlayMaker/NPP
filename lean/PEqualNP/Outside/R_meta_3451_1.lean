import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

/-- The 4-cycle-free hypothesis on the incidence relation `I`: no two distinct
points are both incident to two distinct lines. -/
abbrev NoFourCycle3451 (N : ℕ) (I : Fin N → Fin N → Prop) : Prop :=
  ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')

/-- The edge function on `N + N` inputs: the circuit outputs `true` exactly on the
inputs where some incident point-line pair is both on. -/
abbrev EdgeFun3451 (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
  ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
    ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

/-- Every AND gate of `C` is false on every one-hot input: a single point on, or a
single line on. -/
abbrev CleanSingles3451 (N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
  ∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
      PEqualNP.CircuitLowerBounds.GateOp.and →
    (∀ p : Fin N, (C.wires (List.ofFn (fun kc : Fin (N + N) =>
        decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
    ∀ l : Fin N, (C.wires (List.ofFn (fun kd : Fin (N + N) =>
        decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false

/-- Every AND gate of `C` is false on every non-incident point-line input: one point
and one line on, with the point not incident to the line. -/
abbrev CleanPairs3451 (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
  ∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
      PEqualNP.CircuitLowerBounds.GateOp.and →
    ∀ p0 l0 : Fin N, ¬ I p0 l0 →
      (C.wires (List.ofFn (fun ke : Fin (N + N) =>
          decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD
        (N + N + j) false = false

/-- The cut of L-meta-3451 into two smaller statements, as suggested by the gap
sketch: first make every AND false at single inputs, then make every AND false at
one point with one non-incident line, preserving the first cleaning. If both steps
hold, the full statement follows by composition. -/
theorem R_meta_3451_1
    (cleanSinglesStep : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      NoFourCycle3451 N I → PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C →
      EdgeFun3451 N I C →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C' ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C' ∧
        C'.size ≤ C.size ∧ EdgeFun3451 N I C' ∧ CleanSingles3451 N C')
    (cleanPairsStep : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C' : PEqualNP.CircuitLowerBounds.Circuit),
      NoFourCycle3451 N I → PEqualNP.MetaComplexity.Monotone2 C' →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C' →
      EdgeFun3451 N I C' → CleanSingles3451 N C' →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
        D.size ≤ C'.size ∧ EdgeFun3451 N I D ∧
        CleanSingles3451 N D ∧ CleanPairs3451 N I D) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      NoFourCycle3451 N I → PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C →
      EdgeFun3451 N I C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
        D.size ≤ C.size ∧ EdgeFun3451 N I D ∧
        CleanPairs3451 N I D ∧ CleanSingles3451 N D := by
  intro N I hDec C hNoCycle hMono hRB hEdge
  obtain ⟨C', hMono', hRB', hSize', hEdge', hClean'⟩ :=
    cleanSinglesStep N I C hNoCycle hMono hRB hEdge
  obtain ⟨D, hMonoD, hRBD, hSizeD, hEdgeD, hCleanD, hPairsD⟩ :=
    cleanPairsStep N I C' hNoCycle hMono' hRB' hEdge' hClean'
  exact ⟨D, hMonoD, hRBD, hSizeD.trans hSize', hEdgeD, hPairsD, hCleanD⟩

end PEqualNP.Outside

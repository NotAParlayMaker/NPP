import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18063_aux

open PEqualNP.CircuitLowerBounds

def mk {k : ℕ} (t : Bool × Fin k × Fin k) : Gate :=
  { op := if t.1 then GateOp.or else GateOp.and, inputs := [(t.2.1 : ℕ), (t.2.2 : ℕ)] }

theorem fold_eq {k : ℕ} (gs : List (Bool × Fin k × Fin k)) (L : List Bool) :
    (gs.map mk).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) L =
    gs.foldl (fun (x8 : List Bool) (x9 : Bool × Fin k × Fin k) =>
      have x10 : Bool := x8.getD (↑x9.2.1) Bool.false
      have x11 : Bool := x8.getD (↑x9.2.2) Bool.false
      x8 ++ [bif x9.1 then x10 || x11 else x10 && x11]) L := by
  induction gs generalizing L with
  | nil => rfl
  | cons t gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    congr 2
    rcases t with ⟨b, i, j⟩
    cases b <;> simp [mk, GateOp.eval]

end PEqualNP.Outside.L_meta_18063_aux

open PEqualNP.Outside.L_meta_18063_aux in
theorem PEqualNP.Outside.L_meta_18063 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Bool × Fin (x1 + x2) × Fin (x1 + x2)) (x4 : ℕ),   (∀ (x5 : Fin x2), Max.max ↑(x3 x5).2.1 ↑(x3 x5).2.2 < x1 + ↑x5) →     ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.Monotone2 x6 ∧         PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x6 ∧           x6.size = x2 ∧             ∀ (x7 : Fin x1 → Bool),               PEqualNP.MetaComplexity.circuitFun x1 x6 x7 =                 (List.foldl                       (fun (x8 : List Bool) (x9 : Bool × Fin (x1 + x2) × Fin (x1 + x2)) =>                         have x10 : Bool := x8.getD (↑x9.2.1) Bool.false;                         have x11 : Bool := x8.getD (↑x9.2.2) Bool.false;                         x8 ++ [bif x9.1 then x10 || x11 else x10 && x11])                       (List.ofFn x7) (List.ofFn x3)).getD                   x4 Bool.false := by
  intro n m g o hg
  refine ⟨{ gates := (List.ofFn g).map mk, output := o }, ?_, ?_, ?_, ?_⟩
  · intro gt hgt
    simp only [List.mem_map, List.mem_ofFn] at hgt
    obtain ⟨t, _, rfl⟩ := hgt
    by_cases h : t.1 <;> simp [mk, h]
  · intro j hj i hi
    simp only [List.length_map, List.length_ofFn] at hj
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt
        { gates := (List.ofFn g).map mk, output := o } j = mk (g ⟨j, hj⟩) := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
    rw [e] at hi
    have := hg ⟨j, hj⟩
    simp only [Fin.val_mk] at this
    simp only [mk, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires]
    rw [fold_eq]

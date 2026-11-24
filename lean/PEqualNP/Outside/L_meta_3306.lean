import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3306

open PEqualNP.CircuitLowerBounds

def fix (P L : Finset ℕ) (g : Gate) : Gate :=
  match g with
  | ⟨GateOp.and, [a, b]⟩ => if a ∈ L ∧ b ∈ P then ⟨GateOp.and, [a, b]⟩ else ⟨GateOp.and, [b, a]⟩
  | g => g

theorem fix_op (P L : Finset ℕ) (g : Gate) : (fix P L g).op = g.op := by
  rcases g with ⟨op, xs⟩
  cases op <;> rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp [fix] <;> split_ifs <;> rfl

theorem fix_mem (P L : Finset ℕ) (g : Gate) (i : ℕ) : i ∈ (fix P L g).inputs ↔ i ∈ g.inputs := by
  rcases g with ⟨op, xs⟩
  cases op <;> rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp [fix] <;> split_ifs <;> simp [or_comm]

theorem fix_len (P L : Finset ℕ) (g : Gate) : (fix P L g).inputs.length = g.inputs.length := by
  rcases g with ⟨op, xs⟩
  cases op <;> rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp [fix] <;> split_ifs <;> rfl

theorem fix_eval (P L : Finset ℕ) (g : Gate) (F : ℕ → Bool) :
    (fix P L g).op.eval ((fix P L g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  rcases g with ⟨op, xs⟩
  cases op <;> rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp [fix] <;> split_ifs <;>
    simp [GateOp.eval, Bool.and_comm]

theorem fix_or (P L : Finset ℕ) (g : Gate) (h : g.op = GateOp.or) : fix P L g = g := by
  rcases g with ⟨op, xs⟩
  simp only at h
  subst h
  rfl

theorem fix_and (P L : Finset ℕ) (g : Gate) (a b : ℕ) (hin : g.inputs = [a, b])
    (hop : g.op = GateOp.and) (hm : (a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) :
    ∃ c d, (fix P L g).inputs = [c, d] ∧ c ∈ L ∧ d ∈ P := by
  rcases g with ⟨op, xs⟩
  simp only at hin hop
  subst hin hop
  by_cases h : a ∈ L ∧ b ∈ P
  · exact ⟨a, b, by simp [fix, h], h.1, h.2⟩
  · have h' : a ∈ P ∧ b ∈ L := by tauto
    exact ⟨b, a, by simp [fix, h], h'.2, h'.1⟩

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_fix (P L : Finset ℕ) (gs : List Gate) : ∀ w : List Bool,
    wf (gs.map (fix P L)) w = wf gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wf ((g :: gs).map (fix P L)) w = wf (gs.map (fix P L))
        (w ++ [(fix P L g).op.eval ((fix P L g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, fix_eval, ih]

theorem gateAt_fix (P L : Finset ℕ) (C : Circuit) (j : ℕ) :
    PEqualNP.MetaComplexity.NestedCover.gateAt ⟨C.gates.map (fix P L), C.output⟩ j =
      fix P L (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  by_cases hj : j < C.gates.length
  · simp [List.getD_eq_getElem?_getD, hj]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rfl

end PEqualNP.Outside.L_meta_3306

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3306 in
theorem PEqualNP.Outside.L_meta_3306 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  intro n C P L hC hand
  obtain ⟨hao, hrb, h2⟩ := hC
  let D : Circuit := ⟨C.gates.map (fix P L), C.output⟩
  have hD : ∀ j, PEqualNP.MetaComplexity.NestedCover.gateAt D j =
      fix P L (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := gateAt_fix P L C
  refine ⟨D, ⟨?_, ?_, ?_⟩, by simp [D, Circuit.size], ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    rw [fix_op]
    exact hao g0 hg0
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [D] using hj
    rw [hD, fix_mem] at hi
    exact hrb j hj' i hi
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    rw [fix_len]
    exact h2 g0 hg0
  · funext x
    show (wf (C.gates.map (fix P L)) (List.ofFn x)).getD C.output false =
      (wf C.gates (List.ofFn x)).getD C.output false
    rw [wf_fix]
  · intro j
    rw [hD, fix_op]
  · intro j hj
    rw [hD, fix_or P L _ hj]
  · intro j hj hop
    have hj' : j < C.gates.length := by simpa [D] using hj
    rw [hD, fix_op] at hop
    obtain ⟨a, b, hin, hm⟩ := hand j hj' hop
    rw [hD]
    exact fix_and P L _ a b hin hop hm

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4091_aux

open PEqualNP.CircuitLowerBounds

/-- One gate appended to the wire list, exactly as `Circuit.wires` does it. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_prefix : ∀ (gs : List Gate) (x : List Bool), ∃ t, gs.foldl step x = x ++ t
  | [], x => ⟨[], by simp⟩
  | g :: gs, x => by
      obtain ⟨t, ht⟩ := foldl_prefix gs (step x g)
      refine ⟨[g.op.eval (g.inputs.map fun i => x.getD i false)] ++ t, ?_⟩
      rw [List.foldl_cons, ht]
      simp only [step, List.append_assoc]

theorem foldl_length : ∀ (gs : List Gate) (x : List Bool),
    (gs.foldl step x).length = x.length + gs.length
  | [], x => by simp
  | g :: gs, x => by
      rw [List.foldl_cons, foldl_length gs, step]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem getD_prefix (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl step x).getD i false = x.getD i false := by
  obtain ⟨t, ht⟩ := foldl_prefix gs x
  rw [ht, List.getD_append _ _ _ _ hi]

end PEqualNP.Outside.L_meta_4091_aux

open PEqualNP.Outside.L_meta_4091_aux in
theorem PEqualNP.Outside.L_meta_4091 : ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size = (44 : ℕ) → x1.output < (70 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (18 : ℕ) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ (63 : ℕ) ∧ ∀ (x9 : List Bool), x9.length = (26 : ℕ) → x8.eval x9 = (x1.eval x9 || x2.eval (x1.wires x9)) := by
  intro x1 x2 h1 hs1 ho1 h2 hs2
  refine ⟨⟨x1.gates ++ x2.gates ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [x1.output, x2.output]⟩],
      70 + x2.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · rcases List.mem_append.1 hg with hg | hg
      · exact h1 g hg
      · exact h2 g hg
    · rw [List.mem_singleton] at hg
      subst hg
      exact ⟨Or.inr rfl, by simp⟩
  · have e1 : x1.gates.length = 44 := hs1
    have e2 : x2.gates.length ≤ 18 := hs2
    show (x1.gates ++ x2.gates ++ _).length ≤ 63
    rw [List.length_append, List.length_append, List.length_singleton]
    omega
  · intro x hx
    have e1 : x1.gates.length = 44 := hs1
    show ((x1.gates ++ x2.gates ++ _).foldl step x).getD (70 + x2.gates.length) false =
      ((x1.gates.foldl step x).getD x1.output false ||
        (x2.gates.foldl step (x1.gates.foldl step x)).getD x2.output false)
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have l1 : (x1.gates.foldl step x).length = 70 := by rw [foldl_length]; omega
    have l2 : (x2.gates.foldl step (x1.gates.foldl step x)).length = 70 + x2.gates.length := by
      rw [foldl_length, l1]
    have p1 := getD_prefix x2.gates (x1.gates.foldl step x) x1.output (by rw [l1]; exact ho1)
    rw [step, ← l2, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    simp only [List.getD_cons_zero, List.map_cons, List.map_nil,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, p1]

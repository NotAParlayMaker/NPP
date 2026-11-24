import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2438

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma ofFn_last {m : ℕ} (f : Fin m → Bool) (b : Bool) :
    List.ofFn (fun i : Fin (m + 1) => (Fin.lastCases b f i : Bool)) = List.ofFn f ++ [b] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

lemma getD_ofFn {m : ℕ} (f : Fin m → Bool) (i : Fin m) :
    (List.ofFn f).getD i.val false = f i := by
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_2438

open PEqualNP.Outside.L_meta_2438 in
theorem PEqualNP.Outside.L_meta_2438 : ∀ (x1 : Fin (42 : ℕ)) (x2 x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 →       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x7 ∧           x7.size ≤ x4.size + (2 : ℕ) ∧             ∀ (x8 : Fin (42 : ℕ) → Bool),               have x9 : Fin (43 : ℕ) → Bool := fun (x9 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 (0 : Fin (42 : ℕ)) || x8 x1) x8 x9;               x7.eval (List.ofFn x8) = x4.eval (List.ofFn fun (x10 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x9 x2 || x9 x3) x9 x10) := by
  intro x1 x2 x3 C hm _
  refine ⟨⟨⟨.or, [0, x1.val]⟩ :: ⟨.or, [x2.val, x3.val]⟩ :: C.gates, C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · simp
    · exact hm g hg
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro y
    dsimp only
    rw [ofFn_last]
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only [List.foldl_cons]
    have h0 : (List.ofFn y).getD 0 false = y 0 := getD_ofFn y 0
    have e1 : List.ofFn y ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
        (([0, x1.val] : List ℕ).map fun i => (List.ofFn y).getD i false)] =
        List.ofFn (fun i : Fin (42 + 1) => (Fin.lastCases (y 0 || y x1) y i : Bool)) := by
      rw [ofFn_last]
      simp only [List.map_cons, List.map_nil, h0, getD_ofFn]
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    rw [e1]
    simp only [List.map_cons, List.map_nil, getD_ofFn]
    have e2 : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) := by
      intro a b; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    rw [e2]

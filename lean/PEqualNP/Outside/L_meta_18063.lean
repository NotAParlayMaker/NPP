import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_18063 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Bool × Fin (x1 + x2) × Fin (x1 + x2)) (x4 : ℕ),   (∀ (x5 : Fin x2), Max.max ↑(x3 x5).2.1 ↑(x3 x5).2.2 < x1 + ↑x5) →     ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.Monotone2 x6 ∧         PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x6 ∧           x6.size = x2 ∧             ∀ (x7 : Fin x1 → Bool),               PEqualNP.MetaComplexity.circuitFun x1 x6 x7 =                 (List.foldl                       (fun (x8 : List Bool) (x9 : Bool × Fin (x1 + x2) × Fin (x1 + x2)) =>                         have x10 : Bool := x8.getD (↑x9.2.1) Bool.false;                         have x11 : Bool := x8.getD (↑x9.2.2) Bool.false;                         x8 ++ [bif x9.1 then x10 || x11 else x10 && x11])                       (List.ofFn x7) (List.ofFn x3)).getD                   x4 Bool.false := by
  intro n m a output earlier
  let mk : Bool × Fin (n+m) × Fin (n+m) → Gate := fun g =>
    ⟨bif g.1 then .or else .and, [g.2.1.val, g.2.2.val]⟩
  let c : Circuit := ⟨(List.ofFn a).map mk, output⟩
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hg
    cases h : v.1 <;> simp [mk, h]
  · intro j hj w hw
    have hj' : j < m := by simpa [c] using hj
    have eq : NestedCover.gateAt c j = mk (a ⟨j, hj'⟩) := by
      unfold NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hj]
      simp [c]
    rw [eq] at hw
    have h : max (a ⟨j,hj'⟩).2.1.val (a ⟨j,hj'⟩).2.2.val < n+j := earlier ⟨j,hj'⟩
    simp only [mk, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact (le_max_left _ _).trans_lt h
    · exact (le_max_right _ _).trans_lt h
  · simp [Circuit.size, c]
  · intro x
    simp only [circuitFun, c, Circuit.eval, Circuit.wires, List.foldl_map]
    congr 2
    funext w v
    cases h : v.1 <;> simp [mk, h, GateOp.eval]

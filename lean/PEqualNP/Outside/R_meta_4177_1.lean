import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4177_1
    (h_copy :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        x1.size ≤ (14 : ℕ) →
        (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) →
        (∃ g ∈ x1.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (g.inputs = [(0 : ℕ)] ∨ g.inputs = [(0 : ℕ), (0 : ℕ)])) →
        ∃ (x6 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then Bool.true != x6 (0 : Fin (9 : ℕ)) else x6 x7) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h_and :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        x1.size ≤ (14 : ℕ) →
        (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) →
        (∃ g ∈ x1.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ w : ℕ, w ≠ (0 : ℕ) ∧ (g.inputs = [(0 : ℕ), w] ∨ g.inputs = [w, (0 : ℕ)])) →
        ∃ (x6 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then Bool.true != x6 (0 : Fin (9 : ℕ)) else x6 x7) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h_or :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        x1.size ≤ (14 : ℕ) →
        (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) →
        (∃ g ∈ x1.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ w : ℕ, w ≠ (0 : ℕ) ∧ (g.inputs = [(0 : ℕ), w] ∨ g.inputs = [w, (0 : ℕ)])) →
        ∃ (x6 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then Bool.true != x6 (0 : Fin (9 : ℕ)) else x6 x7) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → (¬∃ x5 ∈ x1.gates, (0 : ℕ) ∈ x5.inputs ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x6 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then Bool.true != x6 (0 : Fin (9 : ℕ)) else x6 x7) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hfan hsize hlen hnot
  cases hfilt : List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates with
  | nil =>
    rw [hfilt] at hlen
    exact False.elim (Nat.noConfusion hlen)
  | cons g rest =>
    have hg_filt : g ∈ List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates := by
      rw [hfilt]
      exact List.Mem.head rest
    have hg_pair := List.mem_filter.mp hg_filt
    have hg : g ∈ x1.gates := hg_pair.1
    have h0 : (0 : ℕ) ∈ g.inputs := List.contains_iff_mem.mp hg_pair.2
    obtain ⟨hop, hlen_in⟩ := hfan g hg
    have hop_ao : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      rcases hop with h_eq | h_eq | h_eq
      · exact Or.inl h_eq
      · exact Or.inr h_eq
      · exact False.elim (hnot ⟨g, hg, h0, h_eq⟩)
    cases hin : g.inputs with
    | nil =>
      rw [hin] at h0
      cases h0
    | cons a t =>
      cases t with
      | nil =>
        rw [hin] at h0
        have ha0 : a = (0 : ℕ) := (List.mem_singleton.mp h0).symm
        rw [ha0] at hin
        exact h_copy x1 hfan hsize hlen ⟨g, hg, hop_ao, Or.inl hin⟩
      | cons b t2 =>
        cases t2 with
        | nil =>
          by_cases ha0 : a = (0 : ℕ)
          · rw [ha0] at hin
            by_cases hb0 : b = (0 : ℕ)
            · rw [hb0] at hin
              exact h_copy x1 hfan hsize hlen ⟨g, hg, hop_ao, Or.inr hin⟩
            · rcases hop_ao with hand | hor
              · exact h_and x1 hfan hsize hlen ⟨g, hg, hand, b, hb0, Or.inl hin⟩
              · exact h_or x1 hfan hsize hlen ⟨g, hg, hor, b, hb0, Or.inl hin⟩
          · rw [hin] at h0
            have hb0 : b = (0 : ℕ) := by
              rcases List.mem_cons.mp h0 with hbad | hmem
              · exact False.elim (ha0 hbad.symm)
              · exact (List.mem_singleton.mp hmem).symm
            rw [hb0] at hin
            rcases hop_ao with hand | hor
            · exact h_and x1 hfan hsize hlen ⟨g, hg, hand, a, ha0, Or.inr hin⟩
            · exact h_or x1 hfan hsize hlen ⟨g, hg, hor, a, ha0, Or.inr hin⟩
        | cons c t3 =>
          rw [hin] at hlen_in
          exact False.elim (Nat.not_le_of_gt (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le t3.length)))) hlen_in)

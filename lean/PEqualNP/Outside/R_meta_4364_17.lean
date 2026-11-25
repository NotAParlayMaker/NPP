import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4364_17
    (h_or_not_hi :
      let p6 : PEqualNP.CircuitLowerBounds.Gate → Bool :=
        fun (x6 : PEqualNP.CircuitLowerBounds.Gate) =>
          (if x6.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x6.inputs else x6.inputs).any
            fun (x7 : ℕ) => Decidable.decide (x7 = (6 : ℕ))
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        x1.size = (14 : ℕ) →
        x1.output = (23 : ℕ) →
        List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (_ : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) →
        List.countP p6 x1.gates = (1 : ℕ) →
        x1.gates[k]? = some g →
        p6 g = Bool.true →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        (4 : ℕ) ≤ List.countP (fun (h : PEqualNP.CircuitLowerBounds.Gate) => !h.op.eval [Bool.false] && h.inputs.any fun (w : ℕ) => w == (6 : ℕ) || w == (9 : ℕ) || w == (10 : ℕ) + k) x1.gates →
        ∃ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (h_and_hi :
      let p6 : PEqualNP.CircuitLowerBounds.Gate → Bool :=
        fun (x6 : PEqualNP.CircuitLowerBounds.Gate) =>
          (if x6.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x6.inputs else x6.inputs).any
            fun (x7 : ℕ) => Decidable.decide (x7 = (6 : ℕ))
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        x1.size = (14 : ℕ) →
        x1.output = (23 : ℕ) →
        List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (_ : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) →
        List.countP p6 x1.gates = (1 : ℕ) →
        x1.gates[k]? = some g →
        p6 g = Bool.true →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (3 : ℕ) ≤ List.countP (fun (h : PEqualNP.CircuitLowerBounds.Gate) => !h.op.eval [Bool.false] && h.inputs.any fun (w : ℕ) => w == (6 : ℕ) || w == (10 : ℕ) + k) x1.gates →
        ∃ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (h_and_lo :
      let p6 : PEqualNP.CircuitLowerBounds.Gate → Bool :=
        fun (x6 : PEqualNP.CircuitLowerBounds.Gate) =>
          (if x6.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x6.inputs else x6.inputs).any
            fun (x7 : ℕ) => Decidable.decide (x7 = (6 : ℕ))
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        x1.size = (14 : ℕ) →
        x1.output = (23 : ℕ) →
        List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (_ : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) →
        List.countP p6 x1.gates = (1 : ℕ) →
        x1.gates[k]? = some g →
        p6 g = Bool.true →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        List.countP (fun (h : PEqualNP.CircuitLowerBounds.Gate) => !h.op.eval [Bool.false] && h.inputs.any fun (w : ℕ) => w == (6 : ℕ) || w == (10 : ℕ) + k) x1.gates ≤ (2 : ℕ) →
        ∃ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (h_or_not_lo :
      let p6 : PEqualNP.CircuitLowerBounds.Gate → Bool :=
        fun (x6 : PEqualNP.CircuitLowerBounds.Gate) =>
          (if x6.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x6.inputs else x6.inputs).any
            fun (x7 : ℕ) => Decidable.decide (x7 = (6 : ℕ))
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        x1.size = (14 : ℕ) →
        x1.output = (23 : ℕ) →
        List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (_ : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) →
        List.countP p6 x1.gates = (1 : ℕ) →
        x1.gates[k]? = some g →
        p6 g = Bool.true →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        List.countP (fun (h : PEqualNP.CircuitLowerBounds.Gate) => !h.op.eval [Bool.false] && h.inputs.any fun (w : ℕ) => w == (6 : ℕ) || w == (9 : ℕ) || w == (10 : ℕ) + k) x1.gates ≤ (3 : ℕ) →
        ∃ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (14 : ℕ) → x1.output = (23 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (_ : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) → List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => (if x6.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x6.inputs else x6.inputs).any fun (x7 : ℕ) => Decidable.decide (x7 = (6 : ℕ))) x1.gates = (1 : ℕ) → ∃ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 hfan hsize hout hnot hr6
  have hpos : 0 < List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) =>
      (if x6.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x6.inputs else x6.inputs).any
        fun (x7 : ℕ) => Decidable.decide (x7 = (6 : ℕ))) x1.gates := by
    omega
  obtain ⟨g, hgmem, hgp6⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨k, hklt, rfl⟩ := List.getElem_of_mem hgmem
  have hgk : x1.gates[k]? = some x1.gates[k] := List.getElem?_eq_getElem hklt
  have hmem_op : x1.gates[k].op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) :=
    (hfan x1.gates[k] hgmem).1
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem_op
  rcases hmem_op with hand | hor | hnotop
  · by_cases hc : (3 : ℕ) ≤ List.countP (fun (h : PEqualNP.CircuitLowerBounds.Gate) => !h.op.eval [Bool.false] && h.inputs.any fun (w : ℕ) => w == (6 : ℕ) || w == (10 : ℕ) + k) x1.gates
    · exact h_and_hi x1 k x1.gates[k] hfan hsize hout hnot hr6 hgk hgp6 hand hc
    · exact h_and_lo x1 k x1.gates[k] hfan hsize hout hnot hr6 hgk hgp6 hand (by omega)
  · by_cases hc : (4 : ℕ) ≤ List.countP (fun (h : PEqualNP.CircuitLowerBounds.Gate) => !h.op.eval [Bool.false] && h.inputs.any fun (w : ℕ) => w == (6 : ℕ) || w == (9 : ℕ) || w == (10 : ℕ) + k) x1.gates
    · exact h_or_not_hi x1 k x1.gates[k] hfan hsize hout hnot hr6 hgk hgp6 (Or.inl hor) hc
    · exact h_or_not_lo x1 k x1.gates[k] hfan hsize hout hnot hr6 hgk hgp6 (Or.inl hor) (by omega)
  · by_cases hc : (4 : ℕ) ≤ List.countP (fun (h : PEqualNP.CircuitLowerBounds.Gate) => !h.op.eval [Bool.false] && h.inputs.any fun (w : ℕ) => w == (6 : ℕ) || w == (9 : ℕ) || w == (10 : ℕ) + k) x1.gates
    · exact h_or_not_hi x1 k x1.gates[k] hfan hsize hout hnot hr6 hgk hgp6 (Or.inr hnotop) hc
    · exact h_or_not_lo x1 k x1.gates[k] hfan hsize hout hnot hr6 hgk hgp6 (Or.inr hnotop) (by omega)

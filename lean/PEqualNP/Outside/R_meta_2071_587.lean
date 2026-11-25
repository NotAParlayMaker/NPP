import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2071_587
    (hBridge :
      ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (a b : Fin n) (d : ℕ → Bool), a ≠ b →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ u v : ℕ,
          g.inputs = [u, v] ∧ u ≠ v ∧ u < n + j ∧ v < n + j) →
      ((∀ i < n, d i = decide (i = b.val)) ∧
        let w := C.wires (List.ofFn fun i : Fin n => decide (i = a))
        ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (u v : ℕ),
          C.gates[j]? = some g → g.inputs = [u, v] →
          (g.op = .and → d (n + j) = (w.getD u false && d v || d u && w.getD v false)) ∧
          (g.op = .or → d (n + j) = (d u || d v))) →
      PEqualNP.ReadK.lineSingle C n (fun i => decide (i = b.val)) a.val b.val = true →
      d C.output = true)
    (hSingle :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      let shifts : Finset (Fin 13) := {0, 1, 3, 9}
      C.size ≤ 64 →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ u v : ℕ,
          g.inputs = [u, v] ∧ u ≠ v ∧ u < 26 + j ∧ v < 26 + j) →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p - l ∈ shifts ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      0 < PEqualNP.TopForm.andPairs 26 C →
      (∃ k < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = .and ∧
        ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = true ∧
          C.eval (List.ofFn x) = false) →
      ∀ p l : Fin 13, p - l ∈ shifts →
      PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 13 + l.val)) p.val (13 + l.val) = true ∨
      PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = p.val)) (13 + l.val) p.val = true) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∃ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 ∧ ∃ (x15 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x15)).getD ((26 : ℕ) + x14) Bool.false = Bool.true ∧ x4.eval (List.ofFn x15) = Bool.false) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  dsimp only
  intro C p l d e hsize hgates heval hnested hdirty hinc hd he
  have hne : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have hp := p.isLt
    omega
  rcases hSingle C hsize hgates heval hnested hdirty p l hinc with hleft | hright
  · exact Or.inl (hBridge 26 C (Fin.castAdd 13 p) (Fin.natAdd 13 l) d
      hne hgates hd hleft)
  · exact Or.inr (hBridge 26 C (Fin.natAdd 13 l) (Fin.castAdd 13 p) e
      (Ne.symm hne) hgates he hright)

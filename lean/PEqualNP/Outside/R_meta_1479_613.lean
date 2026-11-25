import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- At cap two the second coordinate records whether a tree repeats the marked leaf.
-- Search with both orders of the two leaves and interpret the same certificate twice.
theorem PEqualNP.Outside.R_meta_1479_613
    (search : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∀ z ∈ (PEqualNP.ReadK.readVectors C 14 [p.val, 7 + l.val] 1).getD C.output [], z.getD 1 0 = 2) ∧ (∀ z ∈ (PEqualNP.ReadK.readVectors C 14 [7 + l.val, p.val] 1).getD C.output [], z.getD 1 0 = 2))
    (interpret : ∀ (C : Circuit), (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) →
      ∀ a b : Fin 14, a ≠ b →
      (∀ z ∈ (PEqualNP.ReadK.readVectors C 14 [a.val, b.val] 1).getD C.output [], z.getD 1 0 = 2) →
      ∃ d : ℕ → Bool, (∀ i : Fin 14, d i.val = decide (i = b)) ∧
        (∀ (k : ℕ) (g : Gate) (u v : ℕ), C.gates[k]? = some g → g.inputs = [u,v] →
          (g.op = .and → d (14+k) = (((C.wires (List.ofFn (fun i : Fin 14 => decide (i=a)))).getD u false && d v) ||
            (d u && (C.wires (List.ofFn (fun i : Fin 14 => decide (i=a)))).getD v false))) ∧
          (g.op = .or → d (14+k) = (d u || d v))) ∧ d C.output = false) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  obtain ⟨C, size, normal, computes, p, l, edge, forward, backward⟩ := search
  have disj (i j : Fin 7) : Fin.castAdd 7 i ≠ Fin.natAdd 7 j := by
    intro h
    have h' := congrArg Fin.val h
    change i.val = 7 + j.val at h'
    omega
  obtain ⟨v, vi, vg, vo⟩ := interpret C normal (Fin.castAdd 7 p) (Fin.natAdd 7 l) (disj p l) forward
  obtain ⟨w, wi, wg, wo⟩ := interpret C normal (Fin.natAdd 7 l) (Fin.castAdd 7 p) (disj p l).symm backward
  refine ⟨C, size, normal, computes, p, l, edge, ⟨v, ?_, vg, vo⟩, w, ?_, wg, wo⟩
  · intro i
    constructor
    · exact (vi (Fin.castAdd 7 i)).trans (by simp only [disj i l, decide_false])
    · exact (vi (Fin.natAdd 7 i)).trans (by congr 1; apply propext; simp only [Fin.ext_iff]; change (7 + i.val = 7 + l.val) ↔ i.val = l.val; omega)
  · intro i
    constructor
    · exact (wi (Fin.castAdd 7 i)).trans (by congr 1; apply propext; simp only [Fin.ext_iff]; rfl)
    · exact (wi (Fin.natAdd 7 i)).trans (by simp only [(disj p i).symm, decide_false])

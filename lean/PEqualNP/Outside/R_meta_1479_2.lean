import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1479_2
  (tests_complete : ∀ C : Circuit, PEqualNP.TopForm.IsAO2 14 C →
    (∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) → C.eval (List.ofFn (fun i : Fin 14 => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l))) = true) → (∀ m ∈ [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539, 2126, 2244, 2376, 2626, 3008, 3078, 4125, 4244, 4361, 4625, 5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250, 9632, 10250, 11778, 12312, 12944, 14600, 16256], C.eval (List.ofFn (fun i : Fin 14 => m.testBit i.val)) = false) →
    ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
  (linear_bridge : ∀ C : Circuit, PEqualNP.TopForm.IsAO2 14 C →
    PEqualNP.ReadK.lineSingle C 14 (fun i => decide (7 ≤ i)) 0 7 = false → PEqualNP.ReadK.lineSingle C 14 (fun i => decide (i < 7)) 0 7 = false → (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = (0 : Fin 7))) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 (0 : Fin 7))))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 (0 : Fin 7))))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = (0 : Fin 7)) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 (0 : Fin 7))))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 (0 : Fin 7))))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false))
  (finite_witness : ∃ C : Circuit, C.size ≤ 27 ∧ PEqualNP.TopForm.IsAO2 14 C ∧
    (∀ g ∈ C.gates, g.inputs.Nodup) ∧ (∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) → C.eval (List.ofFn (fun i : Fin 14 => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l))) = true) ∧ (∀ m ∈ [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539, 2126, 2244, 2376, 2626, 3008, 3078, 4125, 4244, 4361, 4625, 5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250, 9632, 10250, 11778, 12312, 12944, 14600, 16256], C.eval (List.ofFn (fun i : Fin 14 => m.testBit i.val)) = false) ∧ PEqualNP.ReadK.lineSingle C 14 (fun i => decide (7 ≤ i)) 0 7 = false ∧ PEqualNP.ReadK.lineSingle C 14 (fun i => decide (i < 7)) 0 7 = false) :
∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  classical
  obtain ⟨C,hs,hAO,hnodup,hpos,hneg,hline,hpoint⟩ := finite_witness
  refine ⟨C,hs,?_,tests_complete C hAO hpos hneg,0,0,Or.inl rfl,?_⟩
  · intro j g hg
    obtain ⟨hj,hgval⟩ := List.getElem?_eq_some_iff.mp hg
    have hmem : g ∈ C.gates := List.mem_iff_getElem?.mpr ⟨j,hg⟩
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 g hmem)
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
      change C.gates.getD j _ = g
      simp only [List.getD,hg,Option.getD_some]
    have hb := hAO.2.1 j hj
    rw [hgate] at hb
    refine ⟨hAO.1 g hmem,a,b,hab,?_,?_,?_⟩
    · have hn := hnodup g hmem
      rw [hab] at hn
      simpa only [List.mem_singleton] using (List.nodup_cons.mp hn).1
    · exact hb a (by rw [hab]; simp)
    · exact hb b (by rw [hab]; simp)
  · exact linear_bridge C hAO hline hpoint

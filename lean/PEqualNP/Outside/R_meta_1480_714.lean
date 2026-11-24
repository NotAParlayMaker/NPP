import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1480_714
    (hPropagate : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin 14) (z : ℕ → Bool),
      (∀ j g c d, C.gates[j]? = some g → g.inputs = [c, d] →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          z (14+j) = (((C.wires (List.ofFn fun i : Fin 14 => decide (i = a))).getD c false && z d) ||
            (z c && (C.wires (List.ofFn fun i : Fin 14 => decide (i = a))).getD d false))) ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → z (14+j) = (z c || z d))) →
      ∀ s t, Relation.ReflTransGen (fun i k : ℕ => ∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
        k = 14+j ∧ C.gates[j]? = some g ∧ (g.inputs = [i, o] ∨ g.inputs = [o, i]) ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (C.wires (List.ofFn fun m : Fin 14 => decide (m = a))).getD o false = true)) s t →
      z s = true → z t = true)
    (hBound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 →
      PEqualNP.TopForm.IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ p l : Fin 7, p ∈ PEqualNP.CircuitLowerBounds.fanoLines l →
        C.eval (List.ofFn fun i : Fin 14 =>
          decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) = true) →
      (∀ P L : Finset (Fin 7),
        (∀ p ∈ P, ∀ l ∈ L, p ∉ PEqualNP.CircuitLowerBounds.fanoLines l) →
        (∀ p ∉ P, ∃ l ∈ L, p ∈ PEqualNP.CircuitLowerBounds.fanoLines l) →
        (∀ l ∉ L, ∃ p ∈ P, p ∈ PEqualNP.CircuitLowerBounds.fanoLines l) →
        C.eval (List.ofFn (Fin.addCases (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L)))) = false) →
      ∀ p l : Fin 7, p ∈ PEqualNP.CircuitLowerBounds.fanoLines l →
      let R (a : Fin 14) (i k : ℕ) :=
        ∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
          k = 14+j ∧ C.gates[j]? = some g ∧ (g.inputs = [i, o] ∨ g.inputs = [o, i]) ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            (C.wires (List.ofFn fun m : Fin 14 => decide (m = a))).getD o false = true)
      Relation.ReflTransGen (R (Fin.castAdd 7 p)) (7+l.val) C.output ∨
        Relation.ReflTransGen (R (Fin.natAdd 7 l)) p.val C.output) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false)) := by
  intro h
  rcases h with ⟨C, hSize, hGates, hEval, p, l, hFlag, ⟨v, hV0, hVstep, hVout⟩, ⟨w, hW0, hWstep, hWout⟩⟩
  have hInc : ∀ u t : Fin 7, u ∈ PEqualNP.CircuitLowerBounds.fanoLines t ↔
      u = t ∨ u = t + 1 ∨ u = t + 3 := by decide
  have hAO : PEqualNP.TopForm.IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
      exact (hGates j g hj).1
    · intro j hj i hi
      have hget : C.gates[j]? = some (C.gates[j]'hj) := List.getElem?_eq_getElem hj
      obtain ⟨a, b, hab, _, ha, hb⟩ := (hGates j _ hget).2
      have hAt : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b] := by
        change (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs = [a, b]
        simpa only [List.getD_eq_getElem?_getD, hget, Option.getD_some] using hab
      rw [hAt] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    · intro g hg
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨a, b, hab, _⟩ := (hGates j g hj).2
      simp [hab]
  have hNodup : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨a, b, hab, hneq, _, _⟩ := (hGates j g hj).2
    simp [hab, hneq]
  have hPos : ∀ u t : Fin 7, u ∈ PEqualNP.CircuitLowerBounds.fanoLines t →
      C.eval (List.ofFn fun i : Fin 14 => decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 t)) = true := by
    intro u t hut
    exact (hEval _).mpr ⟨u, t, (hInc u t).mp hut, by simp, by simp⟩
  have hNeg : ∀ P L : Finset (Fin 7),
      (∀ u ∈ P, ∀ t ∈ L, u ∉ PEqualNP.CircuitLowerBounds.fanoLines t) →
      (∀ u ∉ P, ∃ t ∈ L, u ∈ PEqualNP.CircuitLowerBounds.fanoLines t) →
      (∀ t ∉ L, ∃ u ∈ P, u ∈ PEqualNP.CircuitLowerBounds.fanoLines t) →
      C.eval (List.ofFn (Fin.addCases (fun u => decide (u ∈ P)) (fun t => decide (t ∈ L)))) = false := by
    intro P L hIndependent _ _
    by_contra hFalse
    have hTrue := Bool.eq_true_of_not_eq_false hFalse
    obtain ⟨u, t, hut, hu, ht⟩ := (hEval _).mp hTrue
    have huP : u ∈ P := by simpa using hu
    have htL : t ∈ L := by
      rw [Fin.addCases_right] at ht
      exact of_decide_eq_true ht
    exact hIndependent u huP t htL ((hInc u t).mpr hut)
  rcases hBound C hSize hAO hNodup hPos hNeg p l ((hInc p l).mpr hFlag) with hPath | hPath
  · have hSeed : v (7+l.val) = true := by simpa using (hV0 l).2
    have h := hPropagate C (Fin.castAdd 7 p) v hVstep _ _ hPath hSeed
    rw [hVout] at h
    contradiction
  · have hSeed : w p.val = true := by simpa using (hW0 p).1
    have h := hPropagate C (Fin.natAdd 7 l) w hWstep _ _ hPath hSeed
    rw [hWout] at h
    contradiction

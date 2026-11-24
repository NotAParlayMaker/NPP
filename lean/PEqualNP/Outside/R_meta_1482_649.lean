import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1482_649
    (hPropagate : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin 26) (z : ℕ → Bool),
      (∀ j g c d, C.gates[j]? = some g → g.inputs = [c, d] →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          z (26+j) = (((C.wires (List.ofFn fun i : Fin 26 => decide (i = a))).getD c false && z d) ||
            (z c && (C.wires (List.ofFn fun i : Fin 26 => decide (i = a))).getD d false))) ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → z (26+j) = (z c || z d))) →
      ∀ s t, Relation.ReflTransGen (fun i k : ℕ => ∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
        k = 26+j ∧ C.gates[j]? = some g ∧ (g.inputs = [i, o] ∨ g.inputs = [o, i]) ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (C.wires (List.ofFn fun m : Fin 26 => decide (m = a))).getD o false = true)) s t →
      z s = true → z t = true)
    (hBound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 →
      PEqualNP.TopForm.IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l →
        C.eval (List.ofFn fun i : Fin 26 =>
          decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
      (∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
        C.eval (List.ofFn (Fin.addCases (fun p => decide (p ∈ Q))
          (fun l => decide (∀ p ∈ Q, p ∉ PEqualNP.HeptadCover.singerLines3 l)))) = false) →
      ∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l →
      let R (a : Fin 26) (i k : ℕ) :=
        ∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
          k = 26+j ∧ C.gates[j]? = some g ∧ (g.inputs = [i, o] ∨ g.inputs = [o, i]) ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            (C.wires (List.ofFn fun m : Fin 26 => decide (m = a))).getD o false = true)
      Relation.ReflTransGen (R (Fin.castAdd 13 p)) (13+l.val) C.output ∨
        Relation.ReflTransGen (R (Fin.natAdd 13 l)) p.val C.output) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false)) := by
  intro h
  rcases h with ⟨C, hSize, hGates, hEval, p, l, hFlag, ⟨v, hV0, hVstep, hVout⟩, ⟨w, hW0, hWstep, hWout⟩⟩
  have hInc : ∀ u t : Fin 13, u ∈ PEqualNP.HeptadCover.singerLines3 t ↔
      u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9 := by decide +kernel
  have hAO : PEqualNP.TopForm.IsAO2 26 C := by
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
  have hPos : ∀ u t : Fin 13, u ∈ PEqualNP.HeptadCover.singerLines3 t →
      C.eval (List.ofFn fun i : Fin 26 => decide (i = Fin.castAdd 13 u ∨ i = Fin.natAdd 13 t)) = true := by
    intro u t hut
    exact (hEval _).mpr ⟨u, t, (hInc u t).mp hut, by simp, by simp⟩
  have hNeg : ∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
        C.eval (List.ofFn (Fin.addCases (fun p => decide (p ∈ Q))
          (fun l => decide (∀ p ∈ Q, p ∉ PEqualNP.HeptadCover.singerLines3 l)))) = false := by
    intro Q _
    by_contra hFalse
    obtain ⟨u, t, hut, hu, ht⟩ := (hEval _).mp (Bool.eq_true_of_not_eq_false hFalse)
    have huQ : u ∈ Q := by
      rw [Fin.addCases_left] at hu
      exact of_decide_eq_true hu
    rw [Fin.addCases_right] at ht
    exact (of_decide_eq_true ht) u huQ ((hInc u t).mpr hut)
  rcases hBound C hSize hAO hNodup hPos hNeg p l ((hInc p l).mpr hFlag) with hPath | hPath
  · have hSeed : v (13+l.val) = true := by simpa using (hV0 l).2
    have h := hPropagate C (Fin.castAdd 13 p) v hVstep _ _ hPath hSeed
    rw [hVout] at h
    contradiction
  · have hSeed : w p.val = true := by simpa using (hW0 p).1
    have h := hPropagate C (Fin.natAdd 13 l) w hWstep _ _ hPath hSeed
    rw [hWout] at h
    contradiction

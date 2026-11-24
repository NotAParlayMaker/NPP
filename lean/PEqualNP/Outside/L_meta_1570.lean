import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570

open PEqualNP.CircuitLowerBounds

private lemma foldl_wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

private lemma foldl_wires_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (w := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
        (by rw [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append w _ false i hi

private lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  have hlen : i < (List.ofFn x).length := by simpa using hi
  rw [List.getD_eq_get (i := ⟨i, hlen⟩), List.get_ofFn]
  congr 1

private lemma line01 (t : Fin 13) (ht : t ≠ 0) :
    (0 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) ∨
      (1 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by
  fin_cases t <;> simp_all

private lemma linediff (t : Fin 13) (ht : t ≠ 0) :
    ∃ v : Fin 13, v ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by
  fin_cases t <;> simp_all

end PEqualNP.Outside.L_meta_1570

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o hg hlen hcor
  have hmem0 : (0 : Fin 13) ∈ L 0 := by rw [hL 0]; simp
  have hmem1 : (1 : Fin 13) ∈ L 0 := by rw [hL 0]; simp
  let x0 : Fin 13 → Bool := fun v => decide (v = 0)
  let x1 : Fin 13 → Bool := fun v => decide (v = 1)
  let xc : Fin 13 → Bool := fun v => decide (v ∉ L 0)
  have hp0 : x0 0 = true ∨ x0 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x0 v = true := Or.inl (by simp [x0])
  have hp1 : x1 0 = true ∨ x1 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x1 v = true := Or.inr (Or.inl (by simp [x1]))
  have hpc : xc 0 = true ∨ xc 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → xc v = true := by
    refine Or.inr (Or.inr ?_)
    intro v hv
    simp [xc, hv]
  have e0 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn x0) = true := by
    rw [hcor 0 x0 hp0, decide_eq_true_eq]
    exact ⟨0, hmem0, by simp [x0]⟩
  have e1 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn x1) = true := by
    rw [hcor 0 x1 hp1, decide_eq_true_eq]
    exact ⟨1, hmem1, by simp [x1]⟩
  have ec : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn xc) = false := by
    rw [hcor 0 xc hpc, decide_eq_false_iff_not]
    rintro ⟨v, hv, hvc⟩
    simp only [xc, decide_eq_true_eq] at hvc
    exact hvc hv
  have hwlen : (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, o 0⟩ (List.ofFn x0)).length =
      13 + gates.length := by
    simpa [PEqualNP.CircuitLowerBounds.Circuit.wires] using
      PEqualNP.Outside.L_meta_1570.foldl_wires_length gates (List.ofFn x0)
  have ho0 : 13 ≤ o 0 := by
    by_contra hlt
    have hlt' : o 0 < 13 := by omega
    have hget : (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, o 0⟩ (List.ofFn x0)).getD (o 0) false =
        x0 ⟨o 0, hlt'⟩ := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.wires]
      rw [PEqualNP.Outside.L_meta_1570.foldl_wires_getD gates (List.ofFn x0) (o 0) (by simpa using hlt')]
      exact PEqualNP.Outside.L_meta_1570.ofFn_getD x0 (o 0) hlt'
    have hev : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn x0) = x0 ⟨o 0, hlt'⟩ := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
      exact hget
    rw [hev] at e0
    have hv0 : o 0 = 0 := by
      have hfin : (⟨o 0, hlt'⟩ : Fin 13) = 0 := by simpa [x0] using e0
      simpa using congrArg Fin.val hfin
    have hget1 : (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, o 0⟩ (List.ofFn x1)).getD (o 0) false =
        x1 ⟨o 0, hlt'⟩ := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.wires]
      rw [PEqualNP.Outside.L_meta_1570.foldl_wires_getD gates (List.ofFn x1) (o 0) (by simpa using hlt')]
      exact PEqualNP.Outside.L_meta_1570.ofFn_getD x1 (o 0) hlt'
    have hev1 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn x1) = x1 ⟨o 0, hlt'⟩ := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
      exact hget1
    rw [hev1] at e1
    have hv1 : o 0 = 1 := by
      have hfin : (⟨o 0, hlt'⟩ : Fin 13) = 1 := by simpa [x1] using e1
      simpa using congrArg Fin.val hfin
    omega
  have ho0' : o 0 < 13 + gates.length := by
    by_contra hge
    have hge' : 13 + gates.length ≤ o 0 := by omega
    have hfalse : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn x0) = false := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
      exact List.getD_eq_default _ _ (by rw [hwlen]; exact hge')
    rw [hfalse] at e0
    exact Bool.noConfusion e0
  have h01 : ∀ t : Fin 13, t ≠ 0 → (0 : Fin 13) ∉ L t ∨ (1 : Fin 13) ∉ L t := by
    intro t ht
    rw [hL t]
    exact PEqualNP.Outside.L_meta_1570.line01 t ht
  have hdiff : ∀ t : Fin 13, t ≠ 0 → ∃ v : Fin 13, v ∈ L 0 ∧ v ∉ L t := by
    intro t ht
    rw [hL 0, hL t]
    exact PEqualNP.Outside.L_meta_1570.linediff t ht
  refine ⟨ho0, ho0', e0, e1, ec, ?_⟩
  intro t ht
  let xt : Fin 13 → Bool := fun v => decide (v ∉ L t)
  have hpt : xt 0 = true ∨ xt 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → xt v = true := by
    rcases h01 t ht with h0 | h1
    · exact Or.inl (by simp [xt, h0])
    · exact Or.inr (Or.inl (by simp [xt, h1]))
  rw [hcor 0 xt hpt, decide_eq_true_eq]
  obtain ⟨v, hv0, hvt⟩ := hdiff t ht
  exact ⟨v, hv0, by simp [xt, hvt]⟩

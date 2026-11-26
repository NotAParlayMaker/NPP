import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18399_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_getD_lt (w : List Bool) (g : Gate) {k : ℕ} (hk : k < w.length) :
    (step w g).getD k false = w.getD k false := by
  simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem step_getD_self (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem step_getD_gt (w : List Bool) (g : Gate) {k : ℕ} (hk : w.length < k) :
    (step w g).getD k false = false := by
  have hle : (step w g).length ≤ k := by simp [step]; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle, Option.getD_none]

theorem foldl_orOnly {n : ℕ} (gs : List Gate) (hor : ∀ g ∈ gs, g.op = GateOp.or)
    (W : List Bool) (S : Fin n → List Bool)
    (hlen : ∀ i, (S i).length = W.length)
    (hcov : ∀ k, W.getD k false = true → ∃ i : Fin n, (S i).getD k false = true) :
    ∀ k, (gs.foldl step W).getD k false = true →
      ∃ i : Fin n, (gs.foldl step (S i)).getD k false = true := by
  induction gs generalizing W S with
  | nil => exact hcov
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg : g.op = GateOp.or := hor g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.or := fun g' hg' => hor g' (List.mem_cons_of_mem _ hg')
    apply ih hgs (step W g) (fun i => step (S i) g)
    · intro i; simp [step, hlen i]
    · intro k hk
      rcases lt_trichotomy k W.length with hlt | rfl | hgt
      · rw [step_getD_lt W g hlt] at hk
        obtain ⟨i, hi⟩ := hcov k hk
        exact ⟨i, by rw [step_getD_lt (S i) g (by rw [hlen i]; exact hlt)]; exact hi⟩
      · rw [step_getD_self W g, hg] at hk
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk
        obtain ⟨_, ⟨j, hj, rfl⟩, hWj⟩ := hk
        obtain ⟨i, hi⟩ := hcov j hWj
        refine ⟨i, ?_⟩
        rw [← hlen i, step_getD_self (S i) g, hg]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        exact ⟨true, ⟨j, hj, hi⟩, rfl⟩
      · rw [step_getD_gt W g hgt] at hk
        cases hk

theorem main :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Circuit),
      (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 →
        ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →
      (∀ (x7 : Fin (x1 + x2) → Bool),
        circuitFun (x1 + x2) x4 x7 =
          Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2),
            (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = true ∧ x7 (Fin.natAdd x1 x9) = true)) →
      (¬∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = GateOp.and) →
      ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)),
        (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + 1 := by
  intro m n E C _ hAO hEval hNoAnd
  have hor : ∀ g ∈ C.gates, g.op = GateOp.or := by
    intro g hg
    rcases hAO.1 g hg with hand | hor'
    · exfalso
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
      exact hNoAnd ⟨j, hand⟩
    · exact hor'
  have hEempty : E = ∅ := by
    by_contra hne
    obtain ⟨⟨u, v⟩, huv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hall : C.eval (List.ofFn (fun _ : Fin (m + n) => true)) = true := by
      have h1 := hEval (fun _ : Fin (m + n) => true)
      change C.eval (List.ofFn (fun _ : Fin (m + n) => true)) = _ at h1
      rw [h1, decide_eq_true_eq]
      exact ⟨u, v, huv, rfl, rfl⟩
    have hstep := foldl_orOnly C.gates hor
      (List.ofFn (fun _ : Fin (m + n) => true))
      (fun i : Fin (m + n) => List.ofFn (fun j : Fin (m + n) => decide (j = i)))
      (fun i => by simp)
      (fun k hk => by
        by_cases hlt : k < m + n
        · refine ⟨⟨k, hlt⟩, ?_⟩
          simp [List.getD_eq_getElem?_getD, hlt]
        · exfalso
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hk
          simp at hk)
      C.output hall
    obtain ⟨i, hi⟩ := hstep
    have h2 := hEval (fun j : Fin (m + n) => decide (j = i))
    change C.eval (List.ofFn (fun j : Fin (m + n) => decide (j = i))) = _ at h2
    change C.eval (List.ofFn (fun j : Fin (m + n) => decide (j = i))) = true at hi
    rw [h2, decide_eq_true_eq] at hi
    obtain ⟨u', v', _, hu', hv'⟩ := hi
    simp only [decide_eq_true_eq] at hu' hv'
    have heq : (Fin.castAdd n u').val = (Fin.natAdd m v').val := congrArg Fin.val (hu'.trans hv'.symm)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
    have := u'.isLt
    omega
  subst hEempty
  refine ⟨∅, ∅, ?_, by simp⟩
  intro e he
  exact absurd he (Finset.notMem_empty e)

end PEqualNP.Outside.L_meta_18399_aux

theorem PEqualNP.Outside.L_meta_18399 : (∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (¬∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ)) :=
  PEqualNP.Outside.L_meta_18399_aux.main

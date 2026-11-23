import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_751

open PEqualNP.CircuitLowerBounds

-- One gate appended to the wire list, as in Circuit.wires.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem len_fold : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem getD_fold_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (step w g) i (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_fold_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  rw [List.getD_eq_default]
  rw [len_fold]
  exact h

theorem getD_fold_gate : ∀ (gs : List Gate) (w : List Bool) (k : ℕ) (g : Gate), gs[k]? = some g →
    (gs.foldl step w).getD (w.length + k) false =
      g.op.eval (g.inputs.map fun i => ((gs.take k).foldl step w).getD i false) := by
  intro gs
  induction gs with
  | nil => intro w k g h; simp at h
  | cons g0 gs ih =>
    intro w k g h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [List.foldl_cons, getD_fold_lt gs (step w g0) (w.length + 0) (by simp [step])]
      simp [step, List.getD_eq_getElem?_getD]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      have hih := ih (step w g0) k g h
      have hl : (step w g0).length = w.length + 1 := by simp [step]
      rw [hl] at hih
      rw [List.foldl_cons, show w.length + (k + 1) = w.length + 1 + k by omega, hih]
      simp only [List.take_succ_cons, List.foldl_cons]

theorem lt_of_get (l : List Gate) (k : ℕ) (g : Gate) (h : l[k]? = some g) : k < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ j ∈ l, f j = true → f' j = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro hall j hj
    exact h j hj (hall j hj)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    rintro ⟨j, hj, hfj⟩
    exact ⟨j, hj, h j hj hfj⟩

end PEqualNP.Outside.L_meta_751

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_751 in
theorem PEqualNP.Outside.L_meta_751 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i : ℕ), (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → Relation.ReflTransGen (fun a b : ℕ => ∃ (k : ℕ) (e : PEqualNP.CircuitLowerBounds.Gate), a = n + k ∧ C.gates[k]? = some e ∧ b ∈ e.inputs ∧ b < a) i (n + j) → g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ x x' : Fin n → Bool, (∀ q : Fin n, x q = true → x' q = true) → (PEqualNP.CircuitLowerBounds.Circuit.wires C (List.ofFn x)).getD i false = true → (PEqualNP.CircuitLowerBounds.Circuit.wires C (List.ofFn x')).getD i false = true := by
  intro n C i hcone x x' hxx'
  suffices key : ∀ w, Relation.ReflTransGen (fun a b : ℕ => ∃ (k : ℕ) (e : Gate), a = n + k ∧
      C.gates[k]? = some e ∧ b ∈ e.inputs ∧ b < a) i w →
      (C.gates.foldl step (List.ofFn x)).getD w false = true →
      (C.gates.foldl step (List.ofFn x')).getD w false = true from key i Relation.ReflTransGen.refl
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw hv
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hlen' : (List.ofFn x').length = n := List.length_ofFn
  by_cases hwn : w < n
  · rw [getD_fold_lt _ _ _ (by rw [hlen]; exact hwn)] at hv
    rw [getD_fold_lt _ _ _ (by rw [hlen']; exact hwn)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hwn, dite_true,
      Option.getD_some] at hv ⊢
    exact hxx' _ hv
  · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rcases hg : C.gates[k]? with _ | g
    · have hk : C.gates.length ≤ k := List.getElem?_eq_none_iff.1 hg
      rw [getD_fold_ge _ _ _ (by rw [hlen]; omega)] at hv
      exact absurd hv (by simp)
    · have hop := hcone k g hg hw
      have hk := lt_of_get C.gates k g hg
      have htake : (C.gates.take k).length = k := by
        rw [List.length_take]; omega
      rw [show n + k = (List.ofFn x).length + k by rw [hlen], getD_fold_gate _ _ k g hg] at hv
      rw [show n + k = (List.ofFn x').length + k by rw [hlen'], getD_fold_gate _ _ k g hg]
      refine eval_mono g.op hop g.inputs _ _ ?_ hv
      intro j hj hfj
      by_cases hjk : j < n + k
      · have hsplit : ∀ y : List Bool, C.gates.foldl step y =
            (C.gates.drop k).foldl step ((C.gates.take k).foldl step y) := by
          intro y
          rw [← List.foldl_append, List.take_append_drop]
        have hP : ∀ y : List Bool, y.length = n →
            ((C.gates.take k).foldl step y).getD j false = (C.gates.foldl step y).getD j false := by
          intro y hy
          have hlt : j < ((C.gates.take k).foldl step y).length := by
            rw [len_fold, htake, hy]; exact hjk
          rw [hsplit y, getD_fold_lt (C.gates.drop k) ((C.gates.take k).foldl step y) j hlt]
        rw [hP _ hlen] at hfj
        rw [hP _ hlen']
        exact ih j hjk (hw.tail ⟨k, g, rfl, hg, hj, hjk⟩) hfj
      · rw [getD_fold_ge _ _ _ (by rw [htake, hlen]; omega)] at hfj
        exact absurd hfj (by simp)

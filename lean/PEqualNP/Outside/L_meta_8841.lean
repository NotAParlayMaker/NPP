import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8841_aux

open PEqualNP.CircuitLowerBounds

theorem sh_fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w1 w2 : List Bool, w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ h; simpa using h
  | cons g gs ih =>
    intro w1 w2 hl h
    simp only [List.foldl_cons]
    apply ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    · simp [hl]
    · have hv : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
          g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
        rcases hgs g (List.mem_cons_self) with ho | ho <;> rw [ho] <;> simp only [GateOp.eval]
        · simp only [List.all_eq_true, List.mem_map, id]
          rintro hall _ ⟨a, ha, rfl⟩
          exact h a (hall _ ⟨a, ha, rfl⟩)
        · simp only [List.any_eq_true, List.mem_map, id]
          rintro ⟨_, ⟨a, ha, rfl⟩, hb⟩
          exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩
      intro i hi
      rcases Nat.lt_trichotomy i w1.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h i hi
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
        rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp at hi ⊢
        exact hv hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact absurd hi (by simp)

theorem sh_ofFn_imp {n : ℕ} (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases hn : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hn)] at hi ⊢
    simp only [List.getElem_ofFn] at hi ⊢
    exact h _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

theorem sh_imp_of_le {n : ℕ} (x y : Fin n → Bool) (h : x ≤ y) : ∀ i, x i = true → y i = true := by
  intro i hi
  have := h i
  revert this hi
  cases x i <;> cases y i <;> simp

theorem sh_wires_fn {n : ℕ} (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn y)).getD i false = true :=
  sh_fold_mono C.gates hC _ _ (by simp) (sh_ofFn_imp x y h) i

theorem sh_eval_fn {n : ℕ} (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
  sh_wires_fn C hC x y h C.output

theorem sh_eval_le {n : ℕ} (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (h : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
  sh_eval_fn C hC x y (sh_imp_of_le x y h)

theorem sh_bool_le {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> simp_all

theorem sh_monotone {n : ℕ} (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    Monotone (fun x : Fin n → Bool => C.eval (List.ofFn x)) :=
  fun x y hxy => sh_bool_le (sh_eval_le C hC x y hxy)

theorem sh_monotone_wires {n : ℕ} (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (i : ℕ) : Monotone (fun x : Fin n → Bool => (C.wires (List.ofFn x)).getD i false) :=
  fun x y hxy => sh_bool_le (sh_wires_fn C hC x y (sh_imp_of_le x y hxy) i)

theorem sh_ao_m2 (C : Circuit) (h : PEqualNP.MetaComplexity.Monotone2 C) :
    ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  have := (h g hg).1
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this

theorem sh_ao_ao2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) :
    ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := h.1

theorem sh_eval_list (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (n : ℕ)
    (x y : List Bool) (h : ∀ i < n, x.getD i false = true → y.getD i false = true)
    (hx : x.length = n) (hy : y.length = n) :
    C.eval x = true → C.eval y = true := by
  apply sh_fold_mono C.gates hC x y (by omega)
  intro i hi
  by_cases hn : i < n
  · exact h i hn hi
  · rw [List.getD_eq_default _ _ (by omega)] at hi
    exact absurd hi (by simp)

end PEqualNP.Outside.L_meta_8841_aux

theorem PEqualNP.Outside.L_meta_8841 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → Monotone (PEqualNP.MetaComplexity.circuitFun x1 x2) := by
  intros
  first
  | exact PEqualNP.Outside.L_meta_8841_aux.sh_monotone _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1)
  | exact PEqualNP.Outside.L_meta_8841_aux.sh_monotone_wires _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1) _
  | exact PEqualNP.Outside.L_meta_8841_aux.sh_eval_fn _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1) _ _ ‹_› ‹_›
  | (apply PEqualNP.Outside.L_meta_8841_aux.sh_eval_fn _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1) <;> assumption)
  | exact PEqualNP.Outside.L_meta_8841_aux.sh_eval_le _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1) _ _ ‹_› ‹_›
  | (apply PEqualNP.Outside.L_meta_8841_aux.sh_eval_le _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1) <;> assumption)
  | exact PEqualNP.Outside.L_meta_8841_aux.sh_wires_fn _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1) _ _ ‹_› _ ‹_›
  | (apply PEqualNP.Outside.L_meta_8841_aux.sh_wires_fn _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1) <;> assumption)
  | exact PEqualNP.Outside.L_meta_8841_aux.sh_eval_list _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1) _ _ _ ‹_› ‹_› ‹_› ‹_›
  | (simp only [PEqualNP.MetaComplexity.circuitFun] at *; first | exact PEqualNP.Outside.L_meta_8841_aux.sh_monotone _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1) | (apply PEqualNP.Outside.L_meta_8841_aux.sh_eval_fn _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1) <;> assumption) | (apply PEqualNP.Outside.L_meta_8841_aux.sh_eval_le _ (by first | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_m2 _ ‹_› | exact PEqualNP.Outside.L_meta_8841_aux.sh_ao_ao2 _ _ ‹_› | assumption | exact fun g hg => (‹∀ g ∈ _, _› g hg).1) <;> assumption))

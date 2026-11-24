import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4871

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

def LeL (l l' : List Bool) : Prop :=
  l.length = l'.length ∧ ∀ i, l.getD i false ≤ l'.getD i false

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) : op.eval (ins.map f) ≤ op.eval (ins.map f') := by
  have h' : ∀ i, f i = true → f' i = true := by
    intro i hi
    have := h i
    rw [hi] at this
    exact top_le_iff.mp this
  rcases hop with rfl | rfl
  · show (ins.map f).all id ≤ (ins.map f').all id
    rw [Bool.le_iff_imp]
    simp only [List.all_eq_true, List.mem_map, id]
    rintro hall b ⟨i, hi, rfl⟩
    exact h' i (hall _ ⟨i, hi, rfl⟩)
  · show (ins.map f).any id ≤ (ins.map f').any id
    rw [Bool.le_iff_imp]
    simp only [List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h' i hb⟩

theorem foldl_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (l l' : List Bool), LeL l l' → LeL (gs.foldl step l) (gs.foldl step l') := by
  intro gs
  induction gs with
  | nil => intro _ l l' h; exact h
  | cons g gs ih =>
    intro hops l l' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hlen, hle⟩ := h
    have hv := eval_mono g.op (hops g (List.mem_cons_self ..)) g.inputs _ _ hle
    refine ⟨by simp [step, hlen], ?_⟩
    intro i
    simp only [step]
    by_cases hi : i < l.length
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
      exact hle i
    · by_cases hi2 : i = l.length
      · subst hi2
        rw [List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (by omega),
          hlen, Nat.sub_self]
        simpa using hv
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_4871

theorem PEqualNP.Outside.L_meta_4871 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → Monotone fun (x3 : Fin (14 : ℕ) → Bool) => x1.eval (List.ofFn x3) := by
  intro C hC x y hxy
  have hops : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := hC.1
  have hin : PEqualNP.Outside.L_meta_4871.LeL (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i
    by_cases hi : i < 14
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hi]
      exact hxy ⟨i, hi⟩
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have h := PEqualNP.Outside.L_meta_4871.foldl_mono C.gates hops _ _ hin
  show (C.wires (List.ofFn x)).getD C.output false ≤ (C.wires (List.ofFn y)).getD C.output false
  rw [PEqualNP.Outside.L_meta_4871.wires_eq, PEqualNP.Outside.L_meta_4871.wires_eq]
  exact h.2 C.output

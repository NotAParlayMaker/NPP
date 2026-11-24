import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2880

open PEqualNP.CircuitLowerBounds

lemma getD_mono {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') :
    ∀ i, w.getD i false ≤ w'.getD i false := by
  induction h with
  | nil => intro i; simp
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma op_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (l : List ℕ) (f f' : ℕ → Bool) (hf : ∀ i, f i ≤ f' i) :
    op.eval (l.map f) ≤ op.eval (l.map f') := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map]
    rw [Bool.le_iff_imp]
    intro h
    rw [List.all_eq_true] at h ⊢
    intro x hx
    have h1 := h x hx
    have h2 := hf x
    simp only [Function.comp_apply, id] at h1 ⊢
    rw [h1] at h2
    revert h2
    cases f' x <;> decide
  · simp only [GateOp.eval, List.any_map]
    rw [Bool.le_iff_imp]
    intro h
    rw [List.any_eq_true] at h ⊢
    obtain ⟨x, hx, h1⟩ := h
    refine ⟨x, hx, ?_⟩
    have h2 := hf x
    simp only [Function.comp_apply, id] at h1 ⊢
    rw [h1] at h2
    revert h2
    cases f' x <;> decide

lemma fold_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ w w' : List Bool, List.Forall₂ (fun a b => a ≤ b) w w' →
    List.Forall₂ (fun a b => a ≤ b)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; simpa using h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    exact List.rel_append h (List.Forall₂.cons
      (op_mono g.op (hg g List.mem_cons_self) g.inputs _ _ (getD_mono h)) List.Forall₂.nil)

lemma eval_mono (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) ≤ C.eval (List.ofFn y) := by
  unfold Circuit.eval Circuit.wires
  apply getD_mono
  apply fold_mono _ (fun g hg => (hC g hg).1)
  rw [List.forall₂_iff_get]
  refine ⟨by simp, ?_⟩
  intro i h1 h2
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  exact hxy _

end PEqualNP.Outside.L_meta_2880

theorem PEqualNP.Outside.L_meta_2880 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : (Fin x1 → Bool) → Prop), (∀ (x5 : Fin x1 → Bool), Minimal x4 x5 → x2.eval (List.ofFn x5) = Bool.true) → (∀ (x6 : Fin x1 → Bool), Maximal (fun (x7 : Fin x1 → Bool) => ¬x4 x7) x6 → x2.eval (List.ofFn x6) = Bool.false) → ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ x4 x7 := by
  intro n C hC p hmin hmax x
  constructor
  · intro hx
    by_contra hp
    obtain ⟨b, hxb, hb⟩ := Finite.exists_le_maximal (p := fun y => ¬p y) hp
    have h1 := PEqualNP.Outside.L_meta_2880.eval_mono n C hC x b hxb
    rw [hx, hmax b hb] at h1
    exact absurd h1 (by decide)
  · intro hp
    obtain ⟨b, hbx, hb⟩ := Finite.exists_le_minimal (p := p) hp
    have h1 := PEqualNP.Outside.L_meta_2880.eval_mono n C hC b x hbx
    rw [hmin b hb] at h1
    revert h1
    cases C.eval (List.ofFn x) <;> decide

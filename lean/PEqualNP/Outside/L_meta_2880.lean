import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2880

open PEqualNP.CircuitLowerBounds

theorem getD_mono {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') (i : ℕ) :
    w.getD i false ≤ w'.getD i false := by
  induction h generalizing i with
  | nil => exact le_rfl
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem map_mono {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') (l : List ℕ) :
    List.Forall₂ (fun a b => a ≤ b) (l.map fun i => w.getD i false)
      (l.map fun i => w'.getD i false) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons i l ih => exact List.Forall₂.cons (getD_mono h i) ih

theorem all_mono {l l' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) l l') :
    l.all id ≤ l'.all id := by
  induction h with
  | nil => exact le_rfl
  | cons hab _ ih =>
    simp only [List.all_cons, id]
    rw [Bool.le_iff_imp] at hab ih ⊢
    simp only [Bool.and_eq_true]
    exact fun h => ⟨hab h.1, ih h.2⟩

theorem any_mono {l l' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) l l') :
    l.any id ≤ l'.any id := by
  induction h with
  | nil => exact le_rfl
  | cons hab _ ih =>
    simp only [List.any_cons, id]
    rw [Bool.le_iff_imp] at hab ih ⊢
    simp only [Bool.or_eq_true]
    exact fun h => h.elim (fun h => Or.inl (hab h)) (fun h => Or.inr (ih h))

theorem op_mono {op : GateOp} (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    {l l' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) l l') :
    op.eval l ≤ op.eval l' := by
  rcases hop with rfl | rfl
  · exact all_mono h
  · exact any_mono h

theorem foldl_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') :
    List.Forall₂ (fun a b => a ≤ b)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs generalizing w w' with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem g hg'))
    exact List.rel_append h
      (List.Forall₂.cons (op_mono (hg g List.mem_cons_self) (map_mono h g.inputs))
        List.Forall₂.nil)

theorem ofFn_mono {n : ℕ} {x y : Fin n → Bool} (hxy : x ≤ y) :
    List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h1 h2 => ?_⟩
  simpa using hxy ⟨i, by simpa using h1⟩

theorem eval_mono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) {n : ℕ}
    {x y : Fin n → Bool} (hxy : x ≤ y) :
    C.eval (List.ofFn x) ≤ C.eval (List.ofFn y) := by
  unfold Circuit.eval Circuit.wires
  exact getD_mono (foldl_mono C.gates (fun g hg => (hC g hg).1) (ofFn_mono hxy)) C.output

end PEqualNP.Outside.L_meta_2880

theorem PEqualNP.Outside.L_meta_2880 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : (Fin x1 → Bool) → Prop), (∀ (x5 : Fin x1 → Bool), Minimal x4 x5 → x2.eval (List.ofFn x5) = Bool.true) → (∀ (x6 : Fin x1 → Bool), Maximal (fun (x7 : Fin x1 → Bool) => ¬x4 x7) x6 → x2.eval (List.ofFn x6) = Bool.false) → ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ x4 x7 := by
  intro n C hC P hmin hmax y
  constructor
  · intro hy
    by_contra hP
    obtain ⟨M, hyM, hM⟩ := Finite.exists_le_maximal (p := fun z => ¬P z) hP
    have h1 := PEqualNP.Outside.L_meta_2880.eval_mono C hC hyM
    rw [hy, hmax M hM] at h1
    exact absurd h1 (by decide)
  · intro hP
    obtain ⟨m, hmy, hm⟩ := Finite.exists_le_minimal (p := P) hP
    have h1 := PEqualNP.Outside.L_meta_2880.eval_mono C hC hmy
    rw [hmin m hm] at h1
    exact Bool.le_iff_imp.mp h1 rfl

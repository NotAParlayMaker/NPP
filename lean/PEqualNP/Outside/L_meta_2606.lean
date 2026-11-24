import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2606_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_le {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') (i : ℕ) :
    w.getD i false ≤ w'.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w w' : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx'
    obtain ⟨i, hi, rfl⟩ := hx'
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, List.Forall₂ (fun a b => a ≤ b) w w' →
      List.Forall₂ (fun a b => a ≤ b) (gs.foldl step w) (gs.foldl step w') := by
  induction gs with
  | nil => intro w w' h; simpa using h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem ext (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem at_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step w).getD i false) ∧
    ∀ i < w.length + j, (gs.foldl step w).getD i false = ((gs.take j).foldl step w).getD i false := by
  have hs : gs = gs.take j ++ gs[j] :: gs.drop (j+1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  obtain ⟨q, hq, hql⟩ := ext (gs.take j) w
  have hQ : ((gs.take j).foldl step w).length = w.length + j := by
    rw [hq]; simp [hql]; omega
  obtain ⟨t, ht, _⟩ := ext (gs.drop (j+1)) (step ((gs.take j).foldl step w) gs[j])
  have hf : gs.foldl step w = step ((gs.take j).foldl step w) gs[j] ++ t := by
    conv_lhs => rw [hs]
    rw [List.foldl_append, List.foldl_cons, ht]
  rw [hf]
  constructor
  · rw [← hQ]
    simp [step, List.getD_eq_getElem?_getD]
  · intro i hi
    rw [← hQ] at hi
    have hi2 : i < (step ((gs.take j).foldl step w) gs[j]).length := by simp [step]; omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi2]
    simp only [step]
    rw [List.getElem?_append_left hi]

end PEqualNP.Outside.L_meta_2606_aux

open PEqualNP.Outside.L_meta_2606_aux in
theorem PEqualNP.Outside.L_meta_2606 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 x2 x1 → (∀ (x4 : ℕ), Monotone fun (x5 : Fin x2 → Bool) => PEqualNP.BlindGate.wireValue x1 x2 x5 x4) ∧ ∀ (x4 x5 x6 : ℕ), x1.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } → ∀ (x8 : Fin x2 → Bool), PEqualNP.BlindGate.wireValue x1 x2 x8 (x2 + x4) = (PEqualNP.BlindGate.wireValue x1 x2 x8 x5 && PEqualNP.BlindGate.wireValue x1 x2 x8 x6) := by
  intro C n hC
  obtain ⟨hAO, hRB, _⟩ := hC
  have hw : ∀ x : Fin n → Bool, ∀ w, PEqualNP.BlindGate.wireValue C n x w = (C.gates.foldl step (List.ofFn x)).getD w false := fun _ _ => rfl
  constructor
  · intro w x y hxy
    simp only [hw]
    have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
      rw [List.forall₂_iff_get]
      refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      exact hxy _
    exact getD_le (fold_le C.gates hAO _ _ h0) w
  · intro j a b hg x
    obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg, hgj]
    have hrb := hRB j hj
    rw [hga, hgj] at hrb
    have ha : a < n + j := hrb a (by simp)
    have hb : b < n + j := hrb b (by simp)
    obtain ⟨h1, h2⟩ := at_gate C.gates (List.ofFn x) j hj
    simp only [List.length_ofFn] at h1 h2
    simp only [hw, h1, h2 a ha, h2 b hb, hgj, PEqualNP.CircuitLowerBounds.GateOp.eval]
    simp

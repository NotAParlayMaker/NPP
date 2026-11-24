import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2880_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_le {w v : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w v) (i : ℕ) :
    w.getD i false ≤ v.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w v : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w v) :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx2
    obtain ⟨i, hi, rfl⟩ := hx2
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w v : List Bool, List.Forall₂ (fun a b => a ≤ b) w v →
      List.Forall₂ (fun a b => a ≤ b) (gs.foldl step w) (gs.foldl step v) := by
  induction gs with
  | nil => intro w v h; simpa using h
  | cons g gs ih =>
    intro w v h
    simp only [List.foldl_cons]
    apply ih (fun g2 hg2 => hgs g2 (List.mem_cons_of_mem _ hg2))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem mono (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (o : ℕ) :
    (gs.foldl step (List.ofFn x)).getD o false ≤ (gs.foldl step (List.ofFn y)).getD o false := by
  have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact bool_le.mpr (hxy _)
  exact getD_le (fold_le gs hgs _ _ h0) o

end PEqualNP.Outside.L_meta_2880_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2880_aux in
theorem PEqualNP.Outside.L_meta_2880 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : (Fin x1 → Bool) → Prop), (∀ (x5 : Fin x1 → Bool), Minimal x4 x5 → x2.eval (List.ofFn x5) = Bool.true) → (∀ (x6 : Fin x1 → Bool), Maximal (fun (x7 : Fin x1 → Bool) => ¬x4 x7) x6 → x2.eval (List.ofFn x6) = Bool.false) → ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ x4 x7 := by
  rintro n ⟨gs, out⟩ hC P hmin hmax x
  have hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hC g hg).1
  have hm : ∀ y z : Fin n → Bool, y ≤ z → Circuit.eval ⟨gs, out⟩ (List.ofFn y) = true →
      Circuit.eval ⟨gs, out⟩ (List.ofFn z) = true := by
    intro y z h hy
    exact bool_le.mp (mono n gs hgs y z (fun i => bool_le.mp (h i)) out) hy
  constructor
  · intro hx
    by_contra hP
    obtain ⟨z, hxz, hz⟩ := exists_maximal_ge_of_wellFoundedGT (fun w => ¬P w) x hP
    have h1 := hmax z hz
    have h2 := hm x z hxz hx
    rw [h1] at h2
    exact Bool.false_ne_true h2
  · intro hP
    obtain ⟨y, hyx, hy⟩ := exists_minimal_le_of_wellFoundedLT P x hP
    exact hm y x hyx (hmin y hy)

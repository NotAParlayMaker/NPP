import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2880_aux

open PEqualNP.CircuitLowerBounds

-- Monotonicity of the value of an AND/OR circuit in its inputs.

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

theorem true_le_iff {b : Bool} : (true ≤ b) ↔ b = true := by
  cases b <;> decide

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
      List.Forall₂ (fun a b => a ≤ b)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; simpa using h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem eval_le (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) {n : ℕ}
    {x y : Fin n → Bool} (h : x ≤ y) :
    C.eval (List.ofFn x) ≤ C.eval (List.ofFn y) := by
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h' := (hC g hg).1
    simpa using h'
  have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_ofFn], ?_⟩
    intro i h1 h2
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact h _
  exact getD_le (fold_le C.gates hgs _ _ h0) C.output

end PEqualNP.Outside.L_meta_2880_aux

open PEqualNP.Outside.L_meta_2880_aux in
theorem PEqualNP.Outside.L_meta_2880 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : (Fin x1 → Bool) → Prop), (∀ (x5 : Fin x1 → Bool), Minimal x4 x5 → x2.eval (List.ofFn x5) = Bool.true) → (∀ (x6 : Fin x1 → Bool), Maximal (fun (x7 : Fin x1 → Bool) => ¬x4 x7) x6 → x2.eval (List.ofFn x6) = Bool.false) → ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ x4 x7 := by
  intro x1 x2 hmono x4 hmin hmax x7
  classical
  have mono : ∀ {a b : Fin x1 → Bool}, a ≤ b → x2.eval (List.ofFn a) ≤ x2.eval (List.ofFn b) :=
    fun {_ _} h => eval_le x2 hmono h
  constructor
  · intro he
    by_contra hx4
    let s : Finset (Fin x1 → Bool) := Finset.univ.filter (fun y => ¬ x4 y ∧ x7 ≤ y)
    have hs : s.Nonempty := ⟨x7, by simp [s, hx4]⟩
    obtain ⟨i, hi⟩ := Finset.exists_maximal hs
    have hi_mem : i ∈ s := hi.1
    rw [Finset.mem_filter] at hi_mem
    obtain ⟨-, hni, hx7i⟩ := hi_mem
    have hmaxi : Maximal (fun y : Fin x1 → Bool => ¬ x4 y) i := by
      refine ⟨hni, ?_⟩
      intro y hy hiy
      have hy_mem : y ∈ s := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hy, le_trans hx7i hiy⟩
      exact hi.2 hy_mem hiy
    have hfalse := hmax i hmaxi
    have hle := mono hx7i
    rw [hfalse, he] at hle
    exact absurd hle (by decide)
  · intro hx4
    let s : Finset (Fin x1 → Bool) := Finset.univ.filter (fun y => x4 y ∧ y ≤ x7)
    have hs : s.Nonempty := ⟨x7, by simp [s, hx4]⟩
    obtain ⟨i, hi⟩ := Finset.exists_minimal hs
    have hi_mem : i ∈ s := hi.1
    rw [Finset.mem_filter] at hi_mem
    obtain ⟨-, hx4i, hix7⟩ := hi_mem
    have hmini : Minimal x4 i := by
      refine ⟨hx4i, ?_⟩
      intro y hy hyi
      have hy_mem : y ∈ s := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hy, le_trans hyi hix7⟩
      exact hi.2 hy_mem hyi
    have htrue := hmin i hmini
    have hle := mono hix7
    rw [htrue] at hle
    exact true_le_iff.mp hle

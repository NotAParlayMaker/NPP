import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1322_aux

open PEqualNP.CircuitLowerBounds

def dg (k : ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | GateOp.and, l => if l.all (fun i => decide (i < k)) then ⟨GateOp.or, l⟩ else ⟨GateOp.and, []⟩
  | GateOp.or, l => ⟨GateOp.and, l.filter (fun i => decide (i < k))⟩
  | GateOp.not, [] => ⟨GateOp.or, []⟩
  | GateOp.not, a :: _ => if a < k then ⟨GateOp.not, [a]⟩ else ⟨GateOp.or, []⟩
  | _, _ => g

def dual : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => dg k g :: dual (k + 1) gs

def ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem dg_ok (k : ℕ) (g : Gate) (h : ok g) : ok (dg k g) := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hl⟩ := h
  simp only at hop hl
  rcases hop with rfl | rfl | rfl
  · simp only [dg, ok]; split_ifs <;> simp_all
  · simp only [dg, ok]
    simp only [true_or, or_true, true_and]
    exact le_trans (List.length_filter_le _ _) hl
  · cases l with
    | nil => simp [dg, ok]
    | cons a t => simp only [dg, ok]; split_ifs <;> simp

theorem dg_not (k : ℕ) (g : Gate) (h : (dg k g).op = GateOp.not) : g.op = GateOp.not := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and => simp only [dg] at h; split_ifs at h <;> simp_all
  | or => simp [dg] at h
  | not => rfl
  | mod m => exact h
  | maj => exact h

theorem dg_eval (k : ℕ) (g : Gate) (h : ok g) (f f' : ℕ → Bool)
    (hf : ∀ i, i < k → f' i = !f i) (hf2 : ∀ i, k ≤ i → f i = false ∧ f' i = false) :
    (dg k g).op.eval ((dg k g).inputs.map f') = !(g.op.eval (g.inputs.map f)) := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, -⟩ := h
  simp only at hop
  rcases hop with rfl | rfl | rfl
  · simp only [dg]
    split_ifs with hc
    · simp only [GateOp.eval, List.any_map, List.all_map]
      simp only [List.all_eq_true, decide_eq_true_eq] at hc
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, Function.comp_apply, id_eq, Bool.not_eq_true',
        List.all_eq_false]
      constructor
      · rintro ⟨x, hx, h1⟩; exact ⟨x, hx, by rw [hf x (hc x hx)] at h1; simpa using h1⟩
      · rintro ⟨x, hx, h1⟩; exact ⟨x, hx, by rw [hf x (hc x hx)]; simpa using h1⟩
    · simp only [List.all_eq_true, decide_eq_true_eq, not_forall, not_lt] at hc
      obtain ⟨x, hx, hk⟩ := hc
      simp only [GateOp.eval, List.map_nil, List.all_nil, List.all_map]
      symm
      rw [Bool.not_eq_true']
      rw [List.all_eq_false]
      exact ⟨x, hx, by simp [(hf2 x hk).1]⟩
  · simp only [dg, GateOp.eval, List.any_map, List.all_map]
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_filter, decide_eq_true_eq, Function.comp_apply, id_eq,
      Bool.not_eq_true', List.any_eq_false, and_imp]
    constructor
    · intro H x hx
      by_cases hk : x < k
      · have := H x hx hk; rw [hf x hk] at this; simpa using this
      · simp [(hf2 x (by omega)).1]
    · intro H x hx hk
      rw [hf x hk]; simp [H x hx]
  · cases l with
    | nil => simp [dg, GateOp.eval]
    | cons a t =>
      simp only [dg]
      split_ifs with hk
      · simp [GateOp.eval, hf a hk]
      · simp [GateOp.eval, (hf2 a (by omega)).1]

theorem main (gs : List Gate) (hgs : ∀ g ∈ gs, ok g) : ∀ (k : ℕ) (W W' : List Bool),
    W.length = k → W'.length = k → (∀ i < k, W'.getD i false = !W.getD i false) →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).length
      = k + gs.length ∧
    ∀ i < k + gs.length,
      ((dual k gs).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        W').getD i false =
      !((gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        W).getD i false) := by
  induction gs with
  | nil => intro k W W' h1 h2 h3; simpa [dual] using ⟨h1, h3⟩
  | cons g gs ih =>
    intro k W W' h1 h2 h3
    have hg : ok g := hgs g (by simp)
    have hrest : ∀ g ∈ gs, ok g := fun g' hg' => hgs g' (by simp [hg'])
    have key := dg_eval k g hg (fun i => W.getD i false) (fun i => W'.getD i false)
      (fun i hi => h3 i hi)
      (fun i hi => ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩)
    have := ih hrest (k + 1)
      (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
      (W' ++ [(dg k g).op.eval ((dg k g).inputs.map fun i => W'.getD i false)])
      (by simp [h1]) (by simp [h2]) (by
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact h3 i hi
        · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          simp only [h1, h2, Nat.sub_self, List.getD_cons_zero]
          exact key)
    simp only [List.foldl_cons, dual, List.length_cons]
    refine ⟨by rw [this.1]; omega, fun i hi => this.2 i (by omega)⟩

theorem dual_get (gs : List Gate) : ∀ (k i : ℕ), (dual k gs)[i]? = (gs[i]?).map (dg (k + i)) := by
  induction gs with
  | nil => intro k i; simp [dual]
  | cons g gs ih =>
    intro k i
    cases i with
    | zero => simp [dual]
    | succ i => simp only [dual, List.getElem?_cons_succ]; rw [ih]; congr 2; omega

theorem dual_len (gs : List Gate) : ∀ k, (dual k gs).length = gs.length := by
  induction gs with
  | nil => intro k; rfl
  | cons g gs ih => intro k; simp [dual, ih]

end PEqualNP.Outside.L_meta_1322_aux

open PEqualNP.Outside.L_meta_1322_aux in
theorem PEqualNP.Outside.L_meta_1322 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.length = gates.length ∧ (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), gates'[i]? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ (w : ℕ) (x : Fin n → Bool), w < n + gates.length → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates', 0⟩ (List.ofFn x)).getD w false = !((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun p : Fin n => !x p))).getD w false) := by
  intro n gates hg
  refine ⟨dual n gates, dual_len gates n, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
    have h2 := dual_get gates n i
    rw [List.getElem?_eq_getElem hi] at h2
    obtain ⟨g, hg1, hg2⟩ := Option.map_eq_some_iff.mp h2.symm
    rw [← hg2]
    exact dg_ok _ g (hg g (List.mem_of_getElem? hg1))
  · intro i g' h1 h2
    rw [dual_get] at h1
    obtain ⟨g, hg1, rfl⟩ := Option.map_eq_some_iff.mp h1
    exact ⟨g, hg1, dg_not _ g h2⟩
  · intro w x hw
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    exact (main gates hg n (List.ofFn (fun p : Fin n => !x p)) (List.ofFn x) (by simp) (by simp)
      (by intro i hi; simp [List.getD_eq_getElem?_getD, hi])).2 w hw

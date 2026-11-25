import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12410

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_eq (L : List Bool) (S : Bool) : (L ++ [S]).getD L.length false = S := by
  simp

/-- Step `k`: an AND gate for vertex `k + 1` on both sides, and an OR gate adding it to the
  running OR on wire `2 n + 2 k`. -/
def step (n k : ℕ) : List Gate :=
  [⟨GateOp.and, [k + 1, n + (k + 1)]⟩, ⟨GateOp.or, [2 * n + 2 * k, 2 * n + 2 * k + 1]⟩]

/-- The gates that put on wire `2 n + 2 k` the OR over `a ≤ k` of (left `a` AND right `a`). -/
def pre (n : ℕ) : ℕ → List Gate
  | 0 => [⟨GateOp.and, [0, n + 0]⟩]
  | k + 1 => pre n k ++ step n k

theorem length_pre (n : ℕ) : ∀ k, (pre n k).length = 2 * k + 1
  | 0 => rfl
  | k + 1 => by simp [pre, step, length_pre n k]; omega

/-- The circuit: the running OR over all `n` vertices, then one NOT. -/
def circ (n : ℕ) : Circuit :=
  ⟨pre n (n - 1) ++ [⟨GateOp.not, [2 * n + 2 * (n - 1)]⟩], 2 * n + 2 * (n - 1) + 1⟩

theorem oneEach_left (n : ℕ) (u v : Fin n) (a : ℕ) (h : a < n) :
    (oneEach u v).getD a false = decide (a = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact h),
    List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact h), List.getElem_ofFn]
  simp [Fin.ext_iff]

theorem oneEach_right (n : ℕ) (u v : Fin n) (a : ℕ) (h : a < n) :
    (oneEach u v).getD (n + a) false = decide (a = v.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact h), List.getElem_ofFn]
  simp [Fin.ext_iff]

theorem length_oneEach (n : ℕ) (u v : Fin n) : (oneEach u v).length = n + n := by
  simp [oneEach]

theorem inv (n : ℕ) (u v : Fin n) : ∀ k, k < n →
    (wiresFrom (pre n k) (oneEach u v)).length = 2 * n + 2 * k + 1 ∧
    (wiresFrom (pre n k) (oneEach u v)).getD (2 * n + 2 * k) false
      = decide (u.val = v.val ∧ u.val ≤ k) ∧
    ∀ i, i < n + n → (wiresFrom (pre n k) (oneEach u v)).getD i false = (oneEach u v).getD i false := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨by rw [length_wiresFrom, length_oneEach, length_pre]; omega, ?_,
      fun i hi => getD_wiresFrom _ _ _ (by rw [length_oneEach]; exact hi)⟩
    have e : wiresFrom (pre n 0) (oneEach u v) = oneEach u v ++
        [GateOp.and.eval ([0, n + 0].map fun i => (oneEach u v).getD i false)] := rfl
    have hl := length_oneEach n u v
    rw [e, show 2 * n + 2 * 0 = (oneEach u v).length by omega, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
      Bool.and_true]
    rw [oneEach_left n u v 0 hk, oneEach_right n u v 0 hk]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> intro h <;> omega
  | succ k ih =>
    intro hk
    obtain ⟨hl, hv, hp⟩ := ih (by omega)
    set W := wiresFrom (pre n k) (oneEach u v) with hW
    have e : wiresFrom (pre n (k + 1)) (oneEach u v) = wiresFrom (step n k) W := by
      rw [hW, ← wiresFrom_append]; rfl
    rw [e]
    set A := GateOp.and.eval ([k + 1, n + (k + 1)].map fun i => W.getD i false) with hA
    have e2 : wiresFrom (step n k) W = W ++ [A] ++
        [GateOp.or.eval ([2 * n + 2 * k, 2 * n + 2 * k + 1].map fun i => (W ++ [A]).getD i false)] := rfl
    rw [e2]
    refine ⟨by simp [hl]; omega, ?_, ?_⟩
    · rw [show 2 * n + 2 * (k + 1) = (W ++ [A]).length by simp [hl]; omega, getD_snoc_eq]
      have g1 : (W ++ [A]).getD (2 * n + 2 * k) false = W.getD (2 * n + 2 * k) false :=
        List.getD_append _ _ _ _ (by omega)
      have g2 : (W ++ [A]).getD (2 * n + 2 * k + 1) false = A := by
        rw [show 2 * n + 2 * k + 1 = W.length by omega]; exact getD_snoc_eq W A
      have hk1 : k + 1 < n := hk
      have hl1 : (W.getD (k + 1) false) = decide (k + 1 = u.val) := by
        rw [hp _ (by omega)]; exact oneEach_left n u v _ hk1
      have hr1 : (W.getD (n + (k + 1)) false) = decide (k + 1 = v.val) := by
        rw [hp _ (by omega)]; exact oneEach_right n u v _ hk1
      have hAv : A = (decide (k + 1 = u.val) && decide (k + 1 = v.val)) := by
        rw [hA]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
          Bool.and_true]
        rw [hl1, hr1]
      simp only [List.map_cons, List.map_nil]
      rw [g1, g2, hv, hAv]
      simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor <;> intro h <;> omega
    · intro i hi
      rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
      exact hp i hi

theorem circ_ok (n : ℕ) (hn : 1 ≤ n) : FanInTwo (circ n) ∧ (circ n).size ≤ 2 * n ∧
    Represents (fun u v : Fin n => decide (u ≠ v)) (circ n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [circ, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · revert g
      generalize n - 1 = k
      induction k with
      | zero => intro g hg; simp [pre] at hg; subst hg; simp
      | succ k ih =>
        intro g hg
        simp only [pre, step, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with hg | rfl | rfl
        · exact ih g hg
        · simp
        · simp
    · simp
  · show (pre n (n - 1) ++ _).length ≤ 2 * n
    simp [length_pre]; omega
  · intro u v
    obtain ⟨hl, hv, _⟩ := inv n u v (n - 1) (by omega)
    show (wiresFrom (pre n (n - 1) ++ [⟨GateOp.not, [2 * n + 2 * (n - 1)]⟩]) (oneEach u v)).getD
      (2 * n + 2 * (n - 1) + 1) false = _
    rw [wiresFrom_append]
    set W := wiresFrom (pre n (n - 1)) (oneEach u v)
    have e : wiresFrom [⟨GateOp.not, [2 * n + 2 * (n - 1)]⟩] W
        = W ++ [GateOp.not.eval ([2 * n + 2 * (n - 1)].map fun i => W.getD i false)] := rfl
    rw [e, show 2 * n + 2 * (n - 1) + 1 = W.length by omega, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, hv]
    have hu := u.isLt
    have hv' := v.isLt
    by_cases h : u = v
    · subst h; simp; omega
    · have : u.val ≠ v.val := fun e => h (Fin.ext e)
      simp [h, this]

end PEqualNP.Outside.L_meta_12410

open PEqualNP.Outside.L_meta_12410 in
theorem PEqualNP.Outside.L_meta_12410 : ∀ n : ℕ, ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 * n ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide (u ≠ v)) C := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨⟨[], 0⟩, fun g hg => by simp at hg, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
    intro u
    exact u.elim0
  · exact ⟨circ n, circ_ok n hn⟩

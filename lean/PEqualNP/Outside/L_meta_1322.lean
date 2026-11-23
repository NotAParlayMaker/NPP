import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1322

open PEqualNP.CircuitLowerBounds

def dualGate (k : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if g.inputs.all (fun i => decide (i < k)) then ⟨GateOp.or, g.inputs⟩
      else ⟨GateOp.and, []⟩
  | GateOp.or => ⟨GateOp.and, g.inputs.filter (fun i => decide (i < k))⟩
  | GateOp.not =>
      match g.inputs with
      | [] => ⟨GateOp.or, []⟩
      | j :: _ => if j < k then ⟨GateOp.not, [j]⟩ else ⟨GateOp.or, []⟩
  | _ => g

def dualList : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => dualGate k g :: dualList (k + 1) gs

lemma dualList_length (k : ℕ) (gs : List Gate) : (dualList k gs).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [dualList, ih]

def Rel (k : ℕ) (a b : List Bool) : Prop :=
  a.length = k ∧ b.length = k ∧ ∀ w < k, b.getD w false = !(a.getD w false)

lemma getD_big (a : List Bool) (i : ℕ) (h : a.length ≤ i) : a.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma and_all (k : ℕ) (a b : List Bool) (hw : ∀ w < k, b.getD w false = !(a.getD w false))
    (l : List ℕ) (hl : ∀ i ∈ l, i < k) :
    (l.map fun i => b.getD i false).any id = !((l.map fun i => a.getD i false).all id) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.map_cons, List.map_cons, List.any_cons, List.all_cons,
      ih (fun j hj => hl j (List.mem_cons_of_mem i hj)), hw i (hl i List.mem_cons_self)]
    cases a.getD i false <;> rfl

lemma and_big (k : ℕ) (a : List Bool) (ha : a.length = k)
    (l : List ℕ) (hl : ∃ i ∈ l, ¬ i < k) :
    (l.map fun i => a.getD i false).all id = false := by
  obtain ⟨i, hi, hik⟩ := hl
  rw [Bool.eq_false_iff]
  intro h
  rw [List.all_eq_true] at h
  have := h (a.getD i false) (List.mem_map_of_mem hi)
  rw [getD_big a i (by omega)] at this
  exact absurd this (by decide)

lemma and_case (k : ℕ) (a b : List Bool) (hr : Rel k a b) (l : List ℕ) :
    (if l.all (fun i => decide (i < k)) = true then (l.map fun i => b.getD i false).any id
      else true) = !((l.map fun i => a.getD i false).all id) := by
  obtain ⟨ha, hb, hw⟩ := hr
  by_cases hl : l.all (fun i => decide (i < k)) = true
  · rw [if_pos hl]
    rw [List.all_eq_true] at hl
    exact and_all k a b hw l (fun i hi => of_decide_eq_true (hl i hi))
  · rw [if_neg hl]
    have : ∃ i ∈ l, ¬ i < k := by
      by_contra hc
      apply hl
      rw [List.all_eq_true]
      intro i hi
      by_contra h
      exact hc ⟨i, hi, fun h' => h (decide_eq_true h')⟩
    rw [and_big k a ha l this]
    rfl

lemma or_case (k : ℕ) (a b : List Bool) (hr : Rel k a b) (l : List ℕ) :
    ((l.filter fun i => decide (i < k)).map fun i => b.getD i false).all id
      = !((l.map fun i => a.getD i false).any id) := by
  obtain ⟨ha, hb, hw⟩ := hr
  induction l with
  | nil => simp
  | cons i l ih =>
    by_cases hi : i < k
    · rw [List.filter_cons_of_pos (p := fun i => decide (i < k)) (decide_eq_true hi), List.map_cons, List.all_cons, ih,
        List.map_cons, List.any_cons, hw i hi]
      cases a.getD i false <;> rfl
    · rw [List.filter_cons_of_neg (p := fun i => decide (i < k)) (fun h => hi (of_decide_eq_true h)), ih,
        List.map_cons, List.any_cons, getD_big a i (by omega)]
      rfl

lemma gate_dual (k : ℕ) (a b : List Bool) (hr : Rel k a b) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (dualGate k g).op.eval ((dualGate k g).inputs.map fun i => b.getD i false)
      = !(g.op.eval (g.inputs.map fun i => a.getD i false)) := by
  obtain ⟨op, l⟩ := g
  simp only at hg
  rcases hg with rfl | rfl | rfl
  · have := and_case k a b hr l
    unfold dualGate
    by_cases hl : l.all (fun i => decide (i < k)) = true
    · simp only [hl, if_true] at this ⊢
      simpa [GateOp.eval] using this
    · simp only [hl, Bool.false_eq_true, if_false] at this ⊢
      simpa [GateOp.eval] using this
  · have := or_case k a b hr l
    simpa [dualGate, GateOp.eval] using this
  · obtain ⟨ha, hb, hw⟩ := hr
    cases l with
    | nil => simp [dualGate, GateOp.eval]
    | cons j l =>
      by_cases hj : j < k
      · simp only [dualGate, GateOp.eval, hj, if_true, List.map_cons, List.map_nil,
          List.headD_cons]
        rw [hw j hj]
      · simp only [dualGate, GateOp.eval, hj, if_false, List.map_cons, List.map_nil,
          List.headD_cons, List.any_nil]
        rw [getD_big a j (by omega)]
        rfl

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma main_ind (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (k : ℕ) (a b : List Bool), Rel k a b →
      Rel (k + gs.length) (gs.foldl step a) ((dualList k gs).foldl step b) := by
  induction gs with
  | nil => intro k a b h; simpa [dualList] using h
  | cons g gs ih =>
    intro k a b h
    have hg := hgs g (by simp)
    have ih' := ih (fun g' hg' => hgs g' (by simp [hg'])) (k + 1) (step a g)
      (step b (dualGate k g))
    have hk : k + 1 + gs.length = k + (g :: gs).length := by simp; omega
    rw [← hk]
    simp only [List.foldl_cons, dualList]
    apply ih'
    obtain ⟨ha, hb, hw⟩ := h
    refine ⟨by simp [step, ha], by simp [step, hb], ?_⟩
    intro w hw'
    by_cases hwk : w < k
    · simp only [step]
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact hw w hwk
    · have hwe : w = k := by omega
      subst hwe
      simp only [step]
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ha, hb, Nat.sub_self, List.getD_cons_zero]
      exact gate_dual w a b ⟨ha, hb, hw⟩ g hg

lemma dualGate_ok (k : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ((dualGate k g).op = GateOp.and ∨ (dualGate k g).op = GateOp.or ∨
      (dualGate k g).op = GateOp.not) ∧ (dualGate k g).inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  obtain ⟨h1, h2⟩ := hg
  simp only at h1 h2
  rcases h1 with rfl | rfl | rfl
  · unfold dualGate
    by_cases hl : l.all (fun i => decide (i < k)) = true
    · simp [hl, h2]
    · simp [hl]
  · simp only [dualGate]
    exact ⟨by simp, le_trans (List.length_filter_le _ _) h2⟩
  · cases l with
    | nil => simp [dualGate]
    | cons j l =>
      by_cases hj : j < k
      · simp [dualGate, hj]
      · simp [dualGate, hj]

lemma dualGate_not (k : ℕ) (g : Gate) (h : (dualGate k g).op = GateOp.not) :
    g.op = GateOp.not := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and =>
    unfold dualGate at h
    by_cases hl : l.all (fun i => decide (i < k)) = true
    · simp [hl] at h
    · simp [hl] at h
  | or => simp [dualGate] at h
  | not => rfl
  | mod m => exact h
  | maj => exact h

lemma dual_mem (k : ℕ) (gs : List Gate) (g' : Gate) (h : g' ∈ dualList k gs) :
    ∃ k' : ℕ, ∃ g ∈ gs, g' = dualGate k' g := by
  induction gs generalizing k with
  | nil => simp [dualList] at h
  | cons g gs ih =>
    simp only [dualList, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨k, g, List.mem_cons_self, h⟩
    · obtain ⟨k', g0, hg0, e⟩ := ih (k + 1) h
      exact ⟨k', g0, List.mem_cons_of_mem g hg0, e⟩

lemma dual_get (k : ℕ) (gs : List Gate) (i : ℕ) :
    (dualList k gs)[i]? = (gs[i]?).map (dualGate (k + i)) := by
  induction gs generalizing k i with
  | nil => simp [dualList]
  | cons g gs ih =>
    cases i with
    | zero => simp [dualList]
    | succ i =>
      simp only [dualList, List.getElem?_cons_succ]
      rw [ih (k + 1) i]
      congr 2
      omega

lemma init_rel (n : ℕ) (x : Fin n → Bool) :
    Rel n (List.ofFn fun p : Fin n => !x p) (List.ofFn x) := by
  refine ⟨by simp, by simp, ?_⟩
  intro w hw
  simp [List.getD_eq_getElem?_getD, hw]

end PEqualNP.Outside.L_meta_1322

theorem PEqualNP.Outside.L_meta_1322 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.length = gates.length ∧ (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), gates'[i]? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ (w : ℕ) (x : Fin n → Bool), w < n + gates.length → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates', 0⟩ (List.ofFn x)).getD w false = !((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun p : Fin n => !x p))).getD w false) := by
  intro n gates hg
  refine ⟨PEqualNP.Outside.L_meta_1322.dualList n gates,
    PEqualNP.Outside.L_meta_1322.dualList_length n gates, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨k', g, hgm, rfl⟩ := PEqualNP.Outside.L_meta_1322.dual_mem n gates g' hg'
    exact PEqualNP.Outside.L_meta_1322.dualGate_ok k' g (hg g hgm)
  · intro i g' hi hnot
    rw [PEqualNP.Outside.L_meta_1322.dual_get] at hi
    cases hgi : gates[i]? with
    | none => rw [hgi] at hi; simp at hi
    | some g =>
      rw [hgi] at hi
      simp only [Option.map_some, Option.some.injEq] at hi
      subst hi
      exact ⟨g, rfl, PEqualNP.Outside.L_meta_1322.dualGate_not _ g hnot⟩
  · intro w x hw
    have h := PEqualNP.Outside.L_meta_1322.main_ind gates (fun g hgm => (hg g hgm).1) n
      _ _ (PEqualNP.Outside.L_meta_1322.init_rel n x)
    exact h.2.2 w hw

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1322

open PEqualNP.CircuitLowerBounds

def dualGate (k : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and =>
    if g.inputs.any (fun r => decide (k ≤ r)) then ⟨GateOp.and, []⟩ else ⟨GateOp.or, g.inputs⟩
  | GateOp.or =>
    ⟨GateOp.and, g.inputs.filter (fun r => decide (r < k))⟩
  | GateOp.not =>
    match g.inputs with
    | r :: _ => if r < k then ⟨GateOp.not, [r]⟩ else ⟨GateOp.or, []⟩
    | [] => ⟨GateOp.or, []⟩
  | _ => g

def dualGates (k : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => dualGate k g :: dualGates (k + 1) gs

lemma dualGates_length (k : ℕ) (gs : List Gate) :
    (dualGates k gs).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [dualGates, ih]

lemma dualGate_valid (k : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ((dualGate k g).op = GateOp.and ∨ (dualGate k g).op = GateOp.or ∨ (dualGate k g).op = GateOp.not) ∧
      (dualGate k g).inputs.length ≤ 2 := by
  rcases hg with ⟨hop, hlen⟩
  rcases hop with h | h | h
  · simp only [dualGate, h]
    split_ifs
    · exact ⟨Or.inl rfl, by simp⟩
    · exact ⟨Or.inr (Or.inl rfl), hlen⟩
  · simp only [dualGate, h]
    exact ⟨Or.inl trivial, (List.length_filter_le _ _).trans hlen⟩
  · simp only [dualGate, h]
    cases g.inputs with
    | nil => exact ⟨Or.inr (Or.inl rfl), by simp⟩
    | cons r rs =>
      dsimp only
      split_ifs
      · exact ⟨Or.inr (Or.inr rfl), by simp⟩
      · exact ⟨Or.inr (Or.inl rfl), by simp⟩

lemma dualGates_valid (k : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ∀ g' ∈ dualGates k gs,
      (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 := by
  induction gs generalizing k with
  | nil => intro g' hg'; simp [dualGates] at hg'
  | cons g gs ih =>
    intro g' hg'
    simp only [dualGates, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact dualGate_valid k g (hgs g List.mem_cons_self)
    · exact ih (k + 1) (fun x hx => hgs x (List.mem_cons_of_mem _ hx)) g' hg'

lemma dualGate_not_only (k : ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : (dualGate k g).op = GateOp.not) : g.op = GateOp.not := by
  rcases hg with h | h | h
  · simp only [dualGate, h] at hnot
    split_ifs at hnot
  · simp [dualGate, h] at hnot
  · exact h

lemma dualGates_not_only (k : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (i : ℕ) (g' : Gate), (dualGates k gs)[i]? = some g' → g'.op = GateOp.not →
      ∃ g : Gate, gs[i]? = some g ∧ g.op = GateOp.not := by
  induction gs generalizing k with
  | nil => intro i g' hi; simp [dualGates] at hi
  | cons g gs ih =>
    intro i g' hi hnot
    cases i with
    | zero =>
      simp only [dualGates, List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨g, by simp, dualGate_not_only k g (hgs g List.mem_cons_self) hnot⟩
    | succ i =>
      simp only [dualGates, List.getElem?_cons_succ] at hi
      exact ih (k + 1) (fun x hx => hgs x (List.mem_cons_of_mem _ hx)) i g' hi hnot

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun r => acc.getD r false)]) w

lemma dualGate_eval (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (w w' : List Bool) (hlen : w'.length = w.length)
    (hneg : ∀ r < w.length, w'.getD r false = !(w.getD r false)) :
    (dualGate w.length g).op.eval ((dualGate w.length g).inputs.map fun r => w'.getD r false) =
      !(g.op.eval (g.inputs.map fun r => w.getD r false)) := by
  rcases hg with h | h | h
  · simp only [dualGate, h]
    split_ifs with hany
    · simp only [GateOp.eval, List.map_nil, List.all_nil, List.all_map]
      symm
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro hall
      simp only [List.all_eq_true, Function.comp_apply, id_eq] at hall
      simp only [List.any_eq_true, decide_eq_true_eq] at hany
      obtain ⟨r, hr, hge⟩ := hany
      have hrt := hall r hr
      rw [List.getD_eq_default _ _ hge] at hrt
      exact Bool.noConfusion hrt
    · simp only [GateOp.eval, List.any_map, List.all_map]
      simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and, not_le] at hany
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, Function.comp_apply, id_eq, Bool.not_eq_true',
        Bool.eq_false_iff, ne_eq, List.all_eq_true, not_forall]
      constructor
      · rintro ⟨r, hr, hrt⟩
        refine ⟨r, hr, ?_⟩
        rw [hneg r (hany r hr)] at hrt
        cases hv : w.getD r false
        · decide
        · rw [hv] at hrt; exact Bool.noConfusion hrt
      · rintro ⟨r, hr, hrf⟩
        refine ⟨r, hr, ?_⟩
        rw [hneg r (hany r hr)]
        cases hv : w.getD r false
        · rfl
        · exact absurd hv hrf
  · simp only [dualGate, h, GateOp.eval, List.all_map, List.any_map]
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_filter, decide_eq_true_eq, and_imp,
      Function.comp_apply, id_eq, Bool.not_eq_true', List.any_eq_false]
    constructor
    · intro hall r hr
      by_cases hlt : r < w.length
      · have hrt := hall r hr hlt
        rw [hneg r hlt] at hrt
        cases hv : w.getD r false
        · decide
        · rw [hv] at hrt; exact Bool.noConfusion hrt
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]
        decide
    · intro hnone r hr hlt
      have hrf := hnone r hr
      rw [hneg r hlt]
      cases hv : w.getD r false
      · rfl
      · exact absurd hv hrf
  · simp only [dualGate, h]
    cases h_in : g.inputs with
    | nil => simp [GateOp.eval]
    | cons r rs =>
      dsimp only
      split_ifs with hlt
      · simp only [GateOp.eval, List.map_cons, List.headD_cons, hneg r hlt, Bool.not_not]
      · simp only [GateOp.eval, List.map_nil, List.any_nil, List.map_cons, List.headD_cons,
          List.getD_eq_default _ _ (Nat.le_of_not_lt hlt), Bool.not_false, Bool.not_true]

lemma run_dualGates (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (w w' : List Bool), w'.length = w.length →
      (∀ r < w.length, w'.getD r false = !(w.getD r false)) →
      ∀ r < w.length + gs.length,
        (run (dualGates w.length gs) w').getD r false = !((run gs w).getD r false) := by
  induction gs with
  | nil =>
    intro w w' _ hneg r hr
    exact hneg r (by simpa using hr)
  | cons g gs ih =>
    intro w w' hlen hneg r hr
    have hstep : run (dualGates w.length (g :: gs)) w' =
        run (dualGates (w.length + 1) gs)
          (w' ++ [(dualGate w.length g).op.eval ((dualGate w.length g).inputs.map fun i => w'.getD i false)]) := rfl
    have hstep0 : run (g :: gs) w =
        run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [hstep, hstep0]
    have hev := dualGate_eval g (hgs g List.mem_cons_self) w w' hlen hneg
    have hlen' : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1 := by simp
    rw [← hlen']
    apply ih (fun x hx => hgs x (List.mem_cons_of_mem _ hx))
    · simp [hlen]
    · intro j hj
      rw [hlen'] at hj
      by_cases hlt : j < w.length
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hlt]
        exact hneg j hlt
      · have hjeq : j = w.length := by omega
        subst hjeq
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ le_rfl]
        simp only [hlen, Nat.sub_self, List.getD_cons_zero]
        exact hev
    · simp only [List.length_cons] at hr
      rw [hlen']
      omega

end PEqualNP.Outside.L_meta_1322

theorem PEqualNP.Outside.L_meta_1322 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.length = gates.length ∧ (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), gates'[i]? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ (w : ℕ) (x : Fin n → Bool), w < n + gates.length → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates', 0⟩ (List.ofFn x)).getD w false = !((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun p : Fin n => !x p))).getD w false) := by
  intro n gates hgs
  refine ⟨PEqualNP.Outside.L_meta_1322.dualGates n gates,
    PEqualNP.Outside.L_meta_1322.dualGates_length n gates,
    PEqualNP.Outside.L_meta_1322.dualGates_valid n gates hgs,
    PEqualNP.Outside.L_meta_1322.dualGates_not_only n gates (fun g hg => (hgs g hg).1),
    ?_⟩
  intro w x hw
  have hrun := PEqualNP.Outside.L_meta_1322.run_dualGates gates (fun g hg => (hgs g hg).1)
    (List.ofFn (fun p : Fin n => !x p)) (List.ofFn x)
    (by simp)
    (by
      intro r hr
      simp only [List.length_ofFn] at hr
      rw [List.getD_eq_getElem _ _ (by simp [hr]), List.getD_eq_getElem _ _ (by simp [hr])]
      simp)
    w (by simpa using hw)
  simpa [List.length_ofFn, PEqualNP.Outside.L_meta_1322.run, PEqualNP.CircuitLowerBounds.Circuit.wires] using hrun

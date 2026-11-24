import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3592

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

theorem fold_len (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [F, List.length_append, List.length_cons, List.length_nil]
    omega

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl F w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp only [F, List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [F, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- prefix wires before gate k agree with the full wires below n + k, and read false above -/
theorem take_getD (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k ≤ gs.length) (i : ℕ) :
    ((gs.take k).foldl F w).getD i false
      = if i < w.length + k then (gs.foldl F w).getD i false else false := by
  have hsplit : gs.foldl F w = (gs.drop k).foldl F ((gs.take k).foldl F w) := by
    rw [← List.foldl_append, List.take_append_drop]
  have hlen : ((gs.take k).foldl F w).length = w.length + k := by
    rw [fold_len, List.length_take]; omega
  split_ifs with h
  · rw [hsplit]
    exact (fold_pre (gs.drop k) _ i (by omega)).symm
  · exact List.getD_eq_default _ _ (by omega)

theorem gate_val (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (gs.foldl F w).getD (w.length + k) false
      = gs[k].op.eval (gs[k].inputs.map fun i =>
          if i < w.length + k then (gs.foldl F w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.drop_eq_getElem_cons hk]
  have hlen : ((gs.take k).foldl F w).length = w.length + k := by
    rw [fold_len, List.length_take]; omega
  have e1 : (gs.foldl F w).getD (w.length + k) false
      = gs[k].op.eval (gs[k].inputs.map fun i => ((gs.take k).foldl F w).getD i false) := by
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [fold_pre _ _ _ (by simp only [F, List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [F]
    rw [← hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
    simp
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro i _
  exact take_getD gs w k (le_of_lt hk) i

def rgF (m : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun i => if i < m then i else i - 1)⟩

def rho (m w i : ℕ) : ℕ := if i < m then i else if i = m then w else i - 1

def rgB (m w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho m w)⟩

theorem stageA (m : ℕ) (A : List Gate) :
    ∀ Q : List Bool, Q.length + A.length ≤ m → (A.map (rgF m)).foldl F Q = A.foldl F Q := by
  induction A with
  | nil => intro Q _; rfl
  | cons g A ih =>
    intro Q hQ
    simp only [List.length_cons] at hQ
    simp only [List.map_cons, List.foldl_cons]
    have hF : F Q (rgF m g) = F Q g := by
      simp only [F, rgF, List.map_map]
      congr 3
      apply List.map_congr_left
      intro i _
      simp only [Function.comp]
      split_ifs with h
      · rfl
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rw [hF]
    apply ih
    simp only [F, List.length_append, List.length_cons, List.length_nil]
    omega

theorem key2 (P M : List Bool) (v : Bool) (m w : ℕ) (hP : P.length = m) (hw : w < m) (i : ℕ)
    (hi : i ≠ m ∨ P.getD w false = v) :
    (P ++ M).getD (rho m w i) false = (P ++ v :: M).getD i false := by
  unfold rho
  by_cases h1 : i < m
  · simp only [h1, ite_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · simp only [h1, ite_false]
    by_cases h2 : i = m
    · simp only [h2, ite_true]
      subst h2
      rcases hi with hi | hi
      · exact absurd rfl hi
      · rw [List.getD_append _ _ _ _ (by omega), hi, ← hP, List.getD_append_right _ _ _ _ (le_refl _)]
        simp
    · simp only [h2, ite_false]
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hP]
      obtain ⟨k, hk⟩ : ∃ k, i - m = k + 1 := ⟨i - m - 1, by omega⟩
      rw [hk, List.getD_cons_succ]
      congr 1
      omega

theorem stageB (m w : ℕ) (P : List Bool) (hP : P.length = m) (hw : w < m) (v : Bool) (B : List Gate)
    (hB : ∀ g ∈ B, m ∈ g.inputs → P.getD w false = v) :
    ∀ M : List Bool, ∀ i, (i ≠ m ∨ P.getD w false = v) →
      ((B.map (rgB m w)).foldl F (P ++ M)).getD (rho m w i) false = (B.foldl F (P ++ v :: M)).getD i false := by
  induction B with
  | nil => intro M i hi; exact key2 P M v m w hP hw i hi
  | cons g B ih =>
    intro M i hi
    simp only [List.map_cons, List.foldl_cons]
    have h1 : F (P ++ M) (rgB m w g) = P ++ (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
      simp only [F, rgB, List.map_map, List.append_assoc]
      have hm : List.map ((fun i => (P ++ M).getD i false) ∘ rho m w) g.inputs
          = List.map (fun i => (P ++ v :: M).getD i false) g.inputs := by
        apply List.map_congr_left
        intro i' hi'
        simp only [Function.comp]
        apply key2 P M v m w hP hw i'
        by_cases he : i' = m
        · exact Or.inr (hB g (by simp) (he ▸ hi'))
        · exact Or.inl he
      rw [hm]
    have h2 : F (P ++ v :: M) g = P ++ v :: (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
      simp [F]
    rw [h1, h2]
    exact ih (fun g' hg' => hB g' (by simp [hg'])) _ i hi

theorem del_getD (gs : List Gate) (j : ℕ) (hj : j < gs.length) (x : List Bool) (w : ℕ)
    (hw : w < x.length + j)
    (hB : ∀ g ∈ gs.drop (j + 1), x.length + j ∈ g.inputs →
      (gs.foldl F x).getD w false = (gs.foldl F x).getD (x.length + j) false)
    (i : ℕ) (hi : i ≠ x.length + j ∨ (gs.foldl F x).getD w false = (gs.foldl F x).getD (x.length + j) false) :
    (((gs.take j).map (rgF (x.length + j)) ++ (gs.drop (j + 1)).map (rgB (x.length + j) w)).foldl F x).getD
      (rho (x.length + j) w i) false = (gs.foldl F x).getD i false := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hj]
  set P := (gs.take j).foldl F x with hPdef
  have hPlen : P.length = x.length + j := by rw [hPdef, fold_len, List.length_take]; omega
  set v := gs[j].op.eval (gs[j].inputs.map fun i => P.getD i false) with hv
  have hfull : gs.foldl F x = (gs.drop (j + 1)).foldl F (P ++ [v]) := by
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rfl
  have hfw : (gs.foldl F x).getD w false = P.getD w false := by
    rw [hfull, fold_pre _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
  have hfm : (gs.foldl F x).getD (x.length + j) false = v := by
    rw [hfull, fold_pre _ _ _ (by simp; omega), ← hPlen, List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  rw [List.foldl_append, stageA _ _ x (by rw [List.length_take]; omega), ← hPdef]
  rw [hfw, hfm] at hB hi
  have := stageB (x.length + j) w P hPlen hw v (gs.drop (j + 1)) hB [] i hi
  rw [List.append_nil] at this
  rw [this, hfull]

def Wf (C : Circuit) {n : ℕ} (x : Fin n → Bool) : List Bool := C.gates.foldl F (List.ofFn x)

def Deg (n : ℕ) (C : Circuit) (k : ℕ) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, (Wf C x).getD (n + k) false = c) ∨
  (∃ a < n + k, ∀ x : Fin n → Bool, (Wf C x).getD (n + k) false = (Wf C x).getD a false)

theorem val_eq (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (x : Fin n → Bool) :
    (Wf C x).getD (n + k) false = C.gates[k].op.eval (C.gates[k].inputs.map fun i =>
      if i < n + k then (Wf C x).getD i false else false) := by
  have := gate_val C.gates (List.ofFn x) k hk
  simp only [List.length_ofFn] at this
  exact this

theorem classify (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not)
    (hl : C.gates[k].inputs.length ≤ 2)
    (hnot : C.gates[k].op = GateOp.not → C.gates[k].inputs.length ≤ 1)
    (hviol : ¬ ((∀ i ∈ C.gates[k].inputs, i < n + k) ∧ C.gates[k].inputs.Nodup ∧
      (C.gates[k].op = GateOp.not → C.gates[k].inputs.length = 1) ∧
      (C.gates[k].op ≠ GateOp.not → C.gates[k].inputs.length = 2))) : Deg n C k := by
  have hv := val_eq n C k hk
  generalize C.gates[k] = g at hop hl hnot hviol hv
  rcases g with ⟨op, ins⟩
  simp only at hop hl hnot hviol hv
  rcases hop with rfl | rfl | rfl
  · -- and
    match ins, hl, hviol, hv with
    | [], _, _, hv => exact Or.inl ⟨true, fun x => by rw [hv]; simp [GateOp.eval]⟩
    | [a], _, _, hv =>
      by_cases ha : a < n + k
      · exact Or.inr ⟨a, ha, fun x => by rw [hv]; simp [GateOp.eval, ha]⟩
      · exact Or.inl ⟨false, fun x => by rw [hv]; simp [GateOp.eval, ha]⟩
    | [a, b], _, hviol, hv =>
      by_cases ha : a < n + k
      · by_cases hb : b < n + k
        · by_cases hab : a = b
          · subst hab
            exact Or.inr ⟨a, ha, fun x => by rw [hv]; simp [GateOp.eval, ha]⟩
          · exfalso
            apply hviol
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
            · simp [hab]
            · intro h; cases h
            · intro _; rfl
        · exact Or.inl ⟨false, fun x => by rw [hv]; simp [GateOp.eval, hb]⟩
      · exact Or.inl ⟨false, fun x => by rw [hv]; simp [GateOp.eval, ha]⟩
    | _ :: _ :: _ :: _, hl, _, _ => simp at hl
  · -- or
    match ins, hl, hviol, hv with
    | [], _, _, hv => exact Or.inl ⟨false, fun x => by rw [hv]; simp [GateOp.eval]⟩
    | [a], _, _, hv =>
      by_cases ha : a < n + k
      · exact Or.inr ⟨a, ha, fun x => by rw [hv]; simp [GateOp.eval, ha]⟩
      · exact Or.inl ⟨false, fun x => by rw [hv]; simp [GateOp.eval, ha]⟩
    | [a, b], _, hviol, hv =>
      by_cases ha : a < n + k
      · by_cases hb : b < n + k
        · by_cases hab : a = b
          · subst hab
            exact Or.inr ⟨a, ha, fun x => by rw [hv]; simp [GateOp.eval, ha]⟩
          · exfalso
            apply hviol
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
            · simp [hab]
            · intro h; cases h
            · intro _; rfl
        · exact Or.inr ⟨a, ha, fun x => by rw [hv]; simp [GateOp.eval, ha, hb]⟩
      · by_cases hb : b < n + k
        · exact Or.inr ⟨b, hb, fun x => by rw [hv]; simp [GateOp.eval, ha, hb]⟩
        · exact Or.inl ⟨false, fun x => by rw [hv]; simp [GateOp.eval, ha, hb]⟩
    | _ :: _ :: _ :: _, hl, _, _ => simp at hl
  · -- not
    have hl1 := hnot rfl
    match ins, hl1, hviol, hv with
    | [], _, _, hv => exact Or.inl ⟨true, fun x => by rw [hv]; simp [GateOp.eval]⟩
    | [a], _, hviol, hv =>
      by_cases ha : a < n + k
      · exfalso
        apply hviol
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i hi; simp at hi; subst hi; exact ha
        · simp
        · intro _; rfl
        · intro h; exact absurd rfl h
      · exact Or.inl ⟨true, fun x => by rw [hv]; simp [GateOp.eval, ha]⟩
    | _ :: _ :: _, hl1, _, _ => simp at hl1

theorem readsConst (n : ℕ) (C : Circuit) (k j : ℕ) (hk : k < C.gates.length) (hjk : j < k)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not)
    (hl : C.gates[k].inputs.length ≤ 2)
    (hnot : C.gates[k].op = GateOp.not → C.gates[k].inputs.length ≤ 1)
    (hmem : n + j ∈ C.gates[k].inputs) (c : Bool) (hc : ∀ x : Fin n → Bool, (Wf C x).getD (n + j) false = c) :
    Deg n C k := by
  have hv := val_eq n C k hk
  have hmk : n + j < n + k := by omega
  generalize C.gates[k] = g at hop hl hnot hmem hv
  rcases g with ⟨op, ins⟩
  simp only at hop hl hnot hmem hv
  have hc' : ∀ x : Fin n → Bool, (Wf C x)[n + j]?.getD false = c := by
    intro x; rw [← List.getD_eq_getElem?_getD]; exact hc x
  rcases hop with rfl | rfl | rfl
  · match ins, hl, hmem, hv with
    | [], _, hmem, _ => simp at hmem
    | [a], _, hmem, hv =>
      simp at hmem; subst hmem
      exact Or.inl ⟨c, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x]⟩
    | [a, b], _, hmem, hv =>
      simp at hmem
      rcases hmem with rfl | rfl
      · by_cases hb : b < n + k
        · cases c
          · exact Or.inl ⟨false, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x]⟩
          · exact Or.inr ⟨b, hb, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x, hb]⟩
        · exact Or.inl ⟨false, fun x => by rw [hv]; simp [GateOp.eval, hb]⟩
      · by_cases ha : a < n + k
        · cases c
          · exact Or.inl ⟨false, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x]⟩
          · exact Or.inr ⟨a, ha, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x, ha]⟩
        · exact Or.inl ⟨false, fun x => by rw [hv]; simp [GateOp.eval, ha]⟩
    | _ :: _ :: _ :: _, hl, _, _ => simp at hl
  · match ins, hl, hmem, hv with
    | [], _, hmem, _ => simp at hmem
    | [a], _, hmem, hv =>
      simp at hmem; subst hmem
      exact Or.inl ⟨c, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x]⟩
    | [a, b], _, hmem, hv =>
      simp at hmem
      rcases hmem with rfl | rfl
      · by_cases hb : b < n + k
        · cases c
          · exact Or.inr ⟨b, hb, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x, hb]⟩
          · exact Or.inl ⟨true, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x]⟩
        · exact Or.inl ⟨c, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x, hb]⟩
      · by_cases ha : a < n + k
        · cases c
          · exact Or.inr ⟨a, ha, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x, ha]⟩
          · exact Or.inl ⟨true, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x]⟩
        · exact Or.inl ⟨c, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x, ha]⟩
    | _ :: _ :: _ :: _, hl, _, _ => simp at hl
  · have hl1 := hnot rfl
    match ins, hl1, hmem, hv with
    | [], _, hmem, _ => simp at hmem
    | [a], _, hmem, hv =>
      simp at hmem; subst hmem
      exact Or.inl ⟨!c, fun x => by rw [hv]; simp [GateOp.eval, hmk, hc' x]⟩
    | _ :: _ :: _, hl1, _, _ => simp at hl1

end PEqualNP.Outside.L_meta_3592

theorem PEqualNP.Outside.L_meta_3592 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → (∀ x5 ∈ x2.gates, x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ)) → ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → (∀ x9 ∈ x7.inputs, x9 < x1 + x6) ∧ x7.inputs.Nodup ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.not → x7.inputs.length = (1 : ℕ)) ∧ (x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x7.inputs.length = (2 : ℕ)) := by
  classical
  intro n C hmin hnc hnot k g hg
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hg
  by_contra hviol
  have hfan := hmin.1
  have hok : ∀ k' (hk' : k' < C.gates.length),
      (C.gates[k'].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        C.gates[k'].op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        C.gates[k'].op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ C.gates[k'].inputs.length ≤ 2 ∧
      (C.gates[k'].op = PEqualNP.CircuitLowerBounds.GateOp.not → C.gates[k'].inputs.length ≤ 1) := by
    intro k' hk'
    obtain ⟨h1, h2⟩ := hfan _ (List.getElem_mem hk')
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2, hnot _ (List.getElem_mem hk')⟩
  have hdegk := PEqualNP.Outside.L_meta_3592.classify n C k hk (hok k hk).1 (hok k hk).2.1 (hok k hk).2.2 hviol
  let S : Finset ℕ := (Finset.range C.gates.length).filter (fun k => PEqualNP.Outside.L_meta_3592.Deg n C k)
  have hkS : k ∈ S := by simp [S, hk, hdegk]
  set j := S.max' ⟨k, hkS⟩ with hjdef
  have hjS : j ∈ S := S.max'_mem _
  have hmax : ∀ k' ∈ S, k' ≤ j := fun k' h => S.le_max' k' h
  simp only [S, Finset.mem_filter, Finset.mem_range] at hjS
  obtain ⟨hj, hdegj⟩ := hjS
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      obtain ⟨x4, x5, hne⟩ := hnc
      exfalso
      apply hne
      congr 1
      funext i
      exact i.elim0
    · exact h0
  -- the shrunken circuit
  let D : ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun w =>
    ⟨(C.gates.take j).map (PEqualNP.Outside.L_meta_3592.rgF (n + j)) ++
      (C.gates.drop (j + 1)).map (PEqualNP.Outside.L_meta_3592.rgB (n + j) w),
      PEqualNP.Outside.L_meta_3592.rho (n + j) w C.output⟩
  have hDfan : ∀ w, PEqualNP.MetaComplexity.FanInTwo (D w) := by
    intro w g' hg'
    simp only [D, List.mem_append, List.mem_map] at hg'
    rcases hg' with ⟨g0, hg0, rfl⟩ | ⟨g0, hg0, rfl⟩
    · have := hfan g0 (List.mem_of_mem_take hg0)
      simpa [PEqualNP.Outside.L_meta_3592.rgF] using this
    · have := hfan g0 (List.mem_of_mem_drop hg0)
      simpa [PEqualNP.Outside.L_meta_3592.rgB] using this
  have hDsize : ∀ w, (D w).size < C.size := by
    intro w
    simp only [D, PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_map,
      List.length_take, List.length_drop]
    omega
  have hfun : ∀ w, w < n + j →
      (∀ x : Fin n → Bool, ∀ g' ∈ C.gates.drop (j + 1), n + j ∈ g'.inputs →
        (PEqualNP.Outside.L_meta_3592.Wf C x).getD w false =
          (PEqualNP.Outside.L_meta_3592.Wf C x).getD (n + j) false) →
      (∀ x : Fin n → Bool, C.output ≠ n + j ∨ (PEqualNP.Outside.L_meta_3592.Wf C x).getD w false =
          (PEqualNP.Outside.L_meta_3592.Wf C x).getD (n + j) false) →
      PEqualNP.MetaComplexity.circuitFun n (D w) = PEqualNP.MetaComplexity.circuitFun n C := by
    intro w hw hB hout
    funext x
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [PEqualNP.Outside.L_meta_3592.wires_eq, PEqualNP.Outside.L_meta_3592.wires_eq]
    have := PEqualNP.Outside.L_meta_3592.del_getD C.gates j hj (List.ofFn x) w (by simp; omega)
      (by simpa [List.length_ofFn, PEqualNP.Outside.L_meta_3592.Wf] using hB x) C.output
      (by simpa [List.length_ofFn, PEqualNP.Outside.L_meta_3592.Wf] using hout x)
    simp only [List.length_ofFn] at this
    exact this
  rcases hdegj with ⟨c, hc⟩ | ⟨a, ha, hcopy⟩
  · have hnoread : ∀ g' ∈ C.gates.drop (j + 1), n + j ∉ g'.inputs := by
      intro g' hg' hm
      obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hg'
      rw [List.length_drop] at ht
      rw [List.getElem_drop] at hm
      have hk' : j + 1 + t < C.gates.length := by omega
      have hd := PEqualNP.Outside.L_meta_3592.readsConst n C (j + 1 + t) j hk' (by omega)
        (hok _ hk').1 (hok _ hk').2.1 (hok _ hk').2.2 hm c hc
      have : j + 1 + t ∈ S := by simp [S, hk', hd]
      have := hmax _ this
      omega
    have hout : C.output ≠ n + j := by
      intro ho
      obtain ⟨x4, x5, hne⟩ := hnc
      apply hne
      unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [PEqualNP.Outside.L_meta_3592.wires_eq, PEqualNP.Outside.L_meta_3592.wires_eq, ho]
      have h1 := hc x4
      have h2 := hc x5
      unfold PEqualNP.Outside.L_meta_3592.Wf at h1 h2
      rw [h1, h2]
    have h := hmin.2 (D 0) (hDfan 0) (hfun 0 (by omega)
      (fun x g' hg' hm => absurd hm (hnoread g' hg')) (fun _ => Or.inl hout))
    have := hDsize 0
    omega
  · have h := hmin.2 (D a) (hDfan a) (hfun a ha (fun x _ _ _ => (hcopy x).symm)
      (fun x => Or.inr (hcopy x).symm))
    have := hDsize a
    omega

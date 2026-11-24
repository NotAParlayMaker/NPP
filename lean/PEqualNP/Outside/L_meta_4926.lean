import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4926_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.SingleLevel

def Bound (b : Bool) (d a : ℕ) : Prop :=
  (a = 0 → d ≤ 1 ∧ (0 < d → b = true)) ∧
  (a ≤ 1 → 2 ≤ d → b = true)

lemma bound_zero : Bound false 0 0 := by
  simp [Bound]

lemma bound_and {b c : Bool} {d e a h : ℕ}
    (hb : Bound b d a) (hc : Bound c e h) :
    Bound (b && c) (d + e) (max a h + 1) := by
  constructor
  · intro ha
    omega
  · intro ha hd
    have ha0 : a = 0 := by omega
    have hh0 : h = 0 := by omega
    obtain ⟨hbd, hbt⟩ := hb.1 ha0
    obtain ⟨hce, hct⟩ := hc.1 hh0
    have hb' := hbt (by omega)
    have hc' := hct (by omega)
    simp [hb', hc']

lemma bound_or {b c : Bool} {d e a h : ℕ}
    (hb : Bound b d a) (hc : Bound c e h) :
    Bound (b || c) (max d e) (max a h) := by
  constructor
  · intro ha
    have ha0 : a = 0 := by omega
    have hh0 : h = 0 := by omega
    obtain ⟨hbd, hbt⟩ := hb.1 ha0
    obtain ⟨hce, hct⟩ := hc.1 hh0
    refine ⟨by omega, ?_⟩
    intro hd
    by_cases hpos : 0 < d
    · simp [hbt hpos]
    · have he : 0 < e := by omega
      simp [hct he]
  · intro ha hd
    by_cases hd' : 2 ≤ d
    · simp [hb.2 (by omega) hd']
    · have he : 2 ≤ e := by omega
      simp [hc.2 (by omega) he]

def States (w : List Bool) (d a : List ℕ) : Prop :=
  w.length = d.length ∧ w.length = a.length ∧
    ∀ i, Bound (w.getD i false) (d.getD i 0) (a.getD i 0)

lemma states_append {w : List Bool} {d a : List ℕ} {b : Bool} {e h : ℕ}
    (hs : States w d a) (hb : Bound b e h) :
    States (w ++ [b]) (d ++ [e]) (a ++ [h]) := by
  obtain ⟨hwd, hwa, hs⟩ := hs
  refine ⟨by simp [hwd], by simp [hwa], ?_⟩
  intro i
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ (by omega),
      List.getD_append _ _ _ _ (by omega)]
    exact hs i
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    rw [← hwd, ← hwa]
    by_cases heq : i = w.length
    · simpa [heq] using hb
    · have hn : 1 ≤ i - w.length := by omega
      rw [List.getD_eq_default [b] false (by simpa using hn),
        List.getD_eq_default [e] 0 (by simpa using hn),
        List.getD_eq_default [h] 0 (by simpa using hn)]
      exact bound_zero

lemma states_gate (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2)
    {w : List Bool} {d a : List ℕ} (hs : States w d a) :
    States (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (d ++ [g.lineDegree d])
      (a ++ [(g.inputs.map fun i => a.getD i 0).foldr max 0 + andLevel g]) := by
  obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hlen
  apply states_append hs
  rcases hop with hop | hop
  · simpa [Gate.lineDegree, hop, huv, GateOp.eval, andLevel] using
      bound_and (hs.2.2 u) (hs.2.2 v)
  · simpa [Gate.lineDegree, hop, huv, GateOp.eval, andLevel] using
      bound_or (hs.2.2 u) (hs.2.2 v)

lemma states_fold (gs : List Gate)
    (hok : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    {w : List Bool} {d a : List ℕ} (hs : States w d a) :
    States
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      (gs.foldl (fun d g => d ++ [g.lineDegree d]) d)
      (gs.foldl (fun a g =>
        a ++ [(g.inputs.map fun i => a.getD i 0).foldr max 0 + andLevel g]) a) := by
  induction gs generalizing w d a with
  | nil => exact hs
  | cons g gs ih =>
    apply ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    exact states_gate g (hok g List.mem_cons_self).1 (hok g List.mem_cons_self).2 hs

lemma initial_states (n : ℕ) (v : Fin n) :
    States (List.ofFn fun i : Fin n => decide (i = v))
      ((List.range n).map fun i => if i ∈ ({v.val} : Finset ℕ) then 1 else 0)
      (List.replicate n 0) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases hi : i < n
  · have hiw : i < (List.ofFn fun j : Fin n => decide (j = v)).length := by simpa
    have hid : i < ((List.range n).map fun j =>
        if j ∈ ({v.val} : Finset ℕ) then 1 else 0).length := by simpa
    rw [List.getD_eq_getElem _ _ hiw, List.getD_eq_getElem _ _ hid,
      List.getD_replicate _ hi]
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range,
      Finset.mem_singleton]
    by_cases heq : i = v.val
    · simp [heq, Bound]
    · have heq' : (⟨i, hi⟩ : Fin n) ≠ v := fun h => heq (congrArg Fin.val h)
      simp [heq, heq', Bound]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact bound_zero

lemma output_bound (n : ℕ) (C : Circuit) (v : Fin n)
    (hao : PEqualNP.TopForm.IsAO2 n C) :
    Bound (C.eval (List.ofFn fun i : Fin n => decide (i = v)))
      (C.lineDeg n {v.val}) ((andDepths C n).getD C.output 0) := by
  have hs := states_fold C.gates
    (fun g hg => ⟨hao.1 g hg, hao.2.2 g hg⟩) (initial_states n v)
  exact hs.2.2 C.output

end PEqualNP.Outside.L_meta_4926_aux


theorem PEqualNP.Outside.L_meta_4926 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → x2.eval (List.ofFn fun (x5 : Fin x1) => Decidable.decide (x5 = x3)) = Bool.false → (2 : ℕ) ≤ x2.lineDeg x1 {↑x3} → (2 : ℕ) ≤ (PEqualNP.MetaComplexity.SingleLevel.andDepths x2 x1).getD x2.output (0 : ℕ) := by
  intro n C v hao heval hdeg
  have hb := PEqualNP.Outside.L_meta_4926_aux.output_bound n C v hao
  by_contra! hdepth
  have ht := hb.2 (by omega) hdeg
  rw [heval] at ht
  cases ht

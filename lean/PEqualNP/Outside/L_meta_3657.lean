import PEqualNP.Defs

/- The wire-evaluation and strict-cone lemmas below are adapted from the
   checked proof PEqualNP/Outside/L_meta_1906.lean. No outside module is imported. -/
namespace PEqualNP.Outside.L_meta_3657
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)
theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

open PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.EdgeOwnership

private theorem gate_op {n : Nat} {C : Circuit} (ao : IsAO2 n C)
    {j : Nat} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  rw [gateAt_eq C j hj]
  exact ao.1 _ (List.getElem_mem _)

private theorem operand_of_mem {n : Nat} {C : Circuit} (ao : IsAO2 n C)
    {j t : Nat} (hj : j < C.gates.length) (ht : t ∈ (gateAt C j).inputs) :
    ∃ b : Fin 2, opnd C j b = t := by
  have hgate : gateAt C j ∈ C.gates := by
    rw [gateAt_eq C j hj]; exact List.getElem_mem _
  have len : (gateAt C j).inputs.length = 2 := ao.2.2 _ hgate
  obtain ⟨i,hi,e⟩ := List.getElem_of_mem ht
  refine ⟨⟨i,by omega⟩,?_⟩
  simpa [opnd,hi] using e

private theorem cone_target {n : Nat} {C : Circuit} {i j : Nat}
    (h : InCone n C i j) : j < C.gates.length := by
  unfold InCone at h
  have hl : (cones n C).length = C.gates.length := by
    simp [cones,coneFold_length]
  by_contra! he
  rw [List.getD_eq_default _ _ (hl ▸ he)] at h
  exact List.not_mem_nil h

private theorem or_preserves {n : Nat} (C : Circuit) (x : Fin n → Bool)
    {i j : Nat} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hi : i < j) (read : n+i ∈ (gateAt C j).inputs) (ha : gateVal n C i x = true) :
    gateVal n C j x = true := by
  rw [gateAt_eq C j hj] at hop read
  change val C.gates (n+j) x = true
  apply (val_or C.gates x j hj hop).2
  exact ⟨n+i,read,(by omega),ha⟩

private theorem wire_as_gate {n : Nat} (C : Circuit) (i : Nat) (x : Fin n → Bool) :
    Circuit.eval ⟨C.gates,n+i⟩ (List.ofFn x) = gateVal n C i x := rfl

private theorem above_below {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C)
    (live : ∀ k < C.gates.length, InOutputCone n C k) (fixed : IsLiftFixedPoint G C)
    (noAnd : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t ∈ (gateAt C k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates,t⟩ (List.ofFn x) = true →
          graphFun G ∅ x = true))
    (hasTrue : ∀ k < C.gates.length, ∃ x : Fin n → Bool, gateVal n C k x = true)
    {h k : Nat} (hh : h < C.gates.length) (hk : k < C.gates.length)
    (read : n+h ∈ (gateAt C k).inputs) (below : BelowF G C h) :
    (gateAt C k).op = GateOp.or ∧ BelowF G C k := by
  have ho : (gateAt C k).op = GateOp.or := by
    rcases gate_op ao hk with ha | ho
    · exact (noAnd k hk ha (n+h) read (fun x hx => below x (by simpa only [wire_as_gate] using hx))).elim
    · exact ho
  refine ⟨ho,?_⟩
  by_contra hn
  obtain ⟨b,he⟩ := operand_of_mem ao hk read
  apply fixed
  refine ⟨k,hk,b,live k hk,ho,hn,?_⟩
  rw [he]
  exact ⟨below,hasTrue h hh⟩

private theorem below_all_up {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (step : ∀ {h k : Nat}, h < C.gates.length → k < C.gates.length →
      n+h ∈ (gateAt C k).inputs → BelowF G C h →
      (gateAt C k).op = GateOp.or ∧ BelowF G C k)
    {h : Nat} (below : BelowF G C h) :
    ∀ k < C.gates.length, InCone n C h k → (gateAt C k).op = GateOp.or ∧ BelowF G C k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hc
    obtain ⟨w,hw,hn,hl,hh⟩ := (inCone_iff n C h k hk).1 hc
    let j := w-n
    have hj : j < k := by dsimp [j]; omega
    have jr : n+j ∈ (gateAt C k).inputs := by
      have e : n+j=w := by dsimp [j]; omega
      rw [e]; exact hw
    have bj : BelowF G C j := by
      rcases hh with hEq | hStrict
      · change BelowF G C (w-n)
        rwa [←hEq]
      · exact (ih j hj (hj.trans hk) hStrict).2
    exact step (hj.trans hk) hk jr bj

private theorem all_up_true {n : Nat} (C : Circuit) {h : Nat}
    (orOnly : ∀ k < C.gates.length, InCone n C h k → (gateAt C k).op = GateOp.or)
    (x : Fin n → Bool) (yes : gateVal n C h x = true) :
    ∀ k < C.gates.length, InCone n C h k → gateVal n C k x = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hc
    obtain ⟨w,hw,hn,hl,hh⟩ := (inCone_iff n C h k hk).1 hc
    let j := w-n
    have hj : j < k := by dsimp [j]; omega
    have jr : n+j ∈ (gateAt C k).inputs := by
      have e : n+j=w := by dsimp [j]; omega
      rw [e]; exact hw
    have yj : gateVal n C j x = true := by
      rcases hh with eq | strict
      · change gateVal n C (w-n) x = true
        rwa [←eq]
      · exact ih j hj (hj.trans hk) strict
    exact or_preserves C x hk (orOnly k hk hc) hj jr yj

private theorem below_iff_up {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C)
    (computes : circuitFun n C = graphFun G ∅)
    (live : ∀ k < C.gates.length, InOutputCone n C k)
    (fixed : IsLiftFixedPoint G C)
    (noAnd : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t ∈ (gateAt C k).inputs, ¬ (∀ x : Fin n → Bool,
        Circuit.eval ⟨C.gates,t⟩ (List.ofFn x) = true → graphFun G ∅ x = true))
    (hasTrue : ∀ k < C.gates.length, ∃ x : Fin n → Bool, gateVal n C k x = true)
    {h : Nat} (hh : h < C.gates.length) :
    BelowF G C h ↔ ∀ k < C.gates.length, InCone n C h k → (gateAt C k).op = GateOp.or := by
  constructor
  · intro below k hk hc
    exact (below_all_up G C (fun hh hk hr hb =>
      above_below G C ao live fixed noAnd hasTrue hh hk hr hb) below k hk hc).1
  · intro orOnly x yes
    rw [← computes]
    change (C.wires (List.ofFn x)).getD C.output false = true
    rcases (live h hh).2 with out | ⟨hn,strict⟩
    · rw [out]
      exact yes
    · have e : C.output = n+(C.output-n) := by omega
      rw [e]
      exact all_up_true C orOnly x yes _ (cone_target strict) strict

end PEqualNP.Outside.L_meta_3657

theorem PEqualNP.Outside.L_meta_3657 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.Core.IsLiftFixedPoint G C →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) →
  (∀ k < C.gates.length, ∃ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C k x = true) →
  ∀ h < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op = PEqualNP.CircuitLowerBounds.GateOp.and →
    (PEqualNP.TopForm.BelowF G C h ↔ ∀ k < C.gates.length, PEqualNP.EdgeOwnership.InCone n C h k → (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or) := by
  intro n G _ C ao computes live fixed noAnd hasTrue h hh _
  exact PEqualNP.Outside.L_meta_3657.below_iff_up G C ao computes live fixed noAnd hasTrue hh

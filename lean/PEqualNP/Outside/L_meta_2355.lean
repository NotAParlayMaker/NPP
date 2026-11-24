import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2355

open PEqualNP.CircuitLowerBounds

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

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

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

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]


open PEqualNP.MetaComplexity.NestedCover

private theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

private theorem bothInputs {n : ℕ} {C : Circuit} (model : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (ha : val C.gates ((gateAt C j).inputs.getD 0 0) x = true)
    (hb : val C.gates ((gateAt C j).inputs.getD 1 0) x = true) :
    val C.gates (n + j) x = true := by
  apply (val_and C.gates x j hj (by simpa [gateAt_eq C j hj] using hop)).2
  intro i hi
  rw [← gateAt_eq C j hj] at hi
  refine ⟨model.2.1 j hj i hi, ?_⟩
  have len : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq C j hj]
    exact model.2.2 _ (List.getElem_mem hj)
  generalize (gateAt C j).inputs = xs at len hi ha hb
  rcases xs with _ | ⟨a, _ | ⟨b, tail⟩⟩ <;> simp_all
  rcases hi with rfl | rfl <;> assumption

end PEqualNP.Outside.L_meta_2355

open PEqualNP.Outside.L_meta_2355 PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_2355 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (p : Fin N) (l : Fin M) (L : List (ℕ × ℕ)), I p l → ((∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = pw p ∨ gv.2 = lw l) ∧ (L.filter (fun e1 => decide (e1.2 = pw p))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = lw l))).length ∈ ({1, 2} : Finset ℕ)) → ∃ gv ∈ L, gv.2 = pw p ∧ ∀ q : Fin N, R (pw q) gv.1 → I q l := by
  classical
  intro n N M pw lw I C model _ _ _ pointBound lineBound sound R hR T hT p l L _ data
  obtain ⟨⟨j, A, B, hj, hop, root, left, right, hL⟩, types, count, _⟩ := data
  by_contra none
  let pick (e : ℕ × ℕ) : Fin N :=
    if h : ∃ q, R (pw q) e.1 ∧ ¬ I q l then h.choose else p
  let xs := L.filter (fun e => decide (e.2 = pw p))
  have bad (e) (he : e ∈ xs) : R (pw (pick e)) e.1 ∧ ¬ I (pick e) l := by
    obtain ⟨mem, eq⟩ := List.mem_filter.mp he
    have existsBad : ∃ q, R (pw q) e.1 ∧ ¬ I q l := by
      by_contra! good
      exact none ⟨e, mem, of_decide_eq_true eq, good⟩
    simpa [pick, existsBad] using existsBad.choose_spec
  let P := xs.toFinset.image pick
  have size : P.card ≤ 2 := by
    calc
      P.card ≤ xs.toFinset.card := Finset.card_image_le
      _ ≤ xs.length := List.toFinset_card_le _
      _ ≤ 2 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at count
        change (L.filter _).length ≤ 2
        omega
  have off : ∀ q ∈ P, ∀ s ∈ ({l} : Finset (Fin M)), ¬ I q s := by
    intro q hq s hs
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
    obtain rfl := Finset.mem_singleton.mp hs
    exact (bad e (List.mem_toFinset.mp he)).2
  let x (k : Fin n) := decide (k.val ∈ P.image pw ∪ ({l} : Finset (Fin M)).image lw)
  have along {a b} (h : R a b) (v : val C.gates a x = true) : val C.gates b x = true := by
    rw [hR] at h
    induction h with
    | refl => exact v
    | tail path edge ih =>
      obtain ⟨lt, k, rfl, hk, op, mem⟩ := edge
      rw [gateAt_eq C k hk] at op mem
      exact (val_or C.gates x k hk op).2 ⟨_, mem, lt, ih⟩
  have leaf (e) (he : e ∈ L) : val C.gates e.1 x = true ∨ e.2 = lw l := by
    rcases types e he with hp | hl
    · left
      have hex : e ∈ xs := List.mem_filter.mpr ⟨he, decide_eq_true hp⟩
      apply along (bad e hex).1
      rw [val_input _ _ _ (pointBound _)]
      apply decide_eq_true
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem pw
        (Finset.mem_image_of_mem pick (List.mem_toFinset.mpr hex)))
    · exact Or.inr hl
  let Q (t : ℕ) (S : List (ℕ × ℕ)) :=
    (∀ e ∈ S, val C.gates e.1 x = true ∨ e.2 = lw l) → val C.gates t x = true
  have base (v t : ℕ) (hv : v < n) (path : R v t) : Q t [(t, v)] := by
    intro all
    rcases all (t, v) (by simp) with already | hl
    · exact already
    · apply along path
      rw [val_input _ _ _ hv]
      apply decide_eq_true
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l, by simp, hl.symm⟩)
  have node (k t : ℕ) (S U : List (ℕ × ℕ)) (hk : k < C.gates.length)
      (op : (gateAt C k).op = GateOp.and) (path : R (n+k) t)
      (sa : Q ((gateAt C k).inputs.getD 0 0) S)
      (sb : Q ((gateAt C k).inputs.getD 1 0) U) : Q t (S ++ U) := by
    intro all
    exact along path (bothInputs model x k hk op
      (sa fun e he => all e (List.mem_append_left U he))
      (sb fun e he => all e (List.mem_append_right S he)))
  rw [hT] at left right
  have output := node j C.output A B hj hop root (left Q base node) (right Q base node)
  have accepts := output (hL ▸ leaf)
  have rejects := sound P {l} size (by simp) off
  change val C.gates C.output x = false at rejects
  simp [rejects] at accepts

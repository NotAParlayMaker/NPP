import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds
open Classical

-- One gate appended to the wire list, as in Circuit.wires.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem len_fold : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem getD_fold_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (step w g) i (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_fold_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  rw [List.getD_eq_default]
  rw [len_fold]
  exact h

theorem getD_fold_gate : ∀ (gs : List Gate) (w : List Bool) (k : ℕ) (g : Gate), gs[k]? = some g →
    (gs.foldl step w).getD (w.length + k) false =
      g.op.eval (g.inputs.map fun i => ((gs.take k).foldl step w).getD i false) := by
  intro gs
  induction gs with
  | nil => intro w k g h; simp at h
  | cons g0 gs ih =>
    intro w k g h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [List.foldl_cons, getD_fold_lt gs (step w g0) (w.length + 0) (by simp [step])]
      simp [step, List.getD_eq_getElem?_getD]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      have hih := ih (step w g0) k g h
      have hl : (step w g0).length = w.length + 1 := by simp [step]
      rw [hl] at hih
      rw [List.foldl_cons, show w.length + (k + 1) = w.length + 1 + k by omega, hih]
      simp only [List.take_succ_cons, List.foldl_cons]

theorem lt_of_get (l : List Gate) (k : ℕ) (g : Gate) (h : l[k]? = some g) : k < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ j ∈ l, f j = true → f' j = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro hall j hj
    exact h j hj (hall j hj)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    rintro ⟨j, hj, hfj⟩
    exact ⟨j, hj, h j hj hfj⟩


-- The value of wire w of C on input x.
def val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.gates.foldl step (List.ofFn x)).getD w false

-- The input with exactly one true coordinate p.
def unit (n : ℕ) (p : Fin n) : Fin n → Bool := fun b => decide (b = p)

-- The single-index set of a wire: the p at which the wire is true on the unit input p.
noncomputable def T (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => val n C (unit n p) w = true)

-- A private wire for S: its single-index set lies in S and has at least two indices.
def Pw (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  T n C w ⊆ S ∧ 2 ≤ (T n C w).card

-- One step back from a private gate wire to a wire it reads.
def R (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (a b : ℕ) : Prop :=
  Pw n C S a ∧ ∃ (j : ℕ) (g : Gate), a = n + j ∧ C.gates[j]? = some g ∧ b ∈ g.inputs ∧ b < a

noncomputable def reachF (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (o : ℕ) : Finset ℕ :=
  (Finset.range (o + 1)).filter (fun w => Relation.ReflTransGen (R n C S) o w)

noncomputable def Q (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (o : ℕ) : Finset ℕ :=
  (reachF n C S o).filter (fun w => Pw n C S w)

noncomputable def Ex (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (o : ℕ) : Finset ℕ :=
  (reachF n C S o).filter (fun w => ¬ Pw n C S w)

noncomputable def inp (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  match C.gates[a - n]? with
  | some g => g.inputs.toFinset
  | none => ∅

theorem input_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    val n C x w = x ⟨w, h⟩ := by
  unfold val
  rw [getD_fold_lt _ _ _ (by rw [List.length_ofFn]; exact h)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, dite_true, Option.getD_some]

theorem out_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (h : n + C.gates.length ≤ w) :
    val n C x w = false := by
  unfold val
  exact getD_fold_ge _ _ _ (by rw [List.length_ofFn]; exact h)

theorem gate_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) :
    val n C x (n + j) = g.op.eval (g.inputs.map fun b => if b < n + j then val n C x b else false) := by
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hk := lt_of_get C.gates j g hg
  have htake : (C.gates.take j).length = j := by rw [List.length_take]; omega
  unfold val
  rw [show n + j = (List.ofFn x).length + j by rw [hlen], getD_fold_gate _ _ j g hg]
  congr 1
  apply List.map_congr_left
  intro b _
  split_ifs with hb
  · have hlt : b < ((C.gates.take j).foldl step (List.ofFn x)).length := by
      rw [len_fold, htake]; exact hb
    rw [show C.gates.foldl step (List.ofFn x) =
        (C.gates.drop j).foldl step ((C.gates.take j).foldl step (List.ofFn x)) by
      rw [← List.foldl_append, List.take_append_drop]]
    rw [getD_fold_lt (C.gates.drop j) ((C.gates.take j).foldl step (List.ofFn x)) b hlt]
  · exact getD_fold_ge (C.gates.take j) (List.ofFn x) b (by rw [htake]; omega)

theorem mono_all (n : ℕ) (C : Circuit)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ (w : ℕ) (x x' : Fin n → Bool), (∀ q, x q = true → x' q = true) →
      val n C x w = true → val n C x' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro x x' hxx' hv
  by_cases hwn : w < n
  · rw [input_val n C x w hwn] at hv
    rw [input_val n C x' w hwn]
    exact hxx' _ hv
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    rcases hg : C.gates[j]? with _ | g
    · have hk : C.gates.length ≤ j := List.getElem?_eq_none_iff.1 hg
      rw [out_val n C x (n + j) (by omega)] at hv
      exact absurd hv (by simp)
    · have hmem : g ∈ C.gates := List.mem_of_getElem? hg
      rw [gate_val n C x j g hg] at hv
      rw [gate_val n C x' j g hg]
      refine eval_mono g.op (hgates g hmem).1 g.inputs _ _ ?_ hv
      intro b _ hb
      split_ifs at hb ⊢ with hbj
      all_goals first | exact ih b hbj x x' hxx' hb | exact hb

theorem pw_gate (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) (h : Pw n C S w) :
    ∃ (j : ℕ) (g : Gate), w = n + j ∧ C.gates[j]? = some g := by
  by_cases hwn : w < n
  · exfalso
    have hsub : T n C w ⊆ {⟨w, hwn⟩} := by
      intro p hp
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [input_val n C _ w hwn] at hp
      simp only [unit, decide_eq_true_eq] at hp
      rw [Finset.mem_singleton]
      exact hp.symm
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h1
    have h2 := h.2
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    rcases hg : C.gates[j]? with _ | g
    · exfalso
      have hk : C.gates.length ≤ j := List.getElem?_eq_none_iff.1 hg
      have hT : T n C (n + j) = ∅ := by
        ext p
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [out_val n C _ (n + j) (by omega)]
        simp
      have h2 := h.2
      rw [hT] at h2
      simp at h2
    · exact ⟨j, g, rfl, hg⟩

theorem reach_le (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (o w : ℕ)
    (h : Relation.ReflTransGen (R n C S) o w) : w ≤ o := by
  induction h with
  | refl => exact le_refl _
  | tail _ hab ih =>
    unfold R at hab
    obtain ⟨_, j, g, _, _, _, hlt⟩ := hab
    omega

theorem mem_reachF (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (o w : ℕ) :
    w ∈ reachF n C S o ↔ Relation.ReflTransGen (R n C S) o w := by
  unfold reachF
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by have := reach_le n C S o w h; omega, h⟩

-- Comparison through the private closure: if every exit true at y is true at z, so is every
-- wire of the closure, the output among them.
theorem closure_cmp (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (o : ℕ)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (y z : Fin n → Bool)
    (hex : ∀ e, Relation.ReflTransGen (R n C S) o e → ¬ Pw n C S e →
      val n C y e = true → val n C z e = true) :
    ∀ w, Relation.ReflTransGen (R n C S) o w → val n C y w = true → val n C z w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw hv
  by_cases hp : Pw n C S w
  · obtain ⟨j, g, rfl, hg⟩ := pw_gate n C S w hp
    have hmem : g ∈ C.gates := List.mem_of_getElem? hg
    rw [gate_val n C y j g hg] at hv
    rw [gate_val n C z j g hg]
    refine eval_mono g.op (hgates g hmem).1 g.inputs _ _ ?_ hv
    intro b hb hfb
    split_ifs at hfb ⊢ with hbj
    all_goals first
      | exact ih b hbj (hw.tail (show R n C S (n + j) b from ⟨hp, j, g, rfl, hg, hb, hbj⟩)) hfb
      | exact hfb
  · exact hex w hw hp hv

-- At most one more exit than closure gates: every reached wire but the output is read by a
-- closure gate, and each gate reads two wires.
theorem count (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (o : ℕ)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    (Ex n C S o).card ≤ (Q n C S o).card + 1 := by
  have hsub : (reachF n C S o).erase o ⊆ (Q n C S o).biUnion (inp n C) := by
    intro w hw
    rw [Finset.mem_erase] at hw
    obtain ⟨hwo, hwr⟩ := hw
    rw [mem_reachF] at hwr
    rcases Relation.ReflTransGen.cases_tail hwr with h | ⟨a, hra, hab⟩
    · exact absurd h hwo
    · rw [Finset.mem_biUnion]
      have hab' := hab
      unfold R at hab'
      obtain ⟨hpa, j, g, rfl, hg, hb, _⟩ := hab'
      refine ⟨n + j, ?_, ?_⟩
      · unfold Q
        rw [Finset.mem_filter, mem_reachF]
        exact ⟨hra, hpa⟩
      · unfold inp
        rw [show n + j - n = j by omega, hg]
        exact List.mem_toFinset.2 hb
  have h1 := Finset.card_le_card hsub
  have h2 : ((Q n C S o).biUnion (inp n C)).card ≤ ∑ a ∈ Q n C S o, (inp n C a).card :=
    Finset.card_biUnion_le
  have h3 : ∀ a ∈ Q n C S o, (inp n C a).card ≤ 2 := by
    intro a _
    unfold inp
    split
    · next g hg =>
      have hmem : g ∈ C.gates := List.mem_of_getElem? hg
      calc g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le _
        _ = 2 := (hgates g hmem).2
    · simp
  have h4 : ∑ a ∈ Q n C S o, (inp n C a).card ≤ ∑ _a ∈ Q n C S o, 2 := Finset.sum_le_sum h3
  rw [Finset.sum_const, smul_eq_mul] at h4
  have hoR : o ∈ reachF n C S o := (mem_reachF n C S o o).2 Relation.ReflTransGen.refl
  have h5 := Finset.card_erase_of_mem hoR
  have h6 : (Q n C S o).card + (Ex n C S o).card = (reachF n C S o).card :=
    Finset.card_filter_add_card_filter_not _
  have h7 : 1 ≤ (reachF n C S o).card := Finset.card_pos.2 ⟨o, hoR⟩
  omega

-- The leaving exits: exits whose single-index set leaves S.
noncomputable def Lv (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (o : ℕ) : Finset ℕ :=
  (Ex n C S o).filter (fun e => ¬ T n C e ⊆ S)

-- The bound for one output: at least c private gates.
theorem single (n k c : ℕ) (C : Circuit) (S : Finset (Fin n)) (o : ℕ)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hL2 : 2 ≤ (T n C o).card)
    (hprom : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → val n C x o = false)
    (hck : c ≤ k) (hcL : c + 1 ≤ (T n C o).card) : c ≤ (Q n C S o).card := by
  have hcount := count n C S o hgates
  have : Nonempty (Fin n) := ⟨(Finset.card_pos.1 (by omega : 0 < (T n C o).card)).choose⟩
  have hpick : ∀ e ∈ Lv n C S o, ∃ p, p ∈ T n C e ∧ p ∉ S := by
    intro e he
    unfold Lv at he
    rw [Finset.mem_filter] at he
    exact Finset.not_subset.1 he.2
  choose! pk hpk using hpick
  have hLvle : (Lv n C S o).card ≤ (Ex n C S o).card := Finset.card_filter_le _ _
  have hXle : ((Lv n C S o).image pk).card ≤ (Lv n C S o).card := Finset.card_image_le
  have hxsS : ∀ q ∈ S, decide (q ∈ (Lv n C S o).image pk) = false := by
    intro q hq
    simp only [decide_eq_false_iff_not]
    intro hqX
    obtain ⟨e, he, heq⟩ := Finset.mem_image.1 hqX
    exact (hpk e he).2 (heq ▸ hq)
  have hxcard : (Finset.univ.filter (fun q => decide (q ∈ (Lv n C S o).image pk) = true)).card =
      ((Lv n C S o).image pk).card := by
    congr 1
    ext q
    simp
  have hlvtrue : ∀ e ∈ Lv n C S o,
      val n C (fun q => decide (q ∈ (Lv n C S o).image pk)) e = true := by
    intro e he
    have h1 := (hpk e he).1
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    refine mono_all n C hgates e (unit n (pk e)) _ ?_ h1
    intro q hq
    simp only [unit, decide_eq_true_eq] at hq
    subst hq
    simp only [decide_eq_true_eq]
    exact Finset.mem_image_of_mem pk he
  by_cases hval : val n C (fun q => decide (q ∈ (Lv n C S o).image pk)) o = true
  · have hk : k + 1 ≤ ((Lv n C S o).image pk).card := by
      by_contra hcon
      have hf := hprom (fun q => decide (q ∈ (Lv n C S o).image pk)) (by rw [hxcard]; omega) hxsS
      rw [hf] at hval
      exact absurd hval (by simp)
    omega
  · have hval' : val n C (fun q => decide (q ∈ (Lv n C S o).image pk)) o = false := by
      simpa using hval
    have hsmall : ∀ p ∈ T n C o, ∃ e ∈ Ex n C S o, val n C (unit n p) e = true ∧ T n C e ⊆ S := by
      intro p hp
      by_contra hcon
      push Not at hcon
      have hcmp := closure_cmp n C S o hgates (unit n p)
        (fun q => decide (q ∈ (Lv n C S o).image pk)) (by
          intro e he hne hve
          have heEx : e ∈ Ex n C S o := by
            unfold Ex
            rw [Finset.mem_filter, mem_reachF]
            exact ⟨he, hne⟩
          have heLv : e ∈ Lv n C S o := by
            unfold Lv
            exact Finset.mem_filter.2 ⟨heEx, hcon e heEx hve⟩
          exact hlvtrue e heLv) o Relation.ReflTransGen.refl
      have hpo : val n C (unit n p) o = true := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact hp
      have h2 := hcmp hpo
      rw [hval'] at h2
      exact absurd h2 (by simp)
    choose! ex hex using hsmall
    have hinj : Set.InjOn ex (T n C o) := by
      intro p hp p' hp' hpp
      obtain ⟨heEx, hv, hsub⟩ := hex p hp
      obtain ⟨_, hv', _⟩ := hex p' hp'
      have hnP : ¬ Pw n C S (ex p) := by
        unfold Ex at heEx
        exact (Finset.mem_filter.1 heEx).2
      have hle1 : (T n C (ex p)).card ≤ 1 := by
        unfold Pw at hnP
        push Not at hnP
        have := hnP hsub
        omega
      have hpT : p ∈ T n C (ex p) := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hv
      have hp'T : p' ∈ T n C (ex p) := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hpp]
        exact hv'
      exact Finset.card_le_one.1 hle1 p hpT p' hp'T
    have hcardT : (T n C o).card ≤ (Ex n C S o).card :=
      Finset.card_le_card_of_injOn ex (by intro p hp; exact (hex p hp).1) hinj
    omega

end PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_782 in
theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c hS hL2 hgates hLS hprom hck hcL
  have hQ : ∀ i, c i ≤ (Q n C (S i) (o i)).card := fun i =>
    single n k (c i) C (S i) (o i) hgates (hL2 i) (hprom i) (hck i) (hcL i)
  have hQsub : ∀ i, Q n C (S i) (o i) ⊆ Finset.Ico n (n + C.gates.length) := by
    intro i w hw
    unfold Q at hw
    have hp := (Finset.mem_filter.1 hw).2
    obtain ⟨j, g, rfl, hg⟩ := pw_gate n C (S i) w hp
    have := lt_of_get C.gates j g hg
    simp only [Finset.mem_Ico]
    omega
  have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => Q n C (S i) (o i)) := by
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w hwi hwj
    unfold Q at hwi hwj
    have hpi := (Finset.mem_filter.1 hwi).2
    have hpj := (Finset.mem_filter.1 hwj).2
    have hsub : T n C w ⊆ S i ∩ S j := Finset.subset_inter hpi.1 hpj.1
    have h1 := Finset.card_le_card hsub
    have h2 := hS i j hij
    have h3 := hpi.2
    omega
  calc ∑ i, c i ≤ ∑ i, (Q n C (S i) (o i)).card := Finset.sum_le_sum (fun i _ => hQ i)
    _ = (Finset.univ.biUnion (fun i => Q n C (S i) (o i))).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + C.gates.length)).card :=
        Finset.card_le_card (Finset.biUnion_subset.2 (fun i _ => hQsub i))
    _ = C.size := by simp [Circuit.size]

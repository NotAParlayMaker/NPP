import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2838

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

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

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


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

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h
def oh {n : ℕ} (i : Fin n) : Fin n → Bool := fun k => decide (k = i)

def pr {n : ℕ} (i j : Fin n) : Fin n → Bool := fun k => decide (k = i) || decide (k = j)

def inp (C : Circuit) (j k : ℕ) : ℕ := (gateAt C j).inputs.getD k 0

theorem oh_le_pr_left {n : ℕ} (i j : Fin n) : ∀ v, oh i v = true → pr i j v = true := by
  intro v hv
  simp only [oh, pr, Bool.or_eq_true, decide_eq_true_eq] at hv ⊢
  exact Or.inl hv

theorem oh_le_pr_right {n : ℕ} (i j : Fin n) : ∀ v, oh j v = true → pr i j v = true := by
  intro v hv
  simp only [oh, pr, Bool.or_eq_true, decide_eq_true_eq] at hv ⊢
  exact Or.inr hv

theorem cA_ne_nA {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have h1 := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at h1
  have := p.isLt
  omega

theorem cA_inj {N : ℕ} : Function.Injective (Fin.castAdd N : Fin N → Fin (N + N)) := by
  intro a b h
  have h1 := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_castAdd] at h1
  exact Fin.ext h1

theorem nA_inj {N : ℕ} : Function.Injective (Fin.natAdd N : Fin N → Fin (N + N)) := by
  intro a b h
  have h1 := congrArg Fin.val h
  rw [Fin.val_natAdd, Fin.val_natAdd] at h1
  exact Fin.ext (by omega)

-- Part 1: singleton sets of a wire, good wires, and the union bound.

def T (gates : List Gate) {n M : ℕ} (ι : Fin M → Fin n) (w : ℕ) : Finset (Fin M) :=
  Finset.univ.filter (fun x => val gates w (oh (ι x)) = true)

def gOp (gates : List Gate) (k : ℕ) : GateOp := (gates.getD k ⟨GateOp.or, []⟩).op

open Classical in
noncomputable def ORs (gates : List Gate) (n : ℕ) {M : ℕ} (ι : Fin M → Fin n)
    (z0 : Fin n → Bool) (m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun w => n ≤ w ∧ w < n + gates.length ∧
    gOp gates (w - n) = GateOp.or ∧ val gates w z0 = false ∧ 2 ≤ (T gates ι w).card)

theorem mem_ORs (gates : List Gate) (n : ℕ) {M : ℕ} (ι : Fin M → Fin n)
    (z0 : Fin n → Bool) (m w : ℕ) : w ∈ ORs gates n ι z0 m ↔ w < m ∧ (n ≤ w ∧
      w < n + gates.length ∧ gOp gates (w - n) = GateOp.or ∧ val gates w z0 = false ∧
      2 ≤ (T gates ι w).card) := by
  unfold ORs; simp

theorem ORs_mono (gates : List Gate) (n : ℕ) {M : ℕ} (ι : Fin M → Fin n)
    (z0 : Fin n → Bool) (m : ℕ) : ORs gates n ι z0 m ⊆ ORs gates n ι z0 (m + 1) := by
  intro w hw
  rw [mem_ORs] at hw ⊢
  exact ⟨by omega, hw.2⟩

theorem T_input (gates : List Gate) {n M : ℕ} (ι : Fin M → Fin n) (hι : Function.Injective ι)
    (w : ℕ) (hw : w < n) : (T gates ι w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rw [val_input gates _ w hw] at ha hb
  simp only [oh, decide_eq_true_eq] at ha hb
  exact hι (ha.symm.trans hb)

theorem T_big (gates : List Gate) {n M : ℕ} (ι : Fin M → Fin n)
    (w : ℕ) (hw : n + gates.length ≤ w) : T gates ι w = ∅ := by
  ext x
  simp [T, val_big gates _ w hw]

theorem getD_gate (gates : List Gate) (k : ℕ) (hk : k < gates.length) :
    gates.getD k ⟨GateOp.or, []⟩ = gates[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem union_bound (gates : List Gate) (n M : ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (rb : ∀ (k : ℕ) (hk : k < gates.length), ∀ i ∈ gates[k].inputs, i < n + k)
    (ι : Fin M → Fin n) (hι : Function.Injective ι) (z0 : Fin n → Bool) :
    ∀ (m : ℕ) (S : Finset ℕ), (∀ w ∈ S, w < m ∧ val gates w z0 = false) →
      (S.biUnion (T gates ι)).card ≤ S.card + (ORs gates n ι z0 m).card := by
  intro m
  induction m with
  | zero =>
    intro S hS
    have : S = ∅ := by
      ext w
      simp only [Finset.notMem_empty, iff_false]
      intro h
      have := (hS w h).1
      omega
    subst this
    simp
  | succ m ih =>
    intro S hS
    have hsub := Finset.card_le_card (ORs_mono gates n ι z0 m)
    by_cases hm : m ∈ S
    swap
    · have h1 := ih S (fun w hw => ⟨by
          have h2 := (hS w hw).1
          have h3 : w ≠ m := fun e => hm (e ▸ hw)
          omega, (hS w hw).2⟩)
      omega
    · set S' := S.erase m with hS'def
      have hS' : ∀ w ∈ S', w < m ∧ val gates w z0 = false := by
        intro w hw
        rw [Finset.mem_erase] at hw
        exact ⟨by have := (hS w hw.2).1; omega, (hS w hw.2).2⟩
      have hsplit : S.biUnion (T gates ι) = T gates ι m ∪ S'.biUnion (T gates ι) := by
        conv_lhs => rw [← Finset.insert_erase hm]
        rw [Finset.biUnion_insert]
      have hcardS : S.card = S'.card + 1 := (Finset.card_erase_add_one hm).symm
      have hgood : val gates m z0 = false := (hS m hm).2
      have hih := ih S' hS'
      -- the case where wire m holds at most one singleton
      have small : (T gates ι m).card ≤ 1 →
          (S.biUnion (T gates ι)).card ≤ S.card + (ORs gates n ι z0 (m + 1)).card := by
        intro h1
        rw [hsplit]
        have := Finset.card_union_le (T gates ι m) (S'.biUnion (T gates ι))
        omega
      by_cases hin : m < n
      · exact small (T_input gates ι hι m hin)
      by_cases hbig : n + gates.length ≤ m
      · exact small (by rw [T_big gates ι m hbig]; simp)
      have hk : m - n < gates.length := by omega
      have hme : n + (m - n) = m := by omega
      have hgm : gates[m - n] ∈ gates := List.getElem_mem hk
      rcases (legal _ hgm).1 with hand | hor
      · -- an AND gate: one operand is good and holds every singleton of the gate
        have hv : val gates (n + (m - n)) z0 = false := by rw [hme]; exact hgood
        have hex : ∃ i ∈ gates[m - n].inputs, val gates i z0 = false := by
          by_contra hno
          push Not at hno
          have : val gates (n + (m - n)) z0 = true := by
            rw [val_and gates z0 (m - n) hk hand]
            intro i hi
            exact ⟨rb (m - n) hk i hi, by
              have := hno i hi
              cases h : val gates i z0
              · exact absurd h this
              · rfl⟩
          rw [this] at hv
          exact Bool.noConfusion hv
        obtain ⟨i, hi, hig⟩ := hex
        have hilt : i < m := by have := rb (m - n) hk i hi; omega
        have hTi : T gates ι m ⊆ T gates ι i := by
          intro x hx
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          rw [← hme] at hx
          exact ((val_and gates _ (m - n) hk hand).1 hx i hi).2
        set S'' := insert i S' with hS''def
        have hS'' : ∀ w ∈ S'', w < m ∧ val gates w z0 = false := by
          intro w hw
          rw [Finset.mem_insert] at hw
          rcases hw with rfl | hw
          · exact ⟨hilt, hig⟩
          · exact hS' w hw
        have hcov : S.biUnion (T gates ι) ⊆ S''.biUnion (T gates ι) := by
          rw [hsplit, hS''def, Finset.biUnion_insert]
          exact Finset.union_subset_union hTi (le_refl _)
        have h1 := Finset.card_le_card hcov
        have h2 := ih S'' hS''
        have h3 : S''.card ≤ S'.card + 1 := Finset.card_insert_le _ _
        omega
      · by_cases h2 : 2 ≤ (T gates ι m).card
        swap
        · exact small (by omega)
        -- an OR gate with at least two singletons: every operand is good
        have hall : ∀ i ∈ gates[m - n].inputs, val gates i z0 = false := by
          intro i hi
          have hilt := rb (m - n) hk i hi
          cases h : val gates i z0
          · rfl
          · have : val gates (n + (m - n)) z0 = true :=
              (val_or gates z0 (m - n) hk hor).2 ⟨i, hi, hilt, h⟩
            rw [hme, hgood] at this
            exact Bool.noConfusion this
        set S'' := S' ∪ gates[m - n].inputs.toFinset with hS''def
        have hS'' : ∀ w ∈ S'', w < m ∧ val gates w z0 = false := by
          intro w hw
          rw [Finset.mem_union, List.mem_toFinset] at hw
          rcases hw with hw | hw
          · exact hS' w hw
          · exact ⟨by have := rb (m - n) hk w hw; omega, hall w hw⟩
        have hTm : T gates ι m ⊆ gates[m - n].inputs.toFinset.biUnion (T gates ι) := by
          intro x hx
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          rw [← hme] at hx
          obtain ⟨i, hi, _, hv⟩ := (val_or gates _ (m - n) hk hor).1 hx
          rw [Finset.mem_biUnion]
          exact ⟨i, List.mem_toFinset.2 hi, by simp [T, hv]⟩
        have hcov : S.biUnion (T gates ι) ⊆ S''.biUnion (T gates ι) := by
          rw [hsplit]
          intro x hx
          rw [Finset.mem_union] at hx
          rw [Finset.mem_biUnion]
          rcases hx with hx | hx
          · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 (hTm hx)
            exact ⟨i, Finset.mem_union_right _ hi, hxi⟩
          · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
            exact ⟨i, Finset.mem_union_left _ hi, hxi⟩
        have h1 := Finset.card_le_card hcov
        have h3 := ih S'' hS''
        have h4 : S''.card ≤ S'.card + 2 := by
          rw [hS''def]
          have := Finset.card_union_le S' gates[m - n].inputs.toFinset
          have := List.toFinset_card_le gates[m - n].inputs
          have := (legal _ hgm).2
          omega
        have hmem : m ∈ ORs gates n ι z0 (m + 1) := by
          rw [mem_ORs]
          refine ⟨by omega, by omega, by omega, ?_, hgood, h2⟩
          rw [gOp, getD_gate gates _ hk]; exact hor
        have hnot : m ∉ ORs gates n ι z0 m := by
          rw [mem_ORs]; omega
        have h5 : (ORs gates n ι z0 m).card + 1 ≤ (ORs gates n ι z0 (m + 1)).card := by
          have hss : insert m (ORs gates n ι z0 m) ⊆ ORs gates n ι z0 (m + 1) :=
            Finset.insert_subset hmem (ORs_mono gates n ι z0 m)
          have := Finset.card_le_card hss
          rw [Finset.card_insert_of_notMem hnot] at this
          exact this
        omega

-- Part 2: one side at a time. Owners y, elements x, a forbidden input per owner.

open Classical in
noncomputable def z0 {N : ℕ} (ιX ιY : Fin N → Fin (N + N)) (J : Fin N → Fin N → Prop)
    (y : Fin N) : Fin (N + N) → Bool :=
  fun k => decide (k = ιY y) || decide (∃ x, k = ιX x ∧ ¬ J x y)

theorem good_sub (gates : List Gate) {N : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ιX ιY : Fin N → Fin (N + N)) (J : Fin N → Fin N → Prop) (y : Fin N) (w : ℕ)
    (hw : val gates w (z0 ιX ιY J y) = false) (x : Fin N) (hx : x ∈ T gates ιX w) : J x y := by
  by_contra hJ
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  have := val_mono gates legal (oh (ιX x)) (z0 ιX ιY J y) (by
    intro v hv
    simp only [oh, decide_eq_true_eq] at hv
    subst hv
    simp only [z0, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨x, rfl, hJ⟩) w hx
  rw [hw] at this
  exact Bool.noConfusion this

theorem world (gates : List Gate) (N : ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (rb : ∀ (k : ℕ) (hk : k < gates.length), ∀ i ∈ gates[k].inputs, i < N + N + k)
    (ιX ιY : Fin N → Fin (N + N)) (hιX : Function.Injective ιX) (J : Fin N → Fin N → Prop)
    (norect : ∀ x x' y y', x ≠ x' → y ≠ y' → ¬ (J x y ∧ J x' y ∧ J x y' ∧ J x' y'))
    (Q : Finset (Fin N × ℕ × ℕ))
    (hQ : ∀ t ∈ Q, t.2.1 < gates.length ∧ gOp gates t.2.1 = GateOp.and ∧
      t.2.2 < N + N + gates.length ∧ val gates t.2.2 (z0 ιX ιY J t.1) = false)
    (hinj : Set.InjOn (fun t : Fin N × ℕ × ℕ => t.2.1) Q) :
    (Q.biUnion (fun t => ({t.1} : Finset (Fin N)) ×ˢ T gates ιX t.2.2)).card
      ≤ gates.length := by
  classical
  let Qy : Fin N → Finset ℕ := fun y => (Q.filter (fun t => t.1 = y)).image (fun t => t.2.2)
  let O : Fin N → Finset ℕ := fun y => ORs gates (N + N) ιX (z0 ιX ιY J y) (N + N + gates.length)
  have hcov : Q.biUnion (fun t => ({t.1} : Finset (Fin N)) ×ˢ T gates ιX t.2.2) ⊆
      Finset.univ.biUnion (fun y => ({y} : Finset (Fin N)) ×ˢ (Qy y).biUnion (T gates ιX)) := by
    intro e he
    simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_singleton] at he
    obtain ⟨t, ht, he1, he2⟩ := he
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    refine ⟨t.1, he1, t.2.2, ?_, he2⟩
    simp only [Qy, Finset.mem_image, Finset.mem_filter]
    exact ⟨t, ⟨ht, rfl⟩, rfl⟩
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin N)))
    (t := fun y => ({y} : Finset (Fin N)) ×ˢ (Qy y).biUnion (T gates ιX))
  have h3 : ∀ y, (({y} : Finset (Fin N)) ×ˢ (Qy y).biUnion (T gates ιX)).card
      ≤ (Qy y).card + (O y).card := by
    intro y
    rw [Finset.card_product, Finset.card_singleton, one_mul]
    apply union_bound gates (N + N) N legal rb ιX hιX
    intro w hw
    simp only [Qy, Finset.mem_image, Finset.mem_filter] at hw
    obtain ⟨t, ⟨ht, hty⟩, rfl⟩ := hw
    subst hty
    exact ⟨(hQ t ht).2.2.1, (hQ t ht).2.2.2⟩
  have h4 : ∑ y, (Qy y).card ≤ Q.card := by
    calc ∑ y, (Qy y).card ≤ ∑ y, (Q.filter (fun t => t.1 = y)).card :=
          Finset.sum_le_sum (fun y _ => Finset.card_image_le)
      _ = Q.card := (Finset.card_eq_sum_card_fiberwise (fun t _ => Finset.mem_univ t.1)).symm
  have hdisj : ((Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint O := by
    intro y _ y' _ hyy'
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    simp only [O] at hw hw'
    rw [mem_ORs] at hw hw'
    obtain ⟨x, hx, x', hx', hxx'⟩ : ∃ x ∈ T gates ιX w, ∃ x' ∈ T gates ιX w, x ≠ x' :=
      Finset.one_lt_card.1 (by omega)
    exact norect x x' y y' hxx' hyy'
      ⟨good_sub gates legal ιX ιY J y w hw.2.2.2.2.1 x hx,
       good_sub gates legal ιX ιY J y w hw.2.2.2.2.1 x' hx',
       good_sub gates legal ιX ιY J y' w hw'.2.2.2.2.1 x hx,
       good_sub gates legal ιX ιY J y' w hw'.2.2.2.2.1 x' hx'⟩
  set U := Finset.univ.biUnion O with hUdef
  have h5 : ∑ y, (O y).card = U.card := (Finset.card_biUnion hdisj).symm
  have hmemU : ∀ w ∈ U, N + N ≤ w ∧ w < N + N + gates.length ∧
      gOp gates (w - (N + N)) = GateOp.or := by
    intro w hw
    rw [hUdef, Finset.mem_biUnion] at hw
    obtain ⟨y, _, hy⟩ := hw
    simp only [O] at hy
    rw [mem_ORs] at hy
    exact ⟨hy.2.1, hy.2.2.1, hy.2.2.2.1⟩
  have hA : (Q.image (fun t => t.2.1)).card = Q.card := Finset.card_image_of_injOn hinj
  have hB : (U.image (fun w => w - (N + N))).card = U.card := by
    apply Finset.card_image_of_injOn
    intro w hw w' hw' he
    have := (hmemU w hw).1
    have := (hmemU w' hw').1
    simp only at he
    omega
  let FA := (Finset.range gates.length).filter (fun k => gOp gates k = GateOp.and)
  let FB := (Finset.range gates.length).filter (fun k => gOp gates k = GateOp.or)
  have hAsub : Q.image (fun t => t.2.1) ⊆ FA := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨t, ht, rfl⟩ := hk
    simp only [FA, Finset.mem_filter, Finset.mem_range]
    exact ⟨(hQ t ht).1, (hQ t ht).2.1⟩
  have hBsub : U.image (fun w => w - (N + N)) ⊆ FB := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨w, hw, rfl⟩ := hk
    obtain ⟨h1, h2, h3⟩ := hmemU w hw
    simp only [FB, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h3⟩
  have hinter : FA ∩ FB = ∅ := by
    ext k
    simp only [FA, FB, Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    rw [h1] at h2
    exact GateOp.noConfusion h2
  have hunion : FA ∪ FB ⊆ Finset.range gates.length := by
    intro k hk
    rw [Finset.mem_union] at hk
    rcases hk with hk | hk <;> exact (Finset.mem_filter.1 hk).1
  have h6 := Finset.card_union_add_card_inter FA FB
  rw [hinter, Finset.card_empty, add_zero] at h6
  have h7 := Finset.card_le_card hunion
  rw [Finset.card_range] at h7
  have h8 := Finset.card_le_card hAsub
  have h9 := Finset.card_le_card hBsub
  have h10 : ∑ y, ((Qy y).card + (O y).card) ≤ Q.card + U.card := by
    rw [Finset.sum_add_distrib]; omega
  have h11 := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Fin N))) => h3 y)
  omega

-- Part 3: facts about one witness gate, then the count.

def Sub (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (j : ℕ) : Prop :=
  ∀ z : Fin (N + N) → Bool, val C.gates (N + N + j) z = true →
    ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true

theorem rb_of (C : Circuit) (n : ℕ) (hrb : ReadsBack n C) :
    ∀ (k : ℕ) (hk : k < C.gates.length), ∀ i ∈ C.gates[k].inputs, i < n + k := by
  intro k hk i hi
  exact hrb k hk i (by rw [gateAt_eq C k hk]; exact hi)

theorem gate_true (C : Circuit) (N : ℕ) (hrb : ReadsBack (N + N) C) (j : ℕ)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (a c : ℕ)
    (hin : (gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a])
    (z : Fin (N + N) → Bool) (ha : val C.gates a z = true) (hc : val C.gates c z = true) :
    val C.gates (N + N + j) z = true := by
  have hg : gateAt C j = C.gates[j] := gateAt_eq C j hj
  rw [hg] at hand hin
  rw [val_and C.gates z j hj hand]
  intro i hi
  refine ⟨rb_of C (N + N) hrb j hj i hi, ?_⟩
  rcases hin with h | h <;> rw [h] at hi <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl <;> assumption

theorem pair_inc (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C) (j : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (a c : ℕ)
    (hin : (gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a])
    (hsub : Sub C N I j) (p l : Fin N)
    (ha : val C.gates a (oh (Fin.castAdd N p)) = true)
    (hc : val C.gates c (oh (Fin.natAdd N l)) = true) : I p l := by
  have legal := legal_of C hm
  have hz := gate_true C N hrb j hj hand a c hin (pr (Fin.castAdd N p) (Fin.natAdd N l))
    (val_mono _ legal _ _ (oh_le_pr_left _ _) a ha)
    (val_mono _ legal _ _ (oh_le_pr_right _ _) c hc)
  obtain ⟨p0, l0, hI, hp0, hl0⟩ := hsub _ hz
  simp only [pr, Bool.or_eq_true, decide_eq_true_eq] at hp0 hl0
  rcases hp0 with h | h
  · rcases hl0 with h' | h'
    · exact absurd h'.symm (cA_ne_nA _ _)
    · rw [cA_inj h, nA_inj h'] at hI
      exact hI
  · exact absurd h (cA_ne_nA _ _)

theorem excl_pts (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C) (j : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (a c : ℕ)
    (hin : (gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a])
    (hsub : Sub C N I j) (p p' : Fin N)
    (ha : val C.gates a (oh (Fin.castAdd N p)) = true)
    (hc : val C.gates c (oh (Fin.castAdd N p')) = true) : False := by
  have legal := legal_of C hm
  have hz := gate_true C N hrb j hj hand a c hin (pr (Fin.castAdd N p) (Fin.castAdd N p'))
    (val_mono _ legal _ _ (oh_le_pr_left _ _) a ha)
    (val_mono _ legal _ _ (oh_le_pr_right _ _) c hc)
  obtain ⟨p0, l0, _, _, hl0⟩ := hsub _ hz
  simp only [pr, Bool.or_eq_true, decide_eq_true_eq] at hl0
  rcases hl0 with h | h
  · exact cA_ne_nA _ _ h.symm
  · exact cA_ne_nA _ _ h.symm

theorem excl_lns (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C) (j : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (a c : ℕ)
    (hin : (gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a])
    (hsub : Sub C N I j) (l l' : Fin N)
    (ha : val C.gates a (oh (Fin.natAdd N l)) = true)
    (hc : val C.gates c (oh (Fin.natAdd N l')) = true) : False := by
  have legal := legal_of C hm
  have hz := gate_true C N hrb j hj hand a c hin (pr (Fin.natAdd N l) (Fin.natAdd N l'))
    (val_mono _ legal _ _ (oh_le_pr_left _ _) a ha)
    (val_mono _ legal _ _ (oh_le_pr_right _ _) c hc)
  obtain ⟨p0, l0, _, hp0, _⟩ := hsub _ hz
  simp only [pr, Bool.or_eq_true, decide_eq_true_eq] at hp0
  rcases hp0 with h | h
  · exact cA_ne_nA _ _ h
  · exact cA_ne_nA _ _ h

theorem good_A (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C) (j : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (a c : ℕ)
    (hin : (gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a])
    (hsub : Sub C N I j) (p : Fin N)
    (ha : val C.gates a (oh (Fin.castAdd N p)) = true) :
    val C.gates c (z0 (Fin.natAdd N) (Fin.castAdd N) (fun l p => I p l) p) = false := by
  have legal := legal_of C hm
  cases hcz : val C.gates c (z0 (Fin.natAdd N) (Fin.castAdd N) (fun l p => I p l) p)
  · rfl
  exfalso
  have haz := val_mono _ legal (oh (Fin.castAdd N p))
    (z0 (Fin.natAdd N) (Fin.castAdd N) (fun l p => I p l) p) (by
      intro v hv
      simp only [oh, decide_eq_true_eq] at hv
      simp [z0, hv]) a ha
  obtain ⟨p0, l0, hI, hp0, hl0⟩ := hsub _ (gate_true C N hrb j hj hand a c hin _ haz hcz)
  simp only [z0, Bool.or_eq_true, decide_eq_true_eq] at hp0 hl0
  rcases hp0 with h | ⟨x, hx, _⟩
  · rw [cA_inj h] at hI
    rcases hl0 with h' | ⟨x', hx', hnx'⟩
    · exact cA_ne_nA _ _ h'.symm
    · rw [nA_inj hx'] at hI
      exact hnx' hI
  · exact cA_ne_nA _ _ hx

theorem good_B (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C) (j : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (a c : ℕ)
    (hin : (gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a])
    (hsub : Sub C N I j) (l : Fin N)
    (hc : val C.gates c (oh (Fin.natAdd N l)) = true) :
    val C.gates a (z0 (Fin.castAdd N) (Fin.natAdd N) (fun p l => I p l) l) = false := by
  have legal := legal_of C hm
  cases haz : val C.gates a (z0 (Fin.castAdd N) (Fin.natAdd N) (fun p l => I p l) l)
  · rfl
  exfalso
  have hcz := val_mono _ legal (oh (Fin.natAdd N l))
    (z0 (Fin.castAdd N) (Fin.natAdd N) (fun p l => I p l) l) (by
      intro v hv
      simp only [oh, decide_eq_true_eq] at hv
      simp [z0, hv]) c hc
  obtain ⟨p0, l0, hI, hp0, hl0⟩ := hsub _ (gate_true C N hrb j hj hand a c hin _ haz hcz)
  simp only [z0, Bool.or_eq_true, decide_eq_true_eq] at hp0 hl0
  rcases hl0 with h | ⟨x, hx, _⟩
  · rw [nA_inj h] at hI
    rcases hp0 with h' | ⟨x', hx', hnx'⟩
    · exact cA_ne_nA _ _ h'
    · rw [cA_inj hx'] at hI
      exact hnx' hI
  · exact cA_ne_nA _ _ hx.symm

theorem list_cases (L : List ℕ) (a c a' c' : ℕ) (h : L = [a, c] ∨ L = [c, a])
    (h' : L = [a', c'] ∨ L = [c', a']) :
    (a = a' ∧ c = c') ∨ (a = c' ∧ c = a') := by
  rcases h with rfl | rfl <;> rcases h' with h' | h' <;>
    simp only [List.cons.injEq, and_true] at h' <;> omega

-- Part 4: every counted pair lies on the point side or on the line side.

theorem main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hm : Monotone2 C) (hrb : ReadsBack (N + N) C) :
    {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ,
      (gateAt C j).op = GateOp.and ∧
      ((gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a]) ∧
      Sub C N I j ∧
      val C.gates a (oh (Fin.castAdd N e.1)) = true ∧
      val C.gates c (oh (Fin.natAdd N e.2)) = true}.ncard ≤ 2 * C.gates.length := by
  classical
  have legal := legal_of C hm
  have rb := rb_of C (N + N) hrb
  set len := C.gates.length with hlen
  let PA : Fin N × ℕ × ℕ → Prop := fun t => ∃ a, (gateAt C t.2.1).op = GateOp.and ∧
    ((gateAt C t.2.1).inputs = [a, t.2.2] ∨ (gateAt C t.2.1).inputs = [t.2.2, a]) ∧
    Sub C N I t.2.1 ∧ val C.gates a (oh (Fin.castAdd N t.1)) = true ∧
    ∀ p', val C.gates a (oh (Fin.castAdd N p')) = true → p' = t.1
  let PB : Fin N × ℕ × ℕ → Prop := fun t => ∃ c, (gateAt C t.2.1).op = GateOp.and ∧
    ((gateAt C t.2.1).inputs = [t.2.2, c] ∨ (gateAt C t.2.1).inputs = [c, t.2.2]) ∧
    Sub C N I t.2.1 ∧ val C.gates c (oh (Fin.natAdd N t.1)) = true ∧
    ∀ l', val C.gates c (oh (Fin.natAdd N l')) = true → l' = t.1
  let box : Finset (Fin N × ℕ × ℕ) :=
    (Finset.univ : Finset (Fin N)) ×ˢ (Finset.range len ×ˢ Finset.range (N + N + len))
  let QA := box.filter PA
  let QB := box.filter PB
  have mem_box : ∀ t : Fin N × ℕ × ℕ, t ∈ box ↔ t.2.1 < len ∧ t.2.2 < N + N + len := by
    intro t
    simp [box]
  have hgop : ∀ j, gOp C.gates j = (gateAt C j).op := fun j => rfl
  -- the point side
  have hA := world C.gates N legal rb (Fin.natAdd N) (Fin.castAdd N) nA_inj
    (fun l p => I p l)
    (by
      intro x x' y y' hxx' hyy' ⟨h1, h2, h3, h4⟩
      obtain ⟨l0, _, hl0⟩ := hU y y' hyy'
      exact hxx' ((hl0 x ⟨h1, h3⟩).trans (hl0 x' ⟨h2, h4⟩).symm))
    QA
    (by
      intro t ht
      obtain ⟨hbox, a, hand, hin, hsub, ha, _⟩ := Finset.mem_filter.1 ht
      obtain ⟨hj, hc⟩ := (mem_box t).1 hbox
      exact ⟨hj, by rw [hgop]; exact hand, hc,
        good_A C N I hm hrb t.2.1 hj hand a t.2.2 hin hsub t.1 ha⟩)
    (by
      intro t ht t' ht' he
      obtain ⟨hbox, a, hand, hin, hsub, ha, hsing⟩ := Finset.mem_filter.1 ht
      obtain ⟨_, a', _, hin', _, ha', hsing'⟩ := Finset.mem_filter.1 ht'
      have hj := ((mem_box t).1 hbox).1
      simp only at he
      rw [← he] at hin'
      rcases list_cases _ a t.2.2 a' t'.2.2 hin hin' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1
        have hp := hsing _ ha'
        exact Prod.ext hp.symm (Prod.ext he h2)
      · subst h2
        exact (excl_pts C N I hm hrb t.2.1 hj hand a _ hin hsub t.1 t'.1 ha ha').elim)
  -- the line side
  have hB := world C.gates N legal rb (Fin.castAdd N) (Fin.natAdd N) cA_inj
    (fun p l => I p l)
    (by
      intro x x' y y' hxx' hyy' ⟨h1, h2, h3, h4⟩
      obtain ⟨l0, _, hl0⟩ := hU x x' hxx'
      exact hyy' ((hl0 y ⟨h1, h2⟩).trans (hl0 y' ⟨h3, h4⟩).symm))
    QB
    (by
      intro t ht
      obtain ⟨hbox, c, hand, hin, hsub, hc, _⟩ := Finset.mem_filter.1 ht
      obtain ⟨hj, ha⟩ := (mem_box t).1 hbox
      exact ⟨hj, by rw [hgop]; exact hand, ha,
        good_B C N I hm hrb t.2.1 hj hand t.2.2 c hin hsub t.1 hc⟩)
    (by
      intro t ht t' ht' he
      obtain ⟨hbox, c, hand, hin, hsub, hc, hsing⟩ := Finset.mem_filter.1 ht
      obtain ⟨_, c', _, hin', _, hc', hsing'⟩ := Finset.mem_filter.1 ht'
      have hj := ((mem_box t).1 hbox).1
      simp only at he
      rw [← he] at hin'
      rcases list_cases _ t.2.2 c t'.2.2 c' hin hin' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h2
        have hl := hsing _ hc'
        exact Prod.ext hl.symm (Prod.ext he h1)
      · exact (excl_lns C N I hm hrb t.2.1 hj hand c t.2.2 (by
          rcases hin with h | h
          · exact Or.inr h
          · exact Or.inl h) hsub t.1 t'.1 hc (by rw [h1]; exact hc')).elim)
  -- every counted pair is covered
  set EA := QA.biUnion (fun t => ({t.1} : Finset (Fin N)) ×ˢ T C.gates (Fin.natAdd N) t.2.2)
  set EB := QB.biUnion (fun t => ({t.1} : Finset (Fin N)) ×ˢ T C.gates (Fin.castAdd N) t.2.2)
  have hcov : {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ,
      (gateAt C j).op = GateOp.and ∧
      ((gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a]) ∧
      Sub C N I j ∧
      val C.gates a (oh (Fin.castAdd N e.1)) = true ∧
      val C.gates c (oh (Fin.natAdd N e.2)) = true} ⊆ ↑(EA ∪ EB.image Prod.swap) := by
    rintro ⟨p, l⟩ ⟨hI, j, hj, a, c, hand, hin, hsub, ha, hc⟩
    have hcl : c < N + N + len := by
      have : c ∈ (gateAt C j).inputs := by
        rcases hin with h | h <;> rw [h] <;> simp
      have := hrb j hj c this
      omega
    have hal : a < N + N + len := by
      have : a ∈ (gateAt C j).inputs := by
        rcases hin with h | h <;> rw [h] <;> simp
      have := hrb j hj a this
      omega
    rw [Finset.coe_union, Set.mem_union]
    by_cases hs : ∀ p', val C.gates a (oh (Fin.castAdd N p')) = true → p' = p
    · left
      rw [Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨(p, j, c), ?_, ?_⟩
      · rw [Finset.mem_filter, mem_box]
        exact ⟨⟨hj, hcl⟩, a, hand, hin, hsub, ha, hs⟩
      · rw [Finset.mem_product, Finset.mem_singleton]
        refine ⟨rfl, ?_⟩
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hc
    · right
      push Not at hs
      obtain ⟨p', hp', hpp'⟩ := hs
      have hsl : ∀ l', val C.gates c (oh (Fin.natAdd N l')) = true → l' = l := by
        intro l' hl'
        by_contra hne
        have i1 := pair_inc C N I hm hrb j hj hand a c hin hsub p l' ha hl'
        have i2 := pair_inc C N I hm hrb j hj hand a c hin hsub p' l hp' hc
        have i3 := pair_inc C N I hm hrb j hj hand a c hin hsub p' l' hp' hl'
        obtain ⟨l0, _, hl0⟩ := hU p p' (Ne.symm hpp')
        exact hne ((hl0 l' ⟨i1, i3⟩).trans (hl0 l ⟨hI, i2⟩).symm)
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨(l, p), ?_, rfl⟩
      rw [Finset.mem_biUnion]
      refine ⟨(l, j, a), ?_, ?_⟩
      · rw [Finset.mem_filter, mem_box]
        exact ⟨⟨hj, hal⟩, c, hand, hin, hsub, hc, hsl⟩
      · rw [Finset.mem_product, Finset.mem_singleton]
        refine ⟨rfl, ?_⟩
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ha
  calc _ ≤ (EA ∪ EB.image Prod.swap).card := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hcov (Finset.finite_toSet _)
    _ ≤ EA.card + (EB.image Prod.swap).card := Finset.card_union_le _ _
    _ ≤ EA.card + EB.card := by
        have := Finset.card_image_le (s := EB) (f := Prod.swap)
        omega
    _ ≤ 2 * len := by omega

end PEqualNP.Outside.L_meta_2838

theorem PEqualNP.Outside.L_meta_2838 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, a]) ∧ (∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true) ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N e.1)))).getD a false = true ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N e.2)))).getD c false = true}.ncard ≤ 3 * C.size + 2 * N := by
  intro q N I _ C _ _ _ hU hm hrb _ _
  have h := PEqualNP.Outside.L_meta_2838.main q N I C hU hm hrb
  have hs : C.size = C.gates.length := rfl
  calc _ ≤ 2 * C.gates.length := h
    _ ≤ 3 * C.size + 2 * N := by omega

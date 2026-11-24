import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2234_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

theorem multi_exit_bound {β : Type*} [DecidableEq β]
    (Q R : Finset β) (inputs : β → Finset β)
    (fanin : ∀ j ∈ Q, (inputs j).card ≤ 2)
    (parent : ∀ j ∈ Q, j ∉ R → ∃ a ∈ Q, j ∈ inputs a) :
    (((Q.biUnion inputs) ∪ R) \ Q).card ≤ Q.card + R.card := by
  classical
  let T := (Q.biUnion inputs) ∪ R
  have hQ : Q ⊆ T := by
    intro j hj
    by_cases hr : j ∈ R
    · exact Finset.mem_union_right _ hr
    · obtain ⟨a, ha, hja⟩ := parent j hj hr
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨a, ha, hja⟩)
  have hT : T.card ≤ 2 * Q.card + R.card := by
    calc
      T.card ≤ (Q.biUnion inputs).card + R.card := Finset.card_union_le _ _
      _ ≤ (∑ j ∈ Q, (inputs j).card) + R.card := Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ (∑ j ∈ Q, 2) + R.card := Nat.add_le_add_right (Finset.sum_le_sum fanin) _
      _ = 2 * Q.card + R.card := by simp [Nat.mul_comm]
  have he := Finset.card_sdiff_add_card_eq_card hQ
  change (T \ Q).card ≤ Q.card + R.card
  omega

theorem roots_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Q R : Finset β) (inputs : β → Finset β) (sets : β → Finset α) (rank : β → ℕ)
    (fanin : ∀ j ∈ Q, (inputs j).card ≤ 2)
    (parent : ∀ j ∈ Q, j ∉ R → ∃ a ∈ Q, j ∈ inputs a)
    (decrease : ∀ j ∈ Q, ∀ v ∈ inputs j, rank v < rank j)
    (step : ∀ j ∈ Q, sets j ⊆ (inputs j).biUnion sets)
    (small : ∀ v ∈ ((Q.biUnion inputs) ∪ R) \ Q, (sets v).card ≤ 1) :
    (R.biUnion sets).card ≤ Q.card + R.card := by
  classical
  let T := (Q.biUnion inputs) ∪ R
  let B := T \ Q
  have cover : ∀ m, ∀ j, rank j = m → j ∈ T → sets j ⊆ B.biUnion sets := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro j he hj u hu
      by_cases hQ : j ∈ Q
      · obtain ⟨v, hv, huv⟩ := Finset.mem_biUnion.mp (step j hQ hu)
        exact ih (rank v) (by rw [← he]; exact decrease j hQ v hv) v rfl
          (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, hQ, hv⟩)) huv
      · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_sdiff.mpr ⟨hj, hQ⟩, hu⟩
  have hsub : R.biUnion sets ⊆ B.biUnion sets := by
    intro u hu
    obtain ⟨r, hr, hur⟩ := Finset.mem_biUnion.mp hu
    exact cover (rank r) r rfl (Finset.mem_union_right _ hr) hur
  calc
    (R.biUnion sets).card ≤ (B.biUnion sets).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ B, (sets v).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ B, 1 := Finset.sum_le_sum small
    _ = B.card := by simp
    _ ≤ Q.card + R.card := multi_exit_bound Q R inputs fanin parent


open PEqualNP.TopForm

theorem shadow_mono {n : ℕ} {C : Circuit} {w v : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w v) : orIn n C v ⊆ orIn n C w := by
  intro u hu
  exact reach_mem_orIn u (h.trans (mem_orIn_reach u hu))

theorem large_or {n : ℕ} {C : Circuit} {w : ℕ}
    (hl : 2 ≤ (orIn n C w).card) :
    ∃ i, i < C.gates.length ∧ w = n+i ∧ (gateAt C i).op = GateOp.or := by
  classical
  have hex : ∃ u ∈ orIn n C w, (u : ℕ) ≠ w := by
    by_contra hn
    have hall : ∀ u ∈ orIn n C w, (u : ℕ) = w := by
      intro u hu
      by_contra he
      exact hn ⟨u, hu, he⟩
    have hc : (orIn n C w).card ≤ 1 := Finset.card_le_one.mpr (by
      intro a ha b hb
      exact Fin.ext ((hall a ha).trans (hall b hb).symm))
    omega
  obtain ⟨u, hu, hne⟩ := hex
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨v, hs, _⟩
  · exact (hne he.symm).elim
  · obtain ⟨i, hi, he, hop, _, _⟩ := hs
    exact ⟨i, hi, he, hop⟩

theorem shadow_step {n : ℕ} {C : Circuit} {i : ℕ}
    (hi : i < C.gates.length) (hop : (gateAt C i).op = GateOp.or) :
    orIn n C (n+i) ⊆ (gateAt C i).inputs.toFinset.biUnion (orIn n C) := by
  intro u hu
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨v, hs, hrest⟩
  · have := u.isLt
    omega
  · obtain ⟨k, hk, he, _, hin, _⟩ := hs
    have hki : k = i := by omega
    subst k
    exact Finset.mem_biUnion.mpr ⟨v, List.mem_toFinset.mpr hin, reach_mem_orIn u hrest⟩

theorem shadow_singleton_false (n : ℕ) (C : Circuit)
    (hf : ∀ a : Fin n, PEqualNP.MetaComplexity.circuitFun n C
      (fun k => decide (k=a)) = false) : orIn n C C.output = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  let x : Fin n → Bool := fun k => decide (k=a)
  have hv : val C (List.ofFn x) a.val = true := by
    rw [val_input (by simp) a.isLt]
    simp [x, List.getD_eq_getElem?_getD]
  have hout := orStep_up (by simp : (List.ofFn x).length = n) (mem_orIn_reach a ha) hv
  have hfalse := hf a
  change val C (List.ofFn x) C.output = false at hfalse
  rw [hfalse] at hout
  cases hout

theorem serving_avoids (n : ℕ) (C : Circuit)
    (hf : ∀ a : Fin n, PEqualNP.MetaComplexity.circuitFun n C
      (fun k => decide (k=a)) = false) (i : ℕ)
    (hi : i < C.gates.length) (hl : 2 ≤ (orIn n C (n+i)).card) :
    ¬ OrReaches n C C.output i := by
  intro hr
  have hs := shadow_mono (orReaches_reach i C.output hr).1
  rw [shadow_singleton_false n C hf] at hs
  have he : orIn n C (n+i) = ∅ := Finset.subset_empty.mp hs
  simp [he] at hl

end PEqualNP.Outside.L_meta_2234_aux

namespace PEqualNP.Outside.L_meta_2234_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem roots_card (n : ℕ) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ)
    (sh : ℕ → Finset (Fin n)) :
    ((F.image (fun j => (ctr j,lf j))).biUnion
      (fun v : Fin n × ℕ => (sh v.2).image (fun b => (v.1,b)))).card =
    ∑ c : Fin n, (Finset.univ.filter
      (fun b => ∃ j ∈ F, ctr j = c ∧ b ∈ sh (lf j))).card := by
  classical
  let B := (F.image (fun j => (ctr j,lf j))).biUnion
    (fun v : Fin n × ℕ => (sh v.2).image (fun b => (v.1,b)))
  have memB : ∀ p, p ∈ B ↔ ∃ j ∈ F, ctr j = p.1 ∧ p.2 ∈ sh (lf j) := by
    intro p
    constructor
    · intro hp
      obtain ⟨v, hv, hpv⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hpv
      subst p
      exact ⟨j, hj, rfl, hb⟩
    · rintro ⟨j, hj, hc, hb⟩
      exact Finset.mem_biUnion.mpr ⟨(ctr j,lf j),
        Finset.mem_image.mpr ⟨j,hj,rfl⟩,
        Finset.mem_image.mpr ⟨p.2,hb,Prod.ext hc rfl⟩⟩
  have hsum : B.card = ∑ c : Fin n, (B.filter (fun p => p.1 = c)).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
  change B.card = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro c hc
  let A := Finset.univ.filter (fun b => ∃ j ∈ F, ctr j = c ∧ b ∈ sh (lf j))
  have he : B.filter (fun p => p.1 = c) = A.image (fun b => (c,b)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp,hc⟩ := Finset.mem_filter.mp hp
      obtain ⟨j,hj,hctr,hb⟩ := (memB p).mp hp
      refine Finset.mem_image.mpr ⟨p.2, ?_, Prod.ext hc.symm rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj,hctr.trans hc,hb⟩
    · intro hp
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨_,j,hj,hctr,hbj⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr ⟨(memB (c,b)).mpr ⟨j,hj,hctr,hbj⟩,rfl⟩
  rw [he, Finset.card_image_of_injective _ (by
    intro a b hab
    exact congrArg Prod.snd hab)]

theorem centre_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (F : Finset ℕ)
    (ctr : ℕ → Fin n) (lf : ℕ → ℕ)
    (hcover : ∀ j ∈ F, ∀ b ∈ orIn n C (lf j), G.Adj (ctr j) b)
    (c d : Fin n) (w : ℕ) (hl : 2 ≤ (orIn n C w).card)
    (hc : ∃ j ∈ F, ctr j = c ∧ Relation.ReflTransGen (OrStep n C) (lf j) w)
    (hd : ∃ j ∈ F, ctr j = d ∧ Relation.ReflTransGen (OrStep n C) (lf j) w) : c = d := by
  classical
  by_contra hne
  obtain ⟨j,hj,hjc,hjp⟩ := hc
  obtain ⟨k,hk,hkd,hkp⟩ := hd
  have hsub : orIn n C w ⊆ Finset.univ.filter (fun b => G.Adj c b ∧ G.Adj d b) := by
    intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [← hjc]
      exact hcover j hj b (shadow_mono hjp hb)
    · rw [← hkd]
      exact hcover k hk b (shadow_mono hkp hb)
  have hle := Finset.card_le_card hsub
  have hsmall := h4 c d hne
  omega

end PEqualNP.Outside.L_meta_2234_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Outside.L_meta_2234_aux
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_2234 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  classical
  intro n G _ C F ctr lf h4 hC hf hcover
  constructor
  · intro i hi hop hl hserve
    exact serving_avoids n C hf i hi hl
  · let marked := fun v : Fin n × ℕ => ∃ j ∈ F, ctr j = v.1 ∧
        Relation.ReflTransGen (OrStep n C) (lf j) v.2
    let Q := ((Finset.univ : Finset (Fin n)) ×ˢ Finset.range (n+C.gates.length)).filter
      (fun v => 2 ≤ (orIn n C v.2).card ∧ marked v)
    let R := F.image (fun j => (ctr j,lf j))
    let inputs := fun v : Fin n × ℕ =>
      (gateAt C (v.2-n)).inputs.toFinset.image (fun w => (v.1,w))
    let sets := fun v : Fin n × ℕ => (orIn n C v.2).image (fun b => (v.1,b))
    have memQ : ∀ v, v ∈ Q ↔ 2 ≤ (orIn n C v.2).card ∧ marked v := by
      intro v
      constructor
      · exact fun h => (Finset.mem_filter.mp h).2
      · intro h
        obtain ⟨i,hi,he,hop⟩ := large_or h.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_univ _,Finset.mem_range.mpr (by omega)⟩,h⟩
    have markedR : ∀ v ∈ R, marked v := by
      intro v hv
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨j,hj,rfl,Relation.ReflTransGen.refl⟩
    have children : ∀ v ∈ Q, ∀ u ∈ inputs v,
        u.1 = v.1 ∧ u.2 < v.2 ∧ marked u := by
      intro v hv u hu
      obtain ⟨hl,hm⟩ := (memQ v).mp hv
      obtain ⟨i,hi,he,hop⟩ := large_or hl
      have hidx : v.2-n=i := by omega
      change u ∈ (gateAt C (v.2-n)).inputs.toFinset.image (fun w => (v.1,w)) at hu
      rw [hidx] at hu
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hu
      have hin := List.mem_toFinset.mp hw
      have hlt := hC.2.1 i hi w hin
      obtain ⟨j,hj,hctr,hpath⟩ := hm
      refine ⟨rfl,by omega,j,hj,hctr,?_⟩
      exact hpath.tail ⟨i,hi,he,hop,hin,hlt⟩
    have hfanin : ∀ v ∈ Q, (inputs v).card ≤ 2 := by
      intro v hv
      obtain ⟨i,hi,he,hop⟩ := large_or ((memQ v).mp hv).1
      have hidx : v.2-n=i := by omega
      change ((gateAt C (v.2-n)).inputs.toFinset.image (fun w => (v.1,w))).card ≤ 2
      rw [hidx]
      calc
        _ ≤ (gateAt C i).inputs.toFinset.card := Finset.card_image_le
        _ ≤ (gateAt C i).inputs.length := List.toFinset_card_le _
        _ = 2 := hC.2.2 _ (gateAt_mem hi)
    have hparent : ∀ v ∈ Q, v ∉ R → ∃ a ∈ Q, v ∈ inputs a := by
      intro v hv hnr
      obtain ⟨hl,j,hj,hctr,hpath⟩ := (memQ v).mp hv
      rcases Relation.ReflTransGen.cases_tail hpath with he | ⟨w,hpw,hs⟩
      · exact (hnr (Finset.mem_image.mpr ⟨j,hj,Prod.ext hctr he.symm⟩)).elim
      · obtain ⟨i,hi,he,hop,hin,hlt⟩ := hs
        have hstep : Relation.ReflTransGen (OrStep n C) w v.2 :=
          Relation.ReflTransGen.single ⟨i,hi,he,hop,hin,hlt⟩
        have hlarge : 2 ≤ (orIn n C w).card :=
          le_trans hl (Finset.card_le_card (shadow_mono hstep))
        refine ⟨(v.1,w),(memQ (v.1,w)).mpr ⟨hlarge,j,hj,hctr,hpw⟩,?_⟩
        change v ∈ (gateAt C (w-n)).inputs.toFinset.image (fun u => (v.1,u))
        rw [show w-n=i by omega]
        exact Finset.mem_image.mpr ⟨v.2,List.mem_toFinset.mpr hin,Prod.ext rfl rfl⟩
    have hstep : ∀ v ∈ Q, sets v ⊆ (inputs v).biUnion sets := by
      intro v hv p hp
      obtain ⟨i,hi,he,hop⟩ := large_or ((memQ v).mp hv).1
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
      rw [he] at hb
      obtain ⟨w,hw,hbw⟩ := Finset.mem_biUnion.mp (shadow_step hi hop hb)
      apply Finset.mem_biUnion.mpr
      refine ⟨(v.1,w),?_,Finset.mem_image.mpr ⟨b,hbw,rfl⟩⟩
      change (v.1,w) ∈ (gateAt C (v.2-n)).inputs.toFinset.image (fun u => (v.1,u))
      rw [show v.2-n=i by omega]
      exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
    have hsmall : ∀ v ∈ ((Q.biUnion inputs) ∪ R) \ Q, (sets v).card ≤ 1 := by
      intro v hv
      obtain ⟨ht,hnq⟩ := Finset.mem_sdiff.mp hv
      have hm : marked v := by
        rcases Finset.mem_union.mp ht with ht | ht
        · obtain ⟨a,ha,hva⟩ := Finset.mem_biUnion.mp ht
          exact (children a ha v hva).2.2
        · exact markedR v ht
      have hle : (orIn n C v.2).card ≤ 1 := by
        by_contra hbad
        exact hnq ((memQ v).mpr ⟨by omega,hm⟩)
      exact le_trans Finset.card_image_le hle
    have hbound := roots_bound Q R inputs sets Prod.snd hfanin hparent
      (fun v hv u hu => (children v hv u hu).2.1) hstep hsmall
    have hroot := roots_card n F ctr lf (orIn n C)
    change (R.biUnion sets).card = _ at hroot
    rw [hroot] at hbound
    have hRcard : R.card ≤ F.card := Finset.card_image_le
    let S := (Finset.range C.gates.length).filter (fun i =>
      (gateAt C i).op = GateOp.or ∧ 2 ≤ (orIn n C (n+i)).card ∧
      ∃ j ∈ F, OrReaches n C (lf j) i)
    have himage : Q.image (fun v => v.2-n) ⊆ S := by
      intro i hi
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hl,j,hj,hctr,hpath⟩ := (memQ v).mp hv
      obtain ⟨i,hi,he,hop⟩ := large_or hl
      rw [show v.2-n=i by omega]
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hop,?_,j,hj,?_⟩
      · rwa [← he]
      · exact reach_orReaches hpath i he hi
    have hinj : Set.InjOn (fun v : Fin n × ℕ => v.2-n) (Q : Set (Fin n × ℕ)) := by
      intro v hv u hu heq
      change v.2-n=u.2-n at heq
      obtain ⟨hvl,hvm⟩ := (memQ v).mp hv
      obtain ⟨hul,hum⟩ := (memQ u).mp hu
      obtain ⟨i,hi,hvi,hopi⟩ := large_or hvl
      obtain ⟨k,hk,huk,hopk⟩ := large_or hul
      have hwire : v.2=u.2 := by omega
      have hc : v.1=u.1 := by
        apply centre_unique G h4 C F ctr lf hcover v.1 u.1 v.2 hvl hvm
        simpa only [hwire] using hum
      exact Prod.ext hc hwire
    have hQcard : Q.card ≤ S.card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card himage
    have hScard : Set.ncard {i : ℕ | i < C.gates.length ∧
        (gateAt C i).op = GateOp.or ∧ 2 ≤ (orIn n C (n+i)).card ∧
        ∃ j ∈ F, OrReaches n C (lf j) i} = S.card := by
      have he : {i : ℕ | i < C.gates.length ∧
          (gateAt C i).op = GateOp.or ∧ 2 ≤ (orIn n C (n+i)).card ∧
          ∃ j ∈ F, OrReaches n C (lf j) i} = (S : Set ℕ) := by
        ext i
        simp only [S, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      rw [he,Set.ncard_coe_finset]
    rw [hScard]
    omega

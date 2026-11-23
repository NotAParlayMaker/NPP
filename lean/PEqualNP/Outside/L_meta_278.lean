import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_278

open PEqualNP.CircuitLowerBounds

def wiresPrefix (C : Circuit) (x : List Bool) (t : ℕ) : List Bool :=
  (C.gates.take t).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wiresPrefix_zero (C : Circuit) (x : List Bool) :
    wiresPrefix C x 0 = x := rfl

lemma wiresPrefix_size (C : Circuit) (x : List Bool) :
    wiresPrefix C x C.size = C.wires x := by
  simp [wiresPrefix, Circuit.wires, Circuit.size]

lemma wiresPrefix_succ (C : Circuit) (x : List Bool) {t : ℕ} (ht : t < C.size) :
    wiresPrefix C x (t + 1) =
      wiresPrefix C x t ++
        [(C.gates[t]'ht).op.eval
          ((C.gates[t]'ht).inputs.map fun i => (wiresPrefix C x t).getD i false)] := by
  unfold wiresPrefix
  rw [List.take_succ_eq_append_getElem ht, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma wiresPrefix_succ_of_not_lt (C : Circuit) (x : List Bool) {t : ℕ} (ht : ¬ t < C.size) :
    wiresPrefix C x (t + 1) = wiresPrefix C x t := by
  have hlen : C.gates.length ≤ t := Nat.le_of_not_lt ht
  have hlen1 : C.gates.length ≤ t + 1 := Nat.le_succ_of_le hlen
  simp only [wiresPrefix, List.take_of_length_le hlen1, List.take_of_length_le hlen]

lemma wiresPrefix_length (C : Circuit) (x : List Bool) (t : ℕ) :
    (wiresPrefix C x t).length = x.length + min t C.size := by
  induction t with
  | zero => simp [wiresPrefix_zero]
  | succ t ih =>
    by_cases ht : t < C.size
    · rw [wiresPrefix_succ C x ht, List.length_append, List.length_singleton, ih]
      omega
    · rw [wiresPrefix_succ_of_not_lt C x ht, ih]
      omega

lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD, List.getElem?_append_right h]

lemma getD_of_le_length {α : Type*} (l : List α) (i : ℕ) (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none h]

lemma wiresPrefix_getD_of_le (C : Circuit) (x : List Bool) {t₁ t₂ i : ℕ}
    (hle : t₁ ≤ t₂) (hi : i < (wiresPrefix C x t₁).length) :
    (wiresPrefix C x t₂).getD i false = (wiresPrefix C x t₁).getD i false := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc]
    by_cases ht : t₁ + k < C.size
    · have hi' : i < (wiresPrefix C x (t₁ + k)).length := by
        rw [wiresPrefix_length] at hi ⊢
        omega
      rw [wiresPrefix_succ C x ht, getD_append_left _ _ _ _ hi', ih]
    · rw [wiresPrefix_succ_of_not_lt C x ht]
      exact ih

lemma wires_getD_eq_wiresPrefix (C : Circuit) (x : List Bool) {t i : ℕ}
    (ht : t ≤ C.size) (hi : i < x.length + t) :
    (C.wires x).getD i false = (wiresPrefix C x t).getD i false := by
  rw [← wiresPrefix_size]
  apply wiresPrefix_getD_of_le C x ht
  rw [wiresPrefix_length]
  omega

lemma wiresPrefix_getD_eq_ite (C : Circuit) (x : List Bool) {t : ℕ} (ht : t ≤ C.size) (i : ℕ) :
    (wiresPrefix C x t).getD i false =
      if i < x.length + t then (C.wires x).getD i false else false := by
  by_cases hi : i < x.length + t
  · simp only [hi, ↓reduceIte]
    exact (wires_getD_eq_wiresPrefix C x ht hi).symm
  · simp only [hi, ↓reduceIte]
    apply getD_of_le_length
    rw [wiresPrefix_length]
    omega

lemma wires_getD_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  have h1 := wires_getD_eq_wiresPrefix C (List.ofFn x) (t := 0) (i := i)
    (Nat.zero_le C.size) (by simp [hi])
  rw [h1, wiresPrefix_zero]
  simp [List.getD, hi]

lemma wires_getD_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ} (hi : n + C.size ≤ i) :
    (C.wires (List.ofFn x)).getD i false = false := by
  rw [← wiresPrefix_size]
  apply getD_of_le_length
  rw [wiresPrefix_length, List.length_ofFn]
  omega

lemma pair_eq {l : List ℕ} (h : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp_all

lemma wires_getD_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {j : ℕ} (hj : j < C.size) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      (C.gates[j]'hj).op.eval
        ((C.gates[j]'hj).inputs.map fun i =>
          if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h1 := wires_getD_eq_wiresPrefix C (List.ofFn x) (t := j + 1) (i := n + j)
    (Nat.succ_le_of_lt hj) (by rw [List.length_ofFn]; omega)
  rw [h1, wiresPrefix_succ C (List.ofFn x) hj]
  have hlen : (wiresPrefix C (List.ofFn x) j).length = n + j := by
    rw [wiresPrefix_length, List.length_ofFn]
    omega
  rw [getD_append_right _ _ _ _ (by omega)]
  simp only [hlen, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [wiresPrefix_getD_eq_ite C (List.ofFn x) (Nat.le_of_lt hj) i, List.length_ofFn]

lemma wiresPrefix_mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ q : Fin n, x q = true → y q = true) :
    ∀ t i, (wiresPrefix C (List.ofFn x) t).getD i false = true →
      (wiresPrefix C (List.ofFn y) t).getD i false = true := by
  intro t
  induction t with
  | zero =>
    intro i hi
    simp only [wiresPrefix_zero] at hi ⊢
    by_cases h : i < n
    · simp only [List.getD, List.getElem?_ofFn, h, ↓reduceDIte, Option.getD_some] at hi ⊢
      exact hxy ⟨i, h⟩ hi
    · rw [getD_of_le_length _ _ _ (by simp; omega)] at hi
      contradiction
  | succ t ih =>
    intro i hi
    by_cases ht : t < C.size
    · have hlenx : (wiresPrefix C (List.ofFn x) t).length = n + t := by
        rw [wiresPrefix_length, List.length_ofFn]; omega
      have hleny : (wiresPrefix C (List.ofFn y) t).length = n + t := by
        rw [wiresPrefix_length, List.length_ofFn]; omega
      rw [wiresPrefix_succ C (List.ofFn x) ht] at hi
      rw [wiresPrefix_succ C (List.ofFn y) ht]
      by_cases hlt : i < n + t
      · rw [getD_append_left _ _ _ _ (by omega)] at hi
        rw [getD_append_left _ _ _ _ (by omega)]
        exact ih i hi
      · rw [getD_append_right _ _ _ _ (by omega)] at hi
        rw [getD_append_right _ _ _ _ (by omega)]
        rw [hlenx] at hi
        rw [hleny]
        by_cases heq : i - (n + t) = 0
        · rw [heq] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          have hg := hC (C.gates[t]'ht) (List.getElem_mem ht)
          have hpair := pair_eq hg.2
          rw [hpair] at hi ⊢
          rcases hg.1 with hop | hop <;> rw [hop] at hi ⊢
          · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.and_eq_true] at hi ⊢
            exact ⟨ih _ hi.1, ih _ hi.2⟩
          · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.or_eq_true] at hi ⊢
            rcases hi with h1 | h2
            · exact Or.inl (ih _ h1)
            · exact Or.inr (ih _ h2)
        · have hge : 1 ≤ i - (n + t) := by omega
          rw [getD_of_le_length _ _ _ (by simp; omega)] at hi
          contradiction
    · rw [wiresPrefix_succ_of_not_lt C (List.ofFn x) ht] at hi
      rw [wiresPrefix_succ_of_not_lt C (List.ofFn y) ht]
      exact ih i hi

lemma wires_mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ q : Fin n, x q = true → y q = true)
    (i : ℕ) (hi : (C.wires (List.ofFn x)).getD i false = true) :
    (C.wires (List.ofFn y)).getD i false = true := by
  rw [← wiresPrefix_size] at hi ⊢
  exact wiresPrefix_mono C hC x y hxy C.size i hi

def unitVec {n : ℕ} (p : Fin n) : Fin n → Bool :=
  fun q => decide (q = p)

def singleSet {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (unitVec p))).getD w false = true)

def effSingleSet {n : ℕ} (C : Circuit) (j u : ℕ) : Finset (Fin n) :=
  if u < n + j then singleSet C u else ∅

lemma singleSet_input {n : ℕ} (C : Circuit) {i : ℕ} (hi : i < n) :
    singleSet C i = ({⟨i, hi⟩} : Finset (Fin n)) := by
  ext p
  simp only [singleSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [wires_getD_input C _ hi]
  simp [unitVec, eq_comm]

lemma singleSet_ge {n : ℕ} (C : Circuit) {i : ℕ} (hi : n + C.size ≤ i) :
    (singleSet C i : Finset (Fin n)) = ∅ := by
  ext p
  simp only [singleSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false]
  rw [wires_getD_ge C _ hi]
  decide

lemma singleSet_gate_and {n : ℕ} (C : Circuit) {j : ℕ} (hj : j < C.size)
    (hop : (C.gates[j]'hj).op = GateOp.and) (hlen : (C.gates[j]'hj).inputs.length = 2) :
    (singleSet C (n + j) : Finset (Fin n)) =
      effSingleSet C j ((C.gates[j]'hj).inputs.getD 0 0) ∩
      effSingleSet C j ((C.gates[j]'hj).inputs.getD 1 0) := by
  ext p
  simp only [singleSet, effSingleSet, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and]
  conv_lhs => rw [wires_getD_gate C (unitVec p) hj, hop, pair_eq hlen]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true, Bool.and_eq_true]
  split_ifs <;> simp

lemma singleSet_gate_or {n : ℕ} (C : Circuit) {j : ℕ} (hj : j < C.size)
    (hop : (C.gates[j]'hj).op = GateOp.or) (hlen : (C.gates[j]'hj).inputs.length = 2) :
    (singleSet C (n + j) : Finset (Fin n)) =
      effSingleSet C j ((C.gates[j]'hj).inputs.getD 0 0) ∪
      effSingleSet C j ((C.gates[j]'hj).inputs.getD 1 0) := by
  ext p
  simp only [singleSet, effSingleSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and]
  conv_lhs => rw [wires_getD_gate C (unitVec p) hj, hop, pair_eq hlen]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false, Bool.or_eq_true]
  split_ifs <;> simp

def privSet {n : ℕ} (S : Finset (Fin n)) (C : Circuit) : Finset ℕ :=
  (Finset.range C.size).filter (fun j =>
    (singleSet C (n + j) : Finset (Fin n)) ⊆ S ∧ 2 ≤ (singleSet C (n + j) : Finset (Fin n)).card)

def gateInput (C : Circuit) (j : ℕ) (s : Fin 2) : ℕ :=
  if hj : j < C.size then (C.gates[j]'hj).inputs.getD s.val 0 else 0

def evalV {n : ℕ} (S : Finset (Fin n)) (C : Circuit) : ℕ → Bool
  | w =>
    if n ≤ w then
      if h2 : w - n < C.gates.length then
        if w - n ∈ privSet S C then
          let j := w - n
          let u := gateInput C j 0
          let v := gateInput C j 1
          let bu := if u < w then evalV S C u else false
          let bv := if v < w then evalV S C v else false
          match (C.gates[j]'h2).op with
          | GateOp.and => bu && bv
          | GateOp.or => bu || bv
          | _ => false
        else
          decide (¬ (singleSet C w : Finset (Fin n)) ⊆ S)
      else
        false
    else
      decide (¬ (singleSet C w : Finset (Fin n)) ⊆ S)
termination_by w => w

def effV {n : ℕ} (S : Finset (Fin n)) (C : Circuit) (j u : ℕ) : Bool :=
  if u < n + j then evalV S C u else false

lemma evalV_priv_and {n : ℕ} (S : Finset (Fin n)) (C : Circuit) {j : ℕ}
    (hj : j ∈ privSet S C) (hsize : j < C.size) (hop : (C.gates[j]'hsize).op = GateOp.and) :
    evalV S C (n + j) = (effV S C j (gateInput C j 0) && effV S C j (gateInput C j 1)) := by
  rw [evalV]
  have h1 : n ≤ n + j := Nat.le_add_right n j
  have hsub : n + j - n = j := Nat.add_sub_cancel_left n j
  have hlen : j < C.gates.length := hsize
  simp only [h1, hsub, hlen, hj, ↓reduceDIte, ↓reduceIte, effV]
  have hop' : (C.gates[j]'hlen).op = GateOp.and := hop
  rw [hop']

lemma evalV_priv_or {n : ℕ} (S : Finset (Fin n)) (C : Circuit) {j : ℕ}
    (hj : j ∈ privSet S C) (hsize : j < C.size) (hop : (C.gates[j]'hsize).op = GateOp.or) :
    evalV S C (n + j) = (effV S C j (gateInput C j 0) || effV S C j (gateInput C j 1)) := by
  rw [evalV]
  have h1 : n ≤ n + j := Nat.le_add_right n j
  have hsub : n + j - n = j := Nat.add_sub_cancel_left n j
  have hlen : j < C.gates.length := hsize
  simp only [h1, hsub, hlen, hj, ↓reduceDIte, ↓reduceIte, effV]
  have hop' : (C.gates[j]'hlen).op = GateOp.or := hop
  rw [hop']

lemma evalV_nonpriv {n : ℕ} (S : Finset (Fin n)) (C : Circuit) {w : ℕ}
    (hnp : ∀ j ∈ privSet S C, w ≠ n + j) :
    evalV S C w = decide (¬ (singleSet C w : Finset (Fin n)) ⊆ S) := by
  rw [evalV]
  by_cases h1 : n ≤ w
  · simp only [h1, ↓reduceIte]
    by_cases h2 : w - n < C.gates.length
    · simp only [h2, ↓reduceDIte]
      have hnot : w - n ∉ privSet S C := by
        intro hmem
        exact hnp (w - n) hmem (by omega)
      simp [hnot]
    · simp only [h2, ↓reduceDIte]
      have hge : n + C.size ≤ w := by change n + C.gates.length ≤ w; omega
      simp [singleSet_ge C hge]
  · simp [h1]

lemma effV_nonpriv {n : ℕ} (S : Finset (Fin n)) (C : Circuit) {j u : ℕ}
    (hnp : ¬ (n ≤ u ∧ u < n + j ∧ u - n ∈ privSet S C)) :
    effV S C j u = decide (¬ effSingleSet C j u ⊆ S) := by
  unfold effV effSingleSet
  by_cases hu : u < n + j
  · simp only [hu, ↓reduceIte]
    apply evalV_nonpriv
    intro j' hj' heq
    apply hnp
    refine ⟨by omega, hu, ?_⟩
    have : u - n = j' := by omega
    rw [this]
    exact hj'
  · simp [hu]

def reachPriv {n : ℕ} (S : Finset (Fin n)) (C : Circuit) (j : ℕ) : Finset ℕ :=
  if j ∈ privSet S C then
    let r0 := if _h0 : n ≤ gateInput C j 0 ∧ gateInput C j 0 < n + j ∧
        gateInput C j 0 - n ∈ privSet S C then reachPriv S C (gateInput C j 0 - n) else ∅
    let r1 := if _h1 : n ≤ gateInput C j 1 ∧ gateInput C j 1 < n + j ∧
        gateInput C j 1 - n ∈ privSet S C then reachPriv S C (gateInput C j 1 - n) else ∅
    insert j (r0 ∪ r1)
  else ∅
termination_by j
decreasing_by all_goals omega

lemma mem_reachPriv_self {n : ℕ} (S : Finset (Fin n)) (C : Circuit) {j : ℕ}
    (hj : j ∈ privSet S C) : j ∈ reachPriv S C j := by
  rw [reachPriv]
  simp [hj]

lemma reachPriv_subset_privSet {n : ℕ} (S : Finset (Fin n)) (C : Circuit) :
    ∀ k, reachPriv S C k ⊆ privSet S C := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [reachPriv]
    by_cases hk : k ∈ privSet S C
    · simp only [hk, ↓reduceIte]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_union] at hx
      rcases hx with rfl | hx | hx
      · exact hk
      · by_cases h0 : n ≤ gateInput C k 0 ∧ gateInput C k 0 < n + k ∧
            gateInput C k 0 - n ∈ privSet S C
        · simp only [h0] at hx
          exact ih (gateInput C k 0 - n) (by omega) hx
        · simp [h0] at hx
      · by_cases h1 : n ≤ gateInput C k 1 ∧ gateInput C k 1 < n + k ∧
            gateInput C k 1 - n ∈ privSet S C
        · simp only [h1] at hx
          exact ih (gateInput C k 1 - n) (by omega) hx
        · simp [h1] at hx
    · simp [hk]

lemma reachPriv_closed {n : ℕ} (S : Finset (Fin n)) (C : Circuit) :
    ∀ k j (s : Fin 2), j ∈ reachPriv S C k →
      n ≤ gateInput C j s → gateInput C j s < n + j →
      gateInput C j s - n ∈ privSet S C →
      gateInput C j s - n ∈ reachPriv S C k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro j s hj h1 h2 h3
    rw [reachPriv] at hj ⊢
    by_cases hk : k ∈ privSet S C
    · simp only [hk, ↓reduceIte, Finset.mem_insert, Finset.mem_union] at hj ⊢
      rcases hj with rfl | hj0 | hj1
      · fin_cases s
        · right; left
          have h0 : n ≤ gateInput C j 0 ∧ gateInput C j 0 < n + j ∧
              gateInput C j 0 - n ∈ privSet S C := ⟨h1, h2, h3⟩
          simp only [Fin.zero_eta, h0]
          exact mem_reachPriv_self S C h3
        · right; right
          have h1' : n ≤ gateInput C j 1 ∧ gateInput C j 1 < n + j ∧
              gateInput C j 1 - n ∈ privSet S C := ⟨h1, h2, h3⟩
          simp only [Fin.mk_one, h1']
          exact mem_reachPriv_self S C h3
      · right; left
        by_cases h0 : n ≤ gateInput C k 0 ∧ gateInput C k 0 < n + k ∧
            gateInput C k 0 - n ∈ privSet S C
        · simp only [h0] at hj0 ⊢
          exact ih (gateInput C k 0 - n) (by omega) j s hj0 h1 h2 h3
        · simp [h0] at hj0
      · right; right
        by_cases h1' : n ≤ gateInput C k 1 ∧ gateInput C k 1 < n + k ∧
            gateInput C k 1 - n ∈ privSet S C
        · simp only [h1'] at hj1 ⊢
          exact ih (gateInput C k 1 - n) (by omega) j s hj1 h1 h2 h3
        · simp [h1'] at hj1
    · simp [hk] at hj

lemma reachPriv_parent {n : ℕ} (S : Finset (Fin n)) (C : Circuit) :
    ∀ k j', j' ∈ reachPriv S C k → j' ≠ k →
      ∃ j ∈ reachPriv S C k, ∃ s : Fin 2,
        n ≤ gateInput C j s ∧ gateInput C j s < n + j ∧ gateInput C j s - n = j' := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro j' hj' hne
    have hdef : reachPriv S C k =
      if k ∈ privSet S C then
        insert k
          ((if n ≤ gateInput C k 0 ∧ gateInput C k 0 < n + k ∧ gateInput C k 0 - n ∈ privSet S C
            then reachPriv S C (gateInput C k 0 - n) else ∅) ∪
           (if n ≤ gateInput C k 1 ∧ gateInput C k 1 < n + k ∧ gateInput C k 1 - n ∈ privSet S C
            then reachPriv S C (gateInput C k 1 - n) else ∅))
      else ∅ := by
      conv_lhs => rw [reachPriv]
      simp only [dite_eq_ite]
    rw [hdef] at hj'
    by_cases hk : k ∈ privSet S C
    · simp only [hk, ↓reduceIte, Finset.mem_insert, Finset.mem_union] at hj'
      rcases hj' with rfl | hj0 | hj1
      · exact absurd rfl hne
      · by_cases h0 : n ≤ gateInput C k 0 ∧ gateInput C k 0 < n + k ∧
            gateInput C k 0 - n ∈ privSet S C
        · simp only [h0] at hj0
          by_cases heq : j' = gateInput C k 0 - n
          · refine ⟨k, mem_reachPriv_self S C hk, 0, h0.1, h0.2.1, heq.symm⟩
          · obtain ⟨j, hj, s, hs1, hs2, hs3⟩ := ih (gateInput C k 0 - n) (by omega) j' hj0 heq
            refine ⟨j, ?_, s, hs1, hs2, hs3⟩
            rw [hdef]
            simp only [hk, ↓reduceIte, Finset.mem_insert, Finset.mem_union]
            right; left
            simp [h0, hj]
        · simp [h0] at hj0
      · by_cases h1 : n ≤ gateInput C k 1 ∧ gateInput C k 1 < n + k ∧
            gateInput C k 1 - n ∈ privSet S C
        · simp only [h1] at hj1
          by_cases heq : j' = gateInput C k 1 - n
          · refine ⟨k, mem_reachPriv_self S C hk, 1, h1.1, h1.2.1, heq.symm⟩
          · obtain ⟨j, hj, s, hs1, hs2, hs3⟩ := ih (gateInput C k 1 - n) (by omega) j' hj1 heq
            refine ⟨j, ?_, s, hs1, hs2, hs3⟩
            rw [hdef]
            simp only [hk, ↓reduceIte, Finset.mem_insert, Finset.mem_union]
            right; right
            simp [h1, hj]
        · simp [h1] at hj1
    · simp [hk] at hj'

lemma case_evalV_true {n k c : ℕ} {S : Finset (Fin n)} {C : Circuit}
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hzero : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD (n + j₀) false = false)
    (hck : c ≤ k)
    (hj₀ : j₀ ∈ privSet S C)
    (hV : evalV S C (n + j₀) = true) :
    c ≤ (privSet S C).card := by
  let R : Finset ℕ := reachPriv S C j₀
  have hRsub : R ⊆ privSet S C := reachPriv_subset_privSet S C j₀
  have hj₀R : j₀ ∈ R := mem_reachPriv_self S C hj₀
  let Slots : Finset (ℕ × Fin 2) := R ×ˢ Finset.univ
  let isInt : ℕ × Fin 2 → Bool := fun p =>
    decide (n ≤ gateInput C p.1 p.2 ∧ gateInput C p.1 p.2 < n + p.1 ∧
      gateInput C p.1 p.2 - n ∈ R)
  let IntSlots : Finset (ℕ × Fin 2) := Slots.filter (fun p => isInt p = true)
  let ExtSlots : Finset (ℕ × Fin 2) := Slots.filter (fun p => isInt p = false)
  have hcard_split : IntSlots.card + ExtSlots.card = 2 * R.card := by
    have hdisj : Disjoint IntSlots ExtSlots := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [IntSlots, ExtSlots, Finset.mem_filter] at hp1 hp2
      rw [hp1.2] at hp2
      exact Bool.noConfusion hp2.2
    have hunion : IntSlots ∪ ExtSlots = Slots := by
      ext p
      simp only [IntSlots, ExtSlots, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        cases hb : isInt p
        · exact Or.inr ⟨h, rfl⟩
        · exact Or.inl ⟨h, rfl⟩
    have h1 : IntSlots.card + ExtSlots.card = Slots.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have h2 : Slots.card = 2 * R.card := by
      simp [Slots, Finset.card_product, Nat.mul_comm]
    omega
  have hInt_ge : R.card - 1 ≤ IntSlots.card := by
    have hsub : R.erase j₀ ⊆ IntSlots.image (fun p => gateInput C p.1 p.2 - n) := by
      intro j' hj'
      rw [Finset.mem_erase] at hj'
      obtain ⟨j, hjR, s, h1, h2, h3⟩ := reachPriv_parent S C j₀ j' hj'.2 hj'.1
      rw [Finset.mem_image]
      refine ⟨(j, s), ?_, h3⟩
      simp only [IntSlots, Slots, isInt, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        and_true, decide_eq_true_eq]
      exact ⟨hjR, h1, h2, h3.symm ▸ hj'.2⟩
    calc R.card - 1 = (R.erase j₀).card := (Finset.card_erase_of_mem hj₀R).symm
      _ ≤ (IntSlots.image (fun p => gateInput C p.1 p.2 - n)).card := Finset.card_le_card hsub
      _ ≤ IntSlots.card := Finset.card_image_le
  have hRpos : 1 ≤ R.card := Finset.one_le_card.mpr ⟨j₀, hj₀R⟩
  have hExt_le : ExtSlots.card ≤ (privSet S C).card + 1 := by
    have hRle : R.card ≤ (privSet S C).card := Finset.card_le_card hRsub
    omega
  let pick : ℕ × Fin 2 → Finset (Fin n) := fun p =>
    if h : ∃ q : Fin n, q ∈ effSingleSet C p.1 (gateInput C p.1 p.2) ∧ q ∉ S then
      {Classical.choose h}
    else ∅
  let X : Finset (Fin n) := ExtSlots.biUnion pick
  have hX_card : X.card ≤ ExtSlots.card := by
    calc X.card ≤ ∑ p ∈ ExtSlots, (pick p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ ExtSlots, 1 := by
        apply Finset.sum_le_sum
        intro p _
        dsimp only [pick]
        split_ifs <;> simp
      _ = ExtSlots.card := by simp
  have hX_disj : ∀ q ∈ S, q ∉ X := by
    intro q hqS hqX
    simp only [X, Finset.mem_biUnion] at hqX
    rcases hqX with ⟨p, _, hqp⟩
    dsimp only [pick] at hqp
    split_ifs at hqp with h
    · rw [Finset.mem_singleton] at hqp
      subst hqp
      exact (Classical.choose_spec h).2 hqS
    · simp at hqp
  let x : Fin n → Bool := fun q => decide (q ∈ X)
  have hx_card : (Finset.univ.filter (fun q : Fin n => x q = true)).card = X.card := by
    congr 1
    ext q
    simp [x]
  have hx_zero : ∀ q ∈ S, x q = false := by
    intro q hqS
    simp [x, hX_disj q hqS]
  have hmain : ∀ j, j ∈ R → evalV S C (n + j) = true →
      (C.wires (List.ofFn x)).getD (n + j) false = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hjR hjV
      have hjP : j ∈ privSet S C := hRsub hjR
      have hjSize : j < C.size := (Finset.mem_range.mp (Finset.mem_filter.mp hjP).1)
      have hslot : ∀ s : Fin 2, effV S C j (gateInput C j s) = true →
          (if gateInput C j s < n + j then
            (C.wires (List.ofFn x)).getD (gateInput C j s) false else false) = true := by
        intro s hsV
        let u := gateInput C j s
        change effV S C j u = true at hsV
        change (if u < n + j then (C.wires (List.ofFn x)).getD u false else false) = true
        by_cases hint : isInt (j, s) = true
        · simp only [isInt, decide_eq_true_eq] at hint
          have hu_eq : u = n + (u - n) := by omega
          have hu_lt : u < n + j := hint.2.1
          simp only [hu_lt, ↓reduceIte]
          have hV' : evalV S C (n + (u - n)) = true := by
            unfold effV at hsV
            simp only [hu_lt, ↓reduceIte] at hsV
            rwa [← hu_eq]
          have := ih (u - n) (by omega) hint.2.2 hV'
          rwa [← hu_eq] at this
        · have hnotP : ¬ (n ≤ u ∧ u < n + j ∧ u - n ∈ privSet S C) := by
            intro h
            apply hint
            simp only [isInt, decide_eq_true_eq]
            exact ⟨h.1, h.2.1, reachPriv_closed S C j₀ j s hjR h.1 h.2.1 h.2.2⟩
          rw [effV_nonpriv S C hnotP, decide_eq_true_eq] at hsV
          rw [Finset.not_subset] at hsV
          have hex : ∃ q : Fin n, q ∈ effSingleSet C j (gateInput C j s) ∧ q ∉ S := hsV
          have hpExt : (j, s) ∈ ExtSlots := by
            simp only [ExtSlots, Slots, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
              and_true]
            refine ⟨hjR, ?_⟩
            cases hb : isInt (j, s)
            · rfl
            · exact absurd hb hint
          have hqSpec := Classical.choose_spec hex
          have hqX : Classical.choose hex ∈ X := by
            simp only [X, Finset.mem_biUnion]
            refine ⟨(j, s), hpExt, ?_⟩
            simp only [pick, hex, ↓reduceDIte, Finset.mem_singleton]
          have hqEff : Classical.choose hex ∈ effSingleSet C j u := hqSpec.1
          unfold effSingleSet at hqEff
          by_cases hult : u < n + j
          · simp only [hult, ↓reduceIte] at hqEff ⊢
            simp only [singleSet, Finset.mem_filter, Finset.mem_univ, true_and] at hqEff
            apply wires_mono C hC (unitVec (Classical.choose hex)) x _ u hqEff
            intro r hr
            simp only [unitVec, decide_eq_true_eq] at hr
            subst hr
            simp [x, hqX]
          · simp [hult] at hqEff
      have hg := hC (C.gates[j]'hjSize) (List.getElem_mem hjSize)
      have hpair := pair_eq hg.2
      rw [wires_getD_gate C x hjSize, hpair]
      have h0 : gateInput C j 0 = (C.gates[j]'hjSize).inputs.getD 0 0 := by
        simp [gateInput, hjSize]
      have h1 : gateInput C j 1 = (C.gates[j]'hjSize).inputs.getD 1 0 := by
        simp [gateInput, hjSize]
      rcases hg.1 with hop | hop
      · rw [evalV_priv_and S C hjP hjSize hop, Bool.and_eq_true] at hjV
        rw [hop]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true, Bool.and_eq_true]
        rw [← h0, ← h1]
        exact ⟨hslot 0 hjV.1, hslot 1 hjV.2⟩
      · rw [evalV_priv_or S C hjP hjSize hop, Bool.or_eq_true] at hjV
        rw [hop]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
          Bool.or_false, Bool.or_eq_true]
        rw [← h0, ← h1]
        rcases hjV with hV0 | hV1
        · exact Or.inl (hslot 0 hV0)
        · exact Or.inr (hslot 1 hV1)
  by_contra hlt
  push Not at hlt
  have hle : X.card ≤ k := by omega
  have htrue := hmain j₀ hj₀R hV
  have hfalse := hzero x (by rw [hx_card]; exact hle) hx_zero
  rw [htrue] at hfalse
  contradiction

lemma card_image_merge {n : ℕ} (S : Finset (Fin n)) (col : Fin n → ℕ) (c₁ c₂ : ℕ) :
    (S.image col).card ≤ (S.image (fun p => if col p = c₂ then c₁ else col p)).card + 1 := by
  have hsub : S.image col ⊆ insert c₂ (S.image (fun p => if col p = c₂ then c₁ else col p)) := by
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨p, hpS, rfl⟩
    rw [Finset.mem_insert, Finset.mem_image]
    by_cases h : col p = c₂
    · exact Or.inl h
    · right
      exact ⟨p, hpS, by simp [h]⟩
  calc (S.image col).card
      ≤ (insert c₂ (S.image (fun p => if col p = c₂ then c₁ else col p))).card :=
        Finset.card_le_card hsub
    _ ≤ (S.image (fun p => if col p = c₂ then c₁ else col p)).card + 1 :=
        Finset.card_insert_le _ _

lemma case_evalV_false {n c j₀ : ℕ} {S : Finset (Fin n)} {C : Circuit}
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hS : (singleSet C (n + j₀) : Finset (Fin n)) = S)
    (hcS : c + 1 ≤ S.card)
    (hj₀ : j₀ ∈ privSet S C)
    (hV : evalV S C (n + j₀) = false) :
    c ≤ (privSet S C).card := by
  let Q : Finset ℕ := (privSet S C).filter (fun j => evalV S C (n + j) = false)
  have hQsub : Q ⊆ privSet S C := Finset.filter_subset _ _
  have hstep : ∀ t ≤ C.size, ∃ col : Fin n → ℕ,
      S.card ≤ (S.image col).card + (Q.filter (· < t)).card ∧
      ∀ j ∈ Q, j < t → ∀ p ∈ singleSet C (n + j), ∀ q ∈ singleSet C (n + j), col p = col q := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨fun p => p.val, ?_, ?_⟩
      · have hinj : Function.Injective (fun p : Fin n => p.val) := Fin.val_injective
        rw [Finset.card_image_of_injective S hinj]
        simp
      · intro j _ hlt
        omega
    | succ t ih =>
      intro ht
      obtain ⟨col, hcard, hconst⟩ := ih (Nat.le_of_succ_le ht)
      by_cases htQ : t ∈ Q
      · have htP : t ∈ privSet S C := hQsub htQ
        have htSize : t < C.size := ht
        have htV : evalV S C (n + t) = false := (Finset.mem_filter.mp htQ).2
        have hAt_sub : (singleSet C (n + t) : Finset (Fin n)) ⊆ S :=
          (Finset.mem_filter.mp htP).2.1
        have hAt_card : 2 ≤ (singleSet C (n + t) : Finset (Fin n)).card :=
          (Finset.mem_filter.mp htP).2.2
        have hfilt_eq : Q.filter (· < t + 1) = insert t (Q.filter (· < t)) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · intro ⟨hxQ, hxlt⟩
            by_cases hxt : x = t
            · exact Or.inl hxt
            · exact Or.inr ⟨hxQ, by omega⟩
          · rintro (rfl | ⟨hxQ, hxlt⟩)
            · exact ⟨htQ, Nat.lt_succ_self _⟩
            · exact ⟨hxQ, Nat.lt_succ_of_lt hxlt⟩
        have htnot : t ∉ Q.filter (· < t) := by simp
        have hfilt_card : (Q.filter (· < t + 1)).card = (Q.filter (· < t)).card + 1 := by
          rw [hfilt_eq, Finset.card_insert_of_notMem htnot]
        have hg := hC (C.gates[t]'htSize) (List.getElem_mem htSize)
        have h0 : gateInput C t 0 = (C.gates[t]'htSize).inputs.getD 0 0 := by
          simp [gateInput, htSize]
        have h1 : gateInput C t 1 = (C.gates[t]'htSize).inputs.getD 1 0 := by
          simp [gateInput, htSize]
        rcases hg.1 with hop | hop
        · have hAt_eq := singleSet_gate_and (n := n) C htSize hop hg.2
          rw [← h0, ← h1] at hAt_eq
          rw [evalV_priv_and S C htP htSize hop, Bool.and_eq_false_iff] at htV
          have hchild : ∀ s : Fin 2, effV S C t (gateInput C t s) = false →
              (singleSet C (n + t) : Finset (Fin n)) ⊆ effSingleSet C t (gateInput C t s) →
              ∀ p ∈ singleSet C (n + t), ∀ q ∈ singleSet C (n + t), col p = col q := by
            intro s hsV hsub
            let u := gateInput C t s
            change effV S C t u = false at hsV
            change (singleSet C (n + t) : Finset (Fin n)) ⊆ effSingleSet C t u at hsub
            have h2le : 2 ≤ (effSingleSet C t u).card := le_trans hAt_card (Finset.card_le_card hsub)
            have hult : u < n + t := by
              by_contra hge
              simp [effSingleSet, hge] at h2le
            have heff_eq : (effSingleSet C t u : Finset (Fin n)) = singleSet C u := by
              simp [effSingleSet, hult]
            rw [heff_eq] at h2le hsub
            have hVu : evalV S C u = false := by
              simpa [effV, hult] using hsV
            have hle_n : n ≤ u := by
              by_contra hlt_n
              push Not at hlt_n
              rw [singleSet_input C hlt_n] at h2le
              simp at h2le
            have hu_priv : u - n ∈ privSet S C := by
              by_contra hnotP
              have hnp : ¬ (n ≤ u ∧ u < n + t ∧ u - n ∈ privSet S C) := fun h => hnotP h.2.2
              have hV' : decide (¬ (effSingleSet C t u : Finset (Fin n)) ⊆ S) = false :=
                (effV_nonpriv S C hnp).symm.trans hsV
              simp only [heff_eq, decide_eq_false_iff_not, not_not] at hV'
              apply hnotP
              simp only [privSet, Finset.mem_filter, Finset.mem_range]
              have hu_eq : n + (u - n) = u := by omega
              rw [hu_eq]
              exact ⟨by omega, hV', h2le⟩
            have huQ : u - n ∈ Q := by
              simp only [Q, Finset.mem_filter]
              have hu_eq : n + (u - n) = u := by omega
              exact ⟨hu_priv, by rwa [hu_eq]⟩
            intro p hp q hq
            have hu_eq : n + (u - n) = u := by omega
            exact hconst (u - n) huQ (by omega) p (by rw [hu_eq]; exact hsub hp)
              q (by rw [hu_eq]; exact hsub hq)
          have hconst_t : ∀ p ∈ singleSet C (n + t), ∀ q ∈ singleSet C (n + t), col p = col q := by
            rcases htV with hV0 | hV1
            · exact hchild 0 hV0 (by rw [hAt_eq]; exact Finset.inter_subset_left)
            · exact hchild 1 hV1 (by rw [hAt_eq]; exact Finset.inter_subset_right)
          refine ⟨col, by omega, ?_⟩
          intro j hjQ hjlt
          by_cases hjt : j = t
          · subst hjt; exact hconst_t
          · exact hconst j hjQ (by omega)
        · have hAt_eq := singleSet_gate_or (n := n) C htSize hop hg.2
          rw [← h0, ← h1] at hAt_eq
          rw [evalV_priv_or S C htP htSize hop, Bool.or_eq_false_iff] at htV
          have hchild_const : ∀ s : Fin 2, effV S C t (gateInput C t s) = false →
              (effSingleSet C t (gateInput C t s) : Finset (Fin n)) ⊆ S →
              ∀ p ∈ effSingleSet C t (gateInput C t s),
              ∀ q ∈ effSingleSet C t (gateInput C t s), col p = col q := by
            intro s hsV hsubS
            let u := gateInput C t s
            change effV S C t u = false at hsV
            change (effSingleSet C t u : Finset (Fin n)) ⊆ S at hsubS
            by_cases hcard1 : (effSingleSet (n := n) C t u).card ≤ 1
            · intro p hp q hq
              have hpq : p = q := Finset.card_le_one.mp hcard1 p hp q hq
              rw [hpq]
            · have h2le : 2 ≤ (effSingleSet (n := n) C t u).card := by omega
              have hult : u < n + t := by
                by_contra hge
                simp [effSingleSet, hge] at h2le
              have heff_eq : (effSingleSet C t u : Finset (Fin n)) = singleSet C u := by
                simp [effSingleSet, hult]
              rw [heff_eq] at h2le hsubS ⊢
              have hle_n : n ≤ u := by
                by_contra hlt_n
                push Not at hlt_n
                rw [singleSet_input C hlt_n] at h2le
                simp at h2le
              have hu_eq : n + (u - n) = u := by omega
              have huP : u - n ∈ privSet S C := by
                simp only [privSet, Finset.mem_filter, Finset.mem_range, hu_eq]
                exact ⟨by omega, hsubS, h2le⟩
              have huQ : u - n ∈ Q := by
                simp only [Q, Finset.mem_filter, hu_eq]
                exact ⟨huP, by simpa [effV, hult] using hsV⟩
              intro p hp q hq
              exact hconst (u - n) huQ (by omega) p (by rwa [hu_eq]) q (by rwa [hu_eq])
          have hc0 := hchild_const 0 htV.1 (by rw [hAt_eq] at hAt_sub; exact Finset.Subset.trans Finset.subset_union_left hAt_sub)
          have hc1 := hchild_const 1 htV.2 (by rw [hAt_eq] at hAt_sub; exact Finset.Subset.trans Finset.subset_union_right hAt_sub)
          by_cases hne0 : (effSingleSet C t (gateInput C t 0) : Finset (Fin n)).Nonempty
          · by_cases hne1 : (effSingleSet C t (gateInput C t 1) : Finset (Fin n)).Nonempty
            · obtain ⟨a, ha⟩ := hne0
              obtain ⟨b, hb⟩ := hne1
              let col' : Fin n → ℕ := fun p => if col p = col b then col a else col p
              have hcard' : S.card ≤ (S.image col').card + (Q.filter (· < t + 1)).card := by
                have hm : (S.image col).card ≤ (S.image col').card + 1 :=
                  card_image_merge S col (col a) (col b)
                omega
              refine ⟨col', hcard', ?_⟩
              intro j hjQ hjlt p hp q hq
              by_cases hjt : j = t
              · subst hjt
                rw [hAt_eq, Finset.mem_union] at hp hq
                have hmap : ∀ r, r ∈ effSingleSet C j (gateInput C j 0) ∨
                    r ∈ effSingleSet C j (gateInput C j 1) → col' r = col a := by
                  rintro r (hr0 | hr1)
                  · have hcol : col r = col a := hc0 r hr0 a ha
                    dsimp only [col']
                    rw [hcol]
                    split_ifs <;> rfl
                  · have hcol : col r = col b := hc1 r hr1 b hb
                    dsimp only [col']
                    simp [hcol]
                rw [hmap p hp, hmap q hq]
              · have hcol := hconst j hjQ (by omega) p hp q hq
                dsimp only [col']
                rw [hcol]
            · rw [Finset.not_nonempty_iff_eq_empty] at hne1
              refine ⟨col, by omega, ?_⟩
              intro j hjQ hjlt
              by_cases hjt : j = t
              · subst hjt
                rw [hAt_eq, hne1, Finset.union_empty]
                exact hc0
              · exact hconst j hjQ (by omega)
          · rw [Finset.not_nonempty_iff_eq_empty] at hne0
            refine ⟨col, by omega, ?_⟩
            intro j hjQ hjlt
            by_cases hjt : j = t
            · subst hjt
              rw [hAt_eq, hne0, Finset.empty_union]
              exact hc1
            · exact hconst j hjQ (by omega)
      · have hfilt_eq : Q.filter (· < t + 1) = Q.filter (· < t) := by
          ext x
          simp only [Finset.mem_filter]
          constructor
          · intro ⟨hxQ, hxlt⟩
            refine ⟨hxQ, ?_⟩
            have hne : x ≠ t := fun h => htQ (h ▸ hxQ)
            omega
          · intro ⟨hxQ, hxlt⟩
            exact ⟨hxQ, Nat.lt_succ_of_lt hxlt⟩
        refine ⟨col, by rwa [hfilt_eq], ?_⟩
        intro j hjQ hjlt
        have hne : j ≠ t := fun h => htQ (h ▸ hjQ)
        exact hconst j hjQ (by omega)
  obtain ⟨col, hcard, hconst⟩ := hstep C.size (le_refl _)
  have hj₀Q : j₀ ∈ Q := Finset.mem_filter.mpr ⟨hj₀, hV⟩
  have hj₀Size : j₀ < C.size := Finset.mem_range.mp (Finset.mem_filter.mp hj₀).1
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₀, hp₀⟩ := hSnonempty
  have himg : S.image col = {col p₀} := by
    ext y
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨p, hpS, rfl⟩
      exact hconst j₀ hj₀Q hj₀Size p (hS.symm ▸ hpS) p₀ (hS.symm ▸ hp₀)
    · rintro rfl
      exact ⟨p₀, hp₀, rfl⟩
  rw [himg, Finset.card_singleton] at hcard
  have hQle : (Q.filter (· < C.size)).card ≤ (privSet S C).card :=
    Finset.card_le_card (Finset.Subset.trans (Finset.filter_subset _ _) hQsub)
  omega

end PEqualNP.Outside.L_meta_278

theorem PEqualNP.Outside.L_meta_278 : ∀ (n k c o : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o false = true ↔ p ∈ S) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD o false = false) → c ≤ k → c + 1 ≤ S.card → c ≤ ((Finset.range C.size).filter (fun j => (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card)).card := by
  intro n k c o S C hC hSingle hZero hck hcS
  by_cases hc0 : c = 0
  · rw [hc0]
    exact Nat.zero_le _
  have hS2 : 2 ≤ S.card := by omega
  have hAo : (PEqualNP.Outside.L_meta_278.singleSet C o : Finset (Fin n)) = S := by
    ext p
    simp only [PEqualNP.Outside.L_meta_278.singleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hSingle p
  have ho_ge : n ≤ o := by
    by_contra hlt
    push Not at hlt
    rw [PEqualNP.Outside.L_meta_278.singleSet_input C hlt] at hAo
    rw [← hAo] at hS2
    simp at hS2
  have ho_lt : o < n + C.size := by
    by_contra hge
    push Not at hge
    rw [PEqualNP.Outside.L_meta_278.singleSet_ge C hge] at hAo
    rw [← hAo] at hS2
    simp at hS2
  let j₀ : ℕ := o - n
  have ho_eq : n + j₀ = o := by omega
  have hj₀ : j₀ ∈ PEqualNP.Outside.L_meta_278.privSet S C := by
    simp only [PEqualNP.Outside.L_meta_278.privSet, Finset.mem_filter, Finset.mem_range, ho_eq, hAo]
    exact ⟨by omega, Finset.Subset.refl S, hS2⟩
  change c ≤ (PEqualNP.Outside.L_meta_278.privSet S C).card
  cases hV : PEqualNP.Outside.L_meta_278.evalV S C (n + j₀)
  · exact PEqualNP.Outside.L_meta_278.case_evalV_false hC (by rw [ho_eq]; exact hAo) hcS hj₀ hV
  · exact PEqualNP.Outside.L_meta_278.case_evalV_true hC (by simpa [ho_eq] using hZero) hck hj₀ hV

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925

open PEqualNP.CircuitLowerBounds

-- Prefix wire lemmas are adapted from L-meta-614.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

theorem expandGate {n : ℕ} (C : Circuit)
    (hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (y : Fin n → Bool) (j : ℕ) (hj : n ≤ j) (hval : val C y j = true) :
    ∃ B : Finset ℕ, B.card ≤ 2 ∧ (∀ i ∈ B, val C y i = true ∧ i < j) ∧
      ∀ x : Fin n → Bool, (∀ i ∈ B, val C x i = true) → val C x j = true := by
  have htop : j < n + C.gates.length := by
    by_contra! hn
    rw [val_beyond C y hn] at hval
    contradiction
  obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n + p := ⟨j - n, by omega, by omega⟩
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
  obtain ⟨hkind, hsize⟩ := hops g (List.getElem_mem hp)
  rw [val_gate C y hg] at hval
  rcases hkind with ha | ho
  · have inputTrue (i : ℕ) (hi : i ∈ g.inputs) : val C y i = true ∧ i < n + p := by
      rw [ha, GateOp.eval, List.all_eq_true] at hval
      have ht := hval _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
      by_cases hn : i < n + p
      · exact ⟨by simpa [operand, hn] using ht, hn⟩
      · simp [operand, hn] at ht
    refine ⟨g.inputs.toFinset, (List.toFinset_card_le _).trans hsize, ?_, ?_⟩
    · intro i hi
      exact inputTrue i (List.mem_toFinset.mp hi)
    · intro x hx
      rw [val_gate C x hg, ha, GateOp.eval, List.all_eq_true]
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      simpa [operand, (inputTrue i hi).2] using hx i (List.mem_toFinset.mpr hi)
  · rw [ho, GateOp.eval, List.any_eq_true] at hval
    obtain ⟨_, hb, hTrue⟩ := hval
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hn : i < n + p := by
      by_contra h
      simp [operand, h] at hTrue
    refine ⟨{i}, by simp, ?_, ?_⟩
    · intro b hb
      rw [Finset.mem_singleton] at hb
      subst b
      exact ⟨by simpa [operand, hn] using hTrue, hn⟩
    · intro x hx
      rw [val_gate C x hg, ho, GateOp.eval, List.any_eq_true]
      exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, by simpa [operand, hn] using hx i (by simp)⟩

theorem val_mono {n : ℕ} (C : Circuit)
    (hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (y x : Fin n → Bool) (h : ∀ i, y i = true → x i = true) (j : ℕ)
    (hy : val C y j = true) : val C x j = true := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases hj : j < n
    · have hiy : y ⟨j, hj⟩ = true := by simpa only [val_input C y ⟨j, hj⟩] using hy
      simpa only [val_input C x ⟨j, hj⟩] using h _ hiy
    · obtain ⟨B, _, hB, hStep⟩ := expandGate C hops y j (by omega) hy
      exact hStep x (fun i hi => ih i (hB i hi).2 (hB i hi).1)

end PEqualNP.Outside.L_meta_925

namespace PEqualNP.Outside.L_meta_925.Frontier

/-- Expand a frontier through private wires, paying at most one new wire for each
private wire below the cutoff. The final wires jointly imply each original wire. -/
theorem compress {α : Type*} (valid privateWire : ℕ → Prop) [DecidablePred privateWire]
    (holds : α → ℕ → Prop)
    (expand : ∀ i : ℕ, privateWire i → valid i → ∃ B : Finset ℕ,
      B.card ≤ 2 ∧ (∀ j ∈ B, valid j ∧ j < i) ∧
        ∀ x, (∀ j ∈ B, holds x j) → holds x i)
    (k : ℕ) (F : Finset ℕ) (hvalid : ∀ i ∈ F, valid i)
    (hcut : ∀ i ∈ F, privateWire i → i < k) :
    ∃ R : Finset ℕ, (∀ j ∈ R, valid j ∧ ¬ privateWire j) ∧
      R.card ≤ F.card + ((Finset.range k).filter privateWire).card ∧
      ∀ x, (∀ j ∈ R, holds x j) → ∀ j ∈ F, holds x j := by
  induction k generalizing F with
  | zero =>
    refine ⟨F, ?_, by simp, fun _ h => h⟩
    intro j hj
    exact ⟨hvalid j hj, fun hp => (Nat.not_lt_zero _) (hcut j hj hp)⟩
  | succ k ih =>
    let cost : ℕ := ((Finset.range k).filter privateWire).card
    let costNext : ℕ := ((Finset.range (k+1)).filter privateWire).card
    have hCost : cost ≤ costNext := by
      apply Finset.card_le_card
      exact Finset.filter_subset_filter _ (Finset.range_mono (Nat.le_succ _))
    by_cases hTop : k ∈ F ∧ privateWire k
    · obtain ⟨hIn, hPriv⟩ := hTop
      have hCostNext : costNext = cost + 1 := by
        simp [cost, costNext, Finset.range_add_one, Finset.filter_insert, hPriv]
      obtain ⟨B, hBcard, hBval, hBholds⟩ := expand k hPriv (hvalid k hIn)
      let F' := F.erase k ∪ B
      have hValid' : ∀ i ∈ F', valid i := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact hvalid i (Finset.mem_of_mem_erase hi)
        · exact (hBval i hi).1
      have hCut' : ∀ i ∈ F', privateWire i → i < k := by
        intro i hi hp
        rcases Finset.mem_union.mp hi with hi | hi
        · have hb := hcut i (Finset.mem_of_mem_erase hi) hp
          have he := (Finset.mem_erase.mp hi).1
          omega
        · exact (hBval i hi).2
      obtain ⟨R, hR, hRc, hRh⟩ := ih F' hValid' hCut'
      have hF' : F'.card ≤ F.card + 1 := by
        have hUnion : F'.card ≤ (F.erase k).card + B.card :=
          Finset.card_union_le _ _
        have hErase : (F.erase k).card + 1 = F.card :=
          Finset.card_erase_add_one hIn
        omega
      change R.card ≤ F'.card + cost at hRc
      refine ⟨R, hR, ?_, ?_⟩
      · change R.card ≤ F.card + costNext
        omega
      · intro x hx j hj
        have hFx := hRh x hx
        by_cases he : j = k
        · subst j
          exact hBholds x (fun t ht => hFx t (Finset.mem_union_right _ ht))
        · exact hFx j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hj⟩))
    · have hCut' : ∀ i ∈ F, privateWire i → i < k := by
        intro i hi hp
        have hlt := hcut i hi hp
        have hne : i ≠ k := by
          rintro rfl
          exact hTop ⟨hi, hp⟩
        omega
      obtain ⟨R, hR, hRc, hRh⟩ := ih F hvalid hCut'
      change R.card ≤ F.card + cost at hRc
      refine ⟨R, hR, ?_, hRh⟩
      change R.card ≤ F.card + costNext
      omega

end PEqualNP.Outside.L_meta_925.Frontier

namespace PEqualNP.Outside.L_meta_925

def terminalUnion {α : Type*} [DecidableEq α] : List (Finset α) → Finset α
  | [] => ∅
  | T :: L => T ∪ terminalUnion L

theorem mem_terminalUnion {α : Type*} [DecidableEq α] (L : List (Finset α)) (a : α) :
    a ∈ terminalUnion L ↔ ∃ T ∈ L, a ∈ T := by
  induction L with
  | nil => simp [terminalUnion]
  | cons T L ih =>
    simp only [terminalUnion, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨U, hu, ha⟩)
      · exact ⟨T, Or.inl rfl, h⟩
      · exact ⟨U, Or.inr hu, ha⟩
    · rintro ⟨U, rfl | hu, ha⟩
      · exact Or.inl ha
      · exact Or.inr ⟨U, hu, ha⟩

private theorem card_terminalUnion_diff {α : Type*} [DecidableEq α]
    (q : ℕ) (R : Finset α) (L : List (Finset α))
    (hL : ∀ T ∈ L, (T \ R).card ≤ q) :
    (terminalUnion L \ R).card ≤ q * L.length := by
  induction L with
  | nil => simp [terminalUnion]
  | cons T L ih =>
    rw [terminalUnion, Finset.union_sdiff_distrib, List.length_cons, Nat.mul_succ]
    calc
      _ ≤ (T \ R).card + (terminalUnion L \ R).card := Finset.card_union_le _ _
      _ ≤ q + q * L.length := Nat.add_le_add (hL T (by simp))
        (ih (fun U hU => hL U (List.mem_cons_of_mem _ hU)))
      _ = _ := Nat.add_comm _ _

private theorem card_terminalUnion_inter {α : Type*} [DecidableEq α]
    (R : Finset α) (L : List (Finset α)) (hL : ∀ T ∈ L, (T ∩ R).card ≤ 1) :
    (terminalUnion L ∩ R).card ≤ L.length := by
  induction L with
  | nil => simp [terminalUnion]
  | cons T L ih =>
    rw [terminalUnion, Finset.union_inter_distrib_right, List.length_cons]
    calc
      _ ≤ (T ∩ R).card + (terminalUnion L ∩ R).card := Finset.card_union_le _ _
      _ ≤ 1 + L.length := Nat.add_le_add (hL T (by simp))
        (ih (fun U hU => hL U (List.mem_cons_of_mem _ hU)))
      _ = _ := Nat.add_comm _ _

theorem terminalUnion_bounds {α ι : Type*} [DecidableEq α] (q : ℕ)
    (S : ι → Finset α) (w : ι) (hq : 1 ≤ q)
    (hcard : ∀ i, (S i).card = q + 1)
    (hmeet : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (L : List (Finset α))
    (hL : ∀ T ∈ L, (∃ a ∈ S w, T = {a}) ∨ (∃ v, v ≠ w ∧ T = S v)) :
    (terminalUnion L).card ≤ q * L.length + 1 ∧
      (terminalUnion L ∩ S w).card ≤ L.length := by
  classical
  constructor
  · have diffBound (T : Finset α)
        (hT : (∃ a ∈ S w, T = {a}) ∨ (∃ v, v ≠ w ∧ T = S v))
        (i : ι) : (T \ S i).card ≤ q := by
      rcases hT with ⟨a, _, rfl⟩ | ⟨v, _, rfl⟩
      · exact (Finset.card_le_card Finset.sdiff_subset).trans (by simpa using hq)
      · by_cases hv : v = i
        · subst i
          simp
        · have h := Finset.card_sdiff_add_card_inter (S v) (S i)
          rw [hmeet v i hv, hcard] at h
          omega
    induction L with
    | nil => simp [terminalUnion]
    | cons T L ih =>
      have htail : ∀ U ∈ L, (∃ a ∈ S w, U = {a}) ∨ (∃ v, v ≠ w ∧ U = S v) :=
        fun U hu => hL U (List.mem_cons_of_mem _ hu)
      rcases hL T (by simp) with ⟨a, _, rfl⟩ | ⟨v, _, rfl⟩
      · rw [terminalUnion, List.length_cons, Nat.mul_succ]
        have hu := Finset.card_union_le ({a} : Finset α) (terminalUnion L)
        rw [Finset.card_singleton] at hu
        have hi := ih htail
        omega
      · have hd := card_terminalUnion_diff q (S v) L (fun U hu => diffBound U (htail U hu) v)
        rw [terminalUnion, List.length_cons, Nat.mul_succ, ← Finset.union_sdiff_self_eq_union]
        have hu := Finset.card_union_le (S v) (terminalUnion L \ S v)
        rw [hcard v] at hu
        omega
  · apply card_terminalUnion_inter
    intro T hT
    rcases hL T hT with ⟨a, _, rfl⟩ | ⟨v, hv, rfl⟩
    · exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton a)
    · rw [hmeet v w hv]

end PEqualNP.Outside.L_meta_925

namespace PEqualNP.Outside.L_meta_925.Frontier

open scoped BigOperators

/-- The private sets of different outputs are disjoint, so their local lower bounds add. -/
theorem total_private {m n g c : ℕ} (privateWire : Fin m → ℕ → Prop)
    [DecidableRel privateWire]
    (hgate : ∀ w i, privateWire w i → n ≤ i)
    (hUnique : ∀ i w v, privateWire w i → privateWire v i → w = v)
    (hLower : ∀ w, c ≤ ((Finset.range (n+g)).filter (privateWire w)).card) :
    m * c ≤ g := by
  classical
  let U := Finset.Ico n (n+g)
  let W (w : Fin m) := U.filter (privateWire w)
  have hE (w : Fin m) : W w = (Finset.range (n+g)).filter (privateWire w) := by
    ext i
    simp only [W, U, Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
    exact ⟨fun ⟨hi, hp⟩ => ⟨hi.2, hp⟩, fun ⟨hi, hp⟩ => ⟨⟨hgate w i hp, hi⟩, hp⟩⟩
  have hDisj : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint W := by
    intro w _ v _ hne
    apply Finset.disjoint_left.mpr
    intro i hw hv
    exact hne (hUnique i w v (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp hv).2)
  have hSub : (Finset.univ.biUnion W) ⊆ U := by
    intro i hi
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hw).1
  have hCard : U.card = g := by simp [U]
  calc
    m*c = ∑ w : Fin m, c := by simp
    _ ≤ ∑ w : Fin m, (W w).card := Finset.sum_le_sum fun w _ => by rw [hE]; exact hLower w
    _ = (Finset.univ.biUnion W).card := (Finset.card_biUnion hDisj).symm
    _ ≤ g := (Finset.card_le_card hSub).trans_eq hCard

end PEqualNP.Outside.L_meta_925.Frontier

namespace PEqualNP.Outside.L_meta_925

open PEqualNP.CircuitLowerBounds

private def point {n : ℕ} (A : Finset (Fin n)) (a : Fin n) : Bool := decide (a ∈ A)

private theorem point_card {n : ℕ} (A : Finset (Fin n)) :
    (Finset.univ.filter (fun i => point A i = true)).card = A.card := by
  congr 1
  ext i
  simp [point]

private def specific {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (w : Fin m) (j : ℕ) : Prop :=
  n ≤ j ∧ val C (point (S w)) j = true ∧ ∀ v, v ≠ w → val C (point (S v)) j = false

private theorem terminal {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (w : Fin m) (j : ℕ)
    (hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hv : val C (point (S w)) j = true) (hnp : ¬ specific C S w j) :
    ∃ A : Finset (Fin n),
      ((∃ a ∈ S w, A = {a}) ∨ ∃ v, v ≠ w ∧ A = S v) ∧
      ∀ U : Finset (Fin n), A ⊆ U → val C (point U) j = true := by
  by_cases hi : j < n
  · let a : Fin n := ⟨j, hi⟩
    have ha : a ∈ S w := by
      have e := val_input C (point (S w)) a
      simpa [a, e, point] using hv
    refine ⟨{a}, Or.inl ⟨a, ha, rfl⟩, ?_⟩
    intro U hU
    have hu : a ∈ U := hU (Finset.mem_singleton_self a)
    change val C (point U) a.val = true
    rw [val_input]
    exact decide_eq_true hu
  · have exists_other : ∃ v, v ≠ w ∧ val C (point (S v)) j = true := by
      by_contra! hno
      apply hnp
      exact ⟨by omega, hv, fun v hne => Bool.eq_false_iff.mpr (hno v hne)⟩
    obtain ⟨v, hvw, hval⟩ := exists_other
    refine ⟨S v, Or.inr ⟨v, hvw, rfl⟩, ?_⟩
    intro U hU
    exact val_mono C hops (point (S v)) (point U)
      (fun i hi => decide_eq_true (hU (of_decide_eq_true hi))) j hval

theorem prove (q n m K : ℕ) (S : Fin m → Finset (Fin n)) (hq : 2 ≤ q)
    (hcard : ∀ i : Fin m, (S i).card = q + 1)
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun i => x i = true)).card ≤ K →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true))
    (c : ℕ) (hc : c ≤ q) (hk : c * q < K) : m * c ≤ gates.length := by
  classical
  by_cases hc0 : c = 0
  · simp [hc0]
  let C : Circuit := ⟨gates, 0⟩
  let privateSet (w : Fin m) := (Finset.range (n + gates.length)).filter (specific C S w)
  have hline : q + 1 ≤ K := by
    have hp := Nat.mul_le_mul_right q (show 1 ≤ c by omega)
    simp only [one_mul] at hp
    omega
  have hbound : ∀ w : Fin m, c ≤ (privateSet w).card := by
    intro w
    by_contra! hbad
    have hroot : val C (point (S w)) (out w) = true := by
      have e := hcorrect w (point (S w)) (by rw [point_card, hcard]; exact hline)
      change val C (point (S w)) (out w) =
        decide (∀ v ∈ S w, point (S w) v = true) at e
      exact e.trans (decide_eq_true (fun v hv => decide_eq_true hv))
    have expand : ∀ i, specific C S w i → val C (point (S w)) i = true →
        ∃ B : Finset ℕ, B.card ≤ 2 ∧
          (∀ j ∈ B, val C (point (S w)) j = true ∧ j < i) ∧
          ∀ x : Fin n → Bool, (∀ j ∈ B, val C x j = true) → val C x i = true :=
      fun i hi hv => expandGate C hops (point (S w)) i hi.1 hv
    have hrange : out w < n + gates.length := by
      by_contra! hn
      exact Bool.noConfusion ((val_beyond C _ hn).symm.trans hroot)
    obtain ⟨R, hR, hsize, hforce⟩ := Frontier.compress
      (fun i => val C (point (S w)) i = true) (specific C S w)
      (fun x : Fin n → Bool => fun j => val C x j = true)
      expand (n + gates.length) ({out w} : Finset ℕ)
      (by simpa using hroot) (by simp [hrange])
    have hRsize : R.card ≤ c := by
      change R.card ≤ ({out w} : Finset ℕ).card + (privateSet w).card at hsize
      simp at hsize
      omega
    have hWitness : ∀ j ∈ R, ∃ A : Finset (Fin n),
        ((∃ a ∈ S w, A = {a}) ∨ ∃ v, v ≠ w ∧ A = S v) ∧
        ∀ U : Finset (Fin n), A ⊆ U → val C (point U) j = true := by
      intro j hj
      exact terminal C S w j hops (hR j hj).1 (hR j hj).2
    choose sites siteType siteTrue using hWitness
    let pieces := R.attach.toList.map (fun i => sites i.val i.property)
    let U := terminalUnion pieces
    have hPieces : ∀ T ∈ pieces, (∃ a ∈ S w, T = {a}) ∨ ∃ v, v ≠ w ∧ T = S v := by
      intro T hT
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hT
      exact siteType j.val j.property
    obtain ⟨hUcard, hUint⟩ := terminalUnion_bounds q S w (by omega) hcard hmeet pieces hPieces
    have hlength : pieces.length = R.card := by simp [pieces]
    rw [hlength] at hUcard hUint
    have hLight : U.card ≤ K := by
      have hmul := Nat.mul_le_mul_left q hRsize
      rw [Nat.mul_comm q c] at hmul
      change U.card ≤ q * R.card + 1 at hUcard
      omega
    have hmiss : ¬ S w ⊆ U := by
      intro hsub
      have hsub' : S w ⊆ U ∩ S w := fun a ha => Finset.mem_inter.2 ⟨hsub ha, ha⟩
      have := Finset.card_le_card hsub'
      rw [hcard] at this
      change (U ∩ S w).card ≤ R.card at hUint
      omega
    have hval : val C (point U) (out w) = true := by
      apply hforce (point U) _ _ (Finset.mem_singleton_self _)
      intro j hj
      apply siteTrue j hj U
      intro a ha
      apply (mem_terminalUnion pieces a).2
      exact ⟨sites j hj, List.mem_map.2 ⟨⟨j, hj⟩, by simp, rfl⟩, ha⟩
    have he := hcorrect w (point U) (by rwa [point_card])
    change val C (point U) (out w) = decide (∀ v ∈ S w, point U v = true) at he
    rw [hval, eq_comm, decide_eq_true_eq] at he
    exact hmiss (fun v hv => of_decide_eq_true (he v hv))
  refine Frontier.total_private (specific C S) (fun w i hp => hp.1) ?_ hbound
  intro i w v hw hv
  by_contra hn
  exact Bool.noConfusion ((hw.2.2 v (fun he => hn he.symm)).symm.trans hv.2.1)

end PEqualNP.Outside.L_meta_925

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length :=
  PEqualNP.Outside.L_meta_925.prove

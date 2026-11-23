import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_667

open Finset PEqualNP.CircuitLowerBounds

def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

lemma line_card (w : Fin 13) : (line w).card = 4 := by
  revert w
  decide

lemma line_inter (w1 w2 : Fin 13) (h : w1 ≠ w2) : (line w1 ∩ line w2).card ≤ 1 := by
  revert w1 w2 h
  decide

def credit (s : Finset (Fin 13)) (w : Fin 13) : ℕ :=
  if s ⊆ line w ∧ 2 ≤ s.card then 2
  else if line w ⊆ s ∧ s.card ≤ 6 then 2
  else if line w ⊆ s ∧ s.card = 7 then 1
  else 0

lemma line_union_card {w1 w2 : Fin 13} (h : w1 ≠ w2) :
    7 ≤ (line w1 ∪ line w2).card := by
  have h1 := card_union_add_card_inter (line w1) (line w2)
  have h2 := line_card w1
  have h3 := line_card w2
  have h4 := line_inter w1 w2 h
  omega

lemma capacity (s : Finset (Fin 13)) : ∑ w : Fin 13, credit s w ≤ 2 := by
  by_cases hsub : ∃ w0 : Fin 13, s ⊆ line w0 ∧ 2 ≤ s.card
  · obtain ⟨w0, hs0, hcard⟩ := hsub
    have hzero : ∀ w : Fin 13, w ≠ w0 → credit s w = 0 := by
      intro w hne
      have hns : ¬ (s ⊆ line w ∧ 2 ≤ s.card) := by
        rintro ⟨hsw, _⟩
        have hle : s.card ≤ (line w ∩ line w0).card :=
          card_le_card (subset_inter hsw hs0)
        have hi := line_inter w w0 hne
        omega
      have hnl : ¬ (line w ⊆ s) := by
        intro hws
        have hle : (line w).card ≤ (line w ∩ line w0).card :=
          card_le_card (subset_inter Subset.rfl (hws.trans hs0))
        have hc := line_card w
        have hi := line_inter w w0 hne
        omega
      simp [credit, hns, hnl]
    rw [Finset.sum_eq_single w0 (fun w _ hne => hzero w hne) (by simp)]
    simp [credit, hs0, hcard]
  · have hns : ∀ w : Fin 13, ¬ (s ⊆ line w ∧ 2 ≤ s.card) := fun w hw => hsub ⟨w, hw⟩
    by_cases hc6 : s.card ≤ 6
    · by_cases hex : ∃ w0 : Fin 13, line w0 ⊆ s
      · obtain ⟨w0, hw0⟩ := hex
        have hzero : ∀ w : Fin 13, w ≠ w0 → credit s w = 0 := by
          intro w hne
          have hnl : ¬ (line w ⊆ s) := by
            intro hws
            have hle : (line w ∪ line w0).card ≤ s.card :=
              card_le_card (union_subset hws hw0)
            have hu := line_union_card hne
            omega
          simp [credit, hns w, hnl]
        rw [Finset.sum_eq_single w0 (fun w _ hne => hzero w hne) (by simp)]
        simp [credit, hns w0, hw0, hc6]
      · have hzero : ∀ w : Fin 13, credit s w = 0 := by
          intro w
          have hnl : ¬ (line w ⊆ s) := fun h => hex ⟨w, h⟩
          simp [credit, hns w, hnl]
        simp [hzero]
    · by_cases hc7 : s.card = 7
      · let T : Finset (Fin 13) := Finset.univ.filter (fun w => line w ⊆ s)
        have hsum : ∑ w : Fin 13, credit s w = T.card := by
          have h1 : ∀ w : Fin 13, credit s w = if line w ⊆ s then 1 else 0 := by
            intro w
            have hnsub : ¬ s ⊆ line w := fun h => hns w ⟨h, by omega⟩
            simp [credit, hnsub, hc7]
          simp [h1, T]
        rw [hsum]
        by_contra hgt
        have h3 : 2 < T.card := by omega
        rw [Finset.two_lt_card] at h3
        obtain ⟨w1, hw1, w2, hw2, w3, hw3, h12, h13, h23⟩ := h3
        have hs1 : line w1 ⊆ s := (mem_filter.mp hw1).2
        have hs2 : line w2 ⊆ s := (mem_filter.mp hw2).2
        have hs3 : line w3 ⊆ s := (mem_filter.mp hw3).2
        have heq : line w1 ∪ line w2 = s := by
          apply eq_of_subset_of_card_le (union_subset hs1 hs2)
          have hu := line_union_card h12
          omega
        have hsub3 : line w3 ⊆ (line w3 ∩ line w1) ∪ (line w3 ∩ line w2) := by
          intro p hp
          have hpm : p ∈ line w1 ∪ line w2 := heq ▸ hs3 hp
          rcases mem_union.mp hpm with h1 | h2
          · exact mem_union_left _ (mem_inter.mpr ⟨hp, h1⟩)
          · exact mem_union_right _ (mem_inter.mpr ⟨hp, h2⟩)
        have hle := (card_le_card hsub3).trans (card_union_le _ _)
        have hc3 := line_card w3
        have hi1 := line_inter w3 w1 h13.symm
        have hi2 := line_inter w3 w2 h23.symm
        omega
      · have hzero : ∀ w : Fin 13, credit s w = 0 := by
          intro w
          simp [credit, hns w, hc6, hc7]
        simp [hzero]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def read (v : ℕ → Bool) (j i : ℕ) : Bool :=
  if i < j then v i else false

def evalG (g : Gate) (v : ℕ → Bool) : Bool :=
  g.op.eval (g.inputs.map v)

def defaultGate : Gate := ⟨GateOp.or, []⟩

lemma fold_spec (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length ∧
    (∀ i < w.length, (gs.foldl step w).getD i false = w.getD i false) ∧
    ∀ j < gs.length, (gs.foldl step w).getD (w.length + j) false =
      evalG (gs.getD j defaultGate)
        (read (fun a => (gs.foldl step w).getD a false) (w.length + j)) := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨h1, h2, h3⟩ := ih (step w g)
    have hl : (step w g).length = w.length + 1 := by simp [step]
    simp only [List.foldl_cons]
    refine ⟨by rw [h1, hl]; simp; omega, ?_, ?_⟩
    · intro i hi
      rw [h2 i (by omega)]
      exact List.getD_append _ _ _ _ hi
    · intro j hj
      cases j with
      | zero =>
        rw [Nat.add_zero, h2 _ (by omega)]
        have hv : (step w g).getD w.length false = evalG g (fun a => w.getD a false) := by
          simp [step, evalG]
        rw [hv, List.getD_cons_zero]
        unfold evalG
        congr 1
        apply List.map_congr_left
        intro a _
        unfold read
        split_ifs with ha
        · change w.getD a false = (gs.foldl step (step w g)).getD a false
          rw [h2 a (by omega)]
          exact (List.getD_append _ _ _ _ ha).symm
        · exact List.getD_eq_default _ _ (by omega)
      | succ j =>
        have h := h3 j (by simp at hj; omega)
        rw [hl] at h
        rw [List.getD_cons_succ, show w.length + (j + 1) = w.length + 1 + j by omega]
        exact h

def value (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD w false

def gateAt (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - 13) defaultGate

def Legal (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma value_eq_eval (gs : List Gate) (o : ℕ) (x : Fin 13 → Bool) :
    value gs x o = Circuit.eval ⟨gs, o⟩ (List.ofFn x) := rfl

lemma value_input (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) (hw : w < 13) :
    value gs x w = x ⟨w, hw⟩ := by
  unfold value
  rw [(fold_spec gs (List.ofFn x)).2.1 w (by rw [List.length_ofFn]; exact hw)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hw]

lemma value_missing (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) (hw : 13 + gs.length ≤ w) :
    value gs x w = false := by
  unfold value
  apply List.getD_eq_default
  rw [(fold_spec gs (List.ofFn x)).1, List.length_ofFn]
  exact hw

lemma value_gate (gs : List Gate) (x : Fin 13 → Bool) {w : ℕ}
    (h1 : 13 ≤ w) (h2 : w < 13 + gs.length) :
    value gs x w = evalG (gateAt gs w) (read (value gs x) w) := by
  have h := (fold_spec gs (List.ofFn x)).2.2 (w - 13) (by omega)
  rw [List.length_ofFn, show 13 + (w - 13) = w by omega] at h
  exact h

lemma gateAt_legal (gs : List Gate) (hL : Legal gs) {w : ℕ}
    (h1 : 13 ≤ w) (h2 : w < 13 + gs.length) :
    ((gateAt gs w).op = GateOp.and ∨ (gateAt gs w).op = GateOp.or) ∧
      (gateAt gs w).inputs.length ≤ 2 := by
  apply hL
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

lemma all_mono (l : List ℕ) (u v : ℕ → Bool) (h : ∀ a ∈ l, u a ≤ v a) :
    (l.map u).all id ≤ (l.map v).all id := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id_eq]
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    cases h1 : u a <;> cases h2 : v a <;> cases h3 : (l.map u).all id <;>
      cases h4 : (l.map v).all id <;> simp_all

lemma any_mono (l : List ℕ) (u v : ℕ → Bool) (h : ∀ a ∈ l, u a ≤ v a) :
    (l.map u).any id ≤ (l.map v).any id := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    cases h1 : u a <;> cases h2 : v a <;> cases h3 : (l.map u).any id <;>
      cases h4 : (l.map v).any id <;> simp_all

lemma value_mono (gs : List Gate) (hL : Legal gs) {x y : Fin 13 → Bool}
    (hxy : ∀ p : Fin 13, x p ≤ y p) (w : ℕ) : value gs x w ≤ value gs y w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hin : w < 13
    · rw [value_input gs x w hin, value_input gs y w hin]
      exact hxy ⟨w, hin⟩
    by_cases hout : 13 + gs.length ≤ w
    · rw [value_missing gs x w hout, value_missing gs y w hout]
    have h1 : 13 ≤ w := by omega
    have h2 : w < 13 + gs.length := by omega
    rw [value_gate gs x h1 h2, value_gate gs y h1 h2]
    obtain ⟨hop, _⟩ := gateAt_legal gs hL h1 h2
    have hread : ∀ a ∈ (gateAt gs w).inputs, read (value gs x) w a ≤ read (value gs y) w a := by
      intro a _
      unfold read
      split_ifs with ha
      · exact ih a ha
      · exact le_rfl
    unfold evalG
    rcases hop with hop | hop <;> rw [hop]
    · exact all_mono _ _ _ hread
    · exact any_mono _ _ _ hread

lemma gate_cases (gs : List Gate) (hL : Legal gs) {w : ℕ}
    (h1 : 13 ≤ w) (h2 : w < 13 + gs.length) :
    (∀ x, value gs x w = false) ∨
    (∀ x, value gs x w = true) ∨
    (∃ a < w, ∀ x, value gs x w = value gs x a) ∨
    (∃ a < w, ∃ b < w, ∀ x, value gs x w = (value gs x a || value gs x b)) ∨
    (∃ a < w, ∃ b < w, ∀ x, value gs x w = (value gs x a && value gs x b)) := by
  obtain ⟨hop, hlen⟩ := gateAt_legal gs hL h1 h2
  have hv : ∀ x, value gs x w = (gateAt gs w).op.eval ((gateAt gs w).inputs.map (read (value gs x) w)) :=
    fun x => value_gate gs x h1 h2
  cases hin : (gateAt gs w).inputs with
  | nil =>
    rcases hop with hop | hop
    · right; left; intro x; simp [hv x, hop, hin, GateOp.eval]
    · left; intro x; simp [hv x, hop, hin, GateOp.eval]
  | cons a l =>
    cases l with
    | nil =>
      by_cases ha : a < w
      · right; right; left; refine ⟨a, ha, fun x => ?_⟩
        rcases hop with hop | hop <;> simp [hv x, hop, hin, GateOp.eval, read, ha]
      · left; intro x
        rcases hop with hop | hop <;> simp [hv x, hop, hin, GateOp.eval, read, ha]
    | cons b l =>
      cases l with
      | cons c l =>
        rw [hin] at hlen
        simp at hlen
      | nil =>
        rcases hop with hop | hop
        · by_cases ha : a < w
          · by_cases hb : b < w
            · right; right; right; right; refine ⟨a, ha, b, hb, fun x => ?_⟩
              simp [hv x, hop, hin, GateOp.eval, read, ha, hb]
            · left; intro x
              simp [hv x, hop, hin, GateOp.eval, read, ha, hb]
          · left; intro x
            simp [hv x, hop, hin, GateOp.eval, read, ha]
        · by_cases ha : a < w
          · by_cases hb : b < w
            · right; right; right; left; refine ⟨a, ha, b, hb, fun x => ?_⟩
              simp [hv x, hop, hin, GateOp.eval, read, ha, hb]
            · right; right; left; refine ⟨a, ha, fun x => ?_⟩
              simp [hv x, hop, hin, GateOp.eval, read, ha, hb]
          · by_cases hb : b < w
            · right; right; left; refine ⟨b, hb, fun x => ?_⟩
              simp [hv x, hop, hin, GateOp.eval, read, ha, hb]
            · left; intro x
              simp [hv x, hop, hin, GateOp.eval, read, ha, hb]

def single (p : Fin 13) : Fin 13 → Bool := fun q => decide (q = p)

def pair (p q : Fin 13) : Fin 13 → Bool := fun r => decide (r = p ∨ r = q)

def support (gs : List Gate) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => value gs (single p) w = true)

lemma mem_support (gs : List Gate) (w : ℕ) (p : Fin 13) :
    p ∈ support gs w ↔ value gs (single p) w = true := by
  simp [support]

lemma valid_of_card (gs : List Gate) (w : ℕ) (hw : 2 ≤ (support gs w).card) :
    13 ≤ w ∧ w < 13 + gs.length := by
  constructor
  · by_contra hlt
    have hlt' : w < 13 := by omega
    have he : support gs w = {⟨w, hlt'⟩} := by
      ext p
      rw [mem_support, value_input gs (single p) w hlt', mem_singleton]
      simp [single, eq_comm]
    simp [he] at hw
  · by_contra hge
    have hge' : 13 + gs.length ≤ w := by omega
    have he : support gs w = ∅ := by
      ext p
      rw [mem_support, value_missing gs (single p) w hge']
      simp
    simp [he] at hw

lemma pair_true_left (gs : List Gate) (hL : Legal gs) (w : ℕ) {p q : Fin 13}
    (hp : p ∈ support gs w) : value gs (pair p q) w = true := by
  have hm : ∀ r : Fin 13, single p r ≤ pair p q r := by
    intro r
    by_cases h : r = p <;> simp [single, pair, h]
  have hle := value_mono gs hL hm w
  rw [(mem_support gs w p).mp hp] at hle
  cases hv : value gs (pair p q) w
  · rw [hv] at hle; exact False.elim ((by decide : ¬ (true ≤ false)) hle)
  · rfl

lemma pair_true_right (gs : List Gate) (hL : Legal gs) (w : ℕ) {p q : Fin 13}
    (hq : q ∈ support gs w) : value gs (pair p q) w = true := by
  have hm : ∀ r : Fin 13, single q r ≤ pair p q r := by
    intro r
    by_cases h : r = q <;> simp [single, pair, h]
  have hle := value_mono gs hL hm w
  rw [(mem_support gs w q).mp hq] at hle
  cases hv : value gs (pair p q) w
  · rw [hv] at hle; exact False.elim ((by decide : ¬ (true ≤ false)) hle)
  · rfl

def privSet (gs : List Gate) (S : Finset (Fin 13)) : Finset ℕ :=
  (Finset.Ico 13 (13 + gs.length)).filter (fun i => support gs i ⊆ S ∧ 2 ≤ (support gs i).card)

lemma mem_privSet (gs : List Gate) (S : Finset (Fin 13)) (i : ℕ) :
    i ∈ privSet gs S ↔ support gs i ⊆ S ∧ 2 ≤ (support gs i).card := by
  unfold privSet
  rw [mem_filter, mem_Ico]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨valid_of_card gs i h.2, h⟩

lemma no_priv_below (gs : List Gate) (hL : Legal gs) (S : Finset (Fin 13)) (hScard : S.card = 4)
    (u : ℕ) (hsub : support gs u ⊆ S) (hcard : 3 ≤ (support gs u).card)
    (hpair : ∀ q1 q2 : Fin 13, q1 ∉ S → q2 ∉ S → value gs (pair q1 q2) u = false)
    (hno : ∀ c < u, c ∉ privSet gs S) : False := by
  obtain ⟨h1, h2⟩ := valid_of_card gs u (by omega)
  rcases gate_cases gs hL h1 h2 with hf | ht | ⟨a, ha, hua⟩ | ⟨a, ha, b, hb, huab⟩ | ⟨a, ha, b, hb, huab⟩
  · have he : support gs u = ∅ := by
      ext p; simp [mem_support, hf]
    rw [he] at hcard; simp at hcard
  · have he : support gs u = Finset.univ := by
      ext p; simp [mem_support, ht]
    have hle := card_le_card (he ▸ hsub)
    simp [hScard] at hle
  · have hsup : support gs a = support gs u := by
      ext p; simp [mem_support, hua]
    exact hno a ha ((mem_privSet gs S a).mpr ⟨hsup ▸ hsub, by rw [hsup]; omega⟩)
  · have hsup : support gs u = support gs a ∪ support gs b := by
      ext p; simp [mem_support, huab]
    have hsa : support gs a ⊆ S := (hsup ▸ subset_union_left).trans hsub
    have hsb : support gs b ⊆ S := (hsup ▸ subset_union_right).trans hsub
    have hca : (support gs a).card ≤ 1 := by
      by_contra h
      exact hno a ha ((mem_privSet gs S a).mpr ⟨hsa, by omega⟩)
    have hcb : (support gs b).card ≤ 1 := by
      by_contra h
      exact hno b hb ((mem_privSet gs S b).mpr ⟨hsb, by omega⟩)
    have hle := card_union_le (support gs a) (support gs b)
    rw [← hsup] at hle
    omega
  · have hsup : support gs u = support gs a ∩ support gs b := by
      ext p; simp [mem_support, huab]
    have hca : 3 ≤ (support gs a).card :=
      hcard.trans (card_le_card (hsup ▸ inter_subset_left))
    have hcb : 3 ≤ (support gs b).card :=
      hcard.trans (card_le_card (hsup ▸ inter_subset_right))
    have hnsa : ¬ support gs a ⊆ S := fun h => hno a ha ((mem_privSet gs S a).mpr ⟨h, by omega⟩)
    have hnsb : ¬ support gs b ⊆ S := fun h => hno b hb ((mem_privSet gs S b).mpr ⟨h, by omega⟩)
    obtain ⟨q1, hq1a, hq1S⟩ := Finset.not_subset.mp hnsa
    obtain ⟨q2, hq2b, hq2S⟩ := Finset.not_subset.mp hnsb
    have hv1 := pair_true_left gs hL a (q := q2) hq1a
    have hv2 := pair_true_right gs hL b (p := q1) hq2b
    have hvu := huab (pair q1 q2)
    rw [hv1, hv2, hpair q1 q2 hq1S hq2S] at hvu
    simp at hvu

lemma extra_credit (w : Fin 13) (s1 s2 s3 : Finset (Fin 13))
    (h1 : line w ⊆ s1) (h2 : line w ⊆ s2) (h3 : line w ⊆ s3)
    (hc1 : 5 ≤ s1.card) (hc2 : 5 ≤ s2.card) (hc3 : 5 ≤ s3.card)
    (hsum : s1.card + s2.card + s3.card ≤ 21) :
    2 ≤ credit s1 w + credit s2 w + credit s3 w := by
  have hns : ∀ s : Finset (Fin 13), 5 ≤ s.card → ¬ s ⊆ line w := by
    intro s hs hsub
    have hle := card_le_card hsub
    rw [line_card] at hle
    omega
  by_cases k1 : s1.card ≤ 6
  · have : credit s1 w = 2 := by simp [credit, hns s1 hc1, h1, k1]
    omega
  by_cases k2 : s2.card ≤ 6
  · have : credit s2 w = 2 := by simp [credit, hns s2 hc2, h2, k2]
    omega
  by_cases k3 : s3.card ≤ 6
  · have : credit s3 w = 2 := by simp [credit, hns s3 hc3, h3, k3]
    omega
  have e1 : s1.card = 7 := by omega
  have e2 : s2.card = 7 := by omega
  have e3 : s3.card = 7 := by omega
  have c1 : credit s1 w = 1 := by simp [credit, hns s1 hc1, h1, e1]
  have c2 : credit s2 w = 1 := by simp [credit, hns s2 hc2, h2, e2]
  have c3 : credit s3 w = 1 := by simp [credit, hns s3 hc3, h3, e3]
  omega

lemma and_chain_demand (gs : List Gate) (hL : Legal gs) (w : Fin 13)
    (o a b : ℕ)
    (ho : support gs o = line w)
    (haP : a ∈ privSet gs (line w)) (ha_lt : a < o)
    (hbnot : b ∉ privSet gs (line w))
    (ho_eq : ∀ x, value gs x o = (value gs x a && value gs x b))
    (hpair : ∀ q1 q2 : Fin 13, q1 ∉ line w → q2 ∉ line w → value gs (pair q1 q2) o = false)
    (hno : ∀ c < a, c ∉ privSet gs (line w)) :
    6 ≤ ∑ i ∈ Finset.Ico 13 (13 + gs.length), credit (support gs i) w := by
  let S := line w
  have hScard : S.card = 4 := line_card w
  have hsup_o : support gs o = support gs a ∩ support gs b := by
    ext p; simp [mem_support, ho_eq]
  have hSa : S ⊆ support gs a := by
    dsimp only [S]; rw [← ho, hsup_o]; exact inter_subset_left
  have hSb : S ⊆ support gs b := by
    dsimp only [S]; rw [← ho, hsup_o]; exact inter_subset_right
  have ha_sub : support gs a ⊆ S := ((mem_privSet gs S a).mp haP).1
  have ha_eq : support gs a = S := Subset.antisymm ha_sub hSa
  have hnbS : ¬ support gs b ⊆ S := by
    intro h
    have hcb : 2 ≤ (support gs b).card := by
      have := card_le_card hSb; omega
    exact hbnot ((mem_privSet gs S b).mpr ⟨h, hcb⟩)
  obtain ⟨h1a, h2a⟩ := valid_of_card gs a (by rw [ha_eq, hScard]; omega)
  rcases gate_cases gs hL h1a h2a with hf | ht | ⟨c, hc, hac⟩ | ⟨c, hc, d, hd, hacd⟩ | ⟨c, hc, d, hd, hacd⟩
  · have he : support gs a = ∅ := by ext p; simp [mem_support, hf]
    rw [ha_eq] at he; rw [he] at hScard; simp at hScard
  · have he : support gs a = Finset.univ := by ext p; simp [mem_support, ht]
    rw [ha_eq] at he; rw [he] at hScard; simp at hScard
  · have hsup : support gs c = S := by
      rw [← ha_eq]; ext p; simp [mem_support, hac]
    exact (hno c hc ((mem_privSet gs S c).mpr ⟨hsup ▸ Subset.rfl, by rw [hsup, hScard]; omega⟩)).elim
  · have hsup : S = support gs c ∪ support gs d := by
      rw [← ha_eq]; ext p; simp [mem_support, hacd]
    have hsc : support gs c ⊆ S := hsup ▸ subset_union_left
    have hsd : support gs d ⊆ S := hsup ▸ subset_union_right
    have hcc : (support gs c).card ≤ 1 := by
      by_contra h; exact hno c hc ((mem_privSet gs S c).mpr ⟨hsc, by omega⟩)
    have hcd : (support gs d).card ≤ 1 := by
      by_contra h; exact hno d hd ((mem_privSet gs S d).mpr ⟨hsd, by omega⟩)
    have hle := card_union_le (support gs c) (support gs d)
    rw [← hsup, hScard] at hle
    omega
  · have hsup_a : S = support gs c ∩ support gs d := by
      rw [← ha_eq]; ext p; simp [mem_support, hacd]
    have hSc : S ⊆ support gs c := hsup_a ▸ inter_subset_left
    have hSd : S ⊆ support gs d := hsup_a ▸ inter_subset_right
    have hncS : ¬ support gs c ⊆ S := by
      intro h
      have hcc : 2 ≤ (support gs c).card := by have := card_le_card hSc; omega
      exact hno c hc ((mem_privSet gs S c).mpr ⟨h, hcc⟩)
    have hndS : ¬ support gs d ⊆ S := by
      intro h
      have hcd : 2 ≤ (support gs d).card := by have := card_le_card hSd; omega
      exact hno d hd ((mem_privSet gs S d).mpr ⟨h, hcd⟩)
    let Ab := support gs b \ S
    let Ac := support gs c \ S
    let Ad := support gs d \ S
    have hAb_ne : Ab.Nonempty := by
      obtain ⟨q, hqb, hqS⟩ := Finset.not_subset.mp hnbS
      exact ⟨q, mem_sdiff.mpr ⟨hqb, hqS⟩⟩
    have hAc_ne : Ac.Nonempty := by
      obtain ⟨q, hqc, hqS⟩ := Finset.not_subset.mp hncS
      exact ⟨q, mem_sdiff.mpr ⟨hqc, hqS⟩⟩
    have hAd_ne : Ad.Nonempty := by
      obtain ⟨q, hqd, hqS⟩ := Finset.not_subset.mp hndS
      exact ⟨q, mem_sdiff.mpr ⟨hqd, hqS⟩⟩
    have hdisj_bc : Disjoint Ab Ac := by
      rw [Finset.disjoint_left]
      intro q hqb hqc
      obtain ⟨r, hr⟩ := hAd_ne
      obtain ⟨hqb', hqS⟩ := mem_sdiff.mp hqb
      obtain ⟨hqc', _⟩ := mem_sdiff.mp hqc
      obtain ⟨hrd', hrS⟩ := mem_sdiff.mp hr
      have hb1 := pair_true_left gs hL b (q := r) hqb'
      have hc1 := pair_true_left gs hL c (q := r) hqc'
      have hd1 := pair_true_right gs hL d (p := q) hrd'
      have hvo := ho_eq (pair q r)
      rw [hacd (pair q r), hb1, hc1, hd1, hpair q r hqS hrS] at hvo
      simp at hvo
    have hdisj_bd : Disjoint Ab Ad := by
      rw [Finset.disjoint_left]
      intro q hqb hqd
      obtain ⟨r, hr⟩ := hAc_ne
      obtain ⟨hqb', hqS⟩ := mem_sdiff.mp hqb
      obtain ⟨hqd', _⟩ := mem_sdiff.mp hqd
      obtain ⟨hrc', hrS⟩ := mem_sdiff.mp hr
      have hb1 := pair_true_left gs hL b (q := r) hqb'
      have hd1 := pair_true_left gs hL d (q := r) hqd'
      have hc1 := pair_true_right gs hL c (p := q) hrc'
      have hvo := ho_eq (pair q r)
      rw [hacd (pair q r), hb1, hc1, hd1, hpair q r hqS hrS] at hvo
      simp at hvo
    have hdisj_cd : Disjoint Ac Ad := by
      rw [Finset.disjoint_left]
      intro q hqc hqd
      obtain ⟨r, hr⟩ := hAb_ne
      obtain ⟨hqc', hqS⟩ := mem_sdiff.mp hqc
      obtain ⟨hqd', _⟩ := mem_sdiff.mp hqd
      obtain ⟨hrb', hrS⟩ := mem_sdiff.mp hr
      have hc1 := pair_true_left gs hL c (q := r) hqc'
      have hd1 := pair_true_left gs hL d (q := r) hqd'
      have hb1 := pair_true_right gs hL b (p := q) hrb'
      have hvo := ho_eq (pair q r)
      rw [hacd (pair q r), hb1, hc1, hd1, hpair q r hqS hrS] at hvo
      simp at hvo
    have hcard_b : (support gs b).card = 4 + Ab.card := by
      have h1 := card_sdiff_add_card_eq_card hSb
      change Ab.card + S.card = (support gs b).card at h1
      omega
    have hcard_c : (support gs c).card = 4 + Ac.card := by
      have h1 := card_sdiff_add_card_eq_card hSc
      change Ac.card + S.card = (support gs c).card at h1
      omega
    have hcard_d : (support gs d).card = 4 + Ad.card := by
      have h1 := card_sdiff_add_card_eq_card hSd
      change Ad.card + S.card = (support gs d).card at h1
      omega
    have hAb_pos : 1 ≤ Ab.card := card_pos.mpr hAb_ne
    have hAc_pos : 1 ≤ Ac.card := card_pos.mpr hAc_ne
    have hAd_pos : 1 ≤ Ad.card := card_pos.mpr hAd_ne
    have hsum_A : Ab.card + Ac.card + Ad.card ≤ 9 := by
      have hsubU : Ab ∪ Ac ∪ Ad ⊆ Finset.univ \ S := by
        intro p hp
        rcases mem_union.mp hp with hp1 | hpd
        · rcases mem_union.mp hp1 with hpb | hpc
          · exact mem_sdiff.mpr ⟨mem_univ p, (mem_sdiff.mp hpb).2⟩
          · exact mem_sdiff.mpr ⟨mem_univ p, (mem_sdiff.mp hpc).2⟩
        · exact mem_sdiff.mpr ⟨mem_univ p, (mem_sdiff.mp hpd).2⟩
      have hUcard : (Ab ∪ Ac ∪ Ad).card = Ab.card + Ac.card + Ad.card := by
        rw [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj_bd, hdisj_cd⟩),
          card_union_of_disjoint hdisj_bc]
      have hle := card_le_card hsubU
      have hcomp := card_sdiff_add_card_eq_card (subset_univ S)
      rw [card_univ, Fintype.card_fin, hScard] at hcomp
      omega
    have hextra := extra_credit w (support gs b) (support gs c) (support gs d)
      hSb hSc hSd (by omega) (by omega) (by omega) (by omega)
    have hne_oa : o ≠ a := by omega
    have hne_ob : o ≠ b := fun h => hnbS (h ▸ ho ▸ Subset.rfl)
    have hne_oc : o ≠ c := fun h => hncS (h ▸ ho ▸ Subset.rfl)
    have hne_od : o ≠ d := fun h => hndS (h ▸ ho ▸ Subset.rfl)
    have hne_ab : a ≠ b := fun h => hnbS (h ▸ ha_eq ▸ Subset.rfl)
    have hne_ac : a ≠ c := fun h => hncS (h ▸ ha_eq ▸ Subset.rfl)
    have hne_ad : a ≠ d := fun h => hndS (h ▸ ha_eq ▸ Subset.rfl)
    have hne_bc : b ≠ c := by
      intro h
      obtain ⟨q, hq⟩ := hAb_ne
      exact Finset.disjoint_left.mp hdisj_bc hq (by simpa [Ab, Ac, h] using hq)
    have hne_bd : b ≠ d := by
      intro h
      obtain ⟨q, hq⟩ := hAb_ne
      exact Finset.disjoint_left.mp hdisj_bd hq (by simpa [Ab, Ad, h] using hq)
    have hne_cd : c ≠ d := by
      intro h
      obtain ⟨q, hq⟩ := hAc_ne
      exact Finset.disjoint_left.mp hdisj_cd hq (by simpa [Ac, Ad, h] using hq)
    let F : Finset ℕ := {o, a, b, c, d}
    have hFsub : F ⊆ Finset.Ico 13 (13 + gs.length) := by
      intro i hi
      simp only [F, mem_insert, mem_singleton] at hi
      rw [mem_Ico]
      rcases hi with h | h | h | h | h <;> rw [h]
      · exact valid_of_card gs o (by rw [ho, line_card]; omega)
      · exact valid_of_card gs a (by rw [ha_eq, hScard]; omega)
      · exact valid_of_card gs b (by omega)
      · exact valid_of_card gs c (by omega)
      · exact valid_of_card gs d (by omega)
    have hFsum : ∑ i ∈ F, credit (support gs i) w =
        credit (support gs o) w + credit (support gs a) w +
        credit (support gs b) w + credit (support gs c) w + credit (support gs d) w := by
      simp only [F, sum_insert, sum_singleton, mem_insert, mem_singleton,
        hne_oa, hne_ob, hne_oc, hne_od, hne_ab, hne_ac, hne_ad, hne_bc, hne_bd, hne_cd,
        or_self, not_false_eq_true]
      omega
    have hco : credit (support gs o) w = 2 := by
      simp [credit, ho, line_card]
    have hca : credit (support gs a) w = 2 := by
      have ha_eq' : support gs a = line w := ha_eq
      simp [credit, ha_eq', line_card]
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => credit (support gs i) w)
      hFsub (fun _ _ _ => Nat.zero_le _)
    rw [hFsum, hco, hca] at hle
    omega

lemma line_demand (gs : List Gate) (hL : Legal gs) (o : ℕ) (w : Fin 13)
    (hSingle : ∀ p : Fin 13, value gs (single p) o = true ↔ p ∈ line w)
    (hPair : ∀ q1 q2 : Fin 13, q1 ∉ line w → q2 ∉ line w → value gs (pair q1 q2) o = false) :
    6 ≤ ∑ i ∈ Finset.Ico 13 (13 + gs.length), credit (support gs i) w := by
  let S := line w
  have hScard : S.card = 4 := line_card w
  have ho_sup : support gs o = S := by
    ext p; rw [mem_support, hSingle p]
  have hoP : o ∈ privSet gs S :=
    (mem_privSet gs S o).mpr ⟨ho_sup ▸ Subset.rfl, by rw [ho_sup, hScard]; omega⟩
  by_cases h3 : 3 ≤ (privSet gs S).card
  · have hsub : privSet gs S ⊆ Finset.Ico 13 (13 + gs.length) := filter_subset _ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => credit (support gs i) w)
      hsub (fun _ _ _ => Nat.zero_le _)
    have hval : ∀ i ∈ privSet gs S, credit (support gs i) w = 2 := by
      intro i hi
      obtain ⟨h1, h2⟩ := (mem_privSet gs S i).mp hi
      have h1' : support gs i ⊆ line w := h1
      simp [credit, h1', h2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul] at hle
    omega
  · have hP2 : (privSet gs S).card ≤ 2 := by omega
    have hpair_no : ∀ a ∈ privSet gs S, a < o → ∀ c < o, c ≠ a → c ∉ privSet gs S := by
      intro a haP ha_lt c hc_lt hca hcP
      have hsub3 : ({o, a, c} : Finset ℕ) ⊆ privSet gs S := by
        intro i hi
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl | rfl <;> assumption
      have hcard3 : ({o, a, c} : Finset ℕ).card = 3 := by
        rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
        · simp [hca.symm]
        · simp [show o ≠ a by omega, show o ≠ c by omega]
      have hle := card_le_card hsub3
      omega
    obtain ⟨h1o, h2o⟩ := valid_of_card gs o (by rw [ho_sup, hScard]; omega)
    rcases gate_cases gs hL h1o h2o with hf | ht | ⟨a, ha, hoa⟩ | ⟨a, ha, b, hb, hoab⟩ | ⟨a, ha, b, hb, hoab⟩
    · have he : support gs o = ∅ := by ext p; simp [mem_support, hf]
      rw [ho_sup] at he; rw [he] at hScard; simp at hScard
    · have he : support gs o = Finset.univ := by ext p; simp [mem_support, ht]
      rw [ho_sup] at he; rw [he] at hScard; simp at hScard
    · have ha_sup : support gs a = S := by
        rw [← ho_sup]; ext p; simp [mem_support, hoa]
      have haP : a ∈ privSet gs S :=
        (mem_privSet gs S a).mpr ⟨ha_sup ▸ Subset.rfl, by rw [ha_sup, hScard]; omega⟩
      exact (no_priv_below gs hL S hScard a (ha_sup ▸ Subset.rfl) (by rw [ha_sup, hScard]; omega)
        (fun q1 q2 h1 h2 => by rw [← hoa]; exact hPair q1 q2 h1 h2)
        (fun c hc => hpair_no a haP ha c (by omega) (by omega))).elim
    · have hsup : S = support gs a ∪ support gs b := by
        rw [← ho_sup]; ext p; simp [mem_support, hoab]
      have hsa : support gs a ⊆ S := hsup ▸ subset_union_left
      have hsb : support gs b ⊆ S := hsup ▸ subset_union_right
      have hge2 : 2 ≤ (support gs a).card ∨ 2 ≤ (support gs b).card := by
        have hle := card_union_le (support gs a) (support gs b)
        rw [← hsup, hScard] at hle
        omega
      rcases hge2 with hca | hcb
      · have haP : a ∈ privSet gs S := (mem_privSet gs S a).mpr ⟨hsa, hca⟩
        have h3a : 3 ≤ (support gs a).card := by
          by_cases hab : b = a
          · rw [hab, union_idempotent] at hsup; rw [← hsup, hScard]; omega
          · have hbnot : b ∉ privSet gs S := hpair_no a haP ha b hb hab
            have hcb1 : (support gs b).card ≤ 1 := by
              by_contra h; exact hbnot ((mem_privSet gs S b).mpr ⟨hsb, by omega⟩)
            have hle := card_union_le (support gs a) (support gs b)
            rw [← hsup, hScard] at hle
            omega
        have hpair_a : ∀ q1 q2 : Fin 13, q1 ∉ S → q2 ∉ S → value gs (pair q1 q2) a = false := by
          intro q1 q2 h1 h2
          have hv := hoab (pair q1 q2)
          rw [hPair q1 q2 h1 h2] at hv
          cases ha_v : value gs (pair q1 q2) a
          · rfl
          · rw [ha_v] at hv; simp at hv
        exact (no_priv_below gs hL S hScard a hsa h3a hpair_a
          (fun c hc => hpair_no a haP ha c (by omega) (by omega))).elim
      · have hbP : b ∈ privSet gs S := (mem_privSet gs S b).mpr ⟨hsb, hcb⟩
        have h3b : 3 ≤ (support gs b).card := by
          by_cases hab : a = b
          · rw [hab, union_idempotent] at hsup; rw [← hsup, hScard]; omega
          · have hanot : a ∉ privSet gs S := hpair_no b hbP hb a ha hab
            have hca1 : (support gs a).card ≤ 1 := by
              by_contra h; exact hanot ((mem_privSet gs S a).mpr ⟨hsa, by omega⟩)
            have hle := card_union_le (support gs a) (support gs b)
            rw [← hsup, hScard] at hle
            omega
        have hpair_b : ∀ q1 q2 : Fin 13, q1 ∉ S → q2 ∉ S → value gs (pair q1 q2) b = false := by
          intro q1 q2 h1 h2
          have hv := hoab (pair q1 q2)
          rw [hPair q1 q2 h1 h2] at hv
          cases hb_v : value gs (pair q1 q2) b
          · rfl
          · rw [hb_v] at hv; simp at hv
        exact (no_priv_below gs hL S hScard b hsb h3b hpair_b
          (fun c hc => hpair_no b hbP hb c (by omega) (by omega))).elim
    · have hsup : S = support gs a ∩ support gs b := by
        rw [← ho_sup]; ext p; simp [mem_support, hoab]
      have hSa : S ⊆ support gs a := hsup ▸ inter_subset_left
      have hSb : S ⊆ support gs b := hsup ▸ inter_subset_right
      by_cases haP : a ∈ privSet gs S
      · by_cases hbP : b ∈ privSet gs S
        · by_cases hab : a = b
          · have ha_sup : support gs a = S :=
              Subset.antisymm ((mem_privSet gs S a).mp haP).1 hSa
            have hpair_a : ∀ q1 q2 : Fin 13, q1 ∉ S → q2 ∉ S → value gs (pair q1 q2) a = false := by
              intro q1 q2 h1 h2
              have hv := hoab (pair q1 q2)
              rw [← hab, Bool.and_self, hPair q1 q2 h1 h2] at hv
              exact hv.symm
            exact (no_priv_below gs hL S hScard a (ha_sup ▸ Subset.rfl) (by rw [ha_sup, hScard]; omega)
              hpair_a (fun c hc => hpair_no a haP ha c (by omega) (by omega))).elim
          · exact (hpair_no a haP ha b hb (Ne.symm hab) hbP).elim
        · exact and_chain_demand gs hL w o a b ho_sup haP ha hbP hoab hPair
            (fun c hc => hpair_no a haP ha c (by omega) (by omega))
      · by_cases hbP : b ∈ privSet gs S
        · exact and_chain_demand gs hL w o b a ho_sup hbP hb haP
            (fun x => by rw [hoab x, Bool.and_comm]) hPair
            (fun c hc => hpair_no b hbP hb c (by omega) (by omega))
        · have hnsa : ¬ support gs a ⊆ S := by
            intro h
            have hca : 2 ≤ (support gs a).card := by have := card_le_card hSa; omega
            exact haP ((mem_privSet gs S a).mpr ⟨h, hca⟩)
          have hnsb : ¬ support gs b ⊆ S := by
            intro h
            have hcb : 2 ≤ (support gs b).card := by have := card_le_card hSb; omega
            exact hbP ((mem_privSet gs S b).mpr ⟨h, hcb⟩)
          obtain ⟨q1, hq1a, hq1S⟩ := Finset.not_subset.mp hnsa
          obtain ⟨q2, hq2b, hq2S⟩ := Finset.not_subset.mp hnsb
          have hv1 := pair_true_left gs hL a (q := q2) hq1a
          have hv2 := pair_true_right gs hL b (p := q1) hq2b
          have hvo := hoab (pair q1 q2)
          rw [hv1, hv2, hPair q1 q2 hq1S hq2S] at hvo
          simp at hvo

lemma main_proof (gates : List Gate) (out : Fin 13 → ℕ)
    (hL : Legal gates)
    (ho : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ line w, x v = true)) :
    39 ≤ gates.length := by
  have hdem : ∀ w : Fin 13, 6 ≤ ∑ i ∈ Finset.Ico 13 (13 + gates.length), credit (support gates i) w := by
    intro w
    apply line_demand gates hL (out w) w
    · intro p
      have h := ho w (single p) (by
        intro i j k hi hj _
        simp [single] at hi hj
        exact Or.inl (hi.trans hj.symm))
      rw [← value_eq_eval] at h
      rw [h]
      simp [single]
    · intro q1 q2 hq1 hq2
      have h := ho w (pair q1 q2) (by
        intro i j k hi hj hk
        simp [pair] at hi hj hk
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;>
          simp)
      rw [← value_eq_eval] at h
      rw [h]
      simp only [pair, decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
      intro v hv hq
      rcases hq with rfl | rfl
      · exact hq1 hv
      · exact hq2 hv
  have hlow : 78 ≤ ∑ w : Fin 13, ∑ i ∈ Finset.Ico 13 (13 + gates.length), credit (support gates i) w := by
    have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 13))) (fun w _ => hdem w)
    simpa using h1
  have hup : ∑ i ∈ Finset.Ico 13 (13 + gates.length), ∑ w : Fin 13, credit (support gates i) w ≤
      2 * gates.length := by
    have h1 := Finset.sum_le_sum (s := Finset.Ico 13 (13 + gates.length))
      (fun i _ => capacity (support gates i))
    simpa [Nat.mul_comm] using h1
  rw [Finset.sum_comm] at hlow
  omega

end PEqualNP.Outside.L_meta_667

open PEqualNP.Outside.L_meta_667

theorem PEqualNP.Outside.L_meta_667 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 13) (x : Fin 13 → Bool), (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)), x v = true)) → 39 ≤ gates.length := by
  intro gates out hL ho
  exact main_proof gates out hL ho

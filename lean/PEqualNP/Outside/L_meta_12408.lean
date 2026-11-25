import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12408_aux

open PEqualNP.CircuitLowerBounds

/-- The four target subsets of `Fin 14`, corresponding to bits `0..3` of `p.val + 1`. -/
def target (v : Fin 4) : Finset (Fin 14) :=
  Finset.univ.filter (fun p : Fin 14 => Nat.testBit (p.val + 1) v.val)

/-- One-hot input vector of length 14 with `true` at position `p`. -/
def oneHot (p : Fin 14) : List Bool :=
  List.ofFn (fun q : Fin 14 => decide (q = p))

theorem oneHot_length (p : Fin 14) : (oneHot p).length = 14 := by
  simp [oneHot]

theorem oneHot_getD (p : Fin 14) (w : ℕ) (hw : w < 14) :
    (oneHot p).getD w false = decide (⟨w, hw⟩ = p) := by
  simp only [oneHot, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte,
    Option.getD_some]

/-- Helper for evaluating `Circuit.wires` step by step. -/
def stepWires (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq_foldl (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x) = gs.foldl stepWires x := rfl

theorem foldl_stepWires_length (gs : List Gate) (x : List Bool) :
    (gs.foldl stepWires x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWires, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem foldl_stepWires_prefix (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (gs.foldl stepWires x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hx : w < (stepWires x g).length := by
      simp only [stepWires, List.length_append, List.length_singleton]; omega
    rw [ih (stepWires x g) hx]
    simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

theorem foldl_stepWires_oob (gs : List Gate) (x : List Bool) (w : ℕ)
    (hw : x.length + gs.length ≤ w) :
    (gs.foldl stepWires x).getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [foldl_stepWires_length]; exact hw

theorem foldl_stepWires_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWires x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (gs.foldl stepWires x).getD i false else false) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2, h1]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (gs.take j).foldl stepWires x with hpre
  have hpre_len : pre.length = x.length + j := by
    rw [hpre, foldl_stepWires_length, List.length_take_of_le (Nat.le_of_lt hj)]
  have hlt : x.length + j < (stepWires pre gs[j]).length := by
    simp only [stepWires, List.length_append, List.length_singleton, hpre_len]; omega
  rw [foldl_stepWires_prefix (gs.drop (j + 1)) (stepWires pre gs[j]) (x.length + j) hlt]
  have hstep : (stepWires pre gs[j]).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => pre.getD i false) := by
    simp only [stepWires, List.getD_eq_getElem?_getD, ← hpre_len, List.getElem?_append_right le_rfl,
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hstep]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hi
  · have hpi : i < pre.length := hpre_len ▸ hi
    have hfull : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
    conv_rhs => rw [hfull, List.foldl_append]
    exact (foldl_stepWires_prefix (gs.drop j) pre i hpi).symm
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · omega

/-- Support of wire `w` of circuit `gs` on one-hot inputs of length 14. -/
def supp (gs : List Gate) (w : ℕ) : Finset (Fin 14) :=
  Finset.univ.filter (fun p : Fin 14 => (Circuit.wires ⟨gs, 0⟩ (oneHot p)).getD w false = true)

theorem supp_input (gs : List Gate) (w : ℕ) (hw : w < 14) :
    supp gs w = {⟨w, hw⟩} := by
  ext p
  dsimp only [supp]
  rw [Finset.mem_filter, Finset.mem_singleton]
  simp only [Finset.mem_univ, true_and, wires_eq_foldl]
  rw [foldl_stepWires_prefix gs (oneHot p) w (by rw [oneHot_length]; exact hw),
    oneHot_getD p w hw, decide_eq_true_eq, eq_comm]

theorem supp_oob (gs : List Gate) (w : ℕ) (hw : 14 + gs.length ≤ w) :
    supp gs w = ∅ := by
  ext p
  dsimp only [supp]
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, wires_eq_foldl]
  rw [foldl_stepWires_oob gs (oneHot p) w (by rw [oneHot_length]; exact hw)]
  decide

/-- Valid earlier input wires read by gate `j`. -/
def effIn (gs : List Gate) (j : ℕ) (hj : j < gs.length) : Finset ℕ :=
  (gs[j].inputs.filter (fun i => decide (i < 14 + j))).toFinset

theorem effIn_lt (gs : List Gate) (j : ℕ) (hj : j < gs.length) {i : ℕ}
    (hi : i ∈ effIn gs j hj) : i < 14 + j := by
  simp only [effIn, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hi
  exact hi.2

theorem effIn_card_le (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hlen : gs[j].inputs.length ≤ 2) : (effIn gs j hj).card ≤ 2 := by
  calc (effIn gs j hj).card
      ≤ (gs[j].inputs.filter (fun i => decide (i < 14 + j))).length := List.toFinset_card_le _
    _ ≤ gs[j].inputs.length := List.length_filter_le _ _
    _ ≤ 2 := hlen

theorem supp_gate (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hop : gs[j].op = GateOp.or) :
    supp gs (14 + j) = (effIn gs j hj).biUnion (supp gs) := by
  ext p
  dsimp only [supp]
  rw [Finset.mem_filter, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and, wires_eq_foldl]
  have h14 : (oneHot p).length = 14 := oneHot_length p
  have hgate := foldl_stepWires_gate gs (oneHot p) j hj
  rw [h14, hop] at hgate
  rw [hgate]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, hval⟩
    by_cases hlt : i < 14 + j
    · refine ⟨i, ?_, ?_⟩
      · simp only [effIn, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
        exact ⟨hi, hlt⟩
      · simp only [hlt, ↓reduceIte] at hval
        dsimp only [supp]; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ p, hval⟩
    · simp only [hlt, ↓reduceIte] at hval; exact absurd hval (by decide)
  · rintro ⟨i, hi, hval⟩
    dsimp only [supp] at hval; rw [Finset.mem_filter] at hval
    simp only [effIn, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hi
    exact ⟨i, hi.1, by simp only [hi.2, ↓reduceIte]; exact hval.2⟩

/-- The six unordered pairs of targets `Fin 4`. -/
def pairOf (idx : Fin 6) : Fin 4 × Fin 4 :=
  match idx.val with
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (1, 2)
  | 4 => (1, 3)
  | _ => (2, 3)

/-- The intersection `target a ∩ target b` for each of the 6 pairs (always size 3). -/
def pairMask (idx : Fin 6) : Finset (Fin 14) :=
  target (pairOf idx).1 ∩ target (pairOf idx).2

theorem pairMask_card (idx : Fin 6) : (pairMask idx).card = 3 := by
  revert idx; decide +kernel

/-- The three elements of `pairMask idx` in increasing order. -/
def pairElems (idx : Fin 6) : Fin 14 × Fin 14 × Fin 14 :=
  match idx.val with
  | 0 => (2, 6, 10)
  | 1 => (4, 6, 12)
  | 2 => (8, 10, 12)
  | 3 => (5, 6, 13)
  | 4 => (9, 10, 13)
  | _ => (11, 12, 13)

/-- Choice `c : Fin 5` for pair `idx`: empty, one of three 2-subsets, or all 3 elements. -/
def choiceSet (idx : Fin 6) (c : Fin 5) : Finset (Fin 14) :=
  let (a, b, d) := pairElems idx
  match c.val with
  | 0 => ∅
  | 1 => {a, b}
  | 2 => {a, d}
  | 3 => {b, d}
  | _ => {a, b, d}

def choiceCost (c : Fin 5) : ℕ :=
  match c.val with
  | 0 => 0
  | 4 => 2
  | _ => 1

theorem choiceSet_four (idx : Fin 6) : choiceSet idx 4 = pairMask idx := by
  revert idx; decide +kernel

theorem choiceSet_two_exists (idx : Fin 6) (S : Finset (Fin 14))
    (hsub : S ⊆ pairMask idx) (hcard : S.card = 2) :
    ∃ c : Fin 5, choiceCost c = 1 ∧ S = choiceSet idx c := by
  have hall : ∀ idx : Fin 6, ∀ a b : Fin 14, a ∈ pairMask idx → b ∈ pairMask idx → a ≠ b →
      ({a, b} : Finset (Fin 14)) = choiceSet idx 1 ∨
      ({a, b} : Finset (Fin 14)) = choiceSet idx 2 ∨
      ({a, b} : Finset (Fin 14)) = choiceSet idx 3 := by
    decide +kernel
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ pairMask idx := hsub (by simp)
  have hb : b ∈ pairMask idx := hsub (by simp)
  rcases hall idx a b ha hb hab with h | h | h
  · exact ⟨1, rfl, h⟩
  · exact ⟨2, rfl, h⟩
  · exact ⟨3, rfl, h⟩

/-- Any subset of size ≥ 2 lies in at most one `pairMask idx`. -/
theorem pairMask_inter_card_le_one (i j : Fin 6) (hij : i ≠ j) :
    (pairMask i ∩ pairMask j).card ≤ 1 := by
  revert i j; decide +kernel

/-- Every pair `(a, b)` with `a < b` equals `pairOf idx` for some `idx : Fin 6`. -/
theorem exists_pairOf (a b : Fin 4) (hab : a < b) : ∃ idx : Fin 6, pairOf idx = (a, b) := by
  revert a b; decide +kernel

/-- The 3 pair indices containing target `v`. -/
def pairsOfTarget (v : Fin 4) : Fin 3 → Fin 6 :=
  match v.val with
  | 0 => ![0, 1, 2]
  | 1 => ![0, 3, 4]
  | 2 => ![1, 3, 5]
  | _ => ![2, 4, 5]

theorem pair_in_target_iff (v : Fin 4) (idx : Fin 6) :
    ((pairOf idx).1 = v ∨ (pairOf idx).2 = v) ↔ ∃ k : Fin 3, pairsOfTarget v k = idx := by
  revert v idx; decide +kernel

theorem pairMask_subset_target_iff (v : Fin 4) (idx : Fin 6) (S : Finset (Fin 14))
    (hS : 2 ≤ S.card) (hsub : S ⊆ pairMask idx) (hv : S ⊆ target v) :
    ∃ k : Fin 3, pairsOfTarget v k = idx := by
  have hcheck : ∀ v : Fin 4, ∀ idx : Fin 6,
      (pairMask idx ∩ target v).card ≥ 2 → ∃ k : Fin 3, pairsOfTarget v k = idx := by
    decide +kernel
  apply hcheck v idx
  have h1 : S ⊆ pairMask idx ∩ target v := Finset.subset_inter hsub hv
  exact le_trans hS (Finset.card_le_card h1)

/-- Minimum G1 gates needed for target `v` given the 6 pair choices. -/
def targetMinG1 (v : Fin 4) (c : Fin 6 → Fin 5) : ℕ :=
  (Finset.univ : Finset (Fin 8)).inf' ⟨0, Finset.mem_univ 0⟩ (fun m =>
    let p0 := pairsOfTarget v 0
    let p1 := pairsOfTarget v 1
    let p2 := pairsOfTarget v 2
    let u0 := if Nat.testBit m.val 0 then choiceSet p0 (c p0) else ∅
    let u1 := if Nat.testBit m.val 1 then choiceSet p1 (c p1) else ∅
    let u2 := if Nat.testBit m.val 2 then choiceSet p2 (c p2) else ∅
    let cnt := (if Nat.testBit m.val 0 then 1 else 0) +
               (if Nat.testBit m.val 1 then 1 else 0) +
               (if Nat.testBit m.val 2 then 1 else 0)
    cnt + (target v \ (u0 ∪ u1 ∪ u2)).card - 1)

theorem pairsOfTarget_injective : ∀ v : Fin 4, ∀ k1 k2 : Fin 3,
    k1 ≠ k2 → pairsOfTarget v k1 ≠ pairsOfTarget v k2 := by
  decide +kernel

theorem testBit_mask3 (b0 b1 b2 : Bool) :
    let mv := (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0)
    Nat.testBit mv 0 = b0 ∧ Nat.testBit mv 1 = b1 ∧ Nat.testBit mv 2 = b2 := by
  cases b0 <;> cases b1 <;> cases b2 <;> decide

/-- Bitmask representation of `target v` (14 bits). -/
def targetBit (v : Fin 4) : ℕ :=
  match v.val with
  | 0 => 0b01010101010101
  | 1 => 0b10011001100110
  | 2 => 0b11100001111000
  | _ => 0b11111110000000

/-- Bitmask representation of `choiceSet idx c` (14 bits). -/
def choiceBit (idx : Fin 6) (c : Fin 5) : ℕ :=
  let (a, b, d) := pairElems idx
  match c.val with
  | 0 => 0
  | 1 => (1 <<< a.val) ||| (1 <<< b.val)
  | 2 => (1 <<< a.val) ||| (1 <<< d.val)
  | 3 => (1 <<< b.val) ||| (1 <<< d.val)
  | _ => (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< d.val)

/-- Popcount of the low 14 bits of a natural number. -/
def pop14 (x : ℕ) : ℕ :=
  (if x.testBit 0 then 1 else 0) + (if x.testBit 1 then 1 else 0) +
  (if x.testBit 2 then 1 else 0) + (if x.testBit 3 then 1 else 0) +
  (if x.testBit 4 then 1 else 0) + (if x.testBit 5 then 1 else 0) +
  (if x.testBit 6 then 1 else 0) + (if x.testBit 7 then 1 else 0) +
  (if x.testBit 8 then 1 else 0) + (if x.testBit 9 then 1 else 0) +
  (if x.testBit 10 then 1 else 0) + (if x.testBit 11 then 1 else 0) +
  (if x.testBit 12 then 1 else 0) + (if x.testBit 13 then 1 else 0)

theorem targetBit_spec : ∀ v : Fin 4, ∀ p : Fin 14,
    (targetBit v).testBit p.val = decide (p ∈ target v) := by
  decide +kernel

theorem choiceBit_spec : ∀ idx : Fin 6, ∀ c : Fin 5, ∀ p : Fin 14,
    (choiceBit idx c).testBit p.val = decide (p ∈ choiceSet idx c) := by
  decide +kernel

/-- Fast bitmask version of `targetMinG1 v` taking the 3 choices for `pairsOfTarget v 0..2`. -/
def targetMinG1Fast (v : Fin 4) (a0 a1 a2 : Fin 5) : ℕ :=
  let tv := targetBit v
  let b0 := choiceBit (pairsOfTarget v 0) a0
  let b1 := choiceBit (pairsOfTarget v 1) a1
  let b2 := choiceBit (pairsOfTarget v 2) a2
  let evalM := fun (m : ℕ) =>
    let u0 := if m.testBit 0 then b0 else 0
    let u1 := if m.testBit 1 then b1 else 0
    let u2 := if m.testBit 2 then b2 else 0
    let cnt := (if m.testBit 0 then 1 else 0) +
               (if m.testBit 1 then 1 else 0) +
               (if m.testBit 2 then 1 else 0)
    cnt + pop14 (tv &&& (16383 ^^^ (u0 ||| u1 ||| u2))) - 1
  min (min (min (evalM 0) (evalM 1)) (min (evalM 2) (evalM 3)))
      (min (min (evalM 4) (evalM 5)) (min (evalM 6) (evalM 7)))

theorem targetMinG1Fast_eq (v : Fin 4) (a0 a1 a2 : Fin 5) :
    targetMinG1Fast v a0 a1 a2 =
      (Finset.univ : Finset (Fin 8)).inf' ⟨0, Finset.mem_univ 0⟩ (fun m =>
        let u0 := if Nat.testBit m.val 0 then choiceSet (pairsOfTarget v 0) a0 else ∅
        let u1 := if Nat.testBit m.val 1 then choiceSet (pairsOfTarget v 1) a1 else ∅
        let u2 := if Nat.testBit m.val 2 then choiceSet (pairsOfTarget v 2) a2 else ∅
        let cnt := (if Nat.testBit m.val 0 then 1 else 0) +
                   (if Nat.testBit m.val 1 then 1 else 0) +
                   (if Nat.testBit m.val 2 then 1 else 0)
        cnt + (target v \ (u0 ∪ u1 ∪ u2)).card - 1) := by
  revert v a0 a1 a2; decide +kernel

/-- Exhaustive combinatorial lower bound: across all `5^6 = 15625` pair-sharing profiles,
total gates is at least `20`. -/
theorem comb_bound_all : ∀ c0 c1 c2 c3 c4 c5 : Fin 5,
    20 ≤ choiceCost c0 + choiceCost c1 + choiceCost c2 +
         choiceCost c3 + choiceCost c4 + choiceCost c5 +
         targetMinG1Fast 0 c0 c1 c2 + targetMinG1Fast 1 c0 c3 c4 +
         targetMinG1Fast 2 c1 c3 c5 + targetMinG1Fast 3 c2 c4 c5 := by
  decide +kernel

theorem comb_bound (c : Fin 6 → Fin 5) :
    20 ≤ (∑ idx : Fin 6, choiceCost (c idx)) + ∑ v : Fin 4, targetMinG1 v c := by
  have h := comb_bound_all (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)
  have h0 : targetMinG1Fast 0 (c 0) (c 1) (c 2) = targetMinG1 0 c :=
    targetMinG1Fast_eq 0 (c 0) (c 1) (c 2)
  have h1 : targetMinG1Fast 1 (c 0) (c 3) (c 4) = targetMinG1 1 c :=
    targetMinG1Fast_eq 1 (c 0) (c 3) (c 4)
  have h2 : targetMinG1Fast 2 (c 1) (c 3) (c 5) = targetMinG1 2 c :=
    targetMinG1Fast_eq 2 (c 1) (c 3) (c 5)
  have h3 : targetMinG1Fast 3 (c 2) (c 4) (c 5) = targetMinG1 3 c :=
    targetMinG1Fast_eq 3 (c 2) (c 4) (c 5)
  simp only [Fin.sum_univ_six, Fin.sum_univ_four]
  omega

/-- Frontier-peeling lemma: expanding all `G1 v`-gates from a frontier `U` yields a base frontier
`U'` with `U'.card ≤ U.card + |(G1 v).filter (< k)|`. -/
theorem peel (gs : List Gate)
    (hor : ∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (v : Fin 4) (G1v : Finset ℕ)
    (hG1_lt : ∀ j ∈ G1v, j < gs.length) :
    ∀ k : ℕ, ∀ U : Finset ℕ,
      target v ⊆ U.biUnion (supp gs) →
      (∀ w ∈ U, supp gs w ⊆ target v) →
      (∀ j ∈ G1v, 14 + j ∈ U → j < k) →
      ∃ U' : Finset ℕ,
        target v ⊆ U'.biUnion (supp gs) ∧
        (∀ w ∈ U', supp gs w ⊆ target v) ∧
        (∀ j ∈ G1v, 14 + j ∉ U') ∧
        U'.card ≤ U.card + (G1v.filter (· < k)).card := by
  intro k
  induction k with
  | zero =>
    intro U hcov hsub hlt
    exact ⟨U, hcov, hsub, fun j hj hmem => Nat.not_lt_zero j (hlt j hj hmem), by simp⟩
  | succ k ih =>
    intro U hcov hsub hlt
    by_cases hk : k ∈ G1v ∧ 14 + k ∈ U
    · obtain ⟨hkG, hkU⟩ := hk
      have hkl : k < gs.length := hG1_lt k hkG
      have hgk := hor gs[k] (List.getElem_mem hkl)
      set E := effIn gs k hkl with hE
      set U1 := U.erase (14 + k) ∪ E with hU1
      have hsupp_k : supp gs (14 + k) = E.biUnion (supp gs) := supp_gate gs k hkl hgk.1
      have hcov1 : target v ⊆ U1.biUnion (supp gs) := by
        intro p hp
        obtain ⟨w, hwU, hpw⟩ := Finset.mem_biUnion.mp (hcov hp)
        by_cases hwk : w = 14 + k
        · subst hwk
          rw [hsupp_k] at hpw
          obtain ⟨i, hiE, hpi⟩ := Finset.mem_biUnion.mp hpw
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_union_right _ hiE, hpi⟩
        · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hwU⟩), hpw⟩
      have hsub1 : ∀ w ∈ U1, supp gs w ⊆ target v := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw' | hwE
        · exact hsub w (Finset.mem_of_mem_erase hw')
        · have hksub : supp gs (14 + k) ⊆ target v := hsub (14 + k) hkU
          rw [hsupp_k] at hksub
          exact Finset.Subset.trans (Finset.subset_biUnion_of_mem (supp gs) hwE) hksub
      have hlt1 : ∀ j ∈ G1v, 14 + j ∈ U1 → j < k := by
        intro j hj hmem
        rcases Finset.mem_union.mp hmem with hm' | hmE
        · have hne : 14 + j ≠ 14 + k := (Finset.mem_erase.mp hm').1
          have hlt' := hlt j hj (Finset.mem_of_mem_erase hm')
          omega
        · have := effIn_lt gs k hkl hmE
          omega
      obtain ⟨U', hcov', hsub', hno', hcard'⟩ := ih U1 hcov1 hsub1 hlt1
      have hcardU1 : U1.card ≤ U.card + 1 := by
        have h1 : U1.card ≤ (U.erase (14 + k)).card + E.card := Finset.card_union_le _ _
        have h2 : (U.erase (14 + k)).card = U.card - 1 := Finset.card_erase_of_mem hkU
        have h3 : 1 ≤ U.card := Finset.one_le_card.mpr ⟨14 + k, hkU⟩
        have h4 : E.card ≤ 2 := effIn_card_le gs k hkl hgk.2
        omega
      have hfilt : (G1v.filter (· < k + 1)).card = (G1v.filter (· < k)).card + 1 := by
        have heq : G1v.filter (· < k + 1) = insert k (G1v.filter (· < k)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hj, hjk⟩
            by_cases h : j = k
            · exact Or.inl h
            · exact Or.inr ⟨hj, by omega⟩
          · rintro (rfl | ⟨hj, hjk⟩)
            · exact ⟨hkG, by omega⟩
            · exact ⟨hj, by omega⟩
        rw [heq, Finset.card_insert_of_notMem]
        simp
      exact ⟨U', hcov', hsub', hno', by omega⟩
    · have hlt1 : ∀ j ∈ G1v, 14 + j ∈ U → j < k := by
        intro j hj hmem
        have hlt' := hlt j hj hmem
        by_cases hjk : j = k
        · subst hjk; exact absurd ⟨hj, hmem⟩ hk
        · omega
      obtain ⟨U', hcov', hsub', hno', hcard'⟩ := ih U hcov hsub hlt1
      have hmono : (G1v.filter (· < k)).card ≤ (G1v.filter (· < k + 1)).card :=
        Finset.card_le_card (fun j hj => by
          simp only [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, by omega⟩)
      exact ⟨U', hcov', hsub', hno', by omega⟩

/-- Main lower bound for `L-meta-12408`: any 2-input OR circuit computing the 4 bit outputs on
all 14 one-hot inputs has at least 20 gates. -/
theorem main_lb (C : Circuit)
    (hor : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (hcomp : ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14,
      (C.wires (oneHot p)).getD w false = Nat.testBit (p.val + 1) v.val) :
    20 ≤ C.size := by
  classical
  set gs := C.gates with hgs
  have hwires_eq : ∀ p : Fin 14, C.wires (oneHot p) = Circuit.wires ⟨gs, 0⟩ (oneHot p) := fun _ => rfl
  -- Partition gates with support size ≥ 2 into G2 (shared across ≥ 2 targets) and G1 v (unique target v).
  let G2p : Fin 6 → Finset ℕ := fun idx =>
    (Finset.range gs.length).filter (fun j =>
      2 ≤ (supp gs (14 + j)).card ∧ supp gs (14 + j) ⊆ pairMask idx)
  let G2 : Finset ℕ := Finset.univ.biUnion G2p
  let G1 : Fin 4 → Finset ℕ := fun v =>
    (Finset.range gs.length).filter (fun j =>
      2 ≤ (supp gs (14 + j)).card ∧ supp gs (14 + j) ⊆ target v ∧ j ∉ G2)
  -- Step 1: Pairwise disjointness of G2p idx across idx : Fin 6.
  have hG2p_disj : ∀ i j : Fin 6, i ≠ j → Disjoint (G2p i) (G2p j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro g hgi hgj
    simp only [G2p, Finset.mem_filter] at hgi hgj
    have hsub : supp gs (14 + g) ⊆ pairMask i ∩ pairMask j :=
      Finset.subset_inter hgi.2.2 hgj.2.2
    have hle := pairMask_inter_card_le_one i j hij
    have hge := hgi.2.1
    have hle' := Finset.card_le_card hsub
    omega
  have hG2_card : G2.card = ∑ idx : Fin 6, (G2p idx).card := by
    rw [Finset.card_biUnion]
    intro i _ j _ hij; exact hG2p_disj i j hij
  -- Step 2: Pairwise disjointness of G1 v across v : Fin 4, and disjoint from G2.
  have hG1_disj : ∀ u v : Fin 4, u ≠ v → Disjoint (G1 u) (G1 v) := by
    intro u v huv
    rw [Finset.disjoint_left]
    intro g hgu hgv
    simp only [G1, Finset.mem_filter] at hgu hgv
    have hinG2 : g ∈ G2 := by
      rcases lt_or_gt_of_ne huv with hlt | hgt
      · obtain ⟨idx, hidx⟩ := exists_pairOf u v hlt
        refine Finset.mem_biUnion.mpr ⟨idx, Finset.mem_univ idx, ?_⟩
        simp only [G2p, Finset.mem_filter, pairMask, hidx]
        exact ⟨hgu.1, hgu.2.1, Finset.subset_inter hgu.2.2.1 hgv.2.2.1⟩
      · obtain ⟨idx, hidx⟩ := exists_pairOf v u hgt
        refine Finset.mem_biUnion.mpr ⟨idx, Finset.mem_univ idx, ?_⟩
        simp only [G2p, Finset.mem_filter, pairMask, hidx]
        exact ⟨hgu.1, hgu.2.1, Finset.subset_inter hgv.2.2.1 hgu.2.2.1⟩
    exact hgu.2.2.2 hinG2
  have hG12_disj : Disjoint G2 (Finset.univ.biUnion G1) := by
    rw [Finset.disjoint_left]
    intro g hg2 hg1
    obtain ⟨v, -, hgv⟩ := Finset.mem_biUnion.mp hg1
    simp only [G1, Finset.mem_filter] at hgv
    exact hgv.2.2.2 hg2
  have htotal_le : G2.card + ∑ v : Fin 4, (G1 v).card ≤ gs.length := by
    have hsub : G2 ∪ Finset.univ.biUnion G1 ⊆ Finset.range gs.length := by
      intro g hg
      rcases Finset.mem_union.mp hg with hg2 | hg1
      · obtain ⟨idx, -, hgi⟩ := Finset.mem_biUnion.mp hg2
        exact (Finset.mem_filter.mp hgi).1
      · obtain ⟨v, -, hgv⟩ := Finset.mem_biUnion.mp hg1
        exact (Finset.mem_filter.mp hgv).1
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range, Finset.card_union_of_disjoint hG12_disj] at h1
    have hG1_sum_card : (Finset.univ.biUnion G1).card = ∑ v : Fin 4, (G1 v).card :=
      Finset.card_biUnion (fun u _ v _ huv => hG1_disj u v huv)
    rw [hG1_sum_card] at h1
    exact h1
  -- Step 3: Build choice profile c : Fin 6 → Fin 5 from G2p.
  have hpair_choice : ∀ idx : Fin 6, ∃ c : Fin 5,
      choiceCost c ≤ (G2p idx).card ∧
      ∀ j ∈ G2p idx, supp gs (14 + j) ⊆ choiceSet idx c := by
    intro idx
    by_cases h0 : (G2p idx).card = 0
    · refine ⟨0, Nat.zero_le _, fun j hj => ?_⟩
      exact absurd (Finset.card_pos.mpr ⟨j, hj⟩) (by omega)
    · by_cases h2 : 2 ≤ (G2p idx).card
      · refine ⟨4, h2, fun j hj => ?_⟩
        rw [choiceSet_four]
        exact (Finset.mem_filter.mp hj).2.2
      · have h1 : (G2p idx).card = 1 := by omega
        obtain ⟨j, hj_eq⟩ := Finset.card_eq_one.mp h1
        have hjmem : j ∈ G2p idx := by rw [hj_eq]; exact Finset.mem_singleton_self j
        have hjf := Finset.mem_filter.mp hjmem
        have hjlt : j < gs.length := Finset.mem_range.mp hjf.1
        have hle3 : (supp gs (14 + j)).card ≤ 3 := by
          calc (supp gs (14 + j)).card ≤ (pairMask idx).card := Finset.card_le_card hjf.2.2
            _ = 3 := pairMask_card idx
        have hne3 : (supp gs (14 + j)).card ≠ 3 := by
          intro h3
          have hgj := hor gs[j] (List.getElem_mem hjlt)
          have hsg := supp_gate gs j hjlt hgj.1
          have hE2 := effIn_card_le gs j hjlt hgj.2
          have hex : ∃ i ∈ effIn gs j hjlt, 2 ≤ (supp gs i).card := by
            by_contra hall
            push Not at hall
            have hsum : (supp gs (14 + j)).card ≤ ∑ i ∈ effIn gs j hjlt, (supp gs i).card := by
              rw [hsg]; exact Finset.card_biUnion_le
            have hsum2 : ∑ i ∈ effIn gs j hjlt, (supp gs i).card ≤ ∑ _i ∈ effIn gs j hjlt, 1 :=
              Finset.sum_le_sum (fun i hi => Nat.lt_succ_iff.mp (hall i hi))
            simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum2
            omega
          obtain ⟨i, hiE, hi2⟩ := hex
          have hilt : i < 14 + j := effIn_lt gs j hjlt hiE
          have hi14 : 14 ≤ i := by
            by_contra hlt14
            push Not at hlt14
            rw [supp_input gs i hlt14] at hi2
            simp at hi2
          set j' := i - 14
          have hj'eq : 14 + j' = i := by omega
          have hj'lt : j' < gs.length := by omega
          have hj'sub : supp gs (14 + j') ⊆ pairMask idx := by
            rw [hj'eq]
            exact Finset.Subset.trans (hsg ▸ Finset.subset_biUnion_of_mem (supp gs) hiE) hjf.2.2
          have hj'mem : j' ∈ G2p idx :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj'lt, hj'eq ▸ hi2, hj'sub⟩
          rw [hj_eq, Finset.mem_singleton] at hj'mem
          omega
        have hcard2 : (supp gs (14 + j)).card = 2 := by omega
        obtain ⟨c, hcc, hcs⟩ := choiceSet_two_exists idx (supp gs (14 + j)) hjf.2.2 hcard2
        refine ⟨c, by omega, fun g hg => ?_⟩
        rw [hj_eq, Finset.mem_singleton] at hg
        subst hg; rw [hcs]
  choose c hc_cost hc_sub using hpair_choice
  -- Step 4: Lower bound (G1 v).card by targetMinG1 v c using peel.
  have hG1_lb : ∀ v : Fin 4, targetMinG1 v c ≤ (G1 v).card := by
    intro v
    obtain ⟨w, hw⟩ := hcomp v
    have hsw : supp gs w = target v := by
      ext p
      simp only [supp, target, Finset.mem_filter, Finset.mem_univ, true_and, ← hwires_eq p, hw p]
    have hG1_lt : ∀ j ∈ G1 v, j < gs.length := fun j hj =>
      Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    obtain ⟨U', hcov', hsub', hno', hcard'⟩ :=
      peel gs hor v (G1 v) hG1_lt gs.length {w}
        (by simp [hsw])
        (by intro u hu; simp only [Finset.mem_singleton] at hu; subst hu; rw [hsw])
        (fun j hj _ => hG1_lt j hj)
    have hfilt_eq : (G1 v).filter (· < gs.length) = G1 v :=
      Finset.filter_true_of_mem (fun j hj => hG1_lt j hj)
    rw [hfilt_eq, Finset.card_singleton] at hcard'
    -- Split U' into wires with support card ≥ 2 (must come from G2) and wires with support card ≤ 1.
    let Ubig := U'.filter (fun u => 2 ≤ (supp gs u).card)
    let Usm := U'.filter (fun u => (supp gs u).card ≤ 1)
    have hU'_split : U'.card = Ubig.card + Usm.card := by
      have hun : Ubig ∪ Usm = U' := by
        ext u
        simp only [Ubig, Usm, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          by_cases h2 : 2 ≤ (supp gs u).card
          · exact Or.inl ⟨h, h2⟩
          · exact Or.inr ⟨h, by omega⟩
      have hdj : Disjoint Ubig Usm := by
        rw [Finset.disjoint_left]
        intro u h1 h2
        simp only [Ubig, Usm, Finset.mem_filter] at h1 h2
        omega
      rw [← hun, Finset.card_union_of_disjoint hdj]
    -- Every u ∈ Ubig is of the form 14 + j with j ∈ G2p (pairsOfTarget v k) for some k : Fin 3.
    let Kused : Finset (Fin 3) := Finset.univ.filter (fun k : Fin 3 =>
      ∃ u ∈ Ubig, ∃ j ∈ G2p (pairsOfTarget v k), u = 14 + j)
    have hKused_le : Kused.card ≤ Ubig.card := by
      have hmap : ∀ k ∈ Kused, ∃ u ∈ Ubig, ∃ j ∈ G2p (pairsOfTarget v k), u = 14 + j :=
        fun k hk => (Finset.mem_filter.mp hk).2
      choose f hf using hmap
      have hinj : ∀ k1 (h1 : k1 ∈ Kused) k2 (h2 : k2 ∈ Kused), f k1 h1 = f k2 h2 → k1 = k2 := by
        intro k1 h1 k2 h2 heq
        obtain ⟨-, j1, hj1, he1⟩ := hf k1 h1
        obtain ⟨-, j2, hj2, he2⟩ := hf k2 h2
        have hj12 : j1 = j2 := by omega
        subst hj12
        by_contra hne
        have hpne : pairsOfTarget v k1 ≠ pairsOfTarget v k2 :=
          pairsOfTarget_injective v k1 k2 hne
        exact Finset.disjoint_left.mp (hG2p_disj _ _ hpne) hj1 hj2
      calc Kused.card = (Kused.attach.image (fun x => f x.1 x.2)).card := by
            rw [Finset.card_image_of_injective]
            · simp
            · intro x y hxy; exact Subtype.ext (hinj x.1 x.2 y.1 y.2 hxy)
        _ ≤ Ubig.card := Finset.card_le_card (fun u hu => by
            obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hu
            exact (hf x.1 x.2).1)
    let mval : ℕ := (if decide ((0 : Fin 3) ∈ Kused) then 1 else 0) +
                    (if decide ((1 : Fin 3) ∈ Kused) then 2 else 0) +
                    (if decide ((2 : Fin 3) ∈ Kused) then 4 else 0)
    have hmlt : mval < 8 := by dsimp [mval]; split_ifs <;> omega
    let m : Fin 8 := ⟨mval, hmlt⟩
    have hbits := testBit_mask3 (decide ((0 : Fin 3) ∈ Kused))
      (decide ((1 : Fin 3) ∈ Kused)) (decide ((2 : Fin 3) ∈ Kused))
    have hbit0 : Nat.testBit m.val 0 = decide ((0 : Fin 3) ∈ Kused) := hbits.1
    have hbit1 : Nat.testBit m.val 1 = decide ((1 : Fin 3) ∈ Kused) := hbits.2.1
    have hbit2 : Nat.testBit m.val 2 = decide ((2 : Fin 3) ∈ Kused) := hbits.2.2
    have hKcard : Kused.card =
        (if Nat.testBit m.val 0 then 1 else 0) +
        (if Nat.testBit m.val 1 then 1 else 0) +
        (if Nat.testBit m.val 2 then 1 else 0) := by
      rw [hbit0, hbit1, hbit2]
      have hsum : Kused.card = ∑ k : Fin 3, if k ∈ Kused then 1 else 0 := by simp
      rw [hsum, Fin.sum_univ_three]
      simp
    -- Every element of target v not covered by the chosen pair masks must be covered by Usm.
    let u0 := if Nat.testBit m.val 0 then choiceSet (pairsOfTarget v 0) (c (pairsOfTarget v 0)) else ∅
    let u1 := if Nat.testBit m.val 1 then choiceSet (pairsOfTarget v 1) (c (pairsOfTarget v 1)) else ∅
    let u2 := if Nat.testBit m.val 2 then choiceSet (pairsOfTarget v 2) (c (pairsOfTarget v 2)) else ∅
    have hbig_cov : Ubig.biUnion (supp gs) ⊆ u0 ∪ u1 ∪ u2 := by
      intro p hp
      obtain ⟨u, hu, hpu⟩ := Finset.mem_biUnion.mp hp
      have huU : u ∈ U' := (Finset.mem_filter.mp hu).1
      have hu2 : 2 ≤ (supp gs u).card := (Finset.mem_filter.mp hu).2
      have hu14 : 14 ≤ u := by
        by_contra hlt14; push Not at hlt14
        rw [supp_input gs u hlt14] at hu2; simp at hu2
      have hult : u < 14 + gs.length := by
        by_contra hge; push Not at hge
        rw [supp_oob gs u hge] at hu2; simp at hu2
      set j := u - 14
      have hjeq : 14 + j = u := by omega
      have hjlt : j < gs.length := by omega
      have hjG2 : j ∈ G2 := by
        by_contra hnotG2
        have hjG1 : j ∈ G1 v :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, hjeq ▸ hu2, hjeq ▸ hsub' u huU, hnotG2⟩
        exact hno' j hjG1 (hjeq ▸ huU)
      obtain ⟨idx, -, hjidx⟩ := Finset.mem_biUnion.mp hjG2
      have hjf := Finset.mem_filter.mp hjidx
      obtain ⟨k, hk⟩ := pairMask_subset_target_iff v idx (supp gs (14 + j)) hjf.2.1 hjf.2.2 (hjeq ▸ hsub' u huU)
      have hkK : k ∈ Kused :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, u, hu, j, hk.symm ▸ hjidx, hjeq.symm⟩
      have hpsub : p ∈ choiceSet (pairsOfTarget v k) (c (pairsOfTarget v k)) := by
        rw [hk]; exact hc_sub idx j hjidx (hjeq.symm ▸ hpu)
      fin_cases k
      · have hb : Nat.testBit m.val 0 = true := by rw [hbit0]; exact decide_eq_true hkK
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (by dsimp [u0]; rw [hb]; simpa using hpsub))
      · have hb : Nat.testBit m.val 1 = true := by rw [hbit1]; exact decide_eq_true hkK
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (by dsimp [u1]; rw [hb]; simpa using hpsub))
      · have hb : Nat.testBit m.val 2 = true := by rw [hbit2]; exact decide_eq_true hkK
        exact Finset.mem_union_right _ (by dsimp [u2]; rw [hb]; simpa using hpsub)
    have hrem_cov : target v \ (u0 ∪ u1 ∪ u2) ⊆ Usm.biUnion (supp gs) := by
      intro p hp
      obtain ⟨hpt, hpnot⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨u, huU, hpu⟩ := Finset.mem_biUnion.mp (hcov' hpt)
      by_cases h2 : 2 ≤ (supp gs u).card
      · have huB : u ∈ Ubig := Finset.mem_filter.mpr ⟨huU, h2⟩
        exact absurd (hbig_cov (Finset.mem_biUnion.mpr ⟨u, huB, hpu⟩)) hpnot
      · exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_filter.mpr ⟨huU, by omega⟩, hpu⟩
    have hrem_le : (target v \ (u0 ∪ u1 ∪ u2)).card ≤ Usm.card := by
      calc (target v \ (u0 ∪ u1 ∪ u2)).card
          ≤ (Usm.biUnion (supp gs)).card := Finset.card_le_card hrem_cov
        _ ≤ ∑ u ∈ Usm, (supp gs u).card := Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ Usm, 1 := Finset.sum_le_sum (fun u hu => (Finset.mem_filter.mp hu).2)
        _ = Usm.card := by simp
    have hinf : targetMinG1 v c ≤
        ((if Nat.testBit m.val 0 then 1 else 0) +
         (if Nat.testBit m.val 1 then 1 else 0) +
         (if Nat.testBit m.val 2 then 1 else 0)) +
        (target v \ (u0 ∪ u1 ∪ u2)).card - 1 :=
      Finset.inf'_le _ (Finset.mem_univ m)
    omega
  -- Step 5: Combine everything with comb_bound!
  have hcb := comb_bound c
  have hcost_le : ∑ idx : Fin 6, choiceCost (c idx) ≤ G2.card := by
    rw [hG2_card]
    exact Finset.sum_le_sum (fun idx _ => hc_cost idx)
  have hG1_sum : ∑ v : Fin 4, targetMinG1 v c ≤ ∑ v : Fin 4, (G1 v).card :=
    Finset.sum_le_sum (fun v _ => hG1_lb v)
  change 20 ≤ gs.length
  omega

end PEqualNP.Outside.L_meta_12408_aux

theorem PEqualNP.Outside.L_meta_12408 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size ≤ 19 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14, (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false = Nat.testBit (p.val + 1) v.val)) :=
  fun ⟨C, hor, hsize, hcomp⟩ =>
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt hsize (by decide : 19 < 20))
      (PEqualNP.Outside.L_meta_12408_aux.main_lb C hor hcomp)

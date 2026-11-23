import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
-- The wire evaluation lemmas below are adapted from L-meta-718.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_initial (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_initial gs w
  rw [ht]; simp [hl]

theorem initial_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_initial gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, initial_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
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
        exact initial_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [initial_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]
-- Remove selected wires in descending order. Expanding a wire adds at most one
-- member to the set of wires that still have to be compared.
theorem cut (P : ℕ → Prop) [DecidablePred P] (D : ℕ → Finset ℕ)
    (older : ∀ w, P w → ∀ u ∈ D w, u < w) (binary : ∀ w, P w → (D w).card ≤ 2)
    (N : ℕ) (A : Finset ℕ) (bound : ∀ w ∈ A, P w → w < N) :
    ∃ F : Finset ℕ, F.card ≤ A.card + ((Finset.range N).filter P).card ∧
      (∀ w ∈ F, ¬ P w) ∧
      ∀ R : ℕ → Prop, (∀ w, P w → (∀ u ∈ D w, R u) → R w) →
        (∀ u ∈ F, R u) → ∀ w ∈ A, R w := by
  classical
  induction N generalizing A with
  | zero =>
    refine ⟨A, by simp, ?_, fun _ _ h => h⟩
    intro w hw hp
    exact Nat.not_lt_zero w (bound w hw hp)
  | succ N ih =>
    by_cases expand : N ∈ A ∧ P N
    · let B := A.erase N ∪ D N
      have small : ∀ w ∈ B, P w → w < N := by
        intro w hw hp
        rcases Finset.mem_union.mp hw with h | h
        · obtain ⟨hne, ha⟩ := Finset.mem_erase.mp h
          have := bound w ha hp
          omega
        · exact older N expand.2 w h
      obtain ⟨F, hF, hstop, hspec⟩ := ih B small
      have hu : B.card ≤ (A.erase N).card + (D N).card := Finset.card_union_le _ _
      have he := Finset.card_erase_add_one expand.1
      have hdeg := binary N expand.2
      have hcount : ((Finset.range (N+1)).filter P).card =
          ((Finset.range N).filter P).card + 1 := by
        simp [Finset.range_add_one, Finset.filter_insert, expand.2]
      refine ⟨F, by omega, hstop, ?_⟩
      intro R step hRF w hw
      have hb := hspec R step hRF
      by_cases eq : w = N
      · subst w
        exact step N expand.2 (fun u hu => hb u (Finset.mem_union_right _ hu))
      · exact hb w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq, hw⟩))
    · have small : ∀ w ∈ A, P w → w < N := by
        intro w hw hp
        have := bound w hw hp
        have ne : w ≠ N := by
          rintro rfl
          exact expand ⟨hw, hp⟩
        omega
      obtain ⟨F, hF, hstop, hspec⟩ := ih A small
      have mono : (Finset.range N).filter P ⊆ (Finset.range (N+1)).filter P := by
        intro w hw
        rw [Finset.mem_filter] at hw ⊢
        exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hw.1)), hw.2⟩
      exact ⟨F, hF.trans (Nat.add_le_add_left (Finset.card_le_card mono) _), hstop, hspec⟩
def preds (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  if w < n then ∅ else
    (((C.gates[w - n]?).map Gate.inputs).getD []).toFinset.filter (fun u => u < w)

theorem gate_preds (n : ℕ) (C : Circuit) {j : ℕ} {g : Gate} (hg : C.gates[j]? = some g) :
    preds n C (n+j) = g.inputs.toFinset.filter (fun u => u < n+j) := by
  simp [preds, hg]

theorem preds_older (n : ℕ) (C : Circuit) (w u : ℕ) (hu : u ∈ preds n C w) : u < w := by
  unfold preds at hu
  split at hu
  · simp at hu
  · exact (Finset.mem_filter.mp hu).2

def Legal (C : Circuit) : Prop := ∀ g ∈ C.gates,
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem gate_at (n : ℕ) (C : Circuit) {w : ℕ} (lo : n ≤ w) (hi : w < n+C.gates.length) :
    ∃ j g, w = n+j ∧ C.gates[j]? = some g ∧ g ∈ C.gates := by
  have h : w-n < C.gates.length := by omega
  exact ⟨w-n, C.gates[w-n], by omega, List.getElem?_eq_getElem h, List.getElem_mem h⟩

theorem pass_wire {n : ℕ} (C : Circuit) (hl : Legal C) (x y : Fin n → Bool)
    (w : ℕ) (lo : n ≤ w) (hi : w < n+C.gates.length)
    (hp : ∀ u ∈ preds n C w, val C x u = true → val C y u = true) :
    val C x w = true → val C y w = true := by
  obtain ⟨j,g,rfl,hg,hm⟩ := gate_at n C lo hi
  have lift' (a : ℕ) (ha : a ∈ g.inputs) : operand C x (n+j) a = true →
      operand C y (n+j) a = true := by
    by_cases h : a < n+j
    · simp only [operand, ite_eq_left h]
      apply hp a
      rw [gate_preds n C hg]
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ha, h⟩
    · simp [operand, h]
  rw [val_gate C x hg, val_gate C y hg]
  rcases (hl g hm).1 with ho | ho
  · simpa [ho, GateOp.eval, List.all_eq_true, Function.comp_def] using
      (fun (h : ∀ a ∈ g.inputs, operand C x (n+j) a = true) a ha =>
        lift' a ha (h a ha))
  · have h' : (∃ a ∈ g.inputs, operand C x (n+j) a = true) →
        ∃ a ∈ g.inputs, operand C y (n+j) a = true := by
      rintro ⟨a, ha, hx⟩
      exact ⟨a, ha, lift' a ha hx⟩
    simpa [ho, GateOp.eval, List.any_eq_true, Function.comp_def] using h'

theorem wire_mono {n : ℕ} (C : Circuit) (hl : Legal C) (x y : Fin n → Bool)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) : val C x w = true → val C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : w < n
    · have hx := val_input C x (⟨w,h⟩ : Fin n)
      have hy := val_input C y (⟨w,h⟩ : Fin n)
      simpa only [hx, hy] using hxy ⟨w,h⟩
    by_cases h' : w < n + C.gates.length
    · exact pass_wire C hl x y w (by omega) h' (fun u hu => ih u (preds_older n C w u hu))
    · rw [val_beyond C x (by omega)]
      simp

def unitBit {n : ℕ} (p : Fin n) (q : Fin n) : Bool := decide (q = p)

def accepts (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => val C (unitBit p) w = true)

theorem accept_mem {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ accepts n C w ↔ val C (unitBit p) w = true := by simp [accepts]

theorem accept_input {n : ℕ} (C : Circuit) (i : Fin n) : accepts n C i.val = {i} := by
  ext p
  simp [accept_mem, val_input, unitBit, eq_comm]

theorem accept_location {n : ℕ} (C : Circuit) {w : ℕ} (h : 2 ≤ (accepts n C w).card) :
    n ≤ w ∧ w < n+C.gates.length := by
  constructor
  · by_contra! lt
    have eq := accept_input C (⟨w,lt⟩ : Fin n)
    change accepts n C w = _ at eq
    simp [eq] at h
  · by_contra! ge
    have eq : accepts n C w = ∅ := by
      ext p
      simp [accept_mem, val_beyond C _ ge]
    simp [eq] at h

theorem local_bound {n : ℕ} (C : Circuit) (hl : Legal C) (w : ℕ)
    (hcard : 2 ≤ (accepts n C w).card) : (preds n C w).card ≤ 2 := by
  obtain ⟨lo, hi⟩ := accept_location C hcard
  obtain ⟨j,g,rfl,hg,hm⟩ := gate_at n C lo hi
  rw [gate_preds n C hg, ← (hl g hm).2]
  exact (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)
def Priv (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  accepts n C w ⊆ S ∧ 2 ≤ (accepts n C w).card

noncomputable def owned (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range (n+C.gates.length)).filter (Priv n C S)

-- The frontier has at most one more wire than the number of private gates.
-- A small exit can account for only one accepted singleton. Each other exit
-- can be activated by one point outside the prescribed set.
theorem count_one {n k c : ℕ} (C : Circuit) (hl : Legal C) (S : Finset (Fin n)) (o : ℕ)
    (ho : 2 ≤ (accepts n C o).card) (hs : c+1 ≤ (accepts n C o).card) (hk : c ≤ k)
    (promise : ∀ y : Fin n → Bool, (Finset.univ.filter (fun q => y q = true)).card ≤ k →
      (∀ q ∈ S, y q = false) → val C y o = false) :
    c ≤ (owned n C S).card := by
  classical
  by_contra! bad
  let P := Priv n C S
  obtain ⟨F, hsize, stop, recover⟩ := cut P (preds n C)
    (fun w _ u hu => preds_older n C w u hu)
    (fun w h => local_bound C hl w h.2) (n+C.gates.length) {o}
    (fun w hw _ => (Finset.mem_singleton.mp hw) ▸ (accept_location C ho).2)
  have hf : F.card ≤ c := by
    change (Finset.filter P (Finset.range (n+C.gates.length))).card < c at bad
    simp only [Finset.card_singleton] at hsize
    omega
  let small := F.filter (fun w => accepts n C w ⊆ S)
  let covered := small.biUnion (accepts n C)
  have hcover : covered.card ≤ small.card * 1 := by
    apply Finset.card_biUnion_le_card_mul
    intro w hw
    obtain ⟨inF, sub⟩ := Finset.mem_filter.mp hw
    by_contra! big
    exact stop w inF ⟨sub, by omega⟩
  have hcover' : covered.card < (accepts n C o).card := by
    have le : small.card ≤ F.card := Finset.card_filter_le _ _
    omega
  obtain ⟨p, hp, pfree⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover'
  let extPts (w : ℕ) : Finset (Fin n) :=
    if h : ∃ z ∈ accepts n C w, z ∉ S then {h.choose} else ∅
  let X := F.biUnion extPts
  have ext_le (w : ℕ) : (extPts w).card ≤ 1 := by
    unfold extPts
    split <;> simp
  have ext_spec (w : ℕ) (z : Fin n) (hz : z ∈ extPts w) : z ∈ accepts n C w ∧ z ∉ S := by
    unfold extPts at hz
    split at hz
    next h =>
      have eq := Finset.mem_singleton.mp hz
      exact eq ▸ h.choose_spec
    next => simp at hz
  have hX : X.card ≤ k := by
    have h : X.card ≤ F.card * 1 := Finset.card_biUnion_le_card_mul F extPts 1 (fun w _ => ext_le w)
    omega
  have hout (q : Fin n) (hq : q ∈ X) : q ∉ S := by
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hq
    exact (ext_spec w q hw).2
  let y := fun q : Fin n => decide (q ∈ X)
  have send (w : ℕ) (hw : w ∈ F) (on : val C (unitBit p) w = true) : val C y w = true := by
    have notsub : ¬ accepts n C w ⊆ S := by
      intro sub
      apply pfree
      exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, sub⟩, (accept_mem C w p).mpr on⟩
    have he := Finset.not_subset.mp notsub
    have chosen : he.choose ∈ extPts w := by simp [extPts, he]
    have hmem : he.choose ∈ X := Finset.mem_biUnion.mpr ⟨w, hw, chosen⟩
    apply wire_mono C hl (unitBit he.choose) y _ w
      ((accept_mem C w he.choose).mp (ext_spec w he.choose chosen).1)
    intro q hq
    have eq : q = he.choose := by simpa [unitBit] using hq
    simpa [y, eq] using hmem
  let R := fun w => val C (unitBit p) w = true → val C y w = true
  have advance (w : ℕ) (hP : P w) : (∀ u ∈ preds n C w, R u) → R w :=
    pass_wire C hl (unitBit p) y w (accept_location C hP.2).1 (accept_location C hP.2).2
  have yes := recover R advance send o (Finset.mem_singleton.mpr rfl) ((accept_mem C o p).mp hp)
  have no := promise y (by simpa [y] using hX) (fun q hq => by
    have hx : q ∉ X := fun hin => hout q hin hq
    simp [y, hx])
  simp [no] at yes

theorem finish {n m k : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (c : Fin m → ℕ)
    (meet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (two : ∀ i, 2 ≤ (accepts n C (o i)).card) (hl : Legal C)
    (promise : ∀ i (y : Fin n → Bool), (Finset.univ.filter (fun q => y q = true)).card ≤ k →
      (∀ q ∈ S i, y q = false) → val C y (o i) = false)
    (hk : ∀ i, c i ≤ k) (hs : ∀ i, c i+1 ≤ (accepts n C (o i)).card) :
    ∑ i, c i ≤ C.size := by
  classical
  let G := fun i => owned n C (S i)
  have localCount (i : Fin m) : c i ≤ (G i).card :=
    count_one C hl (S i) (o i) (two i) (hs i) (hk i) (promise i)
  have dis : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ ne
    apply Finset.disjoint_left.mpr
    intro w hi hj
    have a : Priv n C (S i) w := (Finset.mem_filter.mp hi).2
    have b : Priv n C (S j) w := (Finset.mem_filter.mp hj).2
    have sub : accepts n C w ⊆ S i ∩ S j := Finset.subset_inter a.1 b.1
    have h := (Finset.card_le_card sub).trans (meet i j ne)
    have h' := a.2
    omega
  have incl : Finset.univ.biUnion G ⊆ Finset.Ico n (n+C.gates.length) := by
    intro w hw
    obtain ⟨i, _, h⟩ := Finset.mem_biUnion.mp hw
    have a : Priv n C (S i) w := (Finset.mem_filter.mp h).2
    exact Finset.mem_Ico.mpr (accept_location C a.2)
  calc
    ∑ i, c i ≤ ∑ i, (G i).card := Finset.sum_le_sum (fun i _ => localCount i)
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion dis).symm
    _ ≤ (Finset.Ico n (n+C.gates.length)).card := Finset.card_le_card incl
    _ = C.size := by simp [Circuit.size]

end PEqualNP.Outside.L_meta_782_aux

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c meet two legal _ promise hk hs
  exact PEqualNP.Outside.L_meta_782_aux.finish S C o c meet two legal promise hk hs

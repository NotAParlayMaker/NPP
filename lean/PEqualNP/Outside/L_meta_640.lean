import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_640_aux

-- The singleton-input accounting and evaluation lemmas adapt the checked proof of L-meta-666.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Mask := Finset (Fin 7)
def line (w : Fin 7) : Mask := ![{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6}, {2,4,5}] w

-- A pair or a four-point set can help one line. A five-point set can help two.
def credit (s : Mask) (w : Fin 7) : ℕ :=
  if s = line w then 2 else
  if s.card = 2 ∧ s ⊆ line w then 2 else
  if s.card = 4 ∧ line w ⊆ s then 2 else
  if s.card = 5 ∧ line w ⊆ s then 1 else
  if sᶜ = line w then 2 else 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
lemma capacity : ∀ s : Mask, ∑ w, credit s w ≤ 2 := by decide +kernel

-- The complement of a line contains no line, so this extra credit fits the same capacity.
lemma compl_credit : ∀ w, credit (line w)ᶜ w = 2 := by decide +kernel

lemma line_card : ∀ w, (line w).card = 3 := by decide
lemma initial_credit : ∀ w : Fin 7, credit ∅ w = 0 ∧ credit Finset.univ w = 0 ∧
    ∀ v : Fin 7, credit {v} w = 0 := by decide

def amount (S : Finset Mask) (w : Fin 7) := ∑ s ∈ S, credit s w
def budget (S : Finset Mask) := ∑ w, amount S w

lemma cost {S : Finset Mask} {s : Mask} (w : Fin 7) (hs : s ∈ S) :
    credit s w ≤ amount S w := Finset.single_le_sum (f := fun s => credit s w) (fun _ _ => Nat.zero_le _) hs

lemma pair_cost {S : Finset Mask} {s t : Mask} (w : Fin 7)
    (hs : s ∈ S) (ht : t ∈ S) (hne : s ≠ t) : credit s w + credit t w ≤ amount S w := by
  have hsub : ({s,t} : Finset Mask) ⊆ S := by
    intro u hu
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl|rfl <;> assumption
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun x => credit x w) hsub (fun _ _ _ => Nat.zero_le _)
  simpa [hne,amount] using this

lemma union_cost {S : Finset Mask} {s t : Mask} {w} (hs : s ∈ S) (ht : t ∈ S)
    (hn : line w ∉ S) (h : s ∪ t = line w) : 2 ≤ amount S w := by
  have sub1 : s ⊆ line w := h ▸ Finset.subset_union_left
  have sub2 : t ⊆ line w := h ▸ Finset.subset_union_right
  have n1 : s ≠ line w := fun e => hn (e ▸ hs)
  have n2 : t ≠ line w := fun e => hn (e ▸ ht)
  have a := Finset.card_lt_card (ssubset_of_subset_of_ne sub1 n1)
  have b := Finset.card_lt_card (ssubset_of_subset_of_ne sub2 n2)
  have c := Finset.card_union_le s t
  rw [h,line_card] at c
  rw [line_card] at a b
  rcases (show s.card = 2 ∨ t.card = 2 by omega) with e|e
  · simpa [credit,n1,e,sub1] using cost w hs
  · simpa [credit,n2,e,sub2] using cost w ht

lemma inter_cost {S : Finset Mask} {s t : Mask} {w} (hs : s ∈ S) (ht : t ∈ S)
    (hn : line w ∉ S) (h : s ∩ t = line w) : 2 ≤ amount S w := by
  have sub1 : line w ⊆ s := h ▸ Finset.inter_subset_left
  have sub2 : line w ⊆ t := h ▸ Finset.inter_subset_right
  have n1 : s ≠ line w := fun e => hn (e ▸ hs)
  have n2 : t ≠ line w := fun e => hn (e ▸ ht)
  have a := Finset.card_lt_card (ssubset_of_subset_of_ne sub1 n1.symm)
  have b := Finset.card_lt_card (ssubset_of_subset_of_ne sub2 n2.symm)
  rw [line_card] at a b
  have c := Finset.card_union_add_card_inter s t
  rw [h,line_card] at c
  have d : (s ∪ t).card ≤ 7 := (s ∪ t).card_le_univ
  by_cases es : s.card = 4
  · simpa [credit,n1,es,sub1] using cost w hs
  by_cases et : t.card = 4
  · simpa [credit,n2,et,sub2] using cost w ht
  have hne : s ≠ t := by rintro rfl; simp [n1] at h
  have s5 : s.card = 5 := by omega
  have t5 : t.card = 5 := by omega
  simpa [credit,n1,n2,s5,t5,sub1,sub2] using pair_cost w hs ht hne

def pool (xs : List Mask) : Finset Mask := insert ∅ (insert Finset.univ xs.toFinset)
def val (xs : List Mask) (i : ℕ) : Mask := xs.getD i ∅
def gateMask (xs : List Mask) (g : Gate) : Mask :=
  Finset.univ.filter (fun v => g.op.eval (g.inputs.map (fun i => decide (v ∈ val xs i))))

lemma available (xs : List Mask) (i : ℕ) : val xs i ∈ pool xs := by
  by_cases h : i < xs.length
  · unfold val
    rw [List.getD_eq_getElem _ _ h]
    simp [pool,List.getElem_mem]
  · unfold val
    rw [List.getD_eq_default _ _ (by omega : xs.length ≤ i)]
    simp [pool]

lemma gate_cost (xs : List Mask) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (w : Fin 7) (hn : line w ∉ pool xs) (he : gateMask xs g = line w) :
    2 ≤ amount (pool xs) w := by
  obtain ⟨op,ins⟩ := g
  rcases hg with ⟨ha,hl⟩
  change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at ha
  change ins.length ≤ 2 at hl
  have non (s : Mask) (hm : s ∈ pool xs) (eq : s = line w) : False := hn (eq ▸ hm)
  have neg (i : ℕ) (h : (val xs i)ᶜ = line w) : 2 ≤ amount (pool xs) w := by
    have eq : val xs i = (line w)ᶜ := by rw [← h, compl_compl]
    have hcost := cost w (available xs i)
    rwa [eq, compl_credit] at hcost
  cases ins with
  | nil =>
    rcases ha with rfl|rfl|rfl <;> simp [gateMask,GateOp.eval] at he <;>
      exact (non _ (by simp [pool]) he).elim
  | cons i l =>
    cases l with
    | nil =>
      rcases ha with rfl|rfl|rfl
      · simp [gateMask,GateOp.eval] at he
        exact (non _ (available xs i) he).elim
      · simp [gateMask,GateOp.eval] at he
        exact (non _ (available xs i) he).elim
      · apply neg i
        rw [← he]
        ext v
        simp [gateMask,GateOp.eval]
    | cons j l =>
      cases l with
      | cons k l => simp at hl
      | nil =>
        rcases ha with rfl|rfl|rfl
        · apply inter_cost (available xs i) (available xs j) hn
          rw [← he]
          ext v
          simp [gateMask,GateOp.eval]
        · apply union_cost (available xs i) (available xs j) hn
          rw [← he]
          ext v
          simp [gateMask,GateOp.eval]
        · apply neg i
          rw [← he]
          ext v
          simp [gateMask,GateOp.eval]

def rich (xs : List Mask) := ∀ w, line w ∈ pool xs → 4 ≤ amount (pool xs) w
def next (xs : List Mask) (g : Gate) := xs ++ [gateMask xs g]

lemma pool_next (xs : List Mask) (g : Gate) : pool (next xs g) = insert (gateMask xs g) (pool xs) := by
  ext s
  simp [pool,next,or_assoc,or_comm]

lemma push (xs : List Mask) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) (h : rich xs) :
    rich (next xs g) ∧ budget (pool (next xs g)) ≤ budget (pool xs) + 2 := by
  by_cases hm : gateMask xs g ∈ pool xs
  · simpa [rich,pool_next,Finset.insert_eq_of_mem hm] using h
  have add (w : Fin 7) : amount (pool (next xs g)) w =
      credit (gateMask xs g) w + amount (pool xs) w := by simp [amount,pool_next,hm]
  constructor
  · intro w hw
    rw [pool_next,Finset.mem_insert] at hw
    rw [add]
    rcases hw with eq|old
    · have hh := gate_cost xs g hg w (fun e => hm (eq ▸ e)) eq.symm
      rw [← eq]
      simp [credit]
      omega
    · exact (h w old).trans (Nat.le_add_left _ _)
  · simp only [budget,add,Finset.sum_add_distrib]
    have := capacity (gateMask xs g)
    omega

def initial : List Mask := List.ofFn fun v : Fin 7 => {v}
lemma init_rich : rich initial := by unfold rich; decide +kernel
lemma init_budget : budget (pool initial) = 0 := by decide +kernel

lemma accumulate (gs : List Gate) (xs : List Mask) (hr : rich xs)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    rich (gs.foldl next xs) ∧ budget (pool (gs.foldl next xs)) ≤ budget (pool xs) + 2*gs.length := by
  induction gs generalizing xs with
  | nil => simp [hr]
  | cons g gs ih =>
    obtain ⟨h1,h2⟩ := push xs g (hg g (by simp)) hr
    obtain ⟨h3,h4⟩ := ih (next xs g) h1 (fun z hz => hg z (by simp [hz]))
    exact ⟨h3,by simp only [List.foldl_cons,List.length_cons]; omega⟩

def bit (v : Fin 7) (s : Mask) : Bool := decide (v ∈ s)
def boolGate (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

lemma read_bit (v : Fin 7) (xs : List Mask) (i : ℕ) :
    (xs.map (bit v)).getD i false = bit v (val xs i) := by
  have e : bit v ∅ = false := by simp [bit]
  rw [← e]
  exact List.getD_map xs ∅ (bit v)

lemma map_next (v : Fin 7) (xs : List Mask) (g : Gate) :
    (next xs g).map (bit v) = boolGate (xs.map (bit v)) g := by
  simp only [next,boolGate,List.map_append,List.map_cons,List.map_nil,read_bit]
  congr 2
  simp [bit,gateMask]

lemma map_run (v : Fin 7) (gs : List Gate) (xs : List Mask) :
    (gs.foldl next xs).map (bit v) = gs.foldl boolGate (xs.map (bit v)) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih => rw [List.foldl_cons,List.foldl_cons,ih,map_next]

lemma eval_bit (v : Fin 7) (gs : List Gate) (o : ℕ) :
    (Circuit.mk gs o).eval (List.ofFn (fun i : Fin 7 => decide (i = v))) =
      bit v (val (gs.foldl next initial) o) := by
  have hi : initial.map (bit v) = List.ofFn (fun i : Fin 7 => decide (i = v)) := by
    simp [initial,bit,eq_comm]
  change (gs.foldl boolGate _).getD o false = _
  rw [← hi,← map_run,read_bit]


private def construction : Circuit :=
  { gates := [
      ⟨.or, [0, 1]⟩,
      ⟨.or, [7, 2]⟩,
      ⟨.or, [0, 3]⟩,
      ⟨.or, [9, 4]⟩,
      ⟨.or, [0, 5]⟩,
      ⟨.or, [11, 6]⟩,
      ⟨.or, [1, 3]⟩,
      ⟨.or, [13, 5]⟩,
      ⟨.or, [1, 4]⟩,
      ⟨.or, [15, 6]⟩,
      ⟨.or, [2, 3]⟩,
      ⟨.or, [17, 6]⟩,
      ⟨.or, [2, 4]⟩,
      ⟨.or, [19, 5]⟩],
    output := 20 }

private theorem upper : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) := by
  refine ⟨construction, ?_, by decide, fun j => 8 + 2 * j.val, ?_⟩
  · intro g hg
    simp only [construction, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  · intro x
    have inp : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := rfl
    rw [inp]
    simp [construction, Circuit.wires, GateOp.eval]

private theorem lower : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) := by
  rintro ⟨C, hf, hs, out, ho⟩
  let xs := C.gates.foldl next initial
  have all_lines (w : Fin 7) : line w ∈ pool xs := by
    have he : val xs (out w) = line w := by
      ext v
      have ev (u : Fin 7) : ((C.wires (List.ofFn (fun i : Fin 7 => decide (i = v)))).getD (out u) false = true) ↔
          v ∈ val xs (out u) := by
        have eq : (C.wires (List.ofFn (fun i : Fin 7 => decide (i = v)))).getD (out u) false =
            bit v (val xs (out u)) := eval_bit v C.gates (out u)
        rw [eq]
        exact decide_eq_true_iff
      obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := ho (fun i => decide (i = v))
      fin_cases w
      · change v ∈ val xs (out 0) ↔ v ∈ line 0
        rw [← ev 0, h0]
        exact (show ∀ z : Fin 7, (decide ((0 : Fin 7) = z) || decide ((1 : Fin 7) = z) || decide ((2 : Fin 7) = z)) = true ↔ z ∈ line 0 by decide) v
      · change v ∈ val xs (out 1) ↔ v ∈ line 1
        rw [← ev 1, h1]
        exact (show ∀ z : Fin 7, (decide ((0 : Fin 7) = z) || decide ((3 : Fin 7) = z) || decide ((4 : Fin 7) = z)) = true ↔ z ∈ line 1 by decide) v
      · change v ∈ val xs (out 2) ↔ v ∈ line 2
        rw [← ev 2, h2]
        exact (show ∀ z : Fin 7, (decide ((0 : Fin 7) = z) || decide ((5 : Fin 7) = z) || decide ((6 : Fin 7) = z)) = true ↔ z ∈ line 2 by decide) v
      · change v ∈ val xs (out 3) ↔ v ∈ line 3
        rw [← ev 3, h3]
        exact (show ∀ z : Fin 7, (decide ((1 : Fin 7) = z) || decide ((3 : Fin 7) = z) || decide ((5 : Fin 7) = z)) = true ↔ z ∈ line 3 by decide) v
      · change v ∈ val xs (out 4) ↔ v ∈ line 4
        rw [← ev 4, h4]
        exact (show ∀ z : Fin 7, (decide ((1 : Fin 7) = z) || decide ((4 : Fin 7) = z) || decide ((6 : Fin 7) = z)) = true ↔ z ∈ line 4 by decide) v
      · change v ∈ val xs (out 5) ↔ v ∈ line 5
        rw [← ev 5, h5]
        exact (show ∀ z : Fin 7, (decide ((2 : Fin 7) = z) || decide ((3 : Fin 7) = z) || decide ((6 : Fin 7) = z)) = true ↔ z ∈ line 5 by decide) v
      · change v ∈ val xs (out 6) ↔ v ∈ line 6
        rw [← ev 6, h6]
        exact (show ∀ z : Fin 7, (decide ((2 : Fin 7) = z) || decide ((4 : Fin 7) = z) || decide ((5 : Fin 7) = z)) = true ↔ z ∈ line 6 by decide) v
    exact he ▸ available xs (out w)
  have ops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hf g hg
  obtain ⟨hr,hb⟩ := accumulate C.gates initial init_rich ops
  have bound : (∑ _w : Fin 7, (4 : ℕ)) ≤ budget (pool xs) :=
    Finset.sum_le_sum (fun w _ => hr w (all_lines w))
  change budget (pool xs) ≤ _ at hb
  rw [init_budget] at hb
  simp at bound
  change C.gates.length ≤ 13 at hs
  omega

end PEqualNP.Outside.L_meta_640_aux

open PEqualNP.Outside.L_meta_640_aux

theorem PEqualNP.Outside.L_meta_640 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) ∧ ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) :=
  ⟨upper, lower⟩

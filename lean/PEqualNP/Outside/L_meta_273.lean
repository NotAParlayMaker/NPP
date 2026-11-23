import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_273_aux

open PEqualNP.CircuitLowerBounds
abbrev Mask := Finset (Fin 6)
def line (w : Fin 3) : Mask := (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) w

def credit (s : Mask) (w : Fin 3) : ℕ :=
  if s = line w then 2 else
  if s.card = 2 ∧ s ⊆ line w then 2 else
  if s.card = 4 ∧ line w ⊆ s then 2 else
  if s.card = 5 ∧ line w ⊆ s then 1 else 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
lemma capacity : ∀ s : Mask, ∑ w, credit s w ≤ 2 := by decide +kernel

lemma line_card : ∀ w, (line w).card = 3 := by decide
lemma initial_credit : ∀ w : Fin 3, credit ∅ w = 0 ∧ credit Finset.univ w = 0 ∧
    ∀ v : Fin 6, credit {v} w = 0 := by decide

def amount (S : Finset Mask) (w : Fin 3) := ∑ s ∈ S, credit s w
def budget (S : Finset Mask) := ∑ w, amount S w

lemma cost {S : Finset Mask} {s : Mask} (w : Fin 3) (hs : s ∈ S) :
    credit s w ≤ amount S w := Finset.single_le_sum (f := fun s => credit s w) (fun _ _ => Nat.zero_le _) hs

lemma pair_cost {S : Finset Mask} {s t : Mask} (w : Fin 3)
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
  have d : (s ∪ t).card ≤ 6 := (s ∪ t).card_le_univ
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
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 3) (hn : line w ∉ pool xs) (he : gateMask xs g = line w) :
    2 ≤ amount (pool xs) w := by
  obtain ⟨op,ins⟩ := g
  rcases hg with ⟨ha,hl⟩
  change op = GateOp.and ∨ op = GateOp.or at ha
  change ins.length ≤ 2 at hl
  have non (s : Mask) (hm : s ∈ pool xs) (eq : s = line w) : False := hn (eq ▸ hm)
  cases ins with
  | nil =>
    rcases ha with rfl|rfl <;> simp [gateMask,GateOp.eval] at he <;>
      exact (non _ (by simp [pool]) he).elim
  | cons i l =>
    cases l with
    | nil =>
      rcases ha with rfl|rfl <;> simp [gateMask,GateOp.eval] at he <;>
        exact (non _ (available xs i) he).elim
    | cons j l =>
      cases l with
      | cons k l => simp at hl
      | nil =>
        rcases ha with rfl|rfl
        · apply inter_cost (available xs i) (available xs j) hn
          rw [← he]
          ext v
          simp [gateMask,GateOp.eval]
        · apply union_cost (available xs i) (available xs j) hn
          rw [← he]
          ext v
          simp [gateMask,GateOp.eval]

def rich (xs : List Mask) := ∀ w, line w ∈ pool xs → 4 ≤ amount (pool xs) w
def next (xs : List Mask) (g : Gate) := xs ++ [gateMask xs g]

lemma pool_next (xs : List Mask) (g : Gate) : pool (next xs g) = insert (gateMask xs g) (pool xs) := by
  ext s
  simp [pool,next,or_assoc,or_comm]

lemma push (xs : List Mask) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) (h : rich xs) :
    rich (next xs g) ∧ budget (pool (next xs g)) ≤ budget (pool xs) + 2 := by
  by_cases hm : gateMask xs g ∈ pool xs
  · simpa [rich,pool_next,Finset.insert_eq_of_mem hm] using h
  have add (w : Fin 3) : amount (pool (next xs g)) w =
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

def initial : List Mask := List.ofFn fun v : Fin 6 => {v}
lemma init_rich : rich initial := by unfold rich; decide +kernel
lemma init_budget : budget (pool initial) = 0 := by decide +kernel

lemma accumulate (gs : List Gate) (xs : List Mask) (hr : rich xs)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    rich (gs.foldl next xs) ∧ budget (pool (gs.foldl next xs)) ≤ budget (pool xs) + 2*gs.length := by
  induction gs generalizing xs with
  | nil => simp [hr]
  | cons g gs ih =>
    obtain ⟨h1,h2⟩ := push xs g (hg g (by simp)) hr
    obtain ⟨h3,h4⟩ := ih (next xs g) h1 (fun z hz => hg z (by simp [hz]))
    exact ⟨h3,by simp only [List.foldl_cons,List.length_cons]; omega⟩

def bit (v : Fin 6) (s : Mask) : Bool := decide (v ∈ s)
def boolGate (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

lemma read_bit (v : Fin 6) (xs : List Mask) (i : ℕ) :
    (xs.map (bit v)).getD i false = bit v (val xs i) := by
  have e : bit v ∅ = false := by simp [bit]
  rw [← e]
  exact List.getD_map xs ∅ (bit v)

lemma map_next (v : Fin 6) (xs : List Mask) (g : Gate) :
    (next xs g).map (bit v) = boolGate (xs.map (bit v)) g := by
  simp only [next,boolGate,List.map_append,List.map_cons,List.map_nil,read_bit]
  congr 2
  simp [bit,gateMask]

lemma map_run (v : Fin 6) (gs : List Gate) (xs : List Mask) :
    (gs.foldl next xs).map (bit v) = gs.foldl boolGate (xs.map (bit v)) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih => rw [List.foldl_cons,List.foldl_cons,ih,map_next]

lemma eval_bit (v : Fin 6) (gs : List Gate) (o : ℕ) :
    (gs.foldl boolGate (List.ofFn (fun i : Fin 6 => decide (i = v)))).getD o false =
      bit v (val (gs.foldl next initial) o) := by
  have hi : initial.map (bit v) = List.ofFn (fun i : Fin 6 => decide (i = v)) := by
    simp [initial,bit,eq_comm]
  rw [← hi,← map_run,read_bit]

end PEqualNP.Outside.L_meta_273_aux

open PEqualNP.Outside.L_meta_273_aux

theorem PEqualNP.Outside.L_meta_273 : ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 3 → ℕ), C.size ≤ 5 ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ ∀ i : Fin 3, (∀ p : Fin 6, (C.wires (List.ofFn (fun q : Fin 6 => decide (q = p)))).getD (o i) false = true ↔ p ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i) ∧ ∀ x : Fin 6 → Bool, (Finset.univ.filter (fun q : Fin 6 => x q = true)).card ≤ 2 → (∀ q ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false := by
  rintro ⟨C, o, hs, hg, ho⟩
  let xs := C.gates.foldl next initial
  have all_lines (w : Fin 3) : line w ∈ pool xs := by
    have he : val xs (o w) = line w := by
      ext v
      have h := (ho w).1 v
      have e : (C.wires (List.ofFn (fun q : Fin 6 => decide (q = v)))).getD (o w) false =
          bit v (val xs (o w)) := eval_bit v C.gates (o w)
      rw [e] at h
      simpa [bit,line] using h
    exact he ▸ available xs (o w)
  obtain ⟨hr,hb⟩ := accumulate C.gates initial init_rich
    (fun g m => ⟨(hg g m).1, (hg g m).2.le⟩)
  have lower : (∑ _w : Fin 3, (4 : ℕ)) ≤ budget (pool xs) :=
    Finset.sum_le_sum (fun w _ => hr w (all_lines w))
  change budget (pool xs) ≤ _ at hb
  rw [init_budget] at hb
  have hs2 : C.gates.length ≤ 5 := hs
  simp at lower
  omega

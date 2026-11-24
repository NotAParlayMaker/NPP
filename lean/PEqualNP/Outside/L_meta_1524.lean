import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1524

open PEqualNP.CircuitLowerBounds

abbrev Point := Fin 13
abbrev Support := Finset Point

def line (idx : Point) : Support := {idx, idx + 1, idx + 3, idx + 9}

lemma four : ∀ idx, (line idx).card = 4 := by decide

set_option maxRecDepth 12000 in
lemma intersection : ∀ left right, left ≠ right → (line left ∩ line right).card ≤ 1 := by
  decide

def hit (bits : Point → Bool) (support : Support) :=
  decide (∃ point ∈ support, bits point = true)

lemma lookup (bits : Point → Bool) (wires : List Support) (idx : ℕ) :
    (wires.map (hit bits)).getD idx false = hit bits (wires.getD idx ∅) := by
  simpa [hit] using List.getD_map wires (∅ : Support) (n := idx) (hit bits)

def Available (wires : List Support) (part : Support) := part.card ≤ 1 ∨ part ∈ wires

lemma available_lookup (wires : List Support) (idx : ℕ) : Available wires (wires.getD idx ∅) := by
  by_cases bound : idx < wires.length
  · right
    rw [List.getD_eq_getElem _ _ bound]
    exact List.getElem_mem ..
  · left
    rw [List.getD_eq_default _ _ (Nat.le_of_not_gt bound)]
    decide

def Budget (wires : List Support) (idx : Point) (cost : ℕ) : Prop :=
  ∀ family : Finset Support, (∀ part ∈ family, part ⊆ line idx ∧ Available wires part) →
    (family.biUnion id).card ≤ family.card + cost

lemma extend_budget (wires : List Support) (idx : Point) (cost : ℕ) (left right : Support)
    (old : Budget wires idx cost) (ha : Available wires left) (hb : Available wires right) :
    Budget (wires ++ [left ∪ right]) idx
      (cost + if 1 < (left ∪ right).card ∧ left ∪ right ⊆ line idx then 1 else 0) := by
  intro family valid
  by_cases active : left ∪ right ∈ family ∧ 1 < (left ∪ right).card
  · have inside := (valid _ active.1).1
    simp only [active.2, inside, and_self, if_true]
    let rest := family.erase (left ∪ right)
    let prev := insert left (insert right rest)
    have validPrev : ∀ part ∈ prev, part ⊆ line idx ∧ Available wires part := by
      intro part hp
      simp only [prev, Finset.mem_insert] at hp
      rcases hp with rfl | rfl | hp
      · exact ⟨Finset.Subset.trans Finset.subset_union_left inside, ha⟩
      · exact ⟨Finset.Subset.trans Finset.subset_union_right inside, hb⟩
      · obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hp
        obtain ⟨sub, small | avail⟩ := valid _ mem
        · exact ⟨sub, Or.inl small⟩
        · exact ⟨sub, Or.inr (by simpa [ne] using avail)⟩
    have equalUnion : family.biUnion id = prev.biUnion id := by
      have orig : insert (left ∪ right) rest = family := Finset.insert_erase active.1
      conv_lhs => rw [← orig]
      simp [prev, Finset.biUnion_insert, Finset.union_assoc]
    have estimate := old prev validPrev
    have eraseSize := Finset.card_erase_add_one active.1
    have insLeft := Finset.card_insert_le left (insert right rest)
    have insRight := Finset.card_insert_le right rest
    rw [equalUnion]
    change (prev.biUnion id).card ≤ family.card + (cost + 1)
    change prev.card ≤ (insert right rest).card + 1 at insLeft
    change rest.card + 1 = family.card at eraseSize
    omega
  · have bound := old family (by
      intro part hp
      obtain ⟨sub, small | avail⟩ := valid _ hp
      · exact ⟨sub, Or.inl small⟩
      · simp only [List.mem_append, List.mem_singleton] at avail
        rcases avail with avail | rfl
        · exact ⟨sub, Or.inr avail⟩
        · exact ⟨sub, Or.inl (by by_contra! big; exact active ⟨hp, big⟩)⟩)
    omega

lemma total_charge (part : Support) :
    (∑ idx : Point, if 1 < part.card ∧ part ⊆ line idx then 1 else 0 : ℕ) ≤ 1 := by
  by_cases ex : ∃ idx, 1 < part.card ∧ part ⊆ line idx
  · obtain ⟨owner, big, sub⟩ := ex
    have unique : ∀ idx, (1 < part.card ∧ part ⊆ line idx) ↔ idx = owner := by
      intro idx
      constructor
      · intro prop
        by_contra ne
        have bound := Finset.card_le_card (Finset.subset_inter prop.2 sub)
        have small := intersection idx owner ne
        omega
      · rintro rfl
        exact ⟨big, sub⟩
    simp [unique]
  · simp [show ∀ idx, ¬ (1 < part.card ∧ part ⊆ line idx) from fun idx hp => ex ⟨idx, hp⟩]

lemma split_gate (gate : Gate) (wires : List Support) (op : gate.op = GateOp.or)
    (arity : gate.inputs.length ≤ 2) :
    ∃ left right : Support, Available wires left ∧ Available wires right ∧
      ∀ bits : Point → Bool,
        gate.op.eval (gate.inputs.map fun idx => (wires.map (hit bits)).getD idx false) =
          hit bits (left ∪ right) := by
  have empty : Available wires ∅ := Or.inl (by simp)
  cases inputs : gate.inputs with
  | nil => exact ⟨∅, ∅, empty, empty, by simp [op, GateOp.eval, hit]⟩
  | cons first tail =>
    cases tail with
    | nil =>
      refine ⟨wires.getD first ∅, ∅, available_lookup .., empty, ?_⟩
      intro bits
      simp only [List.map_cons, List.map_nil, lookup]
      simp [op, GateOp.eval]
    | cons second more =>
      have nilMore : more = [] := by simpa [inputs] using arity
      subst more
      refine ⟨_, _, available_lookup wires first, available_lookup wires second, ?_⟩
      intro bits
      simp only [List.map_cons, List.map_nil, lookup]
      simp [op, GateOp.eval, hit, Finset.mem_union, or_and_right, exists_or]

def run (gates : List Gate) (values : List Bool) :=
  gates.foldl (fun acc gate => acc ++ [gate.op.eval (gate.inputs.map fun idx => acc.getD idx false)]) values

lemma simulate (gates : List Gate) (wires : List Support) (cost : Point → ℕ)
    (ops : ∀ gate ∈ gates, gate.op = GateOp.or ∧ gate.inputs.length ≤ 2)
    (valid : ∀ idx, Budget wires idx (cost idx)) :
    ∃ (finalWires : List Support) (finalCost : Point → ℕ),
      (∀ bits, run gates (wires.map (hit bits)) = finalWires.map (hit bits)) ∧
      (∀ idx, Budget finalWires idx (finalCost idx)) ∧
      (∑ idx, finalCost idx) ≤ (∑ idx, cost idx) + gates.length := by
  induction gates generalizing wires cost with
  | nil => exact ⟨wires, cost, fun _ => rfl, valid, by simp⟩
  | cons gate tail ih =>
    have spec := ops gate (by simp)
    obtain ⟨left, right, ha, hb, step⟩ := split_gate gate wires spec.1 spec.2
    let newCost := fun idx => cost idx + if 1 < (left ∪ right).card ∧ left ∪ right ⊆ line idx then 1 else 0
    obtain ⟨finalWires, finalCost, sem, validFinal, limit⟩ := ih (wires ++ [left ∪ right]) newCost
      (fun item mem => ops item (List.mem_cons_of_mem _ mem))
      (fun idx => extend_budget wires idx _ left right (valid idx) ha hb)
    refine ⟨finalWires, finalCost, ?_, validFinal, ?_⟩
    · intro bits
      rw [← sem]
      simp only [run, List.foldl_cons, step, List.map_append, List.map_cons, List.map_nil]
    · simp only [newCost, Finset.sum_add_distrib] at limit
      have charge := total_charge (left ∪ right)
      simp only [List.length_cons]
      omega

end PEqualNP.Outside.L_meta_1524

open PEqualNP.Outside.L_meta_1524

theorem PEqualNP.Outside.L_meta_1524 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    39 ≤ gates.length := by
  intro lines lineEq gates outputs ops correct
  let initial := List.ofFn (fun point : Point => ({point} : Support))
  have valid : ∀ idx, Budget initial idx 0 := by
    intro idx family avail
    have small : ∀ part ∈ family, part.card ≤ 1 := by
      intro part mem
      rcases (avail part mem).2 with bound | input
      · exact bound
      · simp only [initial, List.mem_ofFn] at input
        obtain ⟨point, rfl⟩ := input
        simp
    calc
      _ ≤ ∑ part ∈ family, part.card := Finset.card_biUnion_le
      _ ≤ ∑ _part ∈ family, 1 := Finset.sum_le_sum small
      _ = _ := by simp
  obtain ⟨wires, cost, sem, budgets, limit⟩ := simulate gates initial (fun _ => 0) ops valid
  have semantic (idx : Point) (bits : Point → Bool) :
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, outputs idx⟩ (List.ofFn bits) =
      hit bits (wires.getD (outputs idx) ∅) := by
    have initialEq : initial.map (hit bits) = List.ofFn bits := by
      simp [initial, hit]
    change (run gates (List.ofFn bits)).getD _ false = _
    rw [← initialEq, sem, lookup]
  have supportEq (idx : Point) : wires.getD (outputs idx) ∅ = lines idx := by
    let part := wires.getD (outputs idx) ∅
    change part = lines idx
    have test (extra : Support) :
        (∃ point ∈ part, point ∉ lines idx ∨ point ∈ extra) ↔
        ∃ point ∈ lines idx, point ∉ lines idx ∨ point ∈ extra := by
      let bits := fun point => decide (point ∉ lines idx ∨ point ∈ extra)
      have agree := correct idx bits (Or.inr ⟨idx, by
        intro point zero
        by_contra outside
        simp [bits, outside] at zero⟩)
      rw [semantic] at agree
      simpa [part, bits, hit] using agree
    ext point
    constructor
    · intro mem
      by_contra outside
      have impossible := (test ∅).mp ⟨point, mem, Or.inl outside⟩
      simp at impossible
    · intro mem
      have sub : part ⊆ lines idx := by
        intro other inside
        by_contra outside
        have impossible := (test ∅).mp ⟨other, inside, Or.inl outside⟩
        simp at impossible
      obtain ⟨other, inside, outside | equal⟩ := (test {point}).mpr ⟨point, mem, Or.inr (by simp)⟩
      · exact False.elim (outside (sub inside))
      · simpa [Finset.mem_singleton.mp equal] using inside
  have each (idx : Point) : 3 ≤ cost idx := by
    have eqn : wires.getD (outputs idx) ∅ = line idx := (supportEq idx).trans (lineEq idx)
    have avail := available_lookup wires (outputs idx)
    rw [eqn] at avail
    have bound := budgets idx {line idx} (by simpa using And.intro (Finset.Subset.rfl : line idx ⊆ line idx) avail)
    simp [four] at bound
    omega
  have total := Finset.sum_le_sum (fun idx (_ : idx ∈ (Finset.univ : Finset Point)) => each idx)
  simp at total limit
  omega

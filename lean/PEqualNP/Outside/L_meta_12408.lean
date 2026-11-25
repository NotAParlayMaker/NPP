import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12408

open PEqualNP.CircuitLowerBounds

abbrev Pin := Fin 14
abbrev Mask := Finset Pin

def start : Finset Mask := insert ∅ (Finset.univ.image fun (i : Pin) => ({i} : Mask))

def output (i : Fin 4) : Mask := Finset.univ.filter fun p => (p.val + 1).testBit i.val

def Allowed (S : Finset Mask) (z : Mask) : Prop :=
  z ∈ S ∨ ∃ a ∈ S, ∃ b ∈ S, z = a ∪ b

def Valid : Finset Mask → List Mask → Prop
  | _, [] => True
  | S, z :: rest => Allowed S z ∧ Valid (insert z S) rest

def legal (g : Gate) : Prop := g.op = .or ∧ g.inputs.length ≤ 2

def result (w : List Mask) (g : Gate) : Mask :=
  (g.inputs.map (fun i => w.getD i ∅)).foldr (· ∪ ·) ∅

def stepMask (w : List Mask) (g : Gate) : List Mask := w ++ [result w g]

def stepBit (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def hasPin (p : Pin) (s : Mask) : Bool := decide (p ∈ s)

theorem bit_read (p : Pin) (w : List Mask) (i : ℕ) :
    (w.map (hasPin p)).getD i false = hasPin p (w.getD i ∅) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt h), hasPin]

theorem union_bit (p : Pin) (a b : Mask) : hasPin p (a ∪ b) = (hasPin p a || hasPin p b) := by
  simp only [hasPin, Finset.mem_union, Bool.decide_or]

theorem step_bit_spec (p : Pin) (w : List Mask) (g : Gate) (hg : legal g) :
    stepBit (w.map (hasPin p)) g = (stepMask w g).map (hasPin p) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨form,len⟩ := hg
  change op = .or at form
  change args.length ≤ 2 at len
  subst op
  rcases args with _ | ⟨i,_ | ⟨j,_ | ⟨k,rest⟩⟩⟩ <;> simp at len
  all_goals
    simp only [stepBit, stepMask, result, GateOp.eval, List.map_append, List.map_cons,
      List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, bit_read,
      List.foldr_cons, List.foldr_nil, Finset.union_empty, union_bit]
  all_goals simp [hasPin]

theorem evaluator (p : Pin) (gs : List Gate) (w : List Mask) (h : ∀ g ∈ gs, legal g) (o : ℕ) :
    (gs.foldl stepBit (w.map (hasPin p))).getD o false = hasPin p ((gs.foldl stepMask w).getD o ∅) := by
  induction gs generalizing w with
  | nil => exact bit_read p w o
  | cons g gs ih =>
    simp only [List.foldl_cons, step_bit_spec p w g (h _ (by simp))]
    exact ih _ (fun c mem => h c (List.mem_cons_of_mem _ mem))

theorem read_mask (w : List Mask) (S : Finset Mask) (h : ∀ z ∈ w, z ∈ S) (zero : ∅ ∈ S) (i : ℕ) :
    w.getD i ∅ ∈ S := by
  by_cases here : i < w.length
  · exact h _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem here])
  · rwa [List.getD_eq_default _ _ (Nat.le_of_not_gt here)]

theorem allowed_mask (w : List Mask) (S : Finset Mask) (h : ∀ z ∈ w, z ∈ S) (zero : ∅ ∈ S)
    (g : Gate) (hg : legal g) : Allowed S (result w g) := by
  have len := hg.2
  cases g with
  | mk op args =>
    change args.length ≤ 2 at len
    rcases args with _ | ⟨i,_ | ⟨j,_ | ⟨k,rest⟩⟩⟩ <;> simp at len
    · exact Or.inl zero
    · exact Or.inl (by simpa [result] using read_mask w S h zero i)
    · exact Or.inr ⟨_,read_mask w S h zero i,_,read_mask w S h zero j,by simp [result]⟩

theorem program (gs : List Gate) (w : List Mask) (S : Finset Mask) (zero : ∅ ∈ S)
    (h : ∀ z ∈ w, z ∈ S) (well : ∀ g ∈ gs, legal g) :
    ∃ tr : List Mask, tr.length = gs.length ∧ Valid S tr ∧
      ∀ z ∈ gs.foldl stepMask w, z ∈ S ∨ z ∈ tr := by
  induction gs generalizing w S with
  | nil => exact ⟨[], rfl, trivial, fun z mem => Or.inl (h z mem)⟩
  | cons g gs ih =>
    let z := result w g
    have allowed := allowed_mask w S h zero g (well g (by simp))
    have next : ∀ u ∈ stepMask w g, u ∈ insert z S := by
      intro u mem
      rcases List.mem_append.mp mem with old | new
      · exact Finset.mem_insert_of_mem (h _ old)
      · exact Finset.mem_insert.mpr (Or.inl (List.mem_singleton.mp new))
    obtain ⟨tr, len, valid, spec⟩ := ih (stepMask w g) (insert z S) (Finset.mem_insert_of_mem zero) next
      (fun g' mem => well _ (List.mem_cons_of_mem _ mem))
    refine ⟨z :: tr, by simp [len], ⟨allowed,valid⟩, ?_⟩
    intro y present
    rcases spec y present with prior | later
    · rcases Finset.mem_insert.mp prior with eq | old
      · exact Or.inr (List.mem_cons.mpr (.inl eq))
      · exact Or.inl old
    · exact Or.inr (List.mem_cons.mpr (.inr later))

theorem trace_encoder (C : Circuit) (h : ∀ g ∈ C.gates, legal g)
    (correct : ∀ i : Fin 4, ∃ w : ℕ, ∀ p : Pin,
      (C.wires (List.ofFn (fun q : Pin => decide (q = p)))).getD w false = (p.val + 1).testBit i.val) :
    ∃ tr : List Mask, tr.length = C.size ∧ Valid start tr ∧ ∀ i : Fin 4, output i ∈ start ∨ output i ∈ tr := by
  let inputs := List.ofFn fun (p : Pin) => ({p} : Mask)
  have raw : ∀ s ∈ inputs, s ∈ start := by
    intro s mem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp mem
    simp [start]
  obtain ⟨tr,len,legalTrace,spec⟩ := program C.gates inputs start (by simp [start]) raw h
  refine ⟨tr,len,legalTrace,?_⟩
  intro i
  obtain ⟨o,ho⟩ := correct i
  have truth : (C.gates.foldl stepMask inputs).getD o ∅ = output i := by
    ext p
    have hex := evaluator p C.gates inputs h o
    have ineq : inputs.map (hasPin p) = List.ofFn (fun q : Pin => decide (q = p)) := by
      simp [inputs,List.map_ofFn,Function.comp_def,hasPin,eq_comm]
    rw [ineq] at hex
    change (C.wires (List.ofFn (fun q : Pin => decide (q = p)))).getD o false = _ at hex
    rw [ho] at hex
    simp only [hasPin, output, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (decide_eq_true_iff).symm.trans (Bool.eq_iff_iff.mp hex.symm)
  by_cases inRange : o < (C.gates.foldl stepMask inputs).length
  · apply spec
    rw [← truth]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inRange]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt inRange)] at truth
    exact Or.inl (truth ▸ (by simp [start] : (∅ : Mask) ∈ start))

abbrev Pair := Fin 6

def left (p : Pair) : Fin 4 := (![0,0,0,1,1,2] : Fin 6 → Fin 4) p
def right (p : Pair) : Fin 4 := (![1,2,3,2,3,3] : Fin 6 → Fin 4) p

def common (p : Pair) : Mask := output (left p) ∩ output (right p)

abbrev incident (i : Fin 4) (p : Pair) : Prop := i = left p ∨ i = right p

def shared (p : Pair) (s : Mask) : Bool := decide (2 ≤ s.card ∧ s ⊆ common p)

def single (i : Fin 4) (s : Mask) : Bool := decide (2 ≤ s.card ∧ s ⊆ output i ∧
  ∀ j : Fin 4, j ≠ i → ¬ s ⊆ output j)

def pool (tr : List Mask) (p : Pair) : Mask := ((tr.filter (shared p)).toFinset).biUnion id

theorem shared_spec (p : Pair) (s : Mask) : shared p s = true ↔ 2 ≤ s.card ∧ s ⊆ common p := by
  simp [shared]

theorem single_spec (i : Fin 4) (s : Mask) : single i s = true ↔ 2 ≤ s.card ∧ s ⊆ output i ∧
    ∀ j : Fin 4, j ≠ i → ¬ s ⊆ output j := by simp [single]

theorem distinct_sides : ∀ p, left p ≠ right p := by decide +kernel

theorem common_size : ∀ p, (common p).card = 3 := by decide +kernel

theorem plus_third : ∀ p i, ¬ incident i p → (common p ∩ output i).card ≤ 1 := by decide +kernel

theorem distinct_common : ∀ p q, p ≠ q → (common p ∩ common q).card ≤ 1 := by decide +kernel

theorem pair_for : ∀ i j : Fin 4, i ≠ j → ∃ p, (left p = i ∧ right p = j) ∨ (left p = j ∧ right p = i) := by
  decide +kernel

theorem cover_incident {p : Pair} {i : Fin 4} (h : incident i p) : common p ⊆ output i := by
  rcases h with rfl | rfl
  · exact Finset.inter_subset_left
  · exact Finset.inter_subset_right

theorem shared_in_pool {p : Pair} {tr : List Mask} {s : Mask} (mem : s ∈ tr)
    (h : shared p s = true) : s ⊆ pool tr p := by
  intro i present
  apply Finset.mem_biUnion.mpr
  exact ⟨s, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨mem,h⟩), present⟩

theorem pool_subset (tr : List Mask) (p : Pair) : pool tr p ⊆ common p := by
  intro i present
  obtain ⟨s,member,hi⟩ := Finset.mem_biUnion.mp present
  have h := (List.mem_filter.mp (List.mem_toFinset.mp member)).2
  exact (shared_spec p s).mp h |>.2 hi

theorem either_owner {s : Mask} {i : Fin 4} (large : 2 ≤ s.card) (inside : s ⊆ output i) :
    single i s = true ∨ ∃ p : Pair, incident i p ∧ shared p s = true := by
  by_cases sole : ∀ j : Fin 4, j ≠ i → ¬ s ⊆ output j
  · exact Or.inl ((single_spec i s).mpr ⟨large,inside,sole⟩)
  · push Not at sole
    obtain ⟨j, ne, also⟩ := sole
    obtain ⟨p, pair⟩ := pair_for i j ne.symm
    apply Or.inr
    refine ⟨p,?_,(shared_spec p s).mpr ⟨large,?_⟩⟩
    · rcases pair with ⟨a,b⟩ | ⟨a,b⟩
      · exact Or.inl a.symm
      · exact Or.inr b.symm
    · rcases pair with ⟨a,b⟩ | ⟨a,b⟩
      · change s ⊆ output (left p) ∩ output (right p)
        rw [a,b]
        exact fun _ h => Finset.mem_inter.mpr ⟨inside h,also h⟩
      · change s ⊆ output (left p) ∩ output (right p)
        rw [a,b]
        exact fun _ h => Finset.mem_inter.mpr ⟨also h,inside h⟩

theorem pool_empty_or_large (tr : List Mask) (p : Pair) : pool tr p = ∅ ∨ 2 ≤ (pool tr p).card := by
  cases h : tr.filter (shared p) with
  | nil => exact Or.inl (by simp [pool,h])
  | cons s tail =>
    have mem : s ∈ tr.filter (shared p) := by simp [h]
    obtain ⟨earlier, now⟩ := List.mem_filter.mp mem
    have bound := (shared_spec p s).mp now |>.1
    exact Or.inr (bound.trans (Finset.card_le_card (shared_in_pool earlier now)))

theorem small_start {s : Mask} (mem : s ∈ start) : s.card ≤ 1 := by
  simp only [start, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at mem
  rcases mem with rfl | ⟨p,rfl⟩ <;> simp

theorem lone_shared (p : Pair) {S : Finset Mask} {tr : List Mask} {s : Mask} (valid : Valid S tr)
    (none : ∀ x ∈ S, shared p x = false) (only : tr.filter (shared p) = [s]) : s.card ≤ 2 := by
  induction tr generalizing S with
  | nil => simp at only
  | cons x tail ih =>
    change Allowed S x ∧ Valid (insert x S) tail at valid
    by_cases selected : shared p x = true
    · simp only [List.filter_cons, selected, ite_true, List.cons.injEq] at only
      have inside := ((shared_spec p x).mp selected).2
      have small (w : Mask) (mem : w ∈ S) (sub : w ⊆ common p) : w.card ≤ 1 := by
        by_contra! large
        have flag := (shared_spec p w).mpr ⟨large,sub⟩
        rw [none w mem] at flag
        cases flag
      obtain ⟨eq, _⟩ := only
      subst s
      rcases valid.1 with old | ⟨u,hu,v,hv,eq⟩
      · have flag := none x old
        rw [selected] at flag
        cases flag
      · rw [eq] at inside ⊢
        have lu := small u hu (Finset.subset_union_left.trans inside)
        have lv := small v hv (Finset.subset_union_right.trans inside)
        exact (Finset.card_union_le _ _).trans (by omega)
    · have off := Bool.eq_false_of_ne_true selected
      refine ih valid.2 ?_ ?_
      · intro z mem
        rcases Finset.mem_insert.mp mem with rfl | before
        · exact off
        · exact none z before
      · simpa [List.filter_cons, off] using only

theorem pool_charge (p : Pair) {tr : List Mask} (valid : Valid start tr) :
    (pool tr p).card - 1 ≤ tr.countP (shared p) := by
  rw [List.countP_eq_length_filter]
  cases h : tr.filter (shared p) with
  | nil => simp [pool,h]
  | cons s tail =>
    cases tail with
    | nil =>
      have small := lone_shared p valid (fun x mem => by
        by_contra! yes
        have bound := ((shared_spec p x).mp (Bool.eq_true_of_ne_false yes)).1
        have low := small_start mem
        omega) h
      simp only [pool,h,List.toFinset_cons,List.toFinset_nil,Finset.biUnion_insert,Finset.biUnion_empty,
        id_eq, Finset.union_empty,List.length_cons,List.length_nil]
      omega
    | cons w ws =>
      have cap := Finset.card_le_card (pool_subset tr p)
      rw [common_size] at cap
      simp only [List.length_cons]
      omega

def kind : Fin 4 ⊕ Pair → Mask → Bool
  | .inl i => single i
  | .inr p => shared p

theorem single_shared_exclude {i : Fin 4} {p : Pair} {s : Mask}
    (hi : single i s = true) (hp : shared p s = true) : False := by
  have forbidden := ((single_spec i s).mp hi).2.2
  have commonSub := ((shared_spec p s).mp hp).2
  by_cases eq : left p = i
  · exact forbidden (right p) (fun r => distinct_sides p (eq.trans r.symm))
      (commonSub.trans Finset.inter_subset_right)
  · exact forbidden (left p) eq (commonSub.trans Finset.inter_subset_left)

theorem unique_kind {k l : Fin 4 ⊕ Pair} {s : Mask} (hk : kind k s = true) (hl : kind l s = true) : k = l := by
  cases k with
  | inl i =>
    cases l with
    | inl j =>
      by_contra! ne
      have different : j ≠ i := fun e => ne (congrArg Sum.inl e.symm)
      exact ((single_spec i s).mp hk).2.2 j different ((single_spec j s).mp hl).2.1
    | inr p => exact (single_shared_exclude hk hl).elim
  | inr p =>
    cases l with
    | inl i => exact (single_shared_exclude hl hk).elim
    | inr q =>
      by_contra! ne
      have diff : p ≠ q := fun e => ne (congrArg Sum.inr e)
      have a := (shared_spec p s).mp hk
      have b := (shared_spec q s).mp hl
      have sub : s ⊆ common p ∩ common q := fun w h => Finset.mem_inter.mpr ⟨a.2 h,b.2 h⟩
      have le := Finset.card_le_card sub
      have cap := distinct_common p q diff
      omega

theorem count_one_kind (s : Mask) : (∑ k : Fin 4 ⊕ Pair, if kind k s = true then 1 else 0) ≤ 1 := by
  let seen := Finset.univ.filter fun k : Fin 4 ⊕ Pair => kind k s = true
  have atMost : seen.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk l hl
    exact unique_kind (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2
  have eq : seen.card = ∑ k : Fin 4 ⊕ Pair, if kind k s = true then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_filter _ _
  exact eq ▸ atMost

theorem total_charge (tr : List Mask) :
    (∑ i : Fin 4, tr.countP (single i)) + (∑ p : Pair, tr.countP (shared p)) ≤ tr.length := by
  have once : (∑ k : Fin 4 ⊕ Pair, tr.countP (kind k)) ≤ tr.length := by
    induction tr with
    | nil => simp
    | cons s tr ih =>
      simp only [List.countP_cons, Finset.sum_add_distrib, List.length_cons]
      have cap := count_one_kind s
      omega
  have split : (∑ k : Fin 4 ⊕ Pair, tr.countP (kind k)) =
      (∑ i : Fin 4, tr.countP (single i)) + (∑ p : Pair, tr.countP (shared p)) :=
    Fintype.sum_sum_type _
  exact split ▸ once

-- Live-wire compression adapted from L-meta-10588 (Apache-2.0).
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live


def positions (i : Fin 4) : Fin 3 → Pair :=
  (![![0,1,2], ![0,3,4], ![1,3,5], ![2,4,5]] : Fin 4 → Fin 3 → Pair) i

theorem represents_pair : ∀ i p, incident i p ↔ ∃ j : Fin 3, positions i j = p := by decide +kernel

def candidates (i : Fin 4) (group : Pair → Mask) : List Mask :=
  (List.ofFn fun j => group (positions i j)).filter (fun s => decide (2 ≤ s.card))

def basis (i : Fin 4) (tr : List Mask) : Finset Mask :=
  (start.filter fun s => s ⊆ output i) ∪ (candidates i (pool tr)).toFinset

def joinOps (a b : Mask) : Finset Mask := {a ∪ b}

def retains (i : Fin 4) (S A : Finset Mask) : Prop :=
  ∀ s ∈ S, s ⊆ output i → ∃ q ∈ A, s ⊆ q ∧ q ⊆ output i

theorem enlarge {i : Fin 4} {S A B : Finset Mask} (inv : retains i S A) (sub : A ⊆ B) : retains i S B := by
  intro w hw inside
  obtain ⟨z,mem,contains,small⟩ := inv w hw inside
  exact ⟨z,sub mem,contains,small⟩

theorem update {i : Fin 4} {S A : Finset Mask} {w : Mask}
    (inv : retains i S A) (new : w ⊆ output i → ∃ q ∈ A, w ⊆ q ∧ q ⊆ output i) : retains i (insert w S) A := by
  intro s present inside
  rcases Finset.mem_insert.mp present with rfl | old
  · exact new inside
  · exact inv s old inside

theorem raw_of_small {s : Mask} (small : s.card ≤ 1) : s ∈ start := by
  obtain ⟨i, sub⟩ := Finset.card_le_one_iff_subset_singleton.mp small
  by_cases none : s = ∅
  · simp [start, none]
  have some : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr none
  obtain ⟨j, hj⟩ := some
  have eq : j = i := Finset.mem_singleton.mp (sub hj)
  subst j
  have h : s = {i} := Finset.Subset.antisymm sub (Finset.singleton_subset_iff.mpr hj)
  simp [start,h]

theorem pool_candidate {i : Fin 4} {tr : List Mask} {p : Pair} (inc : incident i p) (big : 2 ≤ (pool tr p).card) :
    pool tr p ∈ (candidates i (pool tr)).toFinset := by
  apply List.mem_toFinset.mpr
  obtain ⟨j,eq⟩ := (represents_pair i p).mp inc
  exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨j, congrArg (pool tr) eq⟩, by simpa using big⟩

theorem collapse (i : Fin 4) (full : List Mask) {tr : List Mask} {S A : Finset Mask}
    (valid : Valid S tr) (contained : ∀ z ∈ tr, z ∈ full)
    (available : basis i full ⊆ A) (inv : retains i S A)
    (ready : output i ∈ S ∨ output i ∈ tr) : build joinOps (output i) (tr.countP (single i)) A := by
  induction tr generalizing S A with
  | nil =>
    have present := ready.resolve_right List.not_mem_nil
    obtain ⟨q, mem, sup, sub⟩ := inv _ present (Finset.Subset.refl _)
    exact (Finset.Subset.antisymm sup sub).symm ▸ mem
  | cons z tail ih =>
    change Allowed S z ∧ Valid (insert z S) tail at valid
    have remains : output i ∈ insert z S ∨ output i ∈ tail := by
      rcases ready with earlier | after
      · exact Or.inl (Finset.mem_insert_of_mem earlier)
      · rcases List.mem_cons.mp after with e | after
        · exact Or.inl (Finset.mem_insert.mpr (.inl e))
        · exact Or.inr after
    have includes : ∀ w ∈ tail, w ∈ full := fun w mem => contained w (List.mem_cons_of_mem _ mem)
    by_cases privateGate : single i z = true
    · rw [List.countP_cons_of_pos privateGate]
      have inOutput := ((single_spec i z).mp privateGate).2.1
      rcases valid.1 with copy | ⟨a,ha,b,hb,union⟩
      · exact Or.inl (ih valid.2 includes available (update inv (inv z copy)) remains)
      · have aSub : a ⊆ output i := Finset.subset_union_left.trans (union ▸ inOutput)
        have bSub : b ⊆ output i := Finset.subset_union_right.trans (union ▸ inOutput)
        obtain ⟨x,hx,aIn,xIn⟩ := inv a ha aSub
        obtain ⟨y,hy,bIn,yIn⟩ := inv b hb bSub
        have contained : z ⊆ x ∪ y := union.symm ▸ Finset.union_subset
          (aIn.trans Finset.subset_union_left) (bIn.trans Finset.subset_union_right)
        by_cases same : x = y
        · subst y
          have zIn : z ⊆ x := by simpa using contained
          exact Or.inl (ih valid.2 includes available (update inv (fun _ => ⟨x,hx,zIn,xIn⟩)) remains)
        · have bankSub : A ⊆ insert (x ∪ y) A := fun _ mem => Finset.mem_insert_of_mem mem
          refine Or.inr ⟨x,hx,y,hy,same,x ∪ y,by simp [joinOps],?_⟩
          exact ih valid.2 includes (available.trans bankSub)
            (update (enlarge inv bankSub) (fun _ => ⟨x ∪ y,Finset.mem_insert_self ..,contained,
              Finset.union_subset xIn yIn⟩)) remains
    · rw [List.countP_cons_of_neg privateGate]
      refine ih valid.2 includes available (update inv ?_) remains
      intro safe
      by_cases tiny : z.card ≤ 1
      · exact ⟨z,available (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨raw_of_small tiny,safe⟩)),
          Finset.Subset.refl _,safe⟩
      · obtain ⟨p,inc,used⟩ := (either_owner (by omega) safe).resolve_left privateGate
        have sub := shared_in_pool (contained z List.mem_cons_self) used
        have large : 2 ≤ (pool full p).card := ((shared_spec p z).mp used).1.trans (Finset.card_le_card sub)
        exact ⟨pool full p, available (Finset.mem_union_right _ (pool_candidate inc large)), sub,
          (pool_subset full p).trans (cover_incident inc)⟩

theorem private_run (i : Fin 4) {tr : List Mask} (valid : Valid start tr)
    (present : output i ∈ start ∨ output i ∈ tr) :
    build joinOps (output i) (tr.countP (single i)) (basis i tr) := by
  refine collapse i tr valid (fun _ h => h) (Finset.Subset.refl _) ?_ present
  intro s mem inside
  exact ⟨s,Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨mem,inside⟩),Finset.Subset.refl _,inside⟩

def costWith (t : Mask) (ws : List Mask) : ℕ :=
  ws.toFinset.card + (t \ ws.toFinset.biUnion id).card

def coverCost (t : Mask) (choices : List Mask) : ℕ :=
  (choices.sublists.map (costWith t)).foldl min t.card

theorem min_acc (ls : List ℕ) (cur : ℕ) : ls.foldl min cur ≤ cur := by
  induction ls generalizing cur with
  | nil => exact le_rfl
  | cons a as ih => exact (ih (min cur a)).trans (min_le_left ..)

theorem min_member {a : ℕ} {ls : List ℕ} (h : a ∈ ls) (cur : ℕ) : ls.foldl min cur ≤ a := by
  induction ls generalizing cur with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl | present
    · exact (min_acc bs (min cur a)).trans (min_le_right ..)
    · exact ih present (min cur b)

theorem source_covers {t : Mask} {k : ℕ} {S : Finset Mask} (run : live joinOps t k S)
    (p : Pin) (yes : p ∈ t) : ∃ s ∈ S, p ∈ s := by
  apply live_separates (fun s : Mask => p ∈ s) yes _ run
  intro a b z allowed pos
  obtain rfl := Finset.mem_singleton.mp allowed
  exact Finset.mem_union.mp pos

theorem private_charge (i : Fin 4) {tr : List Mask} (valid : Valid start tr)
    (present : output i ∈ start ∨ output i ∈ tr) :
    coverCost (output i) (candidates i (pool tr)) ≤ tr.countP (single i) + 1 := by
  obtain ⟨S,sub,run⟩ := compress (private_run i valid present)
  let big := S.filter fun s => 2 ≤ s.card
  let small := S.filter fun s => ¬ 2 ≤ s.card
  let options := candidates i (pool tr)
  let selected := options.filter fun s => decide (s ∈ big)
  have bigIsOption : big ⊆ options.toFinset := by
    intro s mem
    obtain ⟨atBank,large⟩ := Finset.mem_filter.mp mem
    rcases Finset.mem_union.mp (sub atBank) with raw | pool
    · have := small_start (Finset.mem_filter.mp raw).1
      omega
    · exact pool
  have eq : selected.toFinset = big := by
    ext s
    simp only [selected, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun mem => ⟨List.mem_toFinset.mp (bigIsOption mem),mem⟩⟩
  let unmarked := output i \ big.biUnion id
  have singletons : unmarked.image (fun p => ({p} : Mask)) ⊆ small := by
    intro s hs
    obtain ⟨p,mem,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨yes, missed⟩ := Finset.mem_sdiff.mp mem
    obtain ⟨s,avail,has⟩ := source_covers run p yes
    have low : ¬ 2 ≤ s.card := fun large => missed (Finset.mem_biUnion.mpr
      ⟨s,Finset.mem_filter.mpr ⟨avail,large⟩,has⟩)
    have one : s = {p} := by
      have sub : {p} ⊆ s := Finset.singleton_subset_iff.mpr has
      apply (Finset.eq_of_subset_of_card_le sub (by simp; omega)).symm
    exact Finset.mem_filter.mpr ⟨one ▸ avail, one ▸ low⟩
  have injective : Function.Injective (fun p : Pin => ({p} : Mask)) := fun _ _ eq => Finset.singleton_injective eq
  have restCount := Finset.card_le_card singletons
  rw [Finset.card_image_of_injective _ injective] at restCount
  have size := live_card run
  have split : big.card + small.card = S.card := Finset.card_filter_add_card_filter_not ..
  have candidate : costWith (output i) selected ∈ (options.sublists.map (costWith (output i))) :=
    List.mem_map.mpr ⟨selected,List.mem_sublists.mpr (List.filter_sublist ..),rfl⟩
  have lower := min_member candidate (output i).card
  change coverCost (output i) options ≤ costWith (output i) selected at lower
  simp only [costWith, eq] at lower
  change coverCost (output i) options ≤ big.card + unmarked.card at lower
  change coverCost (output i) options ≤ _
  omega

def options (p : Pair) : Fin 5 → Mask :=
  (![
    ![∅, {2, 6}, {2, 10}, {6, 10}, {2, 6, 10}],
    ![∅, {4, 6}, {4, 12}, {6, 12}, {4, 6, 12}],
    ![∅, {8, 10}, {8, 12}, {10, 12}, {8, 10, 12}],
    ![∅, {5, 6}, {5, 13}, {6, 13}, {5, 6, 13}],
    ![∅, {9, 10}, {9, 13}, {10, 13}, {9, 10, 13}],
    ![∅, {11, 12}, {11, 13}, {12, 13}, {11, 12, 13}]] : Pair → Fin 5 → Mask) p

def rankTables : List (List ℕ) :=
  [
    [7, 6, 6, 6, 5, 6, 5, 5, 5, 4, 6, 5, 6, 6, 5, 6, 5, 6, 6, 5, 5, 4, 5, 5, 4, 6, 5, 5, 5, 4, 6, 5, 5, 5, 4, 5, 4, 5, 5, 4, 6, 5, 5, 5, 4, 5, 4, 5, 5, 4, 6, 6, 5, 6, 5, 5, 5, 4, 5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 6, 6, 5, 6, 5, 6, 5, 5, 5, 4, 5, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 4, 5, 5, 4, 5, 5, 4, 5, 4, 5, 5, 4, 5, 4, 4, 4, 4, 4, 4, 5, 5, 4, 5, 4, 4, 4, 4, 4, 4],
    [7, 6, 6, 6, 5, 6, 5, 5, 5, 4, 6, 5, 6, 6, 5, 6, 5, 6, 6, 5, 5, 4, 5, 5, 4, 6, 5, 5, 5, 4, 6, 5, 5, 5, 4, 5, 4, 5, 5, 4, 6, 5, 5, 5, 4, 5, 4, 5, 5, 4, 6, 6, 5, 6, 5, 5, 5, 4, 5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 6, 6, 5, 6, 5, 6, 5, 5, 5, 4, 5, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 4, 5, 5, 4, 5, 5, 4, 5, 4, 5, 5, 4, 5, 4, 4, 4, 4, 4, 4, 5, 5, 4, 5, 4, 4, 4, 4, 4, 4],
    [7, 6, 6, 6, 5, 6, 5, 5, 5, 4, 6, 5, 6, 6, 5, 6, 5, 6, 6, 5, 5, 4, 5, 5, 4, 6, 5, 5, 5, 4, 6, 5, 5, 5, 4, 5, 4, 5, 5, 4, 6, 5, 5, 5, 4, 5, 4, 5, 5, 4, 6, 6, 5, 6, 5, 5, 5, 4, 5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 6, 6, 5, 6, 5, 6, 5, 5, 5, 4, 5, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 4, 5, 5, 4, 5, 5, 4, 5, 4, 5, 5, 4, 5, 4, 4, 4, 4, 4, 4, 5, 5, 4, 5, 4, 4, 4, 4, 4, 4],
    [7, 6, 6, 6, 5, 6, 5, 5, 5, 4, 6, 5, 6, 6, 5, 6, 5, 6, 6, 5, 5, 4, 5, 5, 4, 6, 5, 5, 5, 4, 6, 5, 5, 5, 4, 5, 4, 5, 5, 4, 6, 5, 5, 5, 4, 5, 4, 5, 5, 4, 6, 6, 5, 6, 5, 5, 5, 4, 5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 6, 6, 5, 6, 5, 6, 5, 5, 5, 4, 5, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 4, 5, 5, 4, 5, 5, 4, 5, 4, 5, 5, 4, 5, 4, 4, 4, 4, 4, 4, 5, 5, 4, 5, 4, 4, 4, 4, 4, 4]]
def localChoices (i : Fin 4) (pick : Fin 3 → Fin 5) : List Mask :=
  (List.ofFn fun j => options (positions i j) (pick j)).filter (fun s => decide (2 ≤ s.card))

set_option maxRecDepth 32768 in
theorem masks_listed : ∀ p : Pair, ∀ s : (common p).powerset,
    (s.val = ∅ ∨ 2 ≤ s.val.card) → ∃ c : Fin 5, options p c = s.val := by decide +kernel

def shareWeight (c : Fin 5) : ℕ := if c = 0 then 0 else if c = 4 then 2 else 1

theorem weight_exact : ∀ p c, (options p c).card - 1 = shareWeight c := by decide +kernel

def tableRank (i : Fin 4) (a b c : Fin 5) : ℕ :=
  (rankTables.getD i.val []).getD (25 * a.val + 5 * b.val + c.val) 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rank_exact : ∀ (i : Fin 4) (a b c : Fin 5),
    coverCost (output i) (localChoices i ![a,b,c]) = tableRank i a b c := by
  intro i
  fin_cases i <;> decide +kernel

def minExtension (i : Fin 4) (code : Pair → Fin 5) : ℕ :=
  tableRank i (code (positions i 0)) (code (positions i 1)) (code (positions i 2))

theorem local_rank_eq (i : Fin 4) (code : Pair → Fin 5) :
    coverCost (output i) (candidates i (fun p => options p (code p))) = minExtension i code := by
  let pick : Fin 3 → Fin 5 := fun j => code (positions i j)
  have eq : pick = ![pick 0, pick 1, pick 2] := by
    funext j
    fin_cases j <;> rfl
  change coverCost (output i) (localChoices i pick) = tableRank i (pick 0) (pick 1) (pick 2)
  conv_lhs => rw [eq]
  exact rank_exact i (pick 0) (pick 1) (pick 2)

def rankCost (code : Pair → Fin 5) : ℕ :=
  (∑ p : Pair, shareWeight (code p)) + ∑ i : Fin 4, minExtension i code

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem enumerated_cost : ∀ (a b c d e f : Fin 5), 24 ≤ rankCost ![a,b,c,d,e,f] := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rank_cost_lower (code : Pair → Fin 5) : 24 ≤ rankCost code := by
  have eq : code = ![code 0, code 1, code 2, code 3, code 4, code 5] := by
    funext p
    fin_cases p <;> rfl
  conv_rhs => rw [eq]
  exact enumerated_cost ..

theorem pooled_cost (tr : List Mask) : 24 ≤
    (∑ p : Pair, ((pool tr p).card - 1)) + ∑ i : Fin 4, coverCost (output i) (candidates i (pool tr)) := by
  have chosen (p : Pair) : ∃ c : Fin 5, options p c = pool tr p :=
    masks_listed p ⟨pool tr p,Finset.mem_powerset.mpr (pool_subset tr p)⟩ (pool_empty_or_large tr p)
  choose code equality using chosen
  have eq : pool tr = fun p => options p (code p) := funext fun p => (equality p).symm
  simp only [eq, weight_exact, local_rank_eq]
  exact rank_cost_lower code

theorem any_encoder_needs_twenty {tr : List Mask} (valid : Valid start tr)
    (results : ∀ i : Fin 4, output i ∈ start ∨ output i ∈ tr) : 20 ≤ tr.length := by
  have privateCost : (∑ i : Fin 4, coverCost (output i) (candidates i (pool tr))) ≤
      ∑ i : Fin 4, (tr.countP (single i) + 1) :=
    Finset.sum_le_sum fun i _ => private_charge i valid (results i)
  have sharedCost : (∑ p : Pair, ((pool tr p).card - 1)) ≤ ∑ p : Pair, tr.countP (shared p) :=
    Finset.sum_le_sum fun p _ => pool_charge p valid
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.mul_one] at privateCost
  have total := total_charge tr
  have need := pooled_cost tr
  omega

end PEqualNP.Outside.L_meta_12408

open PEqualNP.Outside.L_meta_12408 in
theorem PEqualNP.Outside.L_meta_12408 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size ≤ 19 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14, (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false = Nat.testBit (p.val + 1) v.val) := by
  rintro ⟨C, legal, size, computes⟩
  obtain ⟨tr, length, valid, results⟩ := trace_encoder C legal computes
  have lower := any_encoder_needs_twenty valid results
  omega

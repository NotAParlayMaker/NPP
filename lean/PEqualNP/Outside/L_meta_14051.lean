import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Induction
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14051

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

def goalFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (2827526272 * 2 ^ 32 + 2818613248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def selectedInput (i : Fin 6) : ℕ :=
  ([12,25,9,5,11,7] : List ℕ).getD i.val 0

def start (i : Fin 6) (j : Fin 6) : Bool := (selectedInput i).testBit j.val

def finish (i : Fin 6) (j : Fin 6) : Bool := (selectedInput i + 2^i.val).testBit j.val

theorem essential : ∀ i : Fin 6, goalFun (start i) ≠ goalFun (finish i) ∧
    ∀ j : Fin 6, j ≠ i → start i j = finish i j := by decide +kernel

def witness : Circuit :=
  ⟨[⟨.and,[1,4]⟩, ⟨.or,[2,6]⟩, ⟨.and,[1,5]⟩, ⟨.or,[3,8]⟩,
    ⟨.and,[7,9]⟩, ⟨.and,[0,10]⟩],11⟩

theorem witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witness_correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = goalFun x := by
  decide +kernel

def used (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def charge (g : Gate) : ℕ :=
  match g.op with
  | .not => 0
  | _ => 1

def credits (gs : List Gate) : ℕ := (gs.map charge).sum

def backward (wire : ℕ) (g : Gate) (S : Finset ℕ) : Finset ℕ :=
  if wire ∈ S then S.erase wire ∪ (used g).toFinset else S

def demands (n : ℕ) (gs : List Gate) : Finset ℕ → Finset ℕ :=
  gs.reverseRecOn id fun before g ih S => ih (backward (n + before.length) g S)

theorem demands_append (n : ℕ) (gs : List Gate) (g : Gate) (S : Finset ℕ) :
    demands n (gs ++ [g]) S = demands n gs (backward (n + gs.length) g S) := by
  simp only [demands,List.reverseRecOn_concat]

theorem used_bound (g : Gate) (h : g.inputs.length ≤ 2) :
    (used g).length ≤ 1 + charge g := by
  cases hg : g.op <;> simp [used,charge,hg,h]

theorem backward_size (wire : ℕ) (g : Gate) (b : g.inputs.length ≤ 2) (S : Finset ℕ) :
    (backward wire g S).card ≤ S.card + charge g := by
  unfold backward
  split
  · rename_i h
    have cap := (Finset.card_union_le (S.erase wire) (used g).toFinset).trans
      (Nat.add_le_add_left (List.toFinset_card_le (used g)) (S.erase wire).card)
    rw [Finset.card_erase_of_mem h] at cap
    have hb := used_bound g b
    have pos : 0 < S.card := Finset.card_pos.mpr ⟨wire,h⟩
    omega
  · omega

theorem demands_size (n : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) (S : Finset ℕ) :
    (demands n gs S).card ≤ S.card + credits gs := by
  induction gs using List.reverseRecOn generalizing S with
  | nil => simp [demands,credits]
  | append_singleton prev g ih =>
    have sub (r : Gate) (hr : r ∈ prev) := h r (List.mem_append_left [g] hr)
    have bound := (ih sub (backward (n + prev.length) g S)).trans
      (Nat.add_le_add_right (backward_size _ _ (h g (by simp)) S) (credits prev))
    rw [demands_append]
    simp only [credits,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at *
    omega

def simulate (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def gateVal (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

theorem simulate_length (gs : List Gate) (x : List Bool) :
    (simulate gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [simulate]
  | cons g xs ih =>
    change (simulate xs (x ++ [gateVal g x])).length = _
    rw [ih]
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega

theorem simulate_append (gs : List Gate) (g : Gate) (x : List Bool) :
    simulate (gs ++ [g]) x = simulate gs x ++ [gateVal g (simulate gs x)] := by
  simp only [simulate,List.foldl_append,List.foldl_cons,List.foldl_nil,gateVal]

theorem update_at (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self]
  rfl

theorem update_away (w : List Bool) (b : Bool) (j : ℕ) (h : j ≠ w.length) :
    (w ++ [b]).getD j false = w.getD j false := by
  by_cases q : j < w.length
  · exact List.getD_append _ _ _ _ q
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

theorem used_agrees (g : Gate) (x y : List Bool)
    (h : ∀ j ∈ used g, x.getD j false = y.getD j false) : gateVal g x = gateVal g y := by
  unfold gateVal
  cases e : g.op
  case not =>
    simp only [GateOp.eval,used,e] at *
    cases inputs : g.inputs with
    | nil => rfl
    | cons j q =>
      have b := h j (by simp [inputs])
      simpa only [List.map_cons,List.headD_cons] using congrArg (fun z : Bool => !z) b
  all_goals
    apply congrArg (fun l : List Bool => GateOp.eval _ l)
    apply List.map_congr_left
    exact fun i hi => h i (by simpa only [used,e] using hi)

theorem demands_agree (n : ℕ) (gs : List Gate) (x y : List Bool)
    (hX : x.length = n) (hY : y.length = n) (S : Finset ℕ)
    (h : ∀ j ∈ demands n gs S, x.getD j false = y.getD j false) :
    ∀ j ∈ S, (simulate gs x).getD j false = (simulate gs y).getD j false := by
  induction gs using List.reverseRecOn generalizing S with
  | nil => simpa [demands,simulate] using h
  | append_singleton gs g ih =>
    rw [demands_append] at h
    have prev := ih (backward (n + gs.length) g S) h
    intro j hj
    simp only [simulate_append]
    let k := n + gs.length
    have lx : (simulate gs x).length = k := by rw [simulate_length,hX]
    have ly : (simulate gs y).length = k := by rw [simulate_length,hY]
    by_cases eq : j = k
    · have hk : k ∈ S := eq ▸ hj
      have hx : (simulate gs x ++ [gateVal g (simulate gs x)]).getD j false =
          gateVal g (simulate gs x) := by rw [eq,← lx,update_at]
      have hy : (simulate gs y ++ [gateVal g (simulate gs y)]).getD j false =
          gateVal g (simulate gs y) := by rw [eq,← ly,update_at]
      rw [hx,hy]
      apply used_agrees
      intro i hi
      apply prev i
      rw [backward,show n + gs.length = k from rfl,ite_eq_left hk]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr hi)
    · rw [update_away _ _ _ (lx.symm ▸ eq), update_away _ _ _ (ly.symm ▸ eq)]
      apply prev j
      by_cases hk : k ∈ S
      · rw [backward,show n + gs.length = k from rfl,ite_eq_left hk]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hj⟩)
      · simpa only [backward,show n + gs.length = k from rfl,ite_eq_right hk] using hj

theorem requires_five (C : Circuit) (h : FanInTwo C)
    (eq : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = goalFun x) :
    5 ≤ credits C.gates := by
  let D := demands 6 C.gates {C.output}
  have included : Finset.range 6 ⊆ D := by
    intro i hi
    have small := Finset.mem_range.mp hi
    let k : Fin 6 := ⟨i,small⟩
    have rel := essential k
    by_contra lacks
    have agrees : ∀ j ∈ D, (List.ofFn (start k)).getD j false = (List.ofFn (finish k)).getD j false := by
      intro j hj
      by_cases q : j < 6
      · let r : Fin 6 := ⟨j,q⟩
        have rn : r ≠ k := by
          intro e
          have same : j = i := congrArg Fin.val e
          exact lacks (same ▸ hj)
        have same := rel.2 r rn
        rw [List.getD_eq_getElem _ _ (by simpa using q), List.getD_eq_getElem _ _ (by simpa using q)]
        simpa only [List.getElem_ofFn] using same
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt q),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt q)]
    have both := demands_agree 6 C.gates (List.ofFn (start k)) (List.ofFn (finish k))
      (List.length_ofFn) (List.length_ofFn) {C.output} agrees C.output (Finset.mem_singleton_self _)
    exact rel.1 ((eq _).symm.trans (both.trans (eq _)))
  have lo := Finset.card_le_card included
  have hi := demands_size 6 C.gates (fun g hg => (h g hg).2) {C.output}
  simp only [Finset.card_range] at lo
  simp only [Finset.card_singleton] at hi
  change D.card ≤ 1 + credits C.gates at hi
  omega

theorem charge_le_one (g : Gate) : charge g ≤ 1 := by
  cases hg : g.op <;> simp [charge,hg]

theorem credits_le (gs : List Gate) : credits gs ≤ gs.length := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    have w := charge_le_one g
    change charge g + credits gs ≤ gs.length + 1
    omega

theorem has_not (gs : List Gate) (h : ∃ g ∈ gs, g.op = .not) : credits gs + 1 ≤ gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    have w := charge_le_one g
    change charge g + credits gs + 1 ≤ gs.length + 1
    obtain ⟨v,hv,hNot⟩ := h
    rcases List.mem_cons.mp hv with rfl | hv
    · have le := credits_le gs
      simp only [charge,hNot,Nat.zero_add]
      omega
    · have le := ih ⟨v,hv,hNot⟩
      omega

end PEqualNP.Outside.L_meta_14051

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_14051 in
theorem PEqualNP.Outside.L_meta_14051 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (2827526272 * 2 ^ 32 + 2818613248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (2827526272 * 2 ^ 32 + 2818613248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s
  rintro ⟨C,legal,budget,correct⟩
  by_cases enough : 6 ≤ s
  · exact ⟨witness,witness_mono,enough,witness_correct⟩
  refine ⟨C,?_,budget,correct⟩
  intro g hg
  obtain ⟨op,arity⟩ := legal g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
  refine ⟨?_,arity⟩
  rcases op with oa | oo | on
  · exact Or.inl oa
  · exact Or.inr oo
  · have low := requires_five C legal correct
    have notch := has_not C.gates ⟨g,hg,on⟩
    change C.gates.length ≤ s at budget
    omega

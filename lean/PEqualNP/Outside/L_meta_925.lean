import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925

open PEqualNP.CircuitLowerBounds

abbrev Bits (n : ℕ) := Fin n → Bool

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

def wire {n : ℕ} (w : Bits n → List Bool) (j : ℕ) (x : Bits n) : Bool :=
  (w x).getD j false

def newGate {n : ℕ} (w : Bits n → List Bool) (g : Gate) (x : Bits n) : Bool :=
  g.op.eval (g.inputs.map fun j => wire w j x)

def ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem gate_mono {n : ℕ} {w : Bits n → List Bool} {g : Gate} (hg : ok g)
    (x y : Bits n) (h : ∀ j ∈ g.inputs, wire w j x = true → wire w j y = true) :
    newGate w g x = true → newGate w g y = true := by
  rcases hg.1 with hand | hor
  · simp only [newGate, hand, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx j hj => h j hj (hx j hj)
  · simp only [newGate, hor, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨j,hj,hy⟩
    exact ⟨j,hj,h j hj hy⟩

theorem snoc_wire {n l : ℕ} (w : Bits n → List Bool) (hl : ∀ x, (w x).length = l)
    (g : Gate) (j : ℕ) :
    wire (fun x => step (w x) g) j = if j = l then newGate w g else wire w j := by
  funext x
  have hw := hl x
  by_cases e : j = l
  · subst j
    simp [wire, step, newGate, ← hl x]
  · simp only [ite_eq_right e, wire, step]
    by_cases lt : j < (w x).length
    · exact List.getD_append _ _ _ _ lt
    · rw [List.getD_eq_default _ _ (by simp [hl x]; omega),
          List.getD_eq_default _ _ (by omega)]

def onSet {n : ℕ} (A : Finset (Fin n)) : Bits n := fun a => decide (a ∈ A)

def upward {n : ℕ} (f : Bits n → Bool) : Prop :=
  ∀ A x, (∀ p ∈ A, x p = true) → f (onSet A) = true → f x = true

def specific {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) (f : Bits n → Bool) : Prop :=
  f (onSet (S i)) = true ∧ ∀ j, j ≠ i → f (onSet (S j)) ≠ true

noncomputable def charge {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m)
    (f : Bits n → Bool) : ℕ := @ite _ (specific S i f) (Classical.propDecidable _) 1 0

-- A shared frontier W can be supported by individual points P and other sets I.
-- A specific gate costs one unit even when several frontier wires depend on it.
def covered {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m)
    (w : Bits n → List Bool) (cost : ℕ) : Prop :=
  ∀ W : Finset ℕ, ∃ (P : Finset (Fin n)) (I : Finset (Fin m)), i ∉ I ∧
    P.card + I.card ≤ cost + W.card ∧
    ∀ j ∈ W, wire w j (onSet (S i)) = true → ∀ x : Bits n,
      (∀ p ∈ P, x p = true) → (∀ v ∈ I, ∀ p ∈ S v, x p = true) → wire w j x = true

theorem advance {n m l t : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m)
    (w : Bits n → List Bool) (hl : ∀ x, (w x).length = l) (g : Gate) (hg : ok g)
    (mon : upward (newGate w g)) (paid : covered S i w t) :
    covered S i (fun x => step (w x) g) (t + charge S i (newGate w g)) := by
  classical
  intro W
  by_cases use : l ∈ W
  · let V := W.erase l
    have cardV : V.card + 1 = W.card := Finset.card_erase_add_one use
    by_cases own : specific S i (newGate w g)
    · obtain ⟨P,I,hi,hcard,h⟩ := paid (V ∪ g.inputs.toFinset)
      have := Finset.card_union_le V g.inputs.toFinset
      have := (List.toFinset_card_le g.inputs).trans hg.2
      refine ⟨P,I,hi,by simp [charge,own]; omega,?_⟩
      intro j hj
      rw [snoc_wire w hl]; split_ifs with e
      · intro hnew x hp hI
        exact gate_mono hg _ _ (fun a ha hwire =>
          h a (Finset.mem_union_right _ (List.mem_toFinset.mpr ha)) hwire x hp hI) hnew
      · exact h j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hj⟩))
    · obtain ⟨P,I,hi,hcard,h⟩ := paid V
      by_cases on : newGate w g (onSet (S i)) = true
      · have ex : ∃ v, v ≠ i ∧ newGate w g (onSet (S v)) = true := by
          by_contra! none
          exact own ⟨on,none⟩
        obtain ⟨v,ne,hv⟩ := ex
        have := Finset.card_insert_le v I
        refine ⟨P,insert v I,by simp [Ne.symm ne,hi],by omega,?_⟩
        intro j hj
        rw [snoc_wire w hl]; split_ifs with e
        · intro _ x _ hI
          exact mon (S v) x (hI v (by simp)) hv
        · intro hwire x hp hI
          exact h j (Finset.mem_erase.mpr ⟨e,hj⟩) hwire x hp
            (fun a ha => hI a (Finset.mem_insert_of_mem ha))
      · refine ⟨P,I,hi,by omega,?_⟩
        intro j hj
        rw [snoc_wire w hl]; split_ifs with e
        · exact fun hnew => (on hnew).elim
        · exact h j (Finset.mem_erase.mpr ⟨e,hj⟩)
  · obtain ⟨P,I,hi,hcard,h⟩ := paid W
    refine ⟨P,I,hi,by omega,?_⟩
    intro j hj
    rw [snoc_wire w hl, ite_eq_right (show j ≠ l from fun e => use (e ▸ hj))]
    exact h j hj

theorem total_charge {n m : ℕ} (S : Fin m → Finset (Fin n)) (f : Bits n → Bool) :
    ∑ i, charge S i f ≤ 1 := by
  classical
  have h : (Finset.univ.filter (fun i => specific S i f)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra ne
    exact (Finset.mem_filter.mp hi).2.2 j (Ne.symm ne) (Finset.mem_filter.mp hj).2.1
  simpa [charge,Finset.sum_boole] using h

theorem drive {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gs : List Gate) (hok : ∀ g ∈ gs, ok g) (w : Bits n → List Bool) (l : ℕ)
    (hl : ∀ x, (w x).length = l) (hm : ∀ j, upward (wire w j))
    (cost : Fin m → ℕ) (hcost : ∀ i, covered S i w (cost i)) :
    ∃ d : Fin m → ℕ, (∑ i, d i) ≤ (∑ i, cost i) + gs.length ∧
      ∀ i, covered S i (fun x => gs.foldl step (w x)) (d i) := by
  classical
  induction gs generalizing w l cost with
  | nil => exact ⟨cost, by simp, hcost⟩
  | cons g gs ih =>
    have hg := hok g List.mem_cons_self
    have mon : upward (newGate w g) :=
      fun p x hx => gate_mono hg _ _ (fun j _ => hm j p x hx)
    let w' := fun x => step (w x) g
    let c' := fun i => cost i + charge S i (newGate w g)
    have hl' (x) : (w' x).length = l + 1 := by simp [w', step, hl]
    have hm' (j) : upward (wire w' j) := by
      rw [show wire w' j = _ from snoc_wire w hl g j]
      split_ifs
      · exact mon
      · exact hm j
    have hc' (i) : covered S i w' (c' i) :=
      advance S i w hl g hg mon (hcost i)
    obtain ⟨d, hd, hall⟩ := ih (fun g' h => hok g' (List.mem_cons_of_mem _ h))
      w' (l+1) hl' hm' c' hc'
    refine ⟨d, ?_, hall⟩
    have bound := total_charge S (newGate w g)
    simp only [c', Finset.sum_add_distrib] at hd
    simp only [List.length_cons]
    omega

theorem initial_up {n : ℕ} (j : ℕ) : upward (wire (fun x : Bits n => List.ofFn x) j) := by
  intro A x hx h
  by_cases lt : j < n
  · have mem : (⟨j,lt⟩ : Fin n) ∈ A := by simpa [wire,onSet,lt] using h
    simpa [wire,lt] using hx ⟨j,lt⟩ mem
  · simp [wire,lt] at h

theorem initial_covered {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) :
    covered S i (fun x : Bits n => List.ofFn x) 0 := by
  classical
  intro W
  let P := Finset.univ.filter (fun p : Fin n => p.val ∈ W)
  have sub : P.image Fin.val ⊆ W := by
    rintro _ h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hp).2
  have bound := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at bound
  refine ⟨P,∅,by simp,by simpa using bound,?_⟩
  intro j hj on x hx _
  by_cases lt : j < n
  · simpa [wire,lt] using hx ⟨j,lt⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
  · simp [wire,lt] at on

-- Distinct large blocks intersect. After the first block each adds at most q points.
theorem union_bound {n m q : ℕ} (S : Fin m → Finset (Fin n))
    (size : ∀ i, (S i).card = q+1) (meet : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (I : Finset (Fin m)) : (I.biUnion S).card ≤ I.card*q+1 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.biUnion_insert,Finset.card_insert_of_notMem hi,Nat.add_mul,one_mul]
    rcases I.eq_empty_or_nonempty with rfl | ⟨j,hj⟩
    · simp [size]
    · have ne : i ≠ j := fun e => hi (e ▸ hj)
      have sub : S i ∩ S j ⊆ S i ∩ I.biUnion S := fun p hp =>
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hp).1,
          Finset.mem_biUnion.mpr ⟨j,hj,(Finset.mem_inter.mp hp).2⟩⟩
      have := Finset.card_le_card sub
      have := Finset.card_union_add_card_inter (S i) (I.biUnion S)
      have := meet i j ne
      have := size i
      omega

theorem inside_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (meet : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) (i : Fin m) (I : Finset (Fin m))
    (hi : i ∉ I) : ((I.biUnion S) ∩ S i).card ≤ I.card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert j I hj ih =>
    have ne : j ≠ i := fun e => hi (by simp [e])
    have hI : i ∉ I := fun h => hi (Finset.mem_insert_of_mem h)
    rw [Finset.biUnion_insert,Finset.union_inter_distrib_right,Finset.card_insert_of_notMem hj]
    have := Finset.card_union_le (S j ∩ S i) (I.biUnion S ∩ S i)
    have := meet j i ne
    have := ih hI
    omega

end PEqualNP.Outside.L_meta_925

open PEqualNP.Outside.L_meta_925

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq sizes meet gs out hok correct c hc light
  by_cases zero : c = 0
  · simp [zero]
  have qK : q + 1 ≤ K := by
    have := Nat.mul_le_mul_right q (show 1 ≤ c by omega)
    simp only [Nat.one_mul] at this
    omega
  let w := fun x : Bits n => gs.foldl step (List.ofFn x)
  have eval_set (i : Fin m) (A : Finset (Fin n)) (ha : A.card ≤ K) :
      wire w (out i) (onSet A) = true ↔ S i ⊆ A := by
    have e := correct i (onSet A) (by simpa [onSet] using ha)
    change wire w (out i) (onSet A) = decide _ at e
    rw [e]
    simp only [decide_eq_true_eq,onSet]
    exact ⟨fun h _ hp => h _ hp, fun h _ hp => h hp⟩
  obtain ⟨cost,bound,all⟩ := drive S gs hok (fun x : Bits n => List.ofFn x) n
    (by simp) initial_up (fun _ => 0) (initial_covered S)
  have each (i : Fin m) : c ≤ cost i := by
    by_contra! cheap
    obtain ⟨P,I,hi,card,cert⟩ := all i {out i}
    simp only [Finset.card_singleton] at card
    let A := P ∪ I.biUnion S
    have total := union_bound S sizes meet I
    have le := Finset.card_union_le P (I.biUnion S)
    have num : P.card + I.card ≤ c := by omega
    have mul := Nat.mul_le_mul_right q num
    have pointcost := Nat.mul_le_mul_left P.card (show 1 ≤ q by omega)
    rw [Nat.add_mul] at mul
    simp only [Nat.mul_one] at pointcost
    have small : A.card ≤ K := by dsimp [A]; omega
    have tr := cert (out i) (by simp)
      ((eval_set i (S i) (by rw [sizes]; exact qK)).2 (by rfl)) (onSet A)
      (fun p hp => by simp [onSet,A,hp])
      (fun j hj p hp => by
        have h : p ∈ I.biUnion S := Finset.mem_biUnion.mpr ⟨j,hj,hp⟩
        simp [onSet,A,h])
    have sub := (eval_set i A small).1 tr
    have covered_inside : S i ⊆ P ∪ ((I.biUnion S) ∩ S i) := by
      intro p hp
      rcases Finset.mem_union.mp (sub hp) with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h,hp⟩)
    have := Finset.card_le_card covered_inside
    have := Finset.card_union_le P (I.biUnion S ∩ S i)
    have := inside_bound S meet i I hi
    have := sizes i
    omega
  have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => each i)
  simpa using this.trans (by simpa using bound)

import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_782

def privateGates {n m r : ℕ} (S : Fin m → Finset (Fin n))
    (L : Fin r → Finset (Fin n)) (i : Fin m) : Finset (Fin r) :=
  Finset.univ.filter (fun q => 2 ≤ (L q).card ∧ L q ⊆ S i)

theorem privateGates_disjoint {n m r : ℕ} (S : Fin m → Finset (Fin n))
    (L : Fin r → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    {i j : Fin m} (hij : i ≠ j) :
    Disjoint (privateGates S L i) (privateGates S L j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hi hj
  obtain ⟨hq, hqi⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨_, hqj⟩ := (Finset.mem_filter.mp hj).2
  have hsub : L q ⊆ S i ∩ S j := fun a ha => Finset.mem_inter.mpr ⟨hqi ha, hqj ha⟩
  have := Finset.card_le_card hsub
  have := hS i j hij
  omega

theorem privateGates_sum_le {n m r : ℕ} (S : Fin m → Finset (Fin n))
    (L : Fin r → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∑ i : Fin m, (privateGates S L i).card ≤ r := by
  classical
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (privateGates S L) := by
    intro i _ j _ hij
    exact privateGates_disjoint S L hS hij
  calc
    ∑ i : Fin m, (privateGates S L i).card =
        (Finset.univ.biUnion (privateGates S L)).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = r := by simp

theorem assemble_privateGates {n m r : ℕ} (S : Fin m → Finset (Fin n))
    (L : Fin r → Finset (Fin n)) (c : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hlower : ∀ i, c i ≤ (privateGates S L i).card) :
    ∑ i : Fin m, c i ≤ r := by
  exact (Finset.sum_le_sum (fun i _ => hlower i)).trans (privateGates_sum_le S L hS)

def privateWireSet {n m : ℕ} (S : Fin m → Finset (Fin n))
    (L : ℕ → Finset (Fin n)) (W : Finset ℕ) (i : Fin m) : Finset ℕ :=
  W.filter (fun q => 2 ≤ (L q).card ∧ L q ⊆ S i)

theorem privateWireSet_disjoint {n m : ℕ} (S : Fin m → Finset (Fin n))
    (L : ℕ → Finset (Fin n)) (W : Finset ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    {i j : Fin m} (hij : i ≠ j) :
    Disjoint (privateWireSet S L W i) (privateWireSet S L W j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hi hj
  obtain ⟨hq, hqi⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨_, hqj⟩ := (Finset.mem_filter.mp hj).2
  have hsub : L q ⊆ S i ∩ S j := fun a ha => Finset.mem_inter.mpr ⟨hqi ha, hqj ha⟩
  have := Finset.card_le_card hsub
  have := hS i j hij
  omega

theorem privateWireSet_sum_le {n m : ℕ} (S : Fin m → Finset (Fin n))
    (L : ℕ → Finset (Fin n)) (W : Finset ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∑ i : Fin m, (privateWireSet S L W i).card ≤ W.card := by
  classical
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (privateWireSet S L W) := by
    intro i _ j _ hij
    exact privateWireSet_disjoint S L W hS hij
  calc
    ∑ i : Fin m, (privateWireSet S L W i).card =
        (Finset.univ.biUnion (privateWireSet S L W)).card := (Finset.card_biUnion hd).symm
    _ ≤ W.card := Finset.card_le_card (by
      intro q hq
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hq
      exact (Finset.mem_filter.mp hi).1)

theorem assemble_privateWireSet {n m : ℕ} (S : Fin m → Finset (Fin n))
    (L : ℕ → Finset (Fin n)) (W : Finset ℕ) (c : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hlower : ∀ i, c i ≤ (privateWireSet S L W i).card) :
    ∑ i : Fin m, c i ≤ W.card := by
  exact (Finset.sum_le_sum (fun i _ => hlower i)).trans (privateWireSet_sum_le S L W hS)

end PEqualNP.Outside.L_meta_782


namespace PEqualNP.Outside.L_meta_782

private theorem frontier_aux (P : Finset ℕ) (parents : ℕ → Finset ℕ)
    (hsmall : ∀ p ∈ P, (parents p).card ≤ 2)
    (hearlier : ∀ p ∈ P, ∀ q ∈ parents p, q < p) (k : ℕ) :
    ∀ F : Finset ℕ, (∀ f ∈ F, f < k) →
      ∃ E : Finset ℕ, E.card ≤ F.card + (P.filter (fun p => p < k)).card ∧
        (∀ e ∈ E, e ∉ P) ∧
        ∀ R : ℕ → Prop, (∀ p ∈ P, (∀ q ∈ parents p, R q) → R p) →
          (∀ e ∈ E, R e) → ∀ f ∈ F, R f := by
  induction k with
  | zero =>
    intro F hF
    have hFe : F = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro f hf
      have := hF f hf
      omega)
    subst F
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ k ih =>
    intro F hF
    have hcountle : (P.filter (fun p => p < k)).card ≤
        (P.filter (fun p => p < k + 1)).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, by
        have := (Finset.mem_filter.mp hp).2
        omega⟩
    by_cases hkF : k ∈ F
    · have herase : ∀ f ∈ F.erase k, f < k := by
        intro f hf
        have := hF f (Finset.mem_of_mem_erase hf)
        have := (Finset.mem_erase.mp hf).1
        omega
      have hFcard : (F.erase k).card + 1 = F.card := Finset.card_erase_add_one hkF
      by_cases hkP : k ∈ P
      · let F' := F.erase k ∪ parents k
        have hF' : ∀ f ∈ F', f < k := by
          intro f hf
          rcases Finset.mem_union.mp hf with hf | hf
          · exact herase f hf
          · exact hearlier k hkP f hf
        obtain ⟨E, hE, hEP, hER⟩ := ih F' hF'
        have hcount : (P.filter (fun p => p < k + 1)).card =
            (P.filter (fun p => p < k)).card + 1 := by
          have heq : P.filter (fun p => p < k + 1) =
              insert k (P.filter (fun p => p < k)) := by
            ext p
            by_cases hp : p = k
            · subst p
              simp [hkP]
            · have hlt : p < k + 1 ↔ p < k := by omega
              simp only [Finset.mem_filter, Finset.mem_insert, hp, false_or, hlt]
          rw [heq, Finset.card_insert_of_notMem (by simp)]
        have hF'card : F'.card ≤ (F.erase k).card + 2 := by
          exact (Finset.card_union_le _ _).trans
            (Nat.add_le_add_left (hsmall k hkP) _)
        refine ⟨E, by omega, hEP, ?_⟩
        intro R hR hRE f hf
        by_cases hfk : f = k
        · subst f
          apply hR k hkP
          intro q hq
          exact hER R hR hRE q (Finset.mem_union_right _ hq)
        · exact hER R hR hRE f
            (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hfk, hf⟩))
      · obtain ⟨E, hE, hEP, hER⟩ := ih (F.erase k) herase
        refine ⟨insert k E, ?_, ?_, ?_⟩
        · have := Finset.card_insert_le k E
          omega
        · intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact hkP
          · exact hEP e he
        · intro R hR hRE f hf
          by_cases hfk : f = k
          · exact hfk ▸ hRE k (Finset.mem_insert_self _ _)
          · exact hER R hR (fun e he => hRE e (Finset.mem_insert_of_mem he))
              f (Finset.mem_erase.mpr ⟨hfk,hf⟩)
    · have hFk : ∀ f ∈ F, f < k := by
        intro f hf
        have hlt := hF f hf
        have hne : f ≠ k := fun h => hkF (h ▸ hf)
        omega
      obtain ⟨E, hE, hEP, hER⟩ := ih F hFk
      exact ⟨E, by omega, hEP, hER⟩

theorem frontier_cut (P : Finset ℕ) (parents : ℕ → Finset ℕ)
    (hsmall : ∀ p ∈ P, (parents p).card ≤ 2)
    (hearlier : ∀ p ∈ P, ∀ q ∈ parents p, q < p) (r : ℕ) :
    ∃ E : Finset ℕ, E.card ≤ P.card + 1 ∧ (∀ e ∈ E, e ∉ P) ∧
      ∀ R : ℕ → Prop, (∀ p ∈ P, (∀ q ∈ parents p, R q) → R p) →
        (∀ e ∈ E, R e) → R r := by
  obtain ⟨E, hE, hEP, hER⟩ := frontier_aux P parents hsmall hearlier (r + 1)
    {r} (by simp)
  have hc : (P.filter (fun p => p < r + 1)).card ≤ P.card := Finset.card_filter_le _ _
  simp only [Finset.card_singleton] at hE
  refine ⟨E, by omega, hEP, ?_⟩
  intro R hR hRE
  exact hER R hR hRE r (Finset.mem_singleton_self r)

end PEqualNP.Outside.L_meta_782



namespace PEqualNP.Outside.L_meta_782.Bridge

open PEqualNP.CircuitLowerBounds

private def wireRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma wireRun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wireRun (g :: gs) x = wireRun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma wireRun_length (gs : List Gate) (x : List Bool) :
    (wireRun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wireRun]
  | cons g gs ih => rw [wireRun_cons, ih]; simp; omega

private lemma wireRun_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (wireRun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [wireRun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma wireRun_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    wireRun gs x = wireRun (gs.drop j) (wireRun (gs.take j) x) := by
  simpa only [wireRun, List.foldl_append] using
    congrArg (fun l : List Gate => wireRun l x) (List.take_append_drop j gs).symm

theorem wire_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < n) :
    (C.wires (List.ofFn x)).getD k false = x ⟨k,hk⟩ := by
  change (wireRun C.gates (List.ofFn x)).getD k false = _
  have hp : k < (List.ofFn x).length := by simpa using hk
  rw [wireRun_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

theorem wire_missing {n : ℕ} (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : n + C.gates.length ≤ k) : (C.wires (List.ofFn x)).getD k false = false := by
  change (wireRun C.gates (List.ofFn x)).getD k false = false
  exact List.getD_eq_default _ _ (by simpa [wireRun_length] using hk)

theorem wire_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun q =>
        if q < n + j then (C.wires (List.ofFn x)).getD q false else false) := by
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
  subst g
  let earlier := wireRun (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = n + j := by
    simp [earlier, wireRun_length, Nat.min_eq_left hj.le]
  have hsplit : wireRun C.gates (List.ofFn x) =
      wireRun (C.gates[j] :: C.gates.drop (j + 1)) earlier := by
    rw [wireRun_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (q : ℕ) : earlier.getD q false =
      if q < n + j then (C.wires (List.ofFn x)).getD q false else false := by
    by_cases hq : q < n + j
    · rw [ite_eq_left hq]
      change earlier.getD q false = (wireRun C.gates (List.ofFn x)).getD q false
      rw [hsplit]
      exact (wireRun_getD _ earlier q (by simpa only [plen] using hq)).symm
    · rw [ite_eq_right hq]
      exact List.getD_eq_default _ _ (by omega)
  change (wireRun C.gates (List.ofFn x)).getD (n + j) false = _
  rw (occs := [1]) [hsplit]
  rw (occs := [1]) [wireRun_cons]
  rw [wireRun_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

end PEqualNP.Outside.L_meta_782.Bridge


namespace PEqualNP.Outside.L_meta_782.Bridge

open PEqualNP.CircuitLowerBounds

def wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def singletons {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => wire C (fun b => decide (b = a)) w = true)

theorem binary_inputs (C : Circuit)
    (hc : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, C.gates[j].inputs = [a,b] ∧
      (C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) := by
  have hh := hc C.gates[j] (List.getElem_mem hj)
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp hh.2
  exact ⟨a,b,hab,hh.1⟩

theorem binary_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b c d : Bool) (ha : a = true → c = true) (hb : b = true → d = true) :
    op.eval [a,b] = true → op.eval [c,d] = true := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [GateOp.eval]

theorem wire_monotone {n : ℕ} (C : Circuit)
    (hc : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    wire C x w = true → wire C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · simpa only [wire, wire_input C x w hn, wire_input C y w hn] using hxy ⟨w,hn⟩
    by_cases hs : w < n + C.gates.length
    · let j := w - n
      have hj : j < C.gates.length := by dsimp [j]; omega
      have hw : n+j=w := by dsimp [j]; omega
      obtain ⟨a,b,hab,hop⟩ := binary_inputs C hc j hj
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      have hx := wire_gate C x j C.gates[j] hget
      have hy := wire_gate C y j C.gates[j] hget
      rw [hw] at hx hy
      change (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn y)).getD w false = true
      rw [hx,hy,hab]
      simp only [List.map_cons,List.map_nil]
      apply binary_eval_mono _ hop
      · by_cases hq : a < w
        · simpa only [ite_eq_left hq,wire] using ih a hq
        · simp only [ite_eq_right hq, Bool.false_eq_true, false_implies]
      · by_cases hq : b < w
        · simpa only [ite_eq_left hq,wire] using ih b hq
        · simp only [ite_eq_right hq, Bool.false_eq_true, false_implies]
    · have hm : n+C.gates.length ≤ w := by omega
      simp only [wire,wire_missing C x w hm,Bool.false_eq_true,false_implies]

theorem singleton_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    singletons C w = {⟨w,hw⟩} := by
  apply Finset.ext
  intro a
  change a ∈ Finset.univ.filter (fun a => wire C (fun b => decide (b=a)) w = true) ↔
    a ∈ ({⟨w,hw⟩} : Finset (Fin n))
  constructor
  · intro ha
    have hv := (Finset.mem_filter.mp ha).2
    change (C.wires (List.ofFn (fun b : Fin n => decide (b=a)))).getD w false = true at hv
    rw [wire_input C _ w hw] at hv
    exact Finset.mem_singleton.mpr (of_decide_eq_true hv).symm
  · intro ha
    have he := Finset.mem_singleton.mp ha
    subst a
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (C.wires (List.ofFn (fun b : Fin n => decide (b=⟨w,hw⟩)))).getD w false = true
    rw [wire_input C _ w hw]
    exact decide_eq_true rfl

theorem singleton_missing {n : ℕ} (C : Circuit) (w : ℕ)
    (hw : n+C.gates.length ≤ w) : singletons (n:=n) C w = ∅ := by
  apply Finset.ext
  intro a
  change a ∈ Finset.univ.filter (fun a => wire C (fun b => decide (b=a)) w = true) ↔
    a ∈ (∅ : Finset (Fin n))
  constructor
  · intro ha
    have hv := (Finset.mem_filter.mp ha).2
    change (C.wires (List.ofFn (fun b : Fin n => decide (b=a)))).getD w false = true at hv
    rw [wire_missing C _ w hw] at hv
    cases hv
  · intro ha
    exact False.elim (Finset.notMem_empty a ha)

theorem singleton_gate {n : ℕ} (C : Circuit) (w : ℕ)
    (hw : 2 ≤ (singletons (n:=n) C w).card) : n ≤ w ∧ w < n+C.gates.length := by
  constructor
  · by_contra h
    have hh : w < n := by omega
    rw [singleton_input C w hh,Finset.card_singleton] at hw
    omega
  · by_contra h
    have hh : n+C.gates.length ≤ w := by omega
    rw [singleton_missing C w hh,Finset.card_empty] at hw
    omega

end PEqualNP.Outside.L_meta_782.Bridge


namespace PEqualNP.Outside.L_meta_782.Bridge

open PEqualNP.CircuitLowerBounds

def parents (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  if h : n ≤ w ∧ w < n+C.gates.length then
    ((C.gates[w-n]'(by omega)).inputs.filter (fun q => q < w)).toFinset
  else ∅

def label (n : ℕ) (C : Circuit) (P : Finset ℕ) (base : ℕ → Bool) (w : ℕ) : Bool :=
  if w ∈ P then
    if h : n ≤ w ∧ w < n+C.gates.length then
      (C.gates[w-n]'(by omega)).op.eval
        ((C.gates[w-n]'(by omega)).inputs.map
          (fun q => if hq : q < w then label n C P base q else false))
    else base w
  else base w
termination_by w

theorem label_nonprivate (n : ℕ) (C : Circuit) (P : Finset ℕ) (base : ℕ → Bool)
    (w : ℕ) (hw : w ∉ P) : label n C P base w = base w := by
  rw [label, ite_eq_right hw]

theorem label_private (n : ℕ) (C : Circuit) (P : Finset ℕ) (base : ℕ → Bool)
    (w : ℕ) (hw : w ∈ P) (h : n ≤ w ∧ w < n+C.gates.length) :
    label n C P base w = (C.gates[w-n]'(by omega)).op.eval
      ((C.gates[w-n]'(by omega)).inputs.map
        (fun q => if q < w then label n C P base q else false)) := by
  rw [label, ite_eq_left hw, dite_eq_left h]
  congr 2

theorem parents_lt (n : ℕ) (C : Circuit) (w q : ℕ) (hq : q ∈ parents n C w) : q < w := by
  unfold parents at hq
  split at hq
  · exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hq)).2
  · exact False.elim (Finset.notMem_empty q hq)

theorem mem_parents_iff (n : ℕ) (C : Circuit) (w : ℕ)
    (h : n ≤ w ∧ w < n+C.gates.length) (q : ℕ) :
    q ∈ parents n C w ↔ q ∈ (C.gates[w-n]'(by omega)).inputs ∧ q < w := by
  simp only [parents, dite_eq_left h, List.mem_toFinset,List.mem_filter,decide_eq_true_eq]

theorem wire_at {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (h : n ≤ w ∧ w < n+C.gates.length) :
    wire C x w = (C.gates[w-n]'(by omega)).op.eval
      ((C.gates[w-n]'(by omega)).inputs.map
        (fun q => if q < w then wire C x q else false)) := by
  have hj : w-n < C.gates.length := by omega
  have hh := wire_gate C x (w-n) C.gates[w-n] (List.getElem?_eq_getElem hj)
  have he : n+(w-n)=w := by omega
  simpa only [he,wire] using hh

theorem parents_card (n : ℕ) (C : Circuit)
    (hc : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : ℕ) : (parents n C w).card ≤ 2 := by
  by_cases hw : n ≤ w ∧ w < n+C.gates.length
  · obtain ⟨a,b,hab,hop⟩ := binary_inputs C hc (w-n) (by omega)
    have hh : parents n C w ⊆ ({a,b} : Finset ℕ) := by
      intro q hq
      have := ((mem_parents_iff n C w hw q).mp hq).1
      simpa [hab] using this
    calc
      (parents n C w).card ≤ ({a,b} : Finset ℕ).card := Finset.card_le_card hh
      _ ≤ 2 := by by_cases hab : a=b <;> simp [hab]
  · simp only [parents,dite_eq_right hw,Finset.card_empty,zero_le]

theorem local_eval_mono (n : ℕ) (C : Circuit)
    (hc : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : ℕ) (hw : n ≤ w ∧ w < n+C.gates.length) (f g : ℕ → Bool)
    (hfg : ∀ q ∈ parents n C w, f q = true → g q = true) :
    (C.gates[w-n]'(by omega)).op.eval
      ((C.gates[w-n]'(by omega)).inputs.map (fun q => if q<w then f q else false)) = true →
    (C.gates[w-n]'(by omega)).op.eval
      ((C.gates[w-n]'(by omega)).inputs.map (fun q => if q<w then g q else false)) = true := by
  obtain ⟨a,b,hab,hop⟩ := binary_inputs C hc (w-n) (by omega)
  rw [hab]
  simp only [List.map_cons,List.map_nil]
  apply binary_eval_mono _ hop
  · by_cases ha : a < w
    · simp only [ite_eq_left ha]
      exact hfg a ((mem_parents_iff n C w hw a).mpr ⟨by simp [hab],ha⟩)
    · simp only [ite_eq_right ha,Bool.false_eq_true,false_implies]
  · by_cases hb : b < w
    · simp only [ite_eq_left hb]
      exact hfg b ((mem_parents_iff n C w hw b).mpr ⟨by simp [hab],hb⟩)
    · simp only [ite_eq_right hb,Bool.false_eq_true,false_implies]

theorem label_forward {n : ℕ} (C : Circuit)
    (hc : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (P : Finset ℕ) (base : ℕ → Bool) (w : ℕ) (hw : w ∈ P)
    (hg : n ≤ w ∧ w < n+C.gates.length) (x : Fin n → Bool)
    (hcomp : ∀ q ∈ parents n C w, label n C P base q = true → wire C x q = true) :
    label n C P base w = true → wire C x w = true := by
  rw [label_private n C P base w hw hg,wire_at C x w hg]
  exact local_eval_mono n C hc w hg _ _ hcomp

theorem label_backward {n : ℕ} (C : Circuit)
    (hc : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (P : Finset ℕ) (base : ℕ → Bool) (w : ℕ) (hw : w ∈ P)
    (hg : n ≤ w ∧ w < n+C.gates.length) (x : Fin n → Bool)
    (hcomp : ∀ q ∈ parents n C w, wire C x q = true → label n C P base q = true) :
    wire C x w = true → label n C P base w = true := by
  rw [label_private n C P base w hw hg,wire_at C x w hg]
  exact local_eval_mono n C hc w hg _ _ hcomp

end PEqualNP.Outside.L_meta_782.Bridge



namespace PEqualNP.Outside.L_meta_782

theorem local_budget {n k c : ℕ} (S : Finset (Fin n))
    (V : (Fin n → Bool) → ℕ → Bool) (r : ℕ)
    (L : ℕ → Finset (Fin n)) (P : Finset ℕ)
    (parents : ℕ → Finset ℕ) (label : ℕ → Bool)
    (hL : ∀ a w, a ∈ L w ↔ V (fun b => decide (b = a)) w = true)
    (hmono : ∀ w x y, (∀ a, x a = true → y a = true) →
      V x w = true → V y w = true)
    (hsmall : ∀ w, w ∉ P → L w ⊆ S → (L w).card ≤ 1)
    (hlabel : ∀ w, w ∉ P → (label w = true ↔ ¬ L w ⊆ S))
    (hforward : ∀ x p, p ∈ P →
      (∀ q ∈ parents p, label q = true → V x q = true) →
      label p = true → V x p = true)
    (hbackward : ∀ x p, p ∈ P →
      (∀ q ∈ parents p, V x q = true → label q = true) →
      V x p = true → label p = true)
    (hcut : ∃ E : Finset ℕ, E.card ≤ P.card + 1 ∧
      (∀ e ∈ E, e ∉ P) ∧
      ∀ R : ℕ → Prop,
        (∀ p ∈ P, (∀ q ∈ parents p, R q) → R p) →
        (∀ e ∈ E, R e) → R r)
    (hpromise : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → V x r = false)
    (hc : c ≤ k) (hroot : c + 1 ≤ (L r).card) : c ≤ P.card := by
  classical
  by_contra hn
  have hpk : P.card + 1 ≤ k := by omega
  obtain ⟨E, hEcard, hEP, hE⟩ := hcut
  cases hlroot : label r with
  | false =>
    let F := E.filter (fun e => label e = false)
    have hcover : L r ⊆ F.biUnion L := by
      intro a ha
      by_contra hnot
      have hends : ∀ e ∈ E,
          V (fun b => decide (b = a)) e = true → label e = true := by
        intro e he hae
        cases hle : label e with
        | true => rfl
        | false =>
          apply False.elim
          apply hnot
          apply Finset.mem_biUnion.mpr
          exact ⟨e, Finset.mem_filter.mpr ⟨he, hle⟩, (hL a e).mpr hae⟩
      have hr := hE (fun w => V (fun b => decide (b = a)) w = true → label w = true)
        (fun p hp hpar => hbackward _ p hp hpar) hends ((hL a r).mp ha)
      rw [hlroot] at hr
      cases hr
    have hsmallF : ∀ e ∈ F, (L e).card ≤ 1 := by
      intro e he
      obtain ⟨heE, hle⟩ := Finset.mem_filter.mp he
      apply hsmall e (hEP e heE)
      by_contra hnot
      have := (hlabel e (hEP e heE)).mpr hnot
      rw [hle] at this
      cases this
    have hcard : (L r).card ≤ E.card := by
      calc
        (L r).card ≤ (F.biUnion L).card := Finset.card_le_card hcover
        _ ≤ ∑ e ∈ F, (L e).card := Finset.card_biUnion_le
        _ ≤ ∑ _e ∈ F, 1 := Finset.sum_le_sum hsmallF
        _ = F.card := by simp
        _ ≤ E.card := Finset.card_le_card (Finset.filter_subset ..)
    omega
  | true =>
    let F := E.filter (fun e => label e = true)
    have hwitness : ∀ e ∈ F, ∃ a, a ∈ L e ∧ a ∉ S := by
      intro e he
      obtain ⟨heE, hle⟩ := Finset.mem_filter.mp he
      have hnot := (hlabel e (hEP e heE)).mp hle
      exact Finset.not_subset.mp hnot
    choose a ha using hwitness
    let B : Finset (Fin n) := F.attach.image (fun e => a e.val e.property)
    let x : Fin n → Bool := fun b => decide (b ∈ B)
    have hBcard : B.card ≤ E.card := by
      calc
        B.card ≤ F.attach.card := Finset.card_image_le
        _ = F.card := Finset.card_attach
        _ ≤ E.card := Finset.card_le_card (Finset.filter_subset ..)
    have hBoutside : ∀ b ∈ B, b ∉ S := by
      intro b hb
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hb
      exact (ha e.val e.property).2
    have hends : ∀ e ∈ E, label e = true → V x e = true := by
      intro e he hle
      have heF : e ∈ F := Finset.mem_filter.mpr ⟨he, hle⟩
      apply hmono e (fun b => decide (b = a e heF)) x
      · intro b hb
        have hb' : b = a e heF := of_decide_eq_true hb
        subst b
        apply decide_eq_true
        exact Finset.mem_image.mpr ⟨⟨e, heF⟩, Finset.mem_attach .., rfl⟩
      · exact (hL _ e).mp (ha e heF).1
    have hr : V x r = true := hE (fun w => label w = true → V x w = true)
      (fun p hp hpar => hforward x p hp hpar) hends hlroot
    have hrfalse : V x r = false := hpromise x (by
      have hx : (Finset.univ.filter (fun q => x q = true)) = B := by
        ext b
        simp [x]
      rw [hx]
      omega) (by
        intro b hbS
        change decide (b ∈ B) = false
        exact decide_eq_false (fun hbB => hBoutside b hbB hbS))
    rw [hrfalse] at hr
    cases hr

end PEqualNP.Outside.L_meta_782


namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

theorem circuit_assembly (n m k : ℕ) (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hpromise : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S i, x q = false) → Bridge.wire C x (o i) = false)
    (hck : ∀ i : Fin m, c i ≤ k)
    (hroot : ∀ i : Fin m, c i + 1 ≤ (Bridge.singletons (n := n) C (o i)).card) :
    ∑ i : Fin m, c i ≤ C.size := by
  classical
  let L : ℕ → Finset (Fin n) := Bridge.singletons C
  let W : Finset ℕ := Finset.Ico n (n + C.size)
  have hbudget (i : Fin m) : c i ≤ (privateWireSet S L W i).card := by
    let P := privateWireSet S L W i
    let base : ℕ → Bool := fun w => decide (¬ L w ⊆ S i)
    let lab : ℕ → Bool := Bridge.label n C P base
    have hvalid : ∀ p ∈ P, n ≤ p ∧ p < n + C.gates.length := by
      intro p hp
      have hpW := (Finset.mem_filter.mp hp).1
      simpa only [W, Finset.mem_Ico, Circuit.size] using hpW
    apply local_budget (S i) (Bridge.wire C) (o i) L P
      (Bridge.parents n C) lab
    · intro a w
      simp [L, Bridge.singletons]
    · intro w x y hxy
      exact Bridge.wire_monotone C hC x y hxy w
    · intro w hw hsub
      by_contra hcard
      have htwo : 2 ≤ (L w).card := by omega
      have hg := Bridge.singleton_gate C w htwo
      apply hw
      apply Finset.mem_filter.mpr
      refine ⟨?_, htwo, hsub⟩
      exact Finset.mem_Ico.mpr (by simpa only [Circuit.size] using hg)
    · intro w hw
      change Bridge.label n C P base w = true ↔ ¬ L w ⊆ S i
      rw [Bridge.label_nonprivate n C P base w hw]
      simp only [base, decide_eq_true_eq]
    · intro x p hp hpar
      exact Bridge.label_forward C hC P base p hp (hvalid p hp) x hpar
    · intro x p hp hpar
      exact Bridge.label_backward C hC P base p hp (hvalid p hp) x hpar
    · apply frontier_cut P (Bridge.parents n C)
      · intro p hp
        exact Bridge.parents_card n C hC p
      · intro p hp q hq
        exact Bridge.parents_lt n C p q hq
    · exact hpromise i
    · exact hck i
    · exact hroot i
  have hb := assemble_privateWireSet S L W c hS hbudget
  have hW : W.card = C.size := by simp [W]
  exact hW ▸ hb

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hS _haccept hC _hinside hpromise hck hroot
  exact PEqualNP.Outside.L_meta_782.circuit_assembly n m k S C o c hS hC hpromise hck hroot

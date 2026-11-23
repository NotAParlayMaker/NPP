import Mathlib
import PEqualNP.Defs

-- The gate-evaluation lemmas adapt Adam Bílek’s proof of L-meta-613.

namespace PEqualNP.Outside.L_meta_925

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

private theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

private theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

private theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

private theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

private theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

private def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private theorem val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_step_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem val_none (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hg : C.gates[j]? = none) : val C n x (n + j) = false := by
  unfold val
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length]
  have := List.getElem?_eq_none_iff.mp hg
  simp only [List.length_ofFn]
  omega

private theorem val_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) :
    val C n x (n + j) =
      h.op.eval (h.inputs.map fun i => if i < n + j then val C n x i else false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  have := gate_value C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at this
  exact this

private theorem val_or (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.or) :
    val C n x (n + j) = true ↔ ∃ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨w, hw, hv⟩
    by_cases hlt : w < n + j
    · exact ⟨w, hw, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨w, hw, hlt, hv⟩
    exact ⟨w, hw, by simpa [hlt] using hv⟩

private theorem val_and (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and) :
    val C n x (n + j) = true ↔ ∀ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  constructor
  · intro hall w hw
    have hv := hall w hw
    by_cases hlt : w < n + j
    · exact ⟨hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · intro hall w hw
    obtain ⟨hlt, hv⟩ := hall w hw
    simpa [hlt] using hv


-- Gate lists determine all wire values independently of the designated output.
def wire {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD w false

theorem wire_input {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wire gates x w = x ⟨w,hw⟩ :=
  val_input ⟨gates,0⟩ n x w hw

theorem wire_missing {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : wire gates x w = false := by
  unfold wire
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length, List.length_ofFn]
  exact hw

theorem wire_gate {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : gates[j]? = some g) : wire gates x (n+j) =
    g.op.eval (g.inputs.map fun a => if a < n+j then wire gates x a else false) :=
  val_gate ⟨gates,0⟩ n x j g hj

theorem wire_mono {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) (ht : wire gates x w = true) : wire gates y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hi : w < n
    · rw [wire_input _ _ _ hi] at ht ⊢
      exact hxy _ ht
    · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      by_cases hj : j < gates.length
      · let g := gates[j]
        have atj : (⟨gates,0⟩ : Circuit).gates[j]? = some g := List.getElem?_eq_getElem hj
        rcases (hg g (List.getElem_mem hj)).1 with h | h
        · have all := (val_and ⟨gates,0⟩ n x j g atj h).mp ht
          apply (val_and ⟨gates,0⟩ n y j g atj h).mpr
          intro a ha
          obtain ⟨hprev,hx⟩ := all a ha
          exact ⟨hprev,ih a hprev hx⟩
        · obtain ⟨a,ha,hprev,hx⟩ := (val_or ⟨gates,0⟩ n x j g atj h).mp ht
          exact (val_or ⟨gates,0⟩ n y j g atj h).mpr ⟨a,ha,hprev,ih a hprev hx⟩
      · rw [wire_missing _ _ _ (by omega)] at ht
        contradiction

theorem expand {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) (j : ℕ) (hj : j < gates.length)
    (ht : wire gates x (n+j) = true) :
    ∃ B : Finset ℕ, B.card ≤ 2 ∧ (∀ a ∈ B, a < n+j ∧ wire gates x a = true) ∧
      ∀ y : Fin n → Bool, (∀ a ∈ B, wire gates y a = true) → wire gates y (n+j) = true := by
  let g := gates[j]
  have atj : (⟨gates,0⟩ : Circuit).gates[j]? = some g := List.getElem?_eq_getElem hj
  obtain ⟨hop,hlen⟩ := hg g (List.getElem_mem hj)
  rcases hop with h | h
  · have all := (val_and ⟨gates,0⟩ n x j g atj h).mp ht
    refine ⟨g.inputs.toFinset, g.inputs.toFinset_card_le.trans hlen, ?_, ?_⟩
    · intro a ha
      exact all a (List.mem_toFinset.mp ha)
    · intro y hy
      exact (val_and ⟨gates,0⟩ n y j g atj h).mpr
        (fun a ha => ⟨(all a ha).1, hy a (List.mem_toFinset.mpr ha)⟩)
  · obtain ⟨a,ha,hprev,hx⟩ := (val_or ⟨gates,0⟩ n x j g atj h).mp ht
    refine ⟨{a}, by simp, ?_, ?_⟩
    · intro b hb
      rw [Finset.mem_singleton.mp hb]
      exact ⟨hprev,hx⟩
    · intro y hy
      exact (val_or ⟨gates,0⟩ n y j g atj h).mpr ⟨a,ha,hprev,hy a (Finset.mem_singleton_self _)⟩

end PEqualNP.Outside.L_meta_925

namespace PEqualNP.Outside.L_meta_925

private theorem descend {α : Type*} (G : Finset ℕ) (P : ℕ → Prop) (V : α → ℕ → Prop)
    (step : ∀ j ∈ G, P j → ∃ R : Finset ℕ, R.card ≤ 2 ∧
      (∀ r ∈ R, r < j ∧ P r) ∧ ∀ y, (∀ r ∈ R, V y r) → V y j)
    (t : ℕ) (F : Finset ℕ) (hp : ∀ u ∈ F, P u) (hlt : ∀ u ∈ F, u ∈ G → u < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      (∀ r ∈ B, P r) ∧ ∀ y, (∀ r ∈ B, V y r) → ∀ u ∈ F, V y u := by
  induction t generalizing F with
  | zero =>
    refine ⟨F, Finset.disjoint_left.mpr (fun u hu hg => by have := hlt u hu hg; omega),
      Nat.le_add_right .., hp, fun _ h => h⟩
  | succ t ih =>
    by_cases visit : t ∈ F ∧ t ∈ G
    · obtain ⟨R, hcard, hchild, hgate⟩ := step t visit.2 (hp t visit.1)
      let F' := F.erase t ∪ R
      have hP' : ∀ u ∈ F', P u := by
        intro u hu
        rcases Finset.mem_union.mp hu with hu | hu
        · exact hp u (Finset.mem_of_mem_erase hu)
        · exact (hchild u hu).2
      have hlt' : ∀ u ∈ F', u ∈ G → u < t := by
        intro u hu hg
        rcases Finset.mem_union.mp hu with hu | hu
        · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hu
          have := hlt u hmem hg
          omega
        · exact (hchild u hu).1
      obtain ⟨B, hd, hb, hpB, reach⟩ := ih F' hP' hlt'
      have hFcard : F'.card ≤ F.card + 1 := by
        have h := Finset.card_union_le (F.erase t) R
        have e := Finset.card_erase_add_one visit.1
        change F'.card ≤ _ at h
        omega
      have hf : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hu⟩
          by_cases h : u = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hu⟩)
          · exact ⟨visit.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, hpB, ?_⟩
      · rw [hf, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro y hy u hu
        by_cases h : u = t
        · subst u
          exact hgate y (fun r hr => reach y hy r (Finset.mem_union_right _ hr))
        · exact reach y hy u (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h,hu⟩))
    · have hlt' : ∀ u ∈ F, u ∈ G → u < t := by
        intro u hu hg
        have h := hlt u hu hg
        have hne : u ≠ t := fun e => visit ⟨e ▸ hu, e ▸ hg⟩
        omega
      obtain ⟨B, hd, hb, hpB, reach⟩ := ih F hp hlt'
      have inc : (G.filter (· < t)).card ≤ (G.filter (· < t+1)).card :=
        Finset.card_le_card fun u hu => by
          obtain ⟨hg,hh⟩ := Finset.mem_filter.mp hu
          exact Finset.mem_filter.mpr ⟨hg, by omega⟩
      exact ⟨B,hd,by omega,hpB,reach⟩

-- Expand in descending wire order. Each wire can be charged at most once.
theorem frontier_cut {α : Type*} (G : Finset ℕ) (P : ℕ → Prop) (V : α → ℕ → Prop)
    (step : ∀ j ∈ G, P j → ∃ R : Finset ℕ, R.card ≤ 2 ∧
      (∀ r ∈ R, r < j ∧ P r) ∧ ∀ y, (∀ r ∈ R, V y r) → V y j)
    (o : ℕ) (ho : P o) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ 1 + G.card ∧
      (∀ r ∈ B, P r) ∧ ∀ y, (∀ r ∈ B, V y r) → V y o := by
  obtain ⟨B, hd, hb, hpB, reach⟩ := descend G P V step (o+1) {o}
    (fun u hu => (Finset.mem_singleton.mp hu) ▸ ho)
    (fun u hu _ => (Finset.mem_singleton.mp hu) ▸ Nat.lt_succ_self o)
  have h := Finset.card_filter_le G (· < o+1)
  simp only [Finset.card_singleton] at hb
  exact ⟨B,hd,by omega,hpB,fun y hy => reach y hy o (Finset.mem_singleton_self o)⟩

end PEqualNP.Outside.L_meta_925

namespace PEqualNP.Outside.L_meta_925

open Finset

lemma line_union_bound {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hcard : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) (D : Finset (Fin m)) :
    (D.biUnion S).card ≤ q * D.card + 1 := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert v E hv ih =>
    simp only [Finset.biUnion_insert, Finset.card_insert_of_notMem hv, Nat.mul_add, Nat.mul_one]
    by_cases he : E.Nonempty
    · obtain ⟨u, hu⟩ := he
      have hd : v ≠ u := fun h => hv (h ▸ hu)
      have hs : S v ∩ S u ⊆ S v ∩ E.biUnion S := by
        intro x hx
        obtain ⟨hxv, hxu⟩ := Finset.mem_inter.mp hx
        exact Finset.mem_inter.mpr ⟨hxv, Finset.mem_biUnion.mpr ⟨u, hu, hxu⟩⟩
      have h1 := Finset.card_le_card hs
      rw [hinter v u hd] at h1
      have h2 := Finset.card_union_add_card_inter (S v) (E.biUnion S)
      rw [hcard] at h2
      omega
    · have hE := Finset.not_nonempty_iff_eq_empty.mp he
      subst E
      simp [hcard]

lemma drop_bounds {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hcard : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (w : Fin m) (D : Finset (Fin m)) (A : Finset (Fin n))
    (haway : w ∉ D) (hq : 1 ≤ q) :
    (A ∪ D.biUnion S).card ≤ q * (D.card + A.card) + 1 ∧
      ((A ∪ D.biUnion S) ∩ S w).card ≤ D.card + A.card := by
  classical
  constructor
  · have hu := Finset.card_union_le A (D.biUnion S)
    have hl := line_union_bound S hcard hinter D
    have hm := Nat.le_mul_of_pos_left A.card hq
    rw [Nat.mul_add]
    omega
  · have hs : (A ∪ D.biUnion S) ∩ S w ⊆ A ∪ D.biUnion (fun i => S i ∩ S w) := by
      intro x hx
      obtain ⟨hU, hw⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_union.mp hU with hA | hD
      · exact Finset.mem_union.mpr (Or.inl hA)
      · obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hD
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
          ⟨i, hi, Finset.mem_inter.mpr ⟨hx, hw⟩⟩))
    have h1 := Finset.card_le_card hs
    have h2 := Finset.card_union_le A (D.biUnion (fun i => S i ∩ S w))
    have h3 := Finset.card_biUnion_le_card_mul D (fun i => S i ∩ S w) 1 (fun i hi => by
      rw [hinter i w (fun h => haway (h ▸ hi))])
    omega

lemma sum_assigned {n m g c : ℕ} (assigned : Fin m → Finset ℕ)
    (hsub : ∀ w, assigned w ⊆ Finset.Ico n (n + g))
    (hd : ∀ v w, v ≠ w → Disjoint (assigned v) (assigned w))
    (hl : ∀ w, c ≤ (assigned w).card) : m * c ≤ g := by
  classical
  have hp : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint assigned := by
    intro v _ w _ hvw
    exact hd v w hvw
  calc
    m * c = ∑ _w : Fin m, c := by simp
    _ ≤ ∑ w : Fin m, (assigned w).card := Finset.sum_le_sum fun w _ => hl w
    _ = (Finset.univ.biUnion assigned).card := (Finset.card_biUnion hp).symm
    _ ≤ (Finset.Ico n (n + g)).card := Finset.card_le_card fun j hj => by
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hj
      exact hsub i hi
    _ = g := by simp

end PEqualNP.Outside.L_meta_925

namespace PEqualNP.Outside.L_meta_925

open PEqualNP.CircuitLowerBounds
open Finset

private def pointInput {n : ℕ} (A : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ A)

private theorem pointInput_weight {n : ℕ} (A : Finset (Fin n)) :
    (Finset.univ.filter (fun i => pointInput A i = true)).card = A.card := by
  congr 1
  ext i
  simp [pointInput]

private theorem pointInput_le {n : ℕ} {A B : Finset (Fin n)} (h : A ⊆ B)
    (i : Fin n) (hi : pointInput A i = true) : pointInput B i = true := by
  exact decide_eq_true (h (of_decide_eq_true hi))

private theorem main_bound (q n m K : ℕ) (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hcard : ∀ i : Fin m, (S i).card = q + 1)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (houtputs : ∀ (w : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true))
    (c : ℕ) (hc : c ≤ q) (hK : c * q < K) : m * c ≤ gates.length := by
  classical
  rcases Nat.eq_zero_or_pos c with rfl | hcpos
  · simp
  have hlight : q + 1 ≤ K := by
    have hmul := Nat.mul_le_mul_right q hcpos
    omega
  let hit (w : Fin m) (a : ℕ) : Prop := wire gates (pointInput (S w)) a = true
  let assigned (w : Fin m) : Finset ℕ := (Ico n (n + gates.length)).filter fun a =>
    hit w a ∧ ∀ v : Fin m, v ≠ w → ¬ hit v a
  have bound (w : Fin m) : c ≤ (assigned w).card := by
    by_contra! hsmall
    have ho : hit w (out w) := by
      change Circuit.eval ⟨gates, out w⟩ (List.ofFn (pointInput (S w))) = true
      rw [houtputs w _ (by rw [pointInput_weight, hcard]; exact hlight)]
      simp [pointInput]
    have step (a : ℕ) (ha : a ∈ assigned w) (ht : hit w a) : ∃ B : Finset ℕ,
        B.card ≤ 2 ∧ (∀ b ∈ B, b < a ∧ hit w b) ∧
        ∀ y : Fin n → Bool, (∀ b ∈ B, wire gates y b = true) → wire gates y a = true := by
      obtain ⟨ha₀, ha₁⟩ := mem_Ico.mp (mem_filter.mp ha).1
      obtain ⟨j, rfl⟩ : ∃ j, a = n + j := ⟨a - n, by omega⟩
      exact expand gates hg (pointInput (S w)) j (by omega) ht
    obtain ⟨B, hdisj, hB, hbtrue, hcut⟩ := frontier_cut (assigned w) (hit w)
      (fun (y : Fin n → Bool) (a : ℕ) => wire gates y a = true) step (out w) ho
    have hBc : B.card ≤ c := by omega
    -- An input exit is witnessed by a singleton. Every other exit is witnessed
    -- by a different member of the set system.
    let L := B.filter (· < n)
    let E := B.filter (fun a : ℕ => ¬ a < n)
    let point (a : L) : Fin n := ⟨a.val, (mem_filter.mp a.property).2⟩
    let A : Finset (Fin n) := L.attach.image point
    have other (a : E) : ∃ v : Fin m, v ≠ w ∧ hit v a.val := by
      obtain ⟨haB, ha₀⟩ := mem_filter.mp a.property
      have ha₁ : a.val < n + gates.length := by
        by_contra! hfar
        have hfalse := wire_missing gates (pointInput (S w)) a.val hfar
        have htrue := hbtrue a.val haB
        simp [hit, hfalse] at htrue
      by_contra! hall
      exact (Finset.disjoint_left.mp hdisj haB)
        (mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.le_of_not_gt ha₀, ha₁⟩, hbtrue _ haB, hall⟩)
    choose v hv using other
    let D : Finset (Fin m) := E.attach.image v
    have haway : w ∉ D := by
      intro hw
      obtain ⟨a, _, ha⟩ := mem_image.mp hw
      exact (hv a).1 ha
    have hcardA : A.card ≤ L.card := by simpa [A] using card_image_le (s := L.attach) (f := point)
    have hcardD : D.card ≤ E.card := by simpa [D] using card_image_le (s := E.attach) (f := v)
    have hparts : L.card + E.card = B.card := Finset.card_filter_add_card_filter_not (s := B) (fun a => a < n)
    have hDE : D.card + A.card ≤ c := by omega
    let P := A ∪ D.biUnion S
    obtain ⟨hweight, hoverlap⟩ := drop_bounds S hcard hinter w D A haway (by omega)
    have hPweight : P.card ≤ K := by
      have hmul := Nat.mul_le_mul_left q hDE
      change P.card ≤ _ at hweight
      rw [Nat.mul_comm q c] at hmul
      omega
    have hy : wire gates (pointInput P) (out w) = true := by
      apply hcut
      intro a ha
      by_cases hraw : a < n
      · let z : L := ⟨a, mem_filter.mpr ⟨ha, hraw⟩⟩
        have pIn : point z ∈ A := mem_image_of_mem point (mem_attach L z)
        have hP : (⟨a, hraw⟩ : Fin n) ∈ P := mem_union_left _ pIn
        rw [wire_input gates (pointInput P) a hraw]
        exact decide_eq_true hP
      · let z : E := ⟨a, mem_filter.mpr ⟨ha, hraw⟩⟩
        have hvD : v z ∈ D := mem_image_of_mem v (mem_attach E z)
        have hsub : S (v z) ⊆ P := fun i hi => mem_union_right _ (mem_biUnion.mpr ⟨_, hvD, hi⟩)
        exact wire_mono gates hg (pointInput (S (v z))) (pointInput P) (pointInput_le hsub) a (hv z).2
    have hmiss : ¬ ∀ p ∈ S w, pointInput P p = true := by
      intro hall
      have hsub : S w ⊆ P := fun p hp => of_decide_eq_true (hall p hp)
      change (P ∩ S w).card ≤ _ at hoverlap
      rw [Finset.inter_eq_right.mpr hsub, hcard] at hoverlap
      omega
    have hfalse := houtputs w (pointInput P) (by rwa [pointInput_weight])
    rw [decide_eq_false hmiss] at hfalse
    change wire gates (pointInput P) (out w) = false at hfalse
    rw [hfalse] at hy
    cases hy
  apply sum_assigned assigned (fun _ => filter_subset _ _) ?_ bound
  intro v w hvw
  exact disjoint_left.mpr fun a ha hb =>
    (mem_filter.mp ha).2.2 w hvw.symm (mem_filter.mp hb).2.1

end PEqualNP.Outside.L_meta_925

open PEqualNP.Outside.L_meta_925 in
theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  exact main_bound

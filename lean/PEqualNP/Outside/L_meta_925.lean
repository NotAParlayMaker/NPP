import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925

open PEqualNP.CircuitLowerBounds
open Classical

-- One gate appended to the wire list, as in Circuit.wires.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem len_fold : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem getD_fold_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (step w g) i (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_fold_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  rw [List.getD_eq_default]
  rw [len_fold]
  exact h

theorem getD_fold_gate : ∀ (gs : List Gate) (w : List Bool) (k : ℕ) (g : Gate), gs[k]? = some g →
    (gs.foldl step w).getD (w.length + k) false =
      g.op.eval (g.inputs.map fun i => ((gs.take k).foldl step w).getD i false) := by
  intro gs
  induction gs with
  | nil => intro w k g h; simp at h
  | cons g0 gs ih =>
    intro w k g h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [List.foldl_cons, getD_fold_lt gs (step w g0) (w.length + 0) (by simp [step])]
      simp [step, List.getD_eq_getElem?_getD]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      have hih := ih (step w g0) k g h
      have hl : (step w g0).length = w.length + 1 := by simp [step]
      rw [hl] at hih
      rw [List.foldl_cons, show w.length + (k + 1) = w.length + 1 + k by omega, hih]
      simp only [List.take_succ_cons, List.foldl_cons]

theorem lt_of_get (l : List Gate) (k : ℕ) (g : Gate) (h : l[k]? = some g) : k < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ j ∈ l, f j = true → f' j = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro hall j hj
    exact h j hj (hall j hj)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    rintro ⟨j, hj, hfj⟩
    exact ⟨j, hj, h j hj hfj⟩

-- The value of wire w of C on input x.
def val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.gates.foldl step (List.ofFn x)).getD w false

noncomputable def inp (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  match C.gates[a - n]? with
  | some g => g.inputs.toFinset
  | none => ∅

theorem input_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    val n C x w = x ⟨w, h⟩ := by
  unfold val
  rw [getD_fold_lt _ _ _ (by rw [List.length_ofFn]; exact h)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, dite_true, Option.getD_some]

theorem out_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (h : n + C.gates.length ≤ w) :
    val n C x w = false := by
  unfold val
  exact getD_fold_ge _ _ _ (by rw [List.length_ofFn]; exact h)

theorem gate_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) :
    val n C x (n + j) = g.op.eval (g.inputs.map fun b => if b < n + j then val n C x b else false) := by
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hk := lt_of_get C.gates j g hg
  have htake : (C.gates.take j).length = j := by rw [List.length_take]; omega
  unfold val
  rw [show n + j = (List.ofFn x).length + j by rw [hlen], getD_fold_gate _ _ j g hg]
  congr 1
  apply List.map_congr_left
  intro b _
  split_ifs with hb
  · have hlt : b < ((C.gates.take j).foldl step (List.ofFn x)).length := by
      rw [len_fold, htake]; exact hb
    rw [show C.gates.foldl step (List.ofFn x) =
        (C.gates.drop j).foldl step ((C.gates.take j).foldl step (List.ofFn x)) by
      rw [← List.foldl_append, List.take_append_drop]]
    rw [getD_fold_lt (C.gates.drop j) ((C.gates.take j).foldl step (List.ofFn x)) b hlt]
  · exact getD_fold_ge (C.gates.take j) (List.ofFn x) b (by rw [htake]; omega)

theorem mono_all (n : ℕ) (C : Circuit)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ (w : ℕ) (x x' : Fin n → Bool), (∀ q, x q = true → x' q = true) →
      val n C x w = true → val n C x' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro x x' hxx' hv
  by_cases hwn : w < n
  · rw [input_val n C x w hwn] at hv
    rw [input_val n C x' w hwn]
    exact hxx' _ hv
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    rcases hg : C.gates[j]? with _ | g
    · have hk : C.gates.length ≤ j := List.getElem?_eq_none_iff.1 hg
      rw [out_val n C x (n + j) (by omega)] at hv
      exact absurd hv (by simp)
    · have hmem : g ∈ C.gates := List.mem_of_getElem? hg
      rw [gate_val n C x j g hg] at hv
      rw [gate_val n C x' j g hg]
      refine eval_mono g.op (hgates g hmem).1 g.inputs _ _ ?_ hv
      intro b _ hb
      split_ifs at hb ⊢ with hbj
      all_goals first | exact ih b hbj x x' hxx' hb | exact hb



theorem union_card {n m q : ℕ} (S : Fin m → Finset (Fin n)) (hcard : ∀ i : Fin m, (S i).card = q + 1)
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) :
    ∀ V : Finset (Fin m), (V.biUnion S).card ≤ q * V.card + 1 := by
  intro V
  induction V using Finset.induction_on with
  | empty => simp
  | insert v V' hv ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hv]
    rcases V'.eq_empty_or_nonempty with h | ⟨u, hu⟩
    · subst h
      simp [hcard v]
    · have hvu : v ≠ u := fun h => hv (h ▸ hu)
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hmeet v u hvu)
      have hxm : x ∈ S v ∩ S u := by rw [hx]; exact Finset.mem_singleton_self x
      have hxv : x ∈ S v := (Finset.mem_inter.mp hxm).1
      have hxu : x ∈ S u := (Finset.mem_inter.mp hxm).2
      have hxB : x ∈ V'.biUnion S := Finset.mem_biUnion.mpr ⟨u, hu, hxu⟩
      have hsub : S v \ V'.biUnion S ⊆ (S v).erase x := by
        intro y hy
        rw [Finset.mem_sdiff] at hy
        rw [Finset.mem_erase]
        refine ⟨?_, hy.1⟩
        rintro rfl
        exact hy.2 hxB
      have hq : (S v \ V'.biUnion S).card ≤ q := by
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hxv, hcard v] at this
        simpa using this
      have hu2 : S v ∪ V'.biUnion S = V'.biUnion S ∪ (S v \ V'.biUnion S) := by
        ext y; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
      rw [hu2]
      calc (V'.biUnion S ∪ (S v \ V'.biUnion S)).card
          ≤ (V'.biUnion S).card + (S v \ V'.biUnion S).card := Finset.card_union_le _ _
        _ ≤ q * V'.card + 1 + q := Nat.add_le_add ih hq
        _ = q * (V'.card + 1) + 1 := by ring


-- The indicator input of a set of points.
def ind (n : ℕ) (A : Finset (Fin n)) : Fin n → Bool := fun p => decide (p ∈ A)

-- Wire e is true on the input that is the indicator of A.
def tw (n : ℕ) (C : Circuit) (A : Finset (Fin n)) (e : ℕ) : Prop := val n C (ind n A) e = true

-- Wire e is a gate specific to w: true on S w, false on every other S v.
def Gt {m : ℕ} (n : ℕ) (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m) (e : ℕ) : Prop :=
  tw n C (S w) e ∧ (∀ v, v ≠ w → val n C (ind n (S v)) e = false) ∧
    ∃ (j : ℕ) (g : Gate), e = n + j ∧ C.gates[j]? = some g

-- One step back from a specific gate to a wire it reads that is true on S w.
def R9 {m : ℕ} (n : ℕ) (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m) (a b : ℕ) : Prop :=
  Gt n C S w a ∧ ∃ (j : ℕ) (g : Gate), a = n + j ∧ C.gates[j]? = some g ∧ b ∈ g.inputs ∧ b < a ∧
    tw n C (S w) b

noncomputable def reach9 {m : ℕ} (n : ℕ) (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m)
    (o : ℕ) : Finset ℕ :=
  (Finset.range (o + 1)).filter (fun e => Relation.ReflTransGen (R9 n C S w) o e)

noncomputable def Q9 {m : ℕ} (n : ℕ) (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m)
    (o : ℕ) : Finset ℕ :=
  (reach9 n C S w o).filter (fun e => Gt n C S w e)

noncomputable def Ex9 {m : ℕ} (n : ℕ) (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m)
    (o : ℕ) : Finset ℕ :=
  (reach9 n C S w o).filter (fun e => ¬ Gt n C S w e)

theorem reach_le9 {m : ℕ} (n : ℕ) (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m) (o e : ℕ)
    (h : Relation.ReflTransGen (R9 n C S w) o e) : e ≤ o := by
  induction h with
  | refl => exact le_refl _
  | tail _ hab ih =>
    unfold R9 at hab
    obtain ⟨_, j, g, _, _, _, hlt, _⟩ := hab
    omega

theorem mem_reach9 {m : ℕ} (n : ℕ) (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m) (o e : ℕ) :
    e ∈ reach9 n C S w o ↔ Relation.ReflTransGen (R9 n C S w) o e := by
  unfold reach9
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by have := reach_le9 n C S w o e h; omega, h⟩

theorem reach_tw9 {m : ℕ} (n : ℕ) (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m) (o e : ℕ)
    (h : Relation.ReflTransGen (R9 n C S w) o e) (ho : tw n C (S w) o) : tw n C (S w) e := by
  induction h with
  | refl => exact ho
  | tail _ hab _ =>
    unfold R9 at hab
    obtain ⟨_, j, g, _, _, _, _, hb⟩ := hab
    exact hb

-- If every exit is true at x, every reached wire is true at x.
theorem all_true9 {m : ℕ} (n : ℕ) (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m) (o : ℕ)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) (hall : ∀ e ∈ Ex9 n C S w o, val n C x e = true) :
    ∀ e, Relation.ReflTransGen (R9 n C S w) o e → val n C x e = true := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro he
  by_cases hG : Gt n C S w e
  · have hG' := hG
    obtain ⟨htw, _, j, g, rfl, hg⟩ := hG'
    have hmem : g ∈ C.gates := List.mem_of_getElem? hg
    have hchild : ∀ b ∈ g.inputs, (if b < n + j then val n C (ind n (S w)) b else false) = true →
        (if b < n + j then val n C x b else false) = true := by
      intro b hb hbt
      split_ifs at hbt ⊢ with hbj
      all_goals first
        | exact ih b hbj (he.tail (show R9 n C S w (n + j) b from ⟨hG, j, g, rfl, hg, hb, hbj, hbt⟩))
        | exact hbt
    unfold tw at htw
    rw [gate_val n C _ j g hg] at htw
    rw [gate_val n C x j g hg]
    rcases (hgates g hmem).1 with hop | hop
    · rw [hop] at htw ⊢
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] at htw ⊢
      intro b hb
      exact hchild b hb (htw b hb)
    · rw [hop] at htw ⊢
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and] at htw ⊢
      obtain ⟨b, hb, hbt⟩ := htw
      exact ⟨b, hb, hchild b hb hbt⟩
  · exact hall e (by unfold Ex9; rw [Finset.mem_filter, mem_reach9]; exact ⟨he, hG⟩)

-- At most one more exit than specific gates reached.
theorem count9 {m : ℕ} (n : ℕ) (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m) (o : ℕ)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    (Ex9 n C S w o).card ≤ (Q9 n C S w o).card + 1 := by
  have hsub : (reach9 n C S w o).erase o ⊆ (Q9 n C S w o).biUnion (inp n C) := by
    intro e he
    rw [Finset.mem_erase] at he
    obtain ⟨heo, her⟩ := he
    rw [mem_reach9] at her
    rcases Relation.ReflTransGen.cases_tail her with h | ⟨a, hra, hab⟩
    · exact absurd h heo
    · rw [Finset.mem_biUnion]
      have hab' := hab
      unfold R9 at hab'
      obtain ⟨hga, j, g, rfl, hg, hb, _, _⟩ := hab'
      refine ⟨n + j, ?_, ?_⟩
      · unfold Q9
        rw [Finset.mem_filter, mem_reach9]
        exact ⟨hra, hga⟩
      · unfold inp
        rw [show n + j - n = j by omega, hg]
        exact List.mem_toFinset.2 hb
  have h1 := Finset.card_le_card hsub
  have h2 : ((Q9 n C S w o).biUnion (inp n C)).card ≤ ∑ a ∈ Q9 n C S w o, (inp n C a).card :=
    Finset.card_biUnion_le
  have h3 : ∀ a ∈ Q9 n C S w o, (inp n C a).card ≤ 2 := by
    intro a _
    unfold inp
    split
    · next g hg =>
      have hmem : g ∈ C.gates := List.mem_of_getElem? hg
      calc g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le _
        _ ≤ 2 := (hgates g hmem).2
    · simp
  have h4 : ∑ a ∈ Q9 n C S w o, (inp n C a).card ≤ ∑ _a ∈ Q9 n C S w o, 2 := Finset.sum_le_sum h3
  rw [Finset.sum_const, smul_eq_mul] at h4
  have hoR : o ∈ reach9 n C S w o := (mem_reach9 n C S w o o).2 Relation.ReflTransGen.refl
  have h5 := Finset.card_erase_of_mem hoR
  have h6 : (Q9 n C S w o).card + (Ex9 n C S w o).card = (reach9 n C S w o).card :=
    Finset.card_filter_add_card_filter_not _
  have h7 : 1 ≤ (reach9 n C S w o).card := Finset.card_pos.2 ⟨o, hoR⟩
  omega

theorem ind_weight (n : ℕ) (A : Finset (Fin n)) :
    (Finset.univ.filter (fun i => ind n A i = true)).card = A.card := by
  congr 1
  ext i
  simp [ind]

-- The bound for one output: at least c gates specific to w are reached from its output wire.
theorem single9 {m : ℕ} (q n K c : ℕ) (C : Circuit) (S : Fin m → Finset (Fin n)) (w : Fin m) (o : ℕ)
    (hq : 2 ≤ q) (hcard : ∀ i, (S i).card = q + 1) (hmeet : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorr : ∀ x : Fin n → Bool, (Finset.univ.filter (fun i => x i = true)).card ≤ K →
      val n C x o = decide (∀ v ∈ S w, x v = true))
    (hcq : c ≤ q) (hK : c * q < K) : c ≤ (Q9 n C S w o).card := by
  by_contra hlt
  push Not at hlt
  have hcount := count9 n C S w o hgates
  have hc1 : 1 ≤ c := by omega
  have hqK : q + 1 ≤ K := by
    have := Nat.le_mul_of_pos_left q hc1
    omega
  have hotw : tw n C (S w) o := by
    unfold tw
    rw [hcorr _ (by rw [ind_weight, hcard]; exact hqK)]
    simp [ind]
  have hexit : ∀ e ∈ Ex9 n C S w o, ¬ e < n → ∃ v, v ≠ w ∧ val n C (ind n (S v)) e = true := by
    intro e he hen
    unfold Ex9 at he
    rw [Finset.mem_filter, mem_reach9] at he
    obtain ⟨hr, hnG⟩ := he
    have htw := reach_tw9 n C S w o e hr hotw
    by_cases hgate : ∃ (j : ℕ) (g : Gate), e = n + j ∧ C.gates[j]? = some g
    · by_contra hno
      push Not at hno
      apply hnG
      refine ⟨htw, fun v hv => ?_, hgate⟩
      have h := hno v hv
      simpa using h
    · exfalso
      have hge : n + C.gates.length ≤ e := by
        by_contra hlt2
        apply hgate
        exact ⟨e - n, C.gates[e - n]'(by omega), by omega, List.getElem?_eq_getElem (by omega)⟩
      unfold tw at htw
      rw [out_val n C _ e hge] at htw
      exact absurd htw (by simp)
  have : Nonempty (Fin m) := ⟨w⟩
  choose! vp hvp using hexit
  -- the input: the input exits, and for each other exit a set S v it is true on
  have hallx : ∀ e ∈ Ex9 n C S w o, val n C (ind n
      ((Finset.univ.filter (fun p : Fin n => (p : ℕ) ∈ Ex9 n C S w o)) ∪
        (((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp).biUnion S)) e = true := by
    intro e he
    by_cases hen : e < n
    · rw [input_val n C _ e hen]
      simp only [ind, decide_eq_true_eq]
      exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩)
    · obtain ⟨_, hv⟩ := hvp e he hen
      refine mono_all n C hgates e (ind n (S (vp e))) _ ?_ hv
      intro p hp
      simp only [ind, decide_eq_true_eq] at hp ⊢
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.2 ⟨vp e, Finset.mem_image_of_mem vp (Finset.mem_filter.2 ⟨he, hen⟩), hp⟩
  have hout := all_true9 n C S w o hgates _ hallx o Relation.ReflTransGen.refl
  -- sizes
  have hEx : ((Ex9 n C S w o).filter (fun e => e < n)).card +
      ((Ex9 n C S w o).filter (fun e => ¬ e < n)).card = (Ex9 n C S w o).card :=
    Finset.card_filter_add_card_filter_not _
  have hPin : (Finset.univ.filter (fun p : Fin n => (p : ℕ) ∈ Ex9 n C S w o)).card ≤
      ((Ex9 n C S w o).filter (fun e => e < n)).card := by
    apply Finset.card_le_card_of_injOn (fun p : Fin n => (p : ℕ))
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨hp, p.isLt⟩
    · intro a _ b _ h
      exact Fin.ext h
  have himg : (((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp).card ≤
      ((Ex9 n C S w o).filter (fun e => ¬ e < n)).card := Finset.card_image_le
  have hPg := union_card S hcard hmeet (((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp)
  have hP := Finset.card_union_le (Finset.univ.filter (fun p : Fin n => (p : ℕ) ∈ Ex9 n C S w o))
    ((((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp).biUnion S)
  have hmul : q * (((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp).card ≤
      q * ((Ex9 n C S w o).filter (fun e => ¬ e < n)).card := Nat.mul_le_mul_left q himg
  -- the part of the input inside S w
  have hPS : ((Finset.univ.filter (fun p : Fin n => (p : ℕ) ∈ Ex9 n C S w o)) ∪
        (((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp).biUnion S) ∩ S w ⊆
      (Finset.univ.filter (fun p : Fin n => (p : ℕ) ∈ Ex9 n C S w o)) ∪
        (((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp).biUnion (fun v => S v ∩ S w) := by
    intro p hp
    rw [Finset.mem_inter, Finset.mem_union] at hp
    rcases hp with ⟨h1 | h1, h2⟩
    · exact Finset.mem_union_left _ h1
    · apply Finset.mem_union_right
      obtain ⟨v, hv, hpv⟩ := Finset.mem_biUnion.1 h1
      exact Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_inter.2 ⟨hpv, h2⟩⟩
  have hsum : ∀ v ∈ ((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp, (S v ∩ S w).card ≤ 1 := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hv
    rw [Finset.mem_filter] at he
    rw [hmeet (vp e) w (hvp e he.1 he.2).1]
  have hB : ((((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp).biUnion (fun v => S v ∩ S w)).card ≤
      (((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp).card := by
    calc _ ≤ ∑ v ∈ ((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp, (S v ∩ S w).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ ((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp, 1 := Finset.sum_le_sum hsum
      _ = _ := by simp
  have hPS2 := Finset.card_le_card hPS
  have hPS3 := Finset.card_union_le (Finset.univ.filter (fun p : Fin n => (p : ℕ) ∈ Ex9 n C S w o))
    ((((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp).biUnion (fun v => S v ∩ S w))
  -- S w is not inside the input: too few of its points
  have hnot : ¬ (S w ⊆ (Finset.univ.filter (fun p : Fin n => (p : ℕ) ∈ Ex9 n C S w o)) ∪
        (((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp).biUnion S) := by
    intro hsub
    rw [Finset.inter_eq_right.2 hsub, hcard] at hPS2
    omega
  -- the input is light
  have hlight : (Finset.univ.filter (fun i => ind n
      ((Finset.univ.filter (fun p : Fin n => (p : ℕ) ∈ Ex9 n C S w o)) ∪
        (((Ex9 n C S w o).filter (fun e => ¬ e < n)).image vp).biUnion S) i = true)).card ≤ K := by
    rw [ind_weight]
    have hq1 : ((Ex9 n C S w o).filter (fun e => e < n)).card ≤
        q * ((Ex9 n C S w o).filter (fun e => e < n)).card := Nat.le_mul_of_pos_left _ (by omega)
    have hqc : q * (((Ex9 n C S w o).filter (fun e => e < n)).card +
        ((Ex9 n C S w o).filter (fun e => ¬ e < n)).card) ≤ q * c := Nat.mul_le_mul_left q (by omega)
    rw [Nat.mul_add] at hqc
    have hcomm : c * q = q * c := Nat.mul_comm c q
    omega
  rw [hcorr _ hlight] at hout
  apply hnot
  intro p hp
  have h := of_decide_eq_true hout p hp
  simpa [ind] using h

end PEqualNP.Outside.L_meta_925

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_925 in
theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hcard hmeet gates out hgates hcorr c hcq hK
  rcases Nat.eq_zero_or_pos c with hc0 | hc0
  · subst hc0
    simp
  have hQ : ∀ w, c ≤ (Q9 n ⟨gates, 0⟩ S w (out w)).card := fun w =>
    single9 q n K c ⟨gates, 0⟩ S w (out w) hq hcard hmeet hgates (fun x hx => hcorr w x hx) hcq hK
  have hQsub : ∀ w, Q9 n ⟨gates, 0⟩ S w (out w) ⊆ Finset.Ico n (n + gates.length) := by
    intro w e he
    unfold Q9 at he
    obtain ⟨_, _, j, g, rfl, hg⟩ := (Finset.mem_filter.1 he).2
    have := lt_of_get gates j g hg
    simp only [Finset.mem_Ico]
    omega
  have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun w => Q9 n ⟨gates, 0⟩ S w (out w)) := by
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e hei hej
    unfold Q9 at hei hej
    have hgi := (Finset.mem_filter.1 hei).2
    have hgj := (Finset.mem_filter.1 hej).2
    have h1 := hgi.2.1 j (Ne.symm hij)
    have h2 := hgj.1
    unfold tw at h2
    rw [h1] at h2
    exact absurd h2 (by simp)
  calc m * c = ∑ _w : Fin m, c := by simp
    _ ≤ ∑ w, (Q9 n ⟨gates, 0⟩ S w (out w)).card := Finset.sum_le_sum (fun w _ => hQ w)
    _ = (Finset.univ.biUnion (fun w => Q9 n ⟨gates, 0⟩ S w (out w))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + gates.length)).card :=
        Finset.card_le_card (Finset.biUnion_subset.2 (fun w _ => hQsub w))
    _ = gates.length := by simp

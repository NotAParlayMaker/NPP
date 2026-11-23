import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1042

open PEqualNP.CircuitLowerBounds

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def val (gl : List Gate) (x : Fin 6 → Bool) (w : ℕ) : Bool :=
  (Circuit.wires ⟨gl, 0⟩ (List.ofFn x)).getD w false

private lemma eval_eq_val (gl : List Gate) (o : ℕ) (x : Fin 6 → Bool) :
    Circuit.eval ⟨gl, o⟩ (List.ofFn x) = val gl x o :=
  rfl

private lemma val_input (gl : List Gate) (x : Fin 6 → Bool) (p : Fin 6) :
    val gl x p.val = x p := by
  change (run gl (List.ofFn x)).getD p.val false = x p
  have hp : p.val < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp, List.getElem_ofFn]

private lemma val_missing (gl : List Gate) (x : Fin 6 → Bool) (w : ℕ) (hw : 6 + gl.length ≤ w) :
    val gl x w = false := by
  change (run gl (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length] using hw)

private lemma val_gate (gl : List Gate) (x : Fin 6 → Bool) (w : ℕ)
    (h6 : 6 ≤ w) (hw : w < 6 + gl.length) :
    val gl x w = (gl[w - 6]'(by omega)).op.eval
      ((gl[w - 6]'(by omega)).inputs.map fun r => if r < w then val gl x r else false) := by
  let j := w - 6
  have hj : j < gl.length := by omega
  let g := gl[j]
  let earlier := run (gl.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run gl (List.ofFn x) = run (g :: gl.drop (j + 1)) earlier := by
    rw [run_split gl (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then val gl x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run gl (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run gl (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then val gl x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

private def replConst (gl : List Gate) (i0 : ℕ) (b : Bool) : List Gate :=
  gl.set i0 (if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩)

private lemma replConst_length (gl : List Gate) (i0 : ℕ) (b : Bool) :
    (replConst gl i0 b).length = gl.length := by
  simp [replConst]

private lemma replConst_mono (gl : List Gate) (i0 : Fin gl.length) (b : Bool)
    (hG : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gl.length, (gl.get q).op = GateOp.not → q = i0) :
    ∀ g ∈ replConst gl i0.val b, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gl.length := by simpa [replConst] using hk
  by_cases hki : i0.val = k
  · cases b <;> simp [replConst, hki]
  · have e : (replConst gl i0.val b)[k] = gl[k] := by simp [replConst, hki]
    rw [e]
    obtain ⟨hop, hlen⟩ := hG gl[k] (List.getElem_mem _)
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (hnot ⟨k, hk'⟩ hop)).symm hki

private lemma replConst_val (gl : List Gate) (i0 : Fin gl.length) (b : Bool)
    (hconst : ∀ x : Fin 6 → Bool, val gl x (6 + i0.val) = b)
    (x : Fin 6 → Bool) (w : ℕ) :
    val (replConst gl i0.val b) x w = val gl x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h6 : w < 6
    · have h1 := val_input (replConst gl i0.val b) x ⟨w, h6⟩
      have h2 := val_input gl x ⟨w, h6⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < 6 + gl.length
    · by_cases hne : w = 6 + i0.val
      · rw [hne, val_gate (replConst gl i0.val b) x (6 + i0.val) (by omega)
          (by rw [replConst_length]; omega), hconst x]
        have e : (replConst gl i0.val b)[6 + i0.val - 6]'(by rw [replConst_length]; omega) =
            if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩ := by
          simp [replConst]
        rw [e]
        cases b <;> rfl
      · rw [val_gate (replConst gl i0.val b) x w (by omega) (by rw [replConst_length]; exact hw),
          val_gate gl x w (by omega) hw]
        have e : (replConst gl i0.val b)[w - 6]'(by rw [replConst_length]; omega) =
            gl[w - 6]'(by omega) := by
          simp only [replConst, List.getElem_set]
          rw [ite_eq_right (by omega)]
        rw [e]
        congr 1
        refine List.map_congr_left fun r _ => ?_
        by_cases hr : r < w
        · simp [hr, ih r hr]
        · simp [hr]
    · rw [val_missing (replConst gl i0.val b) x w (by rw [replConst_length]; omega),
        val_missing gl x w (by omega)]

private lemma val_mono_lt (gl : List Gate) (i0 : Fin gl.length)
    (hG : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gl.length, (gl.get q).op = GateOp.not → q = i0)
    (x y : Fin 6 → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) (hw : w < 6 + i0.val) :
    val gl x w = true → val gl y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h6 : w < 6
    · have h1 := val_input gl x ⟨w, h6⟩
      have h2 := val_input gl y ⟨w, h6⟩
      simp only at h1 h2
      rw [h1, h2]
      exact hxy ⟨w, h6⟩
    · have hlt : w < 6 + gl.length := by have := i0.isLt; omega
      rw [val_gate gl x w (by omega) hlt, val_gate gl y w (by omega) hlt]
      have hop : (gl[w - 6]'(by omega)).op = GateOp.and ∨ (gl[w - 6]'(by omega)).op = GateOp.or := by
        rcases (hG (gl[w - 6]'(by omega)) (List.getElem_mem _)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have := congrArg Fin.val (hnot ⟨w - 6, by omega⟩ h)
          simp only at this
          omega
      rcases hop with hop | hop
      · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
        intro hx r hr
        by_cases hrw : r < w
        · simpa [hrw] using ih r hrw (by omega) (by simpa [hrw] using hx r hr)
        · have := hx r hr
          simp [hrw] at this
      · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
        rintro ⟨r, hr, hxv⟩
        refine ⟨r, hr, ?_⟩
        by_cases hrw : r < w
        · simpa [hrw] using ih r hrw (by omega) (by simpa [hrw] using hxv)
        · simp [hrw] at hxv

private lemma not_const_or_anti (gl : List Gate) (i0 : Fin gl.length)
    (hG : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gl.length, (gl.get q).op = GateOp.not → q = i0)
    (hi0 : (gl.get i0).op = GateOp.not) :
    (∃ b : Bool, ∀ x : Fin 6 → Bool, val gl x (6 + i0.val) = b) ∨
    (val gl (fun _ => false) (6 + i0.val) = true ∧ val gl (fun _ => true) (6 + i0.val) = false) := by
  have hval : ∀ x : Fin 6 → Bool,
      val gl x (6 + i0.val) = !((gl[i0.val].inputs.map fun r => if r < 6 + i0.val then val gl x r else false).headD false) := by
    intro x
    rw [val_gate gl x (6 + i0.val) (by omega) (by have := i0.isLt; omega)]
    have e : gl[6 + i0.val - 6]'(by have := i0.isLt; omega) = gl.get i0 := by simp
    have e2 : gl[i0.val] = gl.get i0 := by simp
    rw [e, e2, hi0]
    rfl
  cases hin : gl[i0.val].inputs with
  | nil =>
    left
    refine ⟨true, fun x => ?_⟩
    rw [hval x, hin]
    rfl
  | cons hw rest =>
    by_cases hlt : hw < 6 + i0.val
    · have hv : ∀ x, val gl x (6 + i0.val) = !(val gl x hw) := by
        intro x
        rw [hval x, hin]
        simp [hlt]
      cases h0 : val gl (fun _ => false) hw with
      | true =>
        left
        refine ⟨false, fun x => ?_⟩
        rw [hv x, val_mono_lt gl i0 hG hnot (fun _ => false) x (by intro p hp; simp at hp) hw hlt h0]
        rfl
      | false =>
        cases h1 : val gl (fun _ => true) hw with
        | false =>
          left
          refine ⟨true, fun x => ?_⟩
          have hx : val gl x hw = false := by
            cases hxv : val gl x hw with
            | false => rfl
            | true =>
              have := val_mono_lt gl i0 hG hnot x (fun _ => true) (by intro p _; rfl) hw hlt hxv
              rw [h1] at this
              exact Bool.noConfusion this
          rw [hv x, hx]
          rfl
        | true =>
          right
          rw [hv, hv, h0, h1]
          exact ⟨rfl, rfl⟩
    · left
      refine ⟨true, fun x => ?_⟩
      rw [hval x, hin]
      simp [hlt]

private def pasch : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}]

private lemma pasch_inter : ∀ i j : Fin 4, i ≠ j → (pasch i ∩ pasch j).card ≤ 1 := by
  decide

private lemma pasch_sum : ∑ w : Fin 4, ((pasch w).card - 1) = 8 := by
  decide

private lemma pasch_card : ∀ a : Fin 4, (pasch a).card = 3 := by
  decide

private lemma pasch_diff : ∀ a b : Fin 4, a ≠ b → ∃ p : Fin 6, p ∈ pasch a ∧ p ∉ pasch b := by
  decide

private def eVec (p : Fin 6) : Fin 6 → Bool :=
  fun q => decide (q = p)

private lemma pasch_eval_eVec (a : Fin 4) (p : Fin 6) :
    decide (∃ v ∈ pasch a, eVec p v = true) = decide (p ∈ pasch a) := by
  rw [decide_eq_decide]
  constructor
  · rintro ⟨v, hv, he⟩
    have : v = p := of_decide_eq_true he
    rwa [← this]
  · intro hp
    exact ⟨p, hp, by simp [eVec]⟩

private lemma pasch_eval_false (a : Fin 4) :
    decide (∃ v ∈ pasch a, (fun _ : Fin 6 => false) v = true) = false := by
  simp

private lemma pasch_eval_true (a : Fin 4) :
    decide (∃ v ∈ pasch a, (fun _ : Fin 6 => true) v = true) = true := by
  have hc := pasch_card a
  have hne : (pasch a).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hne
  exact decide_eq_true ⟨p, hp, rfl⟩

private def supp1 (gl : List Gate) (w : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter fun p => val gl (eVec p) w = true

private lemma mem_supp1 (gl : List Gate) (w : ℕ) (p : Fin 6) :
    p ∈ supp1 gl w ↔ val gl (eVec p) w = true := by
  simp [supp1]

private lemma supp1_input_card (gl : List Gate) (w : ℕ) (hw : w < 6) :
    (supp1 gl w).card ≤ 1 := by
  let p0 : Fin 6 := ⟨w, hw⟩
  have hsub : supp1 gl w ⊆ {p0} := by
    intro p hp
    have hv := (mem_supp1 gl w p).mp hp
    have hi := val_input gl (eVec p) p0
    simp only [p0] at hi
    rw [hi] at hv
    have heq : p0 = p := of_decide_eq_true hv
    simp [heq]
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma or_gate_inputs (gl : List Gate) (z : ℕ) (w : ℕ) (a : Fin 4)
    (h6 : 6 ≤ w) (hw : w < 6 + gl.length)
    (hop : (gl[w - 6]'(by omega)).op = GateOp.or)
    (hlen : (gl[w - 6]'(by omega)).inputs.length ≤ 2)
    (heval : ∀ x, val gl x w = decide (∃ v ∈ pasch a, x v = true))
    (hmin : ∀ u < w, ¬ ∀ x, val gl x u = decide (∃ v ∈ pasch a, x v = true))
    (hz0 : val gl (fun _ => false) z = true) :
    ∃ h : ℕ, 6 ≤ h ∧ h < w ∧ h ≠ z ∧ supp1 gl h ⊆ pasch a ∧ 2 ≤ (supp1 gl h).card := by
  have hgv : ∀ x, val gl x w =
      ((gl[w - 6]'(by omega)).inputs.map fun r => if r < w then val gl x r else false).any id := by
    intro x
    rw [val_gate gl x w h6 hw, hop]
    rfl
  cases hins : (gl[w - 6]'(by omega)).inputs with
  | nil =>
    have h1 := heval (fun _ => true)
    rw [hgv, hins, pasch_eval_true] at h1
    simp at h1
  | cons u rest =>
    cases rest with
    | nil =>
      by_cases hu : u < w
      · exfalso
        apply hmin u hu
        intro x
        have hx := heval x
        rw [hgv x, hins] at hx
        simpa [hu] using hx
      · have h1 := heval (fun _ => true)
        rw [hgv, hins] at h1
        rw [pasch_eval_true] at h1
        simp [hu] at h1
    | cons v rest2 =>
      cases rest2 with
      | cons _ _ =>
        rw [hins] at hlen
        simp at hlen
      | nil =>
        have huv : ∀ x, ((if u < w then val gl x u else false) ||
            (if v < w then val gl x v else false)) = decide (∃ p ∈ pasch a, x p = true) := by
          intro x
          have hx := heval x
          rw [hgv x, hins] at hx
          simpa using hx
        have hu : u < w := by
          by_contra hu
          by_cases hv : v < w
          · apply hmin v hv
            intro x
            simpa [hu, hv] using huv x
          · have h1 := huv (fun _ => true)
            rw [pasch_eval_true] at h1
            simp [hu, hv] at h1
        have hv : v < w := by
          by_contra hv
          apply hmin u hu
          intro x
          simpa [hu, hv] using huv x
        have hor : ∀ x, (val gl x u || val gl x v) = decide (∃ p ∈ pasch a, x p = true) := by
          intro x
          simpa [hu, hv] using huv x
        have hsub_u : supp1 gl u ⊆ pasch a := by
          intro p hp
          have h1 := (mem_supp1 gl u p).mp hp
          have h2 := hor (eVec p)
          rw [h1, Bool.true_or, pasch_eval_eVec] at h2
          exact of_decide_eq_true h2.symm
        have hsub_v : supp1 gl v ⊆ pasch a := by
          intro p hp
          have h1 := (mem_supp1 gl v p).mp hp
          have h2 := hor (eVec p)
          rw [h1, Bool.or_true, pasch_eval_eVec] at h2
          exact of_decide_eq_true h2.symm
        have hcov : pasch a ⊆ supp1 gl u ∪ supp1 gl v := by
          intro p hp
          have h2 := hor (eVec p)
          rw [pasch_eval_eVec, decide_eq_true hp] at h2
          rcases Bool.or_eq_true_iff.mp h2 with h1 | h1
          · exact Finset.mem_union_left _ ((mem_supp1 gl u p).mpr h1)
          · exact Finset.mem_union_right _ ((mem_supp1 gl v p).mpr h1)
        have hcard3 : 3 ≤ (supp1 gl u).card + (supp1 gl v).card := by
          have h1 := Finset.card_le_card hcov
          have h2 := Finset.card_union_le (supp1 gl u) (supp1 gl v)
          rw [pasch_card a] at h1
          omega
        have h0 : val gl (fun _ => false) u = false ∧ val gl (fun _ => false) v = false := by
          have h2 := hor (fun _ => false)
          rw [pasch_eval_false] at h2
          exact Bool.or_eq_false_iff.mp h2
        by_cases hcu : 2 ≤ (supp1 gl u).card
        · refine ⟨u, ?_, hu, ?_, hsub_u, hcu⟩
          · by_contra hlt6
            have := supp1_input_card gl u (by omega)
            omega
          · intro heq
            rw [heq, hz0] at h0
            exact Bool.noConfusion h0.1
        · refine ⟨v, ?_, hv, ?_, hsub_v, by omega⟩
          · by_contra hlt6
            have := supp1_input_card gl v (by omega)
            omega
          · intro heq
            rw [heq, hz0] at h0
            exact Bool.noConfusion h0.2

private lemma and_gate_inputs (gl : List Gate) (z : ℕ) (w : ℕ) (a : Fin 4)
    (h6 : 6 ≤ w) (hw : w < 6 + gl.length)
    (hop : (gl[w - 6]'(by omega)).op = GateOp.and)
    (hlen : (gl[w - 6]'(by omega)).inputs.length ≤ 2)
    (heval : ∀ x, val gl x w = decide (∃ v ∈ pasch a, x v = true))
    (hmin : ∀ u < w, ¬ ∀ x, val gl x u = decide (∃ v ∈ pasch a, x v = true))
    (hz1 : val gl (fun _ => true) z = false) :
    ∃ u v : ℕ, 6 ≤ u ∧ u < w ∧ u ≠ z ∧ 6 ≤ v ∧ v < w ∧ v ≠ z ∧ u ≠ v ∧
      pasch a ⊆ supp1 gl u ∧ pasch a ⊆ supp1 gl v ∧
      ∀ x, val gl x w = (val gl x u && val gl x v) := by
  have hgv : ∀ x, val gl x w =
      ((gl[w - 6]'(by omega)).inputs.map fun r => if r < w then val gl x r else false).all id := by
    intro x
    rw [val_gate gl x w h6 hw, hop]
    rfl
  cases hins : (gl[w - 6]'(by omega)).inputs with
  | nil =>
    have h0 := heval (fun _ => false)
    rw [hgv, hins, pasch_eval_false] at h0
    simp at h0
  | cons u rest =>
    cases rest with
    | nil =>
      by_cases hu : u < w
      · exfalso
        apply hmin u hu
        intro x
        have hx := heval x
        rw [hgv x, hins] at hx
        simpa [hu] using hx
      · have h1 := heval (fun _ => true)
        rw [hgv, hins, pasch_eval_true] at h1
        simp [hu] at h1
    | cons v rest2 =>
      cases rest2 with
      | cons _ _ =>
        rw [hins] at hlen
        simp at hlen
      | nil =>
        have huv : ∀ x, ((if u < w then val gl x u else false) &&
            (if v < w then val gl x v else false)) = decide (∃ p ∈ pasch a, x p = true) := by
          intro x
          have hx := heval x
          rw [hgv x, hins] at hx
          simpa using hx
        have hu : u < w := by
          by_contra hu
          have h1 := huv (fun _ => true)
          rw [pasch_eval_true] at h1
          simp [hu] at h1
        have hv : v < w := by
          by_contra hv
          have h1 := huv (fun _ => true)
          rw [pasch_eval_true] at h1
          simp [hv] at h1
        have hand : ∀ x, (val gl x u && val gl x v) = decide (∃ p ∈ pasch a, x p = true) := by
          intro x
          simpa [hu, hv] using huv x
        have hne : u ≠ v := by
          intro heq
          apply hmin u hu
          intro x
          have hx := hand x
          rw [← heq, Bool.and_self] at hx
          exact hx
        have hsup_u : pasch a ⊆ supp1 gl u := by
          intro p hp
          have h2 := hand (eVec p)
          rw [pasch_eval_eVec, decide_eq_true hp] at h2
          exact (mem_supp1 gl u p).mpr (Bool.and_eq_true_iff.mp h2).1
        have hsup_v : pasch a ⊆ supp1 gl v := by
          intro p hp
          have h2 := hand (eVec p)
          rw [pasch_eval_eVec, decide_eq_true hp] at h2
          exact (mem_supp1 gl v p).mpr (Bool.and_eq_true_iff.mp h2).2
        have h1 : val gl (fun _ => true) u = true ∧ val gl (fun _ => true) v = true := by
          have h2 := hand (fun _ => true)
          rw [pasch_eval_true] at h2
          exact Bool.and_eq_true_iff.mp h2
        have hu6 : 6 ≤ u := by
          by_contra hlt6
          have c1 := Finset.card_le_card hsup_u
          have c2 := supp1_input_card gl u (by omega)
          rw [pasch_card a] at c1
          omega
        have hv6 : 6 ≤ v := by
          by_contra hlt6
          have c1 := Finset.card_le_card hsup_v
          have c2 := supp1_input_card gl v (by omega)
          rw [pasch_card a] at c1
          omega
        have huz : u ≠ z := by
          intro heq
          rw [heq, hz1] at h1
          exact Bool.noConfusion h1.1
        have hvz : v ≠ z := by
          intro heq
          rw [heq, hz1] at h1
          exact Bool.noConfusion h1.2
        refine ⟨u, v, hu6, hu, huz, hv6, hv, hvz, hne, hsup_u, hsup_v, ?_⟩
        intro x
        rw [heval x, hand x]

private lemma main_bound
    (hMono : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length)
    (gl : List Gate) (ol : Fin 4 → ℕ)
    (hG : ∀ gg ∈ gl, (gg.op = GateOp.and ∨ gg.op = GateOp.or ∨ gg.op = GateOp.not) ∧ gg.inputs.length ≤ 2)
    (hι : ∃ ι : Fin 1 → Fin gl.length, ∀ qa : Fin gl.length, (gl.get qa).op = GateOp.not → ∃ ka : Fin 1, ι ka = qa)
    (hol : ∀ (oa : Fin 4) (xa : Fin 6 → Bool), Circuit.eval ⟨gl, ol oa⟩ (List.ofFn xa) = decide (∃ va ∈ pasch oa, xa va = true)) :
    8 ≤ gl.length := by
  classical
  obtain ⟨ι, hι⟩ := hι
  let i0 : Fin gl.length := ι 0
  have hnot : ∀ q : Fin gl.length, (gl.get q).op = GateOp.not → q = i0 := by
    intro q hq
    obtain ⟨k, hk⟩ := hι q hq
    rw [Fin.eq_zero k] at hk
    exact hk.symm
  by_cases hi0 : (gl.get i0).op = GateOp.not
  · rcases not_const_or_anti gl i0 hG hnot hi0 with ⟨b, hconst⟩ | ⟨hz0, hz1⟩
    · have h8 := hMono 6 4 pasch pasch_inter (replConst gl i0.val b) ol
        (replConst_mono gl i0 b hG hnot) (fun oa xa => by
          rw [eval_eq_val, replConst_val gl i0 b hconst xa (ol oa)]
          exact hol oa xa)
      rw [pasch_sum, replConst_length] at h8
      exact h8
    · by_contra hlt8
      have hlen7 : gl.length ≤ 7 := by omega
      let z : ℕ := 6 + i0.val
      have hex : ∀ a : Fin 4, ∃ w : ℕ, ∀ x : Fin 6 → Bool, val gl x w = decide (∃ v ∈ pasch a, x v = true) :=
        fun a => ⟨ol a, fun x => hol a x⟩
      let first : Fin 4 → ℕ := fun a => Nat.find (hex a)
      have hfirst_eval : ∀ a x, val gl x (first a) = decide (∃ v ∈ pasch a, x v = true) :=
        fun a => Nat.find_spec (hex a)
      have hfirst_min : ∀ a u, u < first a → ¬ ∀ x, val gl x u = decide (∃ v ∈ pasch a, x v = true) :=
        fun a u hu => Nat.find_min (hex a) hu
      have hfirst_supp : ∀ a, supp1 gl (first a) = pasch a := by
        intro a
        ext p
        rw [mem_supp1, hfirst_eval, pasch_eval_eVec, decide_eq_true_iff]
      have hfirst_ge6 : ∀ a, 6 ≤ first a := by
        intro a
        by_contra hlt6
        have c1 := supp1_input_card gl (first a) (by omega)
        rw [hfirst_supp a, pasch_card a] at c1
        omega
      have hfirst_lt : ∀ a, first a < 6 + gl.length := by
        intro a
        by_contra hge
        have h1 := hfirst_eval a (fun _ => true)
        rw [val_missing gl _ _ (by omega), pasch_eval_true] at h1
        exact Bool.noConfusion h1
      have hfirst_nez : ∀ a, first a ≠ z := by
        intro a heq
        have h0 := hfirst_eval a (fun _ => false)
        rw [heq, hz0, pasch_eval_false] at h0
        exact Bool.noConfusion h0
      have hfirst_inj : Function.Injective first := by
        intro a b hab
        by_contra hne
        obtain ⟨p, hpa, hpb⟩ := pasch_diff a b hne
        have ha := hfirst_eval a (eVec p)
        have hb := hfirst_eval b (eVec p)
        rw [hab] at ha
        rw [ha, pasch_eval_eVec, pasch_eval_eVec] at hb
        rw [decide_eq_true hpa, decide_eq_false hpb] at hb
        exact Bool.noConfusion hb
      let W : Finset ℕ := (Finset.Ico 6 (6 + gl.length)).erase z
      let O : Finset ℕ := Finset.univ.image first
      let E : Finset ℕ := W \ O
      have hOW : O ⊆ W := by
        intro w hw
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
        exact Finset.mem_erase.mpr ⟨hfirst_nez a, Finset.mem_Ico.mpr ⟨hfirst_ge6 a, hfirst_lt a⟩⟩
      have hOcard : O.card = 4 := by
        rw [Finset.card_image_of_injective _ hfirst_inj]
        simp
      have hWcard : W.card = gl.length - 1 := by
        have hzmem : z ∈ Finset.Ico 6 (6 + gl.length) := Finset.mem_Ico.mpr ⟨by omega, by have := i0.isLt; omega⟩
        rw [Finset.card_erase_of_mem hzmem]
        simp
      have hEcard : E.card ≤ 2 := by
        have h := Finset.card_sdiff_add_card_eq_card hOW
        change E.card + O.card = W.card at h
        omega
      have hgate_op : ∀ a : Fin 4,
          (gl[first a - 6]'(by have := hfirst_ge6 a; have := hfirst_lt a; omega)).op = GateOp.and ∨
          (gl[first a - 6]'(by have := hfirst_ge6 a; have := hfirst_lt a; omega)).op = GateOp.or := by
        intro a
        have hlt := hfirst_lt a
        have hge := hfirst_ge6 a
        rcases (hG (gl[first a - 6]'(by omega)) (List.getElem_mem _)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have := congrArg Fin.val (hnot ⟨first a - 6, by omega⟩ h)
          simp only at this
          exact absurd (by omega : first a = z) (hfirst_nez a)
      have hmemE_of_sub : ∀ (a : Fin 4) (h : ℕ), 6 ≤ h → h < first a → h ≠ z →
          supp1 gl h ⊆ pasch a → 2 ≤ (supp1 gl h).card → h ∈ E := by
        intro a h h6 hlt hnez hsub hcard
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hnez, Finset.mem_Ico.mpr ⟨h6, by have := hfirst_lt a; omega⟩⟩, ?_⟩
        intro hmemO
        obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hmemO
        by_cases hab : b = a
        · subst hab
          omega
        · rw [← hb, hfirst_supp b] at hsub
          obtain ⟨p, hpb, hpa⟩ := pasch_diff b a hab
          exact hpa (hsub hpb)
      have hmemE_of_sup : ∀ (a : Fin 4) (h : ℕ), 6 ≤ h → h < first a → h ≠ z →
          pasch a ⊆ supp1 gl h → h ∈ E := by
        intro a h h6 hlt hnez hsup
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hnez, Finset.mem_Ico.mpr ⟨h6, by have := hfirst_lt a; omega⟩⟩, ?_⟩
        intro hmemO
        obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hmemO
        by_cases hab : b = a
        · subst hab
          omega
        · rw [← hb, hfirst_supp b] at hsup
          obtain ⟨p, hpa, hpb⟩ := pasch_diff a b (Ne.symm hab)
          exact hpb (hsup hpa)
      by_cases hAnyAnd : ∃ a : Fin 4, (gl[first a - 6]'(by have := hfirst_ge6 a; have := hfirst_lt a; omega)).op = GateOp.and
      · obtain ⟨a0, ha0_and⟩ := hAnyAnd
        have hlen0 := (hG (gl[first a0 - 6]'(by have := hfirst_ge6 a0; have := hfirst_lt a0; omega)) (List.getElem_mem _)).2
        obtain ⟨u, v, hu6, hult, huz, hv6, hvlt, hvz, huv, hsupu, hsupv, hval0⟩ :=
          and_gate_inputs gl z (first a0) a0 (hfirst_ge6 a0) (hfirst_lt a0) ha0_and hlen0
            (hfirst_eval a0) (hfirst_min a0) hz1
        have huE : u ∈ E := hmemE_of_sup a0 u hu6 hult huz hsupu
        have hvE : v ∈ E := hmemE_of_sup a0 v hv6 hvlt hvz hsupv
        have hEeq : E = {u, v} := by
          have hsub : ({u, v} : Finset ℕ) ⊆ E := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact huE
            · rw [Finset.mem_singleton.mp hw]
              exact hvE
          have hc2 : ({u, v} : Finset ℕ).card = 2 := Finset.card_pair huv
          exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
        let a1 : Fin 4 := if a0 = 0 then 1 else 0
        have ha1ne : a1 ≠ a0 := by
          by_cases h : a0 = 0
          · simp [a1, h]
          · simp [a1, h, Ne.symm h]
        rcases hgate_op a1 with ha1_and | ha1_or
        · have hlen1 := (hG (gl[first a1 - 6]'(by have := hfirst_ge6 a1; have := hfirst_lt a1; omega)) (List.getElem_mem _)).2
          obtain ⟨u1, v1, hu16, hu1lt, hu1z, hv16, hv1lt, hv1z, hu1v1, hsupu1, hsupv1, hval1⟩ :=
            and_gate_inputs gl z (first a1) a1 (hfirst_ge6 a1) (hfirst_lt a1) ha1_and hlen1
              (hfirst_eval a1) (hfirst_min a1) hz1
          have hu1E : u1 ∈ ({u, v} : Finset ℕ) := hEeq ▸ hmemE_of_sup a1 u1 hu16 hu1lt hu1z hsupu1
          have hv1E : v1 ∈ ({u, v} : Finset ℕ) := hEeq ▸ hmemE_of_sup a1 v1 hv16 hv1lt hv1z hsupv1
          have heq_fn : ∀ x, val gl x (first a1) = val gl x (first a0) := by
            intro x
            rw [hval1 x, hval0 x]
            rcases Finset.mem_insert.mp hu1E with rfl | hu1E
            · rcases Finset.mem_insert.mp hv1E with hbad | hv1E
              · exact absurd hbad.symm hu1v1
              · rw [Finset.mem_singleton.mp hv1E]
            · rw [Finset.mem_singleton.mp hu1E]
              rcases Finset.mem_insert.mp hv1E with rfl | hv1E
              · exact Bool.and_comm _ _
              · exact absurd (Finset.mem_singleton.mp hv1E ▸ Finset.mem_singleton.mp hu1E) hu1v1
          obtain ⟨p, hp1, hp0⟩ := pasch_diff a1 a0 ha1ne
          have h := heq_fn (eVec p)
          rw [hfirst_eval a1, hfirst_eval a0, pasch_eval_eVec, pasch_eval_eVec,
            decide_eq_true hp1, decide_eq_false hp0] at h
          exact Bool.noConfusion h
        · have hlen1 := (hG (gl[first a1 - 6]'(by have := hfirst_ge6 a1; have := hfirst_lt a1; omega)) (List.getElem_mem _)).2
          obtain ⟨h, hh6, hhlt, hhz, hsub1, hcard1⟩ :=
            or_gate_inputs gl z (first a1) a1 (hfirst_ge6 a1) (hfirst_lt a1) ha1_or hlen1
              (hfirst_eval a1) (hfirst_min a1) hz0
          have hhE : h ∈ ({u, v} : Finset ℕ) := hEeq ▸ hmemE_of_sub a1 h hh6 hhlt hhz hsub1 hcard1
          have hsub01 : pasch a0 ⊆ pasch a1 := by
            rcases Finset.mem_insert.mp hhE with rfl | hhE
            · exact hsupu.trans hsub1
            · rw [Finset.mem_singleton.mp hhE] at hsub1
              exact hsupv.trans hsub1
          obtain ⟨p, hp0, hp1⟩ := pasch_diff a0 a1 (Ne.symm ha1ne)
          exact hp1 (hsub01 hp0)
      · have hAllOr : ∀ a : Fin 4, (gl[first a - 6]'(by have := hfirst_ge6 a; have := hfirst_lt a; omega)).op = GateOp.or := by
          intro a
          rcases hgate_op a with hand | hor
          · exact absurd ⟨a, hand⟩ hAnyAnd
          · exact hor
        have hexH : ∀ a : Fin 4, ∃ h ∈ E, supp1 gl h ⊆ pasch a ∧ 2 ≤ (supp1 gl h).card := by
          intro a
          have hlen := (hG (gl[first a - 6]'(by have := hfirst_ge6 a; have := hfirst_lt a; omega)) (List.getElem_mem _)).2
          obtain ⟨h, hh6, hhlt, hhz, hsub, hcard⟩ :=
            or_gate_inputs gl z (first a) a (hfirst_ge6 a) (hfirst_lt a) (hAllOr a) hlen
              (hfirst_eval a) (hfirst_min a) hz0
          exact ⟨h, hmemE_of_sub a h hh6 hhlt hhz hsub hcard, hsub, hcard⟩
        choose hFn hhE hhSub hhCard using hexH
        have hhInj : Function.Injective hFn := by
          intro a b hab
          by_contra hne
          have hsub : supp1 gl (hFn a) ⊆ pasch a ∩ pasch b := by
            intro p hp
            exact Finset.mem_inter.mpr ⟨hhSub a hp, hhSub b (hab ▸ hp)⟩
          have c1 := Finset.card_le_card hsub
          have c2 := pasch_inter a b hne
          have c3 := hhCard a
          omega
        have himg : (Finset.univ.image hFn) ⊆ E := by
          intro w hw
          obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
          exact hhE a
        have c1 := Finset.card_le_card himg
        rw [Finset.card_image_of_injective _ hhInj] at c1
        simp only [Finset.card_univ, Fintype.card_fin] at c1
        omega
  · have hNoNot : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      obtain ⟨hop, hlen⟩ := hG gl[k] (List.getElem_mem _)
      refine ⟨?_, hlen⟩
      rcases hop with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · have hq := hnot ⟨k, hk⟩ hop
        have : (gl.get i0).op = GateOp.not := by
          rw [← hq]
          exact hop
        exact absurd this hi0
    have h8 := hMono 6 4 pasch pasch_inter gl ol hNoNot hol
    rw [pasch_sum] at h8
    exact h8

end PEqualNP.Outside.L_meta_1042

open PEqualNP.Outside.L_meta_1042 in
theorem PEqualNP.Outside.L_meta_1042 : (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin 4 → ℕ), (∀ gg ∈ gl, (gg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gg.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gl.length, ∀ qa : Fin gl.length, (gl.get qa).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ ka : Fin 1, ι ka = qa) → (∀ (oa : Fin 4) (xa : Fin 6 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol oa⟩ (List.ofFn xa) = decide (∃ va ∈ (![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 4 → Finset (Fin 6)) oa, xa va = true)) → 8 ≤ gl.length :=
  main_bound

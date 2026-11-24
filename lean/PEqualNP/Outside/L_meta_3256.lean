import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3256

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

private lemma wires_append_gate (gs : List Gate) (g : Gate) (x : List Bool) :
    ({ gates := gs ++ [g], output := 0 : Circuit }.wires x) =
      ({ gates := gs, output := 0 : Circuit }.wires x) ++
        [g.op.eval (g.inputs.map fun i =>
          ({ gates := gs, output := 0 : Circuit }.wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

private lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  have h : ∀ (gs : List Gate) (acc : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
        acc.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g gs ih =>
      intro acc
      rw [List.foldl_cons, ih]
      simp
      omega
  exact h C.gates x

private lemma wires_take (C : Circuit) (x : List Bool) (k : ℕ) (hk : k ≤ C.gates.length) :
    ({ gates := C.gates.take k, output := 0 : Circuit }.wires x) =
      (C.wires x).take (x.length + k) := by
  have hlen : (C.wires x).length = x.length + C.gates.length := wires_length C x
  have htake : ∀ (gs : List Gate) (acc : List Bool) (k : ℕ), k ≤ gs.length →
      ((gs.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc) =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).take
          (acc.length + k) := by
    intro gs
    induction gs with
    | nil =>
      intro acc k hk
      simp at hk
      subst hk
      simp
    | cons g gs ih =>
      intro acc k hk
      cases k with
      | zero =>
        simp only [List.take_zero, List.foldl_nil, Nat.add_zero]
        have hpref : ∀ (gs' : List Gate) (acc' : List Bool),
            ∃ t, (gs'.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc') =
              acc' ++ t := by
          intro gs'
          induction gs' with
          | nil => intro acc'; exact ⟨[], by simp⟩
          | cons g' gs' ih' =>
            intro acc'
            obtain ⟨t, ht⟩ := ih' (acc' ++ [g'.op.eval (g'.inputs.map fun i => acc'.getD i false)])
            exact ⟨g'.op.eval (g'.inputs.map fun i => acc'.getD i false) :: t, by simpa [List.foldl_cons] using ht⟩
        obtain ⟨t, ht⟩ := hpref (g :: gs) acc
        rw [ht, List.take_left]
      | succ k =>
        simp only [List.take_succ_cons, List.foldl_cons]
        have hk' : k ≤ gs.length := Nat.le_of_succ_le_succ hk
        rw [ih _ k hk']
        simp only [List.length_append, List.length_singleton]
        rw [Nat.add_assoc, Nat.add_comm 1 k]
  exact htake C.gates x k hk

private lemma wireValue_lt_add (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    wireValue C x w = x.getD w false := by
  unfold wireValue
  have h0 := wires_take C x 0 (Nat.zero_le _)
  simp only [List.take_zero, Nat.add_zero] at h0
  change x = (C.wires x).take x.length at h0
  have h2 : (C.wires x).getD w false = ((C.wires x).take x.length).getD w false := by
    simp [List.getD, List.getElem?_take_of_lt hw]
  rw [h2, ← h0]

private lemma wireValue_gate (C : Circuit) (n : ℕ) (hRB : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    wireValue C x (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireValue C x i) := by
  unfold wireValue
  have hlen : (C.wires x).length = n + C.gates.length := by rw [wires_length, hx]
  have htake : C.gates.take (j + 1) = C.gates.take j ++ [C.gates[j]] := by
    rw [List.take_succ_eq_append_getElem hj]
  have hw1 := wires_take C x (j + 1) hj
  rw [htake, wires_append_gate] at hw1
  have hget : (C.wires x).getD (n + j) false =
      ((C.wires x).take (x.length + (j + 1))).getD (n + j) false := by
    simp [List.getD, List.getElem?_take_of_lt (by omega : n + j < x.length + (j + 1))]
  rw [hget, ← hw1]
  have hw0 := wires_take C x j (Nat.le_of_lt hj)
  have hlen0 : ({ gates := C.gates.take j, output := 0 : Circuit }.wires x).length = n + j := by
    rw [wires_length, hx, List.length_take_of_le (Nat.le_of_lt hj)]
  rw [List.getD_append_right _ _ _ _ (by omega : n + j ≥ _)]
  simp only [hlen0, Nat.sub_self, List.getD_cons_zero]
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
  rw [hgate]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + j := hRB j hj i (by rwa [hgate])
  rw [hw0]
  simp only [List.getD]
  rw [List.getElem?_take_of_lt (by omega : i < x.length + j)]

private lemma incidenceInput_length {n : ℕ} (S : Finset (Fin n)) (l : Fin n) :
    (incidenceInput S {l}).length = n + n := by
  simp [incidenceInput]

private lemma incidenceInput_getD_left {n : ℕ} (S : Finset (Fin n)) (l : Fin n)
    (w : ℕ) (hw : w < n) :
    (incidenceInput S {l}).getD w false = decide (⟨w, hw⟩ ∈ S) := by
  simp [incidenceInput, List.getD, List.getElem?_append_left (by simp [hw] : w < (List.ofFn (fun p : Fin n => decide (p ∈ S))).length), hw]

private lemma incidenceInput_getD_right {n : ℕ} (S : Finset (Fin n)) (l : Fin n)
    (w : ℕ) (hw1 : n ≤ w) (hw2 : w < n + n) :
    (incidenceInput S {l}).getD w false = decide (⟨w - n, by omega⟩ ∈ ({l} : Finset (Fin n))) := by
  simp only [incidenceInput, List.getD]
  rw [List.getElem?_append_right (by simp; omega)]
  simp [show w - n < n by omega]

private lemma wireValue_mono {n : ℕ} (C : Circuit) (hAO : IsAO2 (n + n) C) (l : Fin n)
    {S T : Finset (Fin n)} (hST : S ⊆ T) (w : ℕ) (hw : w < n + n + C.size) :
    wireValue C (incidenceInput S {l}) w = true →
      wireValue C (incidenceInput T {l}) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hS
    by_cases hwin : w < n + n
    · rw [wireValue_lt_add C _ w (by rw [incidenceInput_length]; exact hwin)] at hS ⊢
      by_cases hw1 : w < n
      · rw [incidenceInput_getD_left S l w hw1] at hS
        rw [incidenceInput_getD_left T l w hw1]
        exact decide_eq_true (hST (of_decide_eq_true hS))
      · have hw1' : n ≤ w := by omega
        rw [incidenceInput_getD_right S l w hw1' hwin] at hS
        rw [incidenceInput_getD_right T l w hw1' hwin]
        exact hS
    · have hj : w - (n + n) < C.gates.length := by
        change w < n + n + C.gates.length at hw
        omega
      have hw_eq : w = n + n + (w - (n + n)) := by omega
      rw [hw_eq] at hS ⊢
      rw [wireValue_gate C (n + n) hAO.2.1 _ (incidenceInput_length S l) (w - (n + n)) hj] at hS
      rw [wireValue_gate C (n + n) hAO.2.1 _ (incidenceInput_length T l) (w - (n + n)) hj]
      set g := gateAt C (w - (n + n))
      have hg_mem : g ∈ C.gates := by
        simp [g, gateAt, List.getD, List.getElem?_eq_getElem hj]
      have hlen : g.inputs.length = 2 := hAO.2.2 g hg_mem
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or := hAO.1 g hg_mem
      obtain ⟨u, v, huv⟩ : ∃ u v, g.inputs = [u, v] := by
        cases h1 : g.inputs with
        | nil => simp [h1] at hlen
        | cons u rest =>
          cases rest with
          | nil => simp [h1] at hlen
          | cons v rest2 =>
            cases rest2 with
            | nil => exact ⟨u, v, rfl⟩
            | cons _ _ => simp [h1] at hlen
      have hu : u < n + n + (w - (n + n)) := hAO.2.1 (w - (n + n)) hj u (by rw [huv]; simp)
      have hv : v < n + n + (w - (n + n)) := hAO.2.1 (w - (n + n)) hj v (by rw [huv]; simp)
      rw [huv] at hS ⊢
      rcases hop with hop | hop <;> rw [hop] at hS ⊢ <;> simp [GateOp.eval] at hS ⊢
      · exact ⟨ih u (by omega) (by omega) hS.1, ih v (by omega) (by omega) hS.2⟩
      · rcases hS with hS | hS
        · exact Or.inl (ih u (by omega) (by omega) hS)
        · exact Or.inr (ih v (by omega) (by omega) hS)

private lemma input_wire_card_le_one {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (l : Fin n)
    (w : ℕ) (hw : w < n + n)
    (hPc : wireValue C (incidenceInput Pᶜ {l}) w = false) :
    (Finset.univ.filter fun p : Fin n => wireValue C (incidenceInput {p} {l}) w = true).card ≤ 1 := by
  by_cases hw1 : w < n
  · have hsub : (Finset.univ.filter fun p : Fin n =>
        wireValue C (incidenceInput {p} {l}) w = true) ⊆ {⟨w, hw1⟩} := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [wireValue_lt_add C _ w (by rw [incidenceInput_length]; exact hw),
        incidenceInput_getD_left {p} l w hw1] at hp
      simp only [decide_eq_true_eq, Finset.mem_singleton] at hp ⊢
      exact hp.symm
    exact (Finset.card_le_card hsub).trans (by simp)
  · have hw1' : n ≤ w := by omega
    rw [wireValue_lt_add C _ w (by rw [incidenceInput_length]; exact hw),
      incidenceInput_getD_right Pᶜ l w hw1' hw] at hPc
    have hempty : (Finset.univ.filter fun p : Fin n =>
        wireValue C (incidenceInput {p} {l}) w = true) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rw [wireValue_lt_add C _ w (by rw [incidenceInput_length]; exact hw),
        incidenceInput_getD_right {p} l w hw1' hw, hPc]
      simp
    rw [hempty]
    simp

private def childWire (C : Circuit) (g : ℕ) (b : Bool) : ℕ :=
  (gateAt C g).inputs.getD (if b then 1 else 0) 0

private lemma childWire_lt {n : ℕ} (C : Circuit) (hRB : ReadsBack n C)
    (g : ℕ) (hg : g < C.gates.length) (h2 : (gateAt C g).inputs.length = 2) (b : Bool) :
    childWire C g b < n + g := by
  apply hRB g hg
  obtain ⟨u, v, huv⟩ : ∃ u v, (gateAt C g).inputs = [u, v] := by
    cases h1 : (gateAt C g).inputs with
    | nil => simp [h1] at h2
    | cons u rest =>
      cases rest with
      | nil => simp [h1] at h2
      | cons v rest2 =>
        cases rest2 with
        | nil => exact ⟨u, v, rfl⟩
        | cons _ _ => simp [h1] at h2
  simp [childWire, huv]
  cases b <;> simp

private lemma gate_eval_children {n : ℕ} (C : Circuit) (hAO : IsAO2 (n + n) C)
    (l : Fin n) (S : Finset (Fin n)) (g : ℕ) (hg : g < C.gates.length) :
    wireValue C (incidenceInput S {l}) (n + n + g) =
      (gateAt C g).op.eval
        [wireValue C (incidenceInput S {l}) (childWire C g false),
         wireValue C (incidenceInput S {l}) (childWire C g true)] := by
  rw [wireValue_gate C (n + n) hAO.2.1 _ (incidenceInput_length S l) g hg]
  have hmem : gateAt C g ∈ C.gates := by
    simp [gateAt, List.getD, List.getElem?_eq_getElem hg]
  have hlen : (gateAt C g).inputs.length = 2 := hAO.2.2 _ hmem
  obtain ⟨u, v, huv⟩ : ∃ u v, (gateAt C g).inputs = [u, v] := by
    cases h1 : (gateAt C g).inputs with
    | nil => simp [h1] at hlen
    | cons u rest =>
      cases rest with
      | nil => simp [h1] at hlen
      | cons v rest2 =>
        cases rest2 with
        | nil => exact ⟨u, v, rfl⟩
        | cons _ _ => simp [h1] at hlen
  simp [childWire, huv]

private def stepGate {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (l : Fin n) (w : ℕ) : ℕ :=
  if h : n + n ≤ w ∧ w < n + n + C.gates.length then
    let g := w - (n + n)
    match (gateAt C g).op with
    | GateOp.and =>
      let u := childWire C g false
      let v := childWire C g true
      if hu : u < w then
        if wireValue C (incidenceInput Pᶜ {l}) u = false then
          stepGate C P l u
        else if hv : v < w then
          stepGate C P l v
        else g
      else if hv : v < w then
        stepGate C P l v
      else g
    | _ => g
  else 0
termination_by w

private def reachGates {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (l : Fin n) (w : ℕ) : Finset ℕ :=
  if h : n + n ≤ w ∧ w < n + n + C.gates.length ∧
      wireValue C (incidenceInput Pᶜ {l}) w = false ∧
      2 ≤ (Finset.univ.filter fun p : Fin n =>
        wireValue C (incidenceInput {p} {l}) w = true).card then
    let g := w - (n + n)
    match (gateAt C g).op with
    | GateOp.and =>
      let u := childWire C g false
      let v := childWire C g true
      if hu : u < w then
        if wireValue C (incidenceInput Pᶜ {l}) u = false then
          reachGates C P l u
        else if hv : v < w then
          reachGates C P l v
        else ∅
      else if hv : v < w then
        reachGates C P l v
      else ∅
    | _ =>
      let u := childWire C g false
      let v := childWire C g true
      insert g ((if u < w then reachGates C P l u else ∅) ∪
        (if v < w then reachGates C P l v else ∅))
  else ∅
termination_by w

private lemma stepGate_and_left {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (l : Fin n) (w : ℕ)
    (hw1 : n + n ≤ w) (hw2 : w < n + n + C.gates.length)
    (hop : (gateAt C (w - (n + n))).op = GateOp.and)
    (hu : childWire C (w - (n + n)) false < w)
    (huPc : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) = false) :
    stepGate C P l w = stepGate C P l (childWire C (w - (n + n)) false) := by
  conv_lhs => unfold stepGate
  simp only [dif_pos (And.intro hw1 hw2), hop, dif_pos hu, if_pos huPc]

private lemma stepGate_and_right {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (l : Fin n) (w : ℕ)
    (hw1 : n + n ≤ w) (hw2 : w < n + n + C.gates.length)
    (hop : (gateAt C (w - (n + n))).op = GateOp.and)
    (hu : childWire C (w - (n + n)) false < w)
    (huPc : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) ≠ false)
    (hv : childWire C (w - (n + n)) true < w) :
    stepGate C P l w = stepGate C P l (childWire C (w - (n + n)) true) := by
  conv_lhs => unfold stepGate
  simp only [dif_pos (And.intro hw1 hw2), hop, dif_pos hu, if_neg huPc, dif_pos hv]

private lemma stepGate_or {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (l : Fin n) (w : ℕ)
    (hw1 : n + n ≤ w) (hw2 : w < n + n + C.gates.length)
    (hop : (gateAt C (w - (n + n))).op = GateOp.or) :
    stepGate C P l w = w - (n + n) := by
  conv_lhs => unfold stepGate
  simp only [dif_pos (And.intro hw1 hw2), hop]

private lemma reachGates_and_left {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (l : Fin n) (w : ℕ)
    (hw1 : n + n ≤ w) (hw2 : w < n + n + C.gates.length)
    (hPc : wireValue C (incidenceInput Pᶜ {l}) w = false)
    (hcard : 2 ≤ (Finset.univ.filter fun p : Fin n =>
      wireValue C (incidenceInput {p} {l}) w = true).card)
    (hop : (gateAt C (w - (n + n))).op = GateOp.and)
    (hu : childWire C (w - (n + n)) false < w)
    (huPc : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) = false) :
    reachGates C P l w = reachGates C P l (childWire C (w - (n + n)) false) := by
  conv_lhs => unfold reachGates
  have hcond : n + n ≤ w ∧ w < n + n + C.gates.length ∧
      wireValue C (incidenceInput Pᶜ {l}) w = false ∧
      2 ≤ (Finset.univ.filter fun p : Fin n =>
        wireValue C (incidenceInput {p} {l}) w = true).card := ⟨hw1, hw2, hPc, hcard⟩
  simp only [dif_pos hcond, hop, dif_pos hu, if_pos huPc]

private lemma reachGates_and_right {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (l : Fin n) (w : ℕ)
    (hw1 : n + n ≤ w) (hw2 : w < n + n + C.gates.length)
    (hPc : wireValue C (incidenceInput Pᶜ {l}) w = false)
    (hcard : 2 ≤ (Finset.univ.filter fun p : Fin n =>
      wireValue C (incidenceInput {p} {l}) w = true).card)
    (hop : (gateAt C (w - (n + n))).op = GateOp.and)
    (hu : childWire C (w - (n + n)) false < w)
    (huPc : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) ≠ false)
    (hv : childWire C (w - (n + n)) true < w) :
    reachGates C P l w = reachGates C P l (childWire C (w - (n + n)) true) := by
  conv_lhs => unfold reachGates
  have hcond : n + n ≤ w ∧ w < n + n + C.gates.length ∧
      wireValue C (incidenceInput Pᶜ {l}) w = false ∧
      2 ≤ (Finset.univ.filter fun p : Fin n =>
        wireValue C (incidenceInput {p} {l}) w = true).card := ⟨hw1, hw2, hPc, hcard⟩
  simp only [dif_pos hcond, hop, dif_pos hu, if_neg huPc, dif_pos hv]

private lemma reachGates_or {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (l : Fin n) (w : ℕ)
    (hw1 : n + n ≤ w) (hw2 : w < n + n + C.gates.length)
    (hPc : wireValue C (incidenceInput Pᶜ {l}) w = false)
    (hcard : 2 ≤ (Finset.univ.filter fun p : Fin n =>
      wireValue C (incidenceInput {p} {l}) w = true).card)
    (hop : (gateAt C (w - (n + n))).op = GateOp.or)
    (hu : childWire C (w - (n + n)) false < w)
    (hv : childWire C (w - (n + n)) true < w) :
    reachGates C P l w = insert (w - (n + n))
      (reachGates C P l (childWire C (w - (n + n)) false) ∪
       reachGates C P l (childWire C (w - (n + n)) true)) := by
  conv_lhs => unfold reachGates
  have hcond : n + n ≤ w ∧ w < n + n + C.gates.length ∧
      wireValue C (incidenceInput Pᶜ {l}) w = false ∧
      2 ≤ (Finset.univ.filter fun p : Fin n =>
        wireValue C (incidenceInput {p} {l}) w = true).card := ⟨hw1, hw2, hPc, hcard⟩
  simp only [dif_pos hcond, hop, if_pos hu, if_pos hv]

private lemma reachGates_props {n : ℕ} (C : Circuit) (hAO : IsAO2 (n + n) C)
    (P : Finset (Fin n)) (l : Fin n) (w : ℕ) :
    ∀ g ∈ reachGates C P l w,
      g < C.gates.length ∧
      n + n + g ≤ w ∧
      (gateAt C g).op = GateOp.or ∧
      wireValue C (incidenceInput Pᶜ {l}) (n + n + g) = false ∧
      2 ≤ (Finset.univ.filter fun p : Fin n =>
        wireValue C (incidenceInput {p} {l}) (n + n + g) = true).card := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hg
    by_cases hcond : n + n ≤ w ∧ w < n + n + C.gates.length ∧
        wireValue C (incidenceInput Pᶜ {l}) w = false ∧
        2 ≤ (Finset.univ.filter fun p : Fin n =>
          wireValue C (incidenceInput {p} {l}) w = true).card
    · have hj : w - (n + n) < C.gates.length := by omega
      have hmem : gateAt C (w - (n + n)) ∈ C.gates := by
        simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
      have hlen : (gateAt C (w - (n + n))).inputs.length = 2 := hAO.2.2 _ hmem
      have hu_lt : childWire C (w - (n + n)) false < w := by
        have := childWire_lt C hAO.2.1 (w - (n + n)) hj hlen false; omega
      have hv_lt : childWire C (w - (n + n)) true < w := by
        have := childWire_lt C hAO.2.1 (w - (n + n)) hj hlen true; omega
      rcases hAO.1 _ hmem with hop | hop
      · by_cases huPc : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) = false
        · rw [reachGates_and_left C P l w hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2 hop hu_lt huPc] at hg
          have hp := ih _ hu_lt g hg
          exact ⟨hp.1, by omega, hp.2.2⟩
        · rw [reachGates_and_right C P l w hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2 hop hu_lt huPc hv_lt] at hg
          have hp := ih _ hv_lt g hg
          exact ⟨hp.1, by omega, hp.2.2⟩
      · rw [reachGates_or C P l w hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2 hop hu_lt hv_lt] at hg
        rcases Finset.mem_insert.mp hg with rfl | hg'
        · refine ⟨hj, by omega, hop, ?_, ?_⟩
          · have hw_eq : n + n + (w - (n + n)) = w := by omega
            rw [hw_eq]; exact hcond.2.2.1
          · have hw_eq : n + n + (w - (n + n)) = w := by omega
            rw [hw_eq]; exact hcond.2.2.2
        · rcases Finset.mem_union.mp hg' with hg1 | hg2
          · have hp := ih _ hu_lt g hg1
            exact ⟨hp.1, by omega, hp.2.2⟩
          · have hp := ih _ hv_lt g hg2
            exact ⟨hp.1, by omega, hp.2.2⟩
    · have hempty : reachGates C P l w = ∅ := by
        conv_lhs => unfold reachGates
        simp only [dif_neg hcond]
      rw [hempty] at hg
      exact absurd hg (Finset.notMem_empty _)

private lemma active_valid_step {n : ℕ} (C : Circuit) (hAO : IsAO2 (n + n) C)
    (P : Finset (Fin n)) (l : Fin n) (w : ℕ)
    (hw_lt : w < n + n + C.gates.length)
    (hPc : wireValue C (incidenceInput Pᶜ {l}) w = false)
    (hcard : 2 ≤ (Finset.univ.filter fun p : Fin n =>
      wireValue C (incidenceInput {p} {l}) w = true).card) :
    let g := stepGate C P l w
    g ∈ reachGates C P l w ∧
    g < C.gates.length ∧
    n + n + g ≤ w ∧
    (gateAt C g).op = GateOp.or ∧
    wireValue C (incidenceInput Pᶜ {l}) (n + n + g) = false ∧
    (Finset.univ.filter fun p : Fin n =>
      wireValue C (incidenceInput {p} {l}) w = true) ⊆
      (Finset.univ.filter fun p : Fin n =>
        wireValue C (incidenceInput {p} {l}) (n + n + g) = true) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hw_ge : n + n ≤ w := by
      by_contra hlt
      have h1 := input_wire_card_le_one C P l w (by omega) hPc
      omega
    have hj : w - (n + n) < C.gates.length := by omega
    have hw_eq : n + n + (w - (n + n)) = w := by omega
    have hmem : gateAt C (w - (n + n)) ∈ C.gates := by
      simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
    have hlen : (gateAt C (w - (n + n))).inputs.length = 2 := hAO.2.2 _ hmem
    have hu_lt : childWire C (w - (n + n)) false < w := by
      have := childWire_lt C hAO.2.1 (w - (n + n)) hj hlen false
      omega
    have hv_lt : childWire C (w - (n + n)) true < w := by
      have := childWire_lt C hAO.2.1 (w - (n + n)) hj hlen true
      omega
    by_cases hand : (gateAt C (w - (n + n))).op = GateOp.and
    · have hevalPc := gate_eval_children C hAO l Pᶜ (w - (n + n)) hj
      rw [hw_eq, hPc, hand] at hevalPc
      simp [GateOp.eval] at hevalPc
      have h_or_false : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) = false ∨
          wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) true) = false := by
        cases h1 : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) <;>
          cases h2 : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) true) <;>
          simp_all
      have hsub_u : (Finset.univ.filter fun p : Fin n =>
          wireValue C (incidenceInput {p} {l}) w = true) ⊆
          (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) false) = true) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        have hev := gate_eval_children C hAO l {p} (w - (n + n)) hj
        rw [hw_eq, hp, hand] at hev
        simp [GateOp.eval] at hev
        exact hev.1
      have hsub_v : (Finset.univ.filter fun p : Fin n =>
          wireValue C (incidenceInput {p} {l}) w = true) ⊆
          (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) true) = true) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        have hev := gate_eval_children C hAO l {p} (w - (n + n)) hj
        rw [hw_eq, hp, hand] at hev
        simp [GateOp.eval] at hev
        exact hev.2
      by_cases huPc : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) = false
      · have hcard_u : 2 ≤ (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) false) = true).card :=
          le_trans hcard (Finset.card_le_card hsub_u)
        have ihu := ih _ hu_lt (by omega) huPc hcard_u
        have hstep_eq := stepGate_and_left C P l w hw_ge hw_lt hand hu_lt huPc
        have hreach_eq := reachGates_and_left C P l w hw_ge hw_lt hPc hcard hand hu_lt huPc
        rw [hstep_eq, hreach_eq]
        exact ⟨ihu.1, ihu.2.1, by omega, ihu.2.2.2.1, ihu.2.2.2.2.1, hsub_u.trans ihu.2.2.2.2.2⟩
      · have hvPc : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) true) = false := by
          rcases h_or_false with h1 | h2
          · exact absurd h1 huPc
          · exact h2
        have hcard_v : 2 ≤ (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) true) = true).card :=
          le_trans hcard (Finset.card_le_card hsub_v)
        have ihv := ih _ hv_lt (by omega) hvPc hcard_v
        have hstep_eq := stepGate_and_right C P l w hw_ge hw_lt hand hu_lt huPc hv_lt
        have hreach_eq := reachGates_and_right C P l w hw_ge hw_lt hPc hcard hand hu_lt huPc hv_lt
        rw [hstep_eq, hreach_eq]
        exact ⟨ihv.1, ihv.2.1, by omega, ihv.2.2.2.1, ihv.2.2.2.2.1, hsub_v.trans ihv.2.2.2.2.2⟩
    · have hop : (gateAt C (w - (n + n))).op = GateOp.or := by
        rcases hAO.1 _ hmem with h1 | h1
        · exact absurd h1 hand
        · exact h1
      have hstep_eq := stepGate_or C P l w hw_ge hw_lt hop
      have hreach_eq := reachGates_or C P l w hw_ge hw_lt hPc hcard hop hu_lt hv_lt
      have hreach_mem : w - (n + n) ∈ reachGates C P l w := by
        rw [hreach_eq]; exact Finset.mem_insert_self _ _
      rw [hstep_eq]
      refine ⟨hreach_mem, hj, by omega, hop, ?_, ?_⟩
      · rw [hw_eq]; exact hPc
      · rw [hw_eq]

private lemma reachGates_target_or_child {n : ℕ} (C : Circuit) (hAO : IsAO2 (n + n) C)
    (P : Finset (Fin n)) (l : Fin n) (w : ℕ)
    (hw_lt : w < n + n + C.gates.length)
    (hPc : wireValue C (incidenceInput Pᶜ {l}) w = false)
    (hcard : 2 ≤ (Finset.univ.filter fun p : Fin n =>
      wireValue C (incidenceInput {p} {l}) w = true).card) :
    ∀ g ∈ reachGates C P l w,
      g = stepGate C P l w ∨
      ∃ gp ∈ reachGates C P l w, ∃ b : Bool,
        wireValue C (incidenceInput Pᶜ {l}) (childWire C gp b) = false ∧
        2 ≤ (Finset.univ.filter fun p : Fin n =>
          wireValue C (incidenceInput {p} {l}) (childWire C gp b) = true).card ∧
        stepGate C P l (childWire C gp b) = g := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hg
    have hw_ge : n + n ≤ w := by
      by_contra hlt
      have h1 := input_wire_card_le_one C P l w (by omega) hPc
      omega
    have hj : w - (n + n) < C.gates.length := by omega
    have hw_eq : n + n + (w - (n + n)) = w := by omega
    have hmem : gateAt C (w - (n + n)) ∈ C.gates := by
      simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
    have hlen : (gateAt C (w - (n + n))).inputs.length = 2 := hAO.2.2 _ hmem
    have hu_lt : childWire C (w - (n + n)) false < w := by
      have := childWire_lt C hAO.2.1 (w - (n + n)) hj hlen false
      omega
    have hv_lt : childWire C (w - (n + n)) true < w := by
      have := childWire_lt C hAO.2.1 (w - (n + n)) hj hlen true
      omega
    by_cases hand : (gateAt C (w - (n + n))).op = GateOp.and
    · have hevalPc := gate_eval_children C hAO l Pᶜ (w - (n + n)) hj
      rw [hw_eq, hPc, hand] at hevalPc
      simp [GateOp.eval] at hevalPc
      have h_or_false : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) = false ∨
          wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) true) = false := by
        cases h1 : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) <;>
          cases h2 : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) true) <;>
          simp_all
      have hsub_u : (Finset.univ.filter fun p : Fin n =>
          wireValue C (incidenceInput {p} {l}) w = true) ⊆
          (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) false) = true) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        have hev := gate_eval_children C hAO l {p} (w - (n + n)) hj
        rw [hw_eq, hp, hand] at hev
        simp [GateOp.eval] at hev
        exact hev.1
      have hsub_v : (Finset.univ.filter fun p : Fin n =>
          wireValue C (incidenceInput {p} {l}) w = true) ⊆
          (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) true) = true) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        have hev := gate_eval_children C hAO l {p} (w - (n + n)) hj
        rw [hw_eq, hp, hand] at hev
        simp [GateOp.eval] at hev
        exact hev.2
      by_cases huPc : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) = false
      · have hcard_u : 2 ≤ (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) false) = true).card :=
          le_trans hcard (Finset.card_le_card hsub_u)
        have hstep_eq := stepGate_and_left C P l w hw_ge hw_lt hand hu_lt huPc
        have hreach_eq := reachGates_and_left C P l w hw_ge hw_lt hPc hcard hand hu_lt huPc
        rw [hreach_eq] at hg
        rw [hstep_eq, hreach_eq]
        exact ih _ hu_lt (by omega) huPc hcard_u g hg
      · have hvPc : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) true) = false := by
          rcases h_or_false with h1 | h2
          · exact absurd h1 huPc
          · exact h2
        have hcard_v : 2 ≤ (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) true) = true).card :=
          le_trans hcard (Finset.card_le_card hsub_v)
        have hstep_eq := stepGate_and_right C P l w hw_ge hw_lt hand hu_lt huPc hv_lt
        have hreach_eq := reachGates_and_right C P l w hw_ge hw_lt hPc hcard hand hu_lt huPc hv_lt
        rw [hreach_eq] at hg
        rw [hstep_eq, hreach_eq]
        exact ih _ hv_lt (by omega) hvPc hcard_v g hg
    · have hop : (gateAt C (w - (n + n))).op = GateOp.or := by
        rcases hAO.1 _ hmem with h1 | h1
        · exact absurd h1 hand
        · exact h1
      have hevalPc := gate_eval_children C hAO l Pᶜ (w - (n + n)) hj
      rw [hw_eq, hPc, hop] at hevalPc
      simp [GateOp.eval] at hevalPc
      have hstep_eq := stepGate_or C P l w hw_ge hw_lt hop
      have hreach_eq := reachGates_or C P l w hw_ge hw_lt hPc hcard hop hu_lt hv_lt
      rw [hreach_eq] at hg
      rcases Finset.mem_insert.mp hg with rfl | hg'
      · exact Or.inl hstep_eq.symm
      · right
        have hg0_mem : w - (n + n) ∈ reachGates C P l w := by
          rw [hreach_eq]; exact Finset.mem_insert_self _ _
        rcases Finset.mem_union.mp hg' with hg1 | hg2
        · have hcard_u : 2 ≤ (Finset.univ.filter fun p : Fin n =>
              wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) false) = true).card := by
            by_contra hlt
            have hru : reachGates C P l (childWire C (w - (n + n)) false) = ∅ := by
              conv_lhs => unfold reachGates
              simp only [hlt, and_false, dif_neg, not_false_eq_true]
            rw [hru] at hg1
            exact Finset.notMem_empty _ hg1
          have ihu := ih _ hu_lt (by omega) hevalPc.1 hcard_u g hg1
          rcases ihu with rfl | ⟨gp, hgp, b, hgpPc, hgpCard, hgpStep⟩
          · exact ⟨w - (n + n), hg0_mem, false, hevalPc.1, hcard_u, rfl⟩
          · refine ⟨gp, ?_, b, hgpPc, hgpCard, hgpStep⟩
            rw [hreach_eq]
            exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hgp)
        · have hcard_v : 2 ≤ (Finset.univ.filter fun p : Fin n =>
              wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) true) = true).card := by
            by_contra hlt
            have hrv : reachGates C P l (childWire C (w - (n + n)) true) = ∅ := by
              conv_lhs => unfold reachGates
              simp only [hlt, and_false, dif_neg, not_false_eq_true]
            rw [hrv] at hg2
            exact Finset.notMem_empty _ hg2
          have ihv := ih _ hv_lt (by omega) hevalPc.2 hcard_v g hg2
          rcases ihv with rfl | ⟨gp, hgp, b, hgpPc, hgpCard, hgpStep⟩
          · exact ⟨w - (n + n), hg0_mem, true, hevalPc.2, hcard_v, rfl⟩
          · refine ⟨gp, ?_, b, hgpPc, hgpCard, hgpStep⟩
            rw [hreach_eq]
            exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hgp)

private lemma reachGates_child_subset {n : ℕ} (C : Circuit) (hAO : IsAO2 (n + n) C)
    (P : Finset (Fin n)) (l : Fin n) (w : ℕ)
    (hw_lt : w < n + n + C.gates.length)
    (hPc : wireValue C (incidenceInput Pᶜ {l}) w = false)
    (hcard : 2 ≤ (Finset.univ.filter fun p : Fin n =>
      wireValue C (incidenceInput {p} {l}) w = true).card)
    (b : Bool) :
    reachGates C P l (childWire C (stepGate C P l w) b) ⊆ reachGates C P l w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hw_ge : n + n ≤ w := by
      by_contra hlt
      have h1 := input_wire_card_le_one C P l w (by omega) hPc
      omega
    have hj : w - (n + n) < C.gates.length := by omega
    have hw_eq : n + n + (w - (n + n)) = w := by omega
    have hmem : gateAt C (w - (n + n)) ∈ C.gates := by
      simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
    have hlen : (gateAt C (w - (n + n))).inputs.length = 2 := hAO.2.2 _ hmem
    have hu_lt : childWire C (w - (n + n)) false < w := by
      have := childWire_lt C hAO.2.1 (w - (n + n)) hj hlen false
      omega
    have hv_lt : childWire C (w - (n + n)) true < w := by
      have := childWire_lt C hAO.2.1 (w - (n + n)) hj hlen true
      omega
    by_cases hand : (gateAt C (w - (n + n))).op = GateOp.and
    · have hevalPc := gate_eval_children C hAO l Pᶜ (w - (n + n)) hj
      rw [hw_eq, hPc, hand] at hevalPc
      simp [GateOp.eval] at hevalPc
      have h_or_false : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) = false ∨
          wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) true) = false := by
        cases h1 : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) <;>
          cases h2 : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) true) <;>
          simp_all
      have hsub_u : (Finset.univ.filter fun p : Fin n =>
          wireValue C (incidenceInput {p} {l}) w = true) ⊆
          (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) false) = true) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        have hev := gate_eval_children C hAO l {p} (w - (n + n)) hj
        rw [hw_eq, hp, hand] at hev
        simp [GateOp.eval] at hev
        exact hev.1
      have hsub_v : (Finset.univ.filter fun p : Fin n =>
          wireValue C (incidenceInput {p} {l}) w = true) ⊆
          (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) true) = true) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        have hev := gate_eval_children C hAO l {p} (w - (n + n)) hj
        rw [hw_eq, hp, hand] at hev
        simp [GateOp.eval] at hev
        exact hev.2
      by_cases huPc : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) false) = false
      · have hcard_u : 2 ≤ (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) false) = true).card :=
          le_trans hcard (Finset.card_le_card hsub_u)
        have hstep_eq := stepGate_and_left C P l w hw_ge hw_lt hand hu_lt huPc
        have hreach_eq := reachGates_and_left C P l w hw_ge hw_lt hPc hcard hand hu_lt huPc
        rw [hstep_eq, hreach_eq]
        exact ih _ hu_lt (by omega) huPc hcard_u
      · have hvPc : wireValue C (incidenceInput Pᶜ {l}) (childWire C (w - (n + n)) true) = false := by
          rcases h_or_false with h1 | h2
          · exact absurd h1 huPc
          · exact h2
        have hcard_v : 2 ≤ (Finset.univ.filter fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (childWire C (w - (n + n)) true) = true).card :=
          le_trans hcard (Finset.card_le_card hsub_v)
        have hstep_eq := stepGate_and_right C P l w hw_ge hw_lt hand hu_lt huPc hv_lt
        have hreach_eq := reachGates_and_right C P l w hw_ge hw_lt hPc hcard hand hu_lt huPc hv_lt
        rw [hstep_eq, hreach_eq]
        exact ih _ hv_lt (by omega) hvPc hcard_v
    · have hop : (gateAt C (w - (n + n))).op = GateOp.or := by
        rcases hAO.1 _ hmem with h1 | h1
        · exact absurd h1 hand
        · exact h1
      have hstep_eq := stepGate_or C P l w hw_ge hw_lt hop
      have hreach_eq := reachGates_or C P l w hw_ge hw_lt hPc hcard hop hu_lt hv_lt
      rw [hstep_eq, hreach_eq]
      cases b
      · intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
      · intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)

private lemma cover_by_leaf_edges {n : ℕ} (C : Circuit) (hAO : IsAO2 (n + n) C)
    (P : Finset (Fin n)) (l : Fin n) (H : Finset ℕ)
    (x : ℕ) (hx_lt : x < n + n + C.gates.length)
    (hxPc : wireValue C (incidenceInput Pᶜ {l}) x = false)
    (hxcard : 2 ≤ (Finset.univ.filter fun p : Fin n =>
      wireValue C (incidenceInput {p} {l}) x = true).card)
    (hsub : reachGates C P l x ⊆ H)
    (p : Fin n) (hp : wireValue C (incidenceInput {p} {l}) x = true) :
    ∃ g ∈ H, ∃ b : Bool,
      (Finset.univ.filter fun q : Fin n =>
        wireValue C (incidenceInput {q} {l}) (childWire C g b) = true).card ≤ 1 ∧
      wireValue C (incidenceInput {p} {l}) (childWire C g b) = true := by
  induction x using Nat.strong_induction_on with
  | ind x ih =>
    have hact := active_valid_step C hAO P l x hx_lt hxPc hxcard
    set g := stepGate C P l x
    have hg_H : g ∈ H := hsub hact.1
    have hg_lt : g < C.gates.length := hact.2.1
    have hg_le : n + n + g ≤ x := hact.2.2.1
    have hg_or : (gateAt C g).op = GateOp.or := hact.2.2.2.1
    have hg_Pc : wireValue C (incidenceInput Pᶜ {l}) (n + n + g) = false := hact.2.2.2.2.1
    have hp_g : wireValue C (incidenceInput {p} {l}) (n + n + g) = true := by
      have hp_mem : p ∈ Finset.univ.filter fun q : Fin n =>
          wireValue C (incidenceInput {q} {l}) x = true := by simp [hp]
      have := hact.2.2.2.2.2 hp_mem
      simpa using this
    have heval_p := gate_eval_children C hAO l {p} g hg_lt
    rw [hp_g, hg_or] at heval_p
    simp [GateOp.eval] at heval_p
    have heval_Pc := gate_eval_children C hAO l Pᶜ g hg_lt
    rw [hg_Pc, hg_or] at heval_Pc
    simp [GateOp.eval] at heval_Pc
    have hmem : gateAt C g ∈ C.gates := by
      simp [gateAt, List.getD, List.getElem?_eq_getElem hg_lt]
    have hlen : (gateAt C g).inputs.length = 2 := hAO.2.2 _ hmem
    have hb_exists : ∃ b : Bool, wireValue C (incidenceInput {p} {l}) (childWire C g b) = true := by
      rcases heval_p.symm with h1 | h2
      · exact ⟨true, h1⟩
      · exact ⟨false, h2⟩
    obtain ⟨b, hpb⟩ := hb_exists
    by_cases hle : (Finset.univ.filter fun q : Fin n =>
        wireValue C (incidenceInput {q} {l}) (childWire C g b) = true).card ≤ 1
    · exact ⟨g, hg_H, b, hle, hpb⟩
    · have hchild_lt : childWire C g b < x := by
        have := childWire_lt C hAO.2.1 g hg_lt hlen b
        omega
      have hchild_Pc : wireValue C (incidenceInput Pᶜ {l}) (childWire C g b) = false := by
        cases b <;> [exact heval_Pc.1; exact heval_Pc.2]
      have hchild_sub : reachGates C P l (childWire C g b) ⊆ H :=
        (reachGates_child_subset C hAO P l x hx_lt hxPc hxcard b).trans hsub
      exact ih (childWire C g b) hchild_lt (by omega) hchild_Pc (by omega) hchild_sub hpb

end PEqualNP.Outside.L_meta_3256

open PEqualNP.Outside.L_meta_3256
open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

theorem PEqualNP.Outside.L_meta_3256 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     x2.output < x1 + x1 + x2.size →       (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) →         x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false →           ∃ (x9 : Finset ℕ),             x3.card ≤ x9.card + (1 : ℕ) ∧               ∀ x10 ∈ x9,                 x10 < x2.size ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                     have x12 : Finset (Fin x1) → Bool := fun (x12 : Finset (Fin x1)) => PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x12 {x4}) (x1 + x1 + x10);                     x12 x3ᶜ = Bool.false ∧ (∃ (x13 : Fin x1) (x14 : Fin x1), x13 ≠ x14 ∧ x12 {x13} = Bool.true ∧ x12 {x14} = Bool.true) ∧ ∀ (x13 : Fin x1), x12 {x13} = Bool.true → x13 ∈ x3 := by
  intro n C P l hAO hout hP hPc
  let A : ℕ → Finset (Fin n) := fun w =>
    Finset.univ.filter fun p : Fin n => wireValue C (incidenceInput {p} {l}) w = true
  have hP_sub : P ⊆ A C.output := by
    intro p hp
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hP p hp
  by_cases hsmall : (A C.output).card ≤ 1
  · refine ⟨∅, by have := Finset.card_le_card hP_sub; omega, ?_⟩
    intro g hg
    exact absurd hg (Finset.notMem_empty _)
  · have hcard2 : 2 ≤ (A C.output).card := by omega
    let H := reachGates C P l C.output
    refine ⟨H, ?_, ?_⟩
    · have hact := active_valid_step C hAO P l C.output hout hPc hcard2
      let edges : Finset (ℕ × Bool) := H ×ˢ ({false, true} : Finset Bool)
      let leafEdges : Finset (ℕ × Bool) := edges.filter fun e => (A (childWire C e.1 e.2)).card ≤ 1
      let intEdges : Finset (ℕ × Bool) := edges.filter fun e => 2 ≤ (A (childWire C e.1 e.2)).card
      have hpart : leafEdges.card + intEdges.card = edges.card := by
        have hdisj : Disjoint leafEdges intEdges := by
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [leafEdges, intEdges, Finset.mem_filter] at he1 he2
          omega
        have hunion : leafEdges ∪ intEdges = edges := by
          ext e
          simp only [leafEdges, intEdges, Finset.mem_union, Finset.mem_filter]
          by_cases h1 : (A (childWire C e.1 e.2)).card ≤ 1
          · simp [h1]
          · simp [h1, show 2 ≤ (A (childWire C e.1 e.2)).card by omega]
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      have hedges : edges.card = 2 * H.card := by
        simp [edges, Finset.card_product]
        ring
      have hint_ge : H.card - 1 ≤ intEdges.card := by
        have hsub_erase : H.erase (stepGate C P l C.output) ⊆
            intEdges.image (fun e => stepGate C P l (childWire C e.1 e.2)) := by
          intro g hg
          rcases Finset.mem_erase.mp hg with ⟨hne, hgH⟩
          rcases reachGates_target_or_child C hAO P l C.output hout hPc hcard2 g hgH with rfl | ⟨gp, hgp, b, _, hgpCard, hgpStep⟩
          · exact absurd rfl hne
          · refine Finset.mem_image.mpr ⟨(gp, b), ?_, hgpStep⟩
            simp only [intEdges, edges, Finset.mem_filter, Finset.mem_product,
              Finset.mem_insert, Finset.mem_singleton]
            refine ⟨⟨hgp, by cases b <;> simp⟩, hgpCard⟩
        have h1 : (H.erase (stepGate C P l C.output)).card = H.card - 1 :=
          Finset.card_erase_of_mem hact.1
        calc H.card - 1
            = (H.erase (stepGate C P l C.output)).card := h1.symm
          _ ≤ (intEdges.image (fun e => stepGate C P l (childWire C e.1 e.2))).card :=
              Finset.card_le_card hsub_erase
          _ ≤ intEdges.card := Finset.card_image_le
      have hleaf_le : leafEdges.card ≤ H.card + 1 := by
        have hpos : 1 ≤ H.card := Finset.card_pos.mpr ⟨_, hact.1⟩
        have hsum : leafEdges.card + intEdges.card = 2 * H.card := hpart.trans hedges
        omega
      have hA_sub : A C.output ⊆ leafEdges.biUnion (fun e => A (childWire C e.1 e.2)) := by
        intro p hp
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨g, hgH, b, hle, hpb⟩ :=
          cover_by_leaf_edges C hAO P l H C.output hout hPc hcard2 (Finset.Subset.refl _) p hp
        refine Finset.mem_biUnion.mpr ⟨(g, b), ?_, ?_⟩
        · simp only [leafEdges, edges, Finset.mem_filter, Finset.mem_product,
            Finset.mem_insert, Finset.mem_singleton]
          exact ⟨⟨hgH, by cases b <;> simp⟩, hle⟩
        · simp [A, hpb]
      have hA_card : (A C.output).card ≤ leafEdges.card := by
        calc (A C.output).card
            ≤ (leafEdges.biUnion (fun e => A (childWire C e.1 e.2))).card :=
              Finset.card_le_card hA_sub
          _ ≤ ∑ e ∈ leafEdges, (A (childWire C e.1 e.2)).card := Finset.card_biUnion_le
          _ ≤ ∑ _e ∈ leafEdges, 1 := by
              apply Finset.sum_le_sum
              intro e he
              exact (Finset.mem_filter.mp he).2
          _ = leafEdges.card := by simp
      have hP_card : P.card ≤ (A C.output).card := Finset.card_le_card hP_sub
      omega
    · intro g hg
      have hp := reachGates_props C hAO P l C.output g hg
      refine ⟨hp.1, hp.2.2.1, hp.2.2.2.1, ?_, ?_⟩
      · obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.mp hp.2.2.2.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
        exact ⟨p1, p2, hne, hp1, hp2⟩
      · intro p hp1
        by_contra hpnot
        have hsub : ({p} : Finset (Fin n)) ⊆ Pᶜ := by
          intro q hq
          rw [Finset.mem_singleton.mp hq]
          exact Finset.mem_compl.mpr hpnot
        have hfalse := wireValue_mono C hAO l hsub (n + n + g) (by change n + n + g < n + n + C.gates.length; omega) hp1
        rw [hp.2.2.2.1] at hfalse
        cases hfalse

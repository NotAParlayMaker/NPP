import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2352_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

/-- Grow a wire list by appending one value per gate. -/
def grow {α β : Type*} (f : List α → β → α) (gs : List β) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem grow_append {α β : Type*} (f : List α → β → α)
    (gs hs : List β) (w : List α) :
    grow f (gs ++ hs) w = grow f hs (grow f gs w) := by
  simp [grow, List.foldl_append]

theorem grow_prefix {α β : Type*} (f : List α → β → α) (gs : List β) :
    ∀ w : List α, ∃ t : List α, grow f gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [grow], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [f w g])
    refine ⟨f w g :: t, ?_, by simp [hl]⟩
    change grow f gs (w ++ [f w g]) = w ++ f w g :: t
    rw [ht]
    simp

theorem grow_length {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) :
    (grow f gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := grow_prefix f gs w
  rw [ht]
  simp [hl]

theorem grow_getD_lt {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (i : ℕ) (d : α) (h : i < w.length) :
    (grow f gs w).getD i d = w.getD i d := by
  obtain ⟨t, ht, _⟩ := grow_prefix f gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem grow_gate {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (d : α) (j : ℕ) (hj : j < gs.length) :
    (grow f gs w).getD (w.length + j) d = f (grow f (gs.take j) w) gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set A := grow f (gs.take j) w with hA
  have hAl : A.length = w.length + j := by
    rw [hA, grow_length]
    simp
    omega
  have hw : grow f gs w = grow f (gs.drop (j + 1)) (A ++ [f A gs[j]]) := by
    conv_lhs => rw [hsplit]
    rw [grow_append]
    rfl
  rw [hw, grow_getD_lt _ _ _ _ _ (by simp [hAl]),
    List.getD_append_right _ _ _ _ (by omega)]
  simp [hAl]

theorem grow_take_read {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (d : α) (j i : ℕ) (hj : j ≤ gs.length) :
    (grow f (gs.take j) w).getD i d =
      if i < w.length + j then (grow f gs w).getD i d else d := by
  have hlen : (grow f (gs.take j) w).length = w.length + j := by
    rw [grow_length, List.length_take, Nat.min_eq_left hj]
  by_cases hi : i < w.length + j
  · rw [ite_eq_left hi]
    conv_rhs => rw [← List.take_append_drop j gs, grow_append]
    exact (grow_getD_lt _ _ _ _ _ (by omega)).symm
  · rw [ite_eq_right hi]
    apply List.getD_eq_default
    omega

/-- The value produced by one gate from the current wire list. -/
def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wires_eq_grow (C : Circuit) (x : List Bool) :
    C.wires x = grow gateValue C.gates x := rfl

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  rw [wires_eq_grow, grow_length]
  rfl

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := grow_getD_lt _ _ _ _ _ hi

theorem wires_gate_prefix (C : Circuit) (x : List Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      gateValue (grow gateValue (C.gates.take j) x) C.gates[j] :=
  grow_gate _ _ _ _ _ hj

theorem wires_gate (C : Circuit) (x : List Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < x.length + j then (C.wires x).getD i false else false) := by
  rw [wires_gate_prefix C x j hj]
  unfold gateValue
  congr 1
  apply List.map_congr_left
  intro i _
  have hjle : j ≤ C.gates.length := Nat.le_of_lt hj
  exact grow_take_read _ _ _ _ j i hjle

end PEqualNP.Outside.L_meta_2352_aux

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds
open PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2352_aux

theorem L_meta_2352 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C →
      ∀ R : ℕ → ℕ → Prop,
        R = Relation.ReflTransGen
          (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
            (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
            ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) →
      ∀ T : ℕ → List (ℕ × ℕ) → Prop,
        T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop,
          (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) →
          (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
            (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            R (n + qj) qt →
            Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 →
            Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 →
            Q qt (qL1 ++ qL2)) →
          Q tt tL) →
      ∀ (top : ℕ) (L : List (ℕ × ℕ)) (z : Fin n → Bool),
        T top L →
        (∀ gv ∈ L, (C.wires (List.ofFn z)).getD (gv.1) false = true) →
        (C.wires (List.ofFn z)).getD top false = true := by
  intro n C hAO R hR T hT top L z hTL hLtrue
  let wire : ℕ → Bool := fun w => (C.wires (List.ofFn z)).getD w false
  have hgateAt : ∀ (j : ℕ) (hj : j < C.gates.length), gateAt C j = C.gates[j] := by
    intro j hj
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hj]
  have hwire_gate : ∀ (j : ℕ) (hj : j < C.gates.length),
      wire (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map wire) := by
    intro j hj
    have hx : (List.ofFn z).length = n := by simp
    have h := wires_gate C (List.ofFn z) j hj
    rw [hx] at h
    rw [hgateAt j hj]
    change (C.wires (List.ofFn z)).getD (n + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map wire)
    rw [h]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hlt : i < n + j := hAO.2.1 j hj i (by simpa [hgateAt j hj] using hi)
    simp only [wire]
    rw [if_pos (by simpa [hx] using hlt)]
  have hstep_prop : ∀ {a b : ℕ},
      (a < b ∧ ∃ rj, b = n + rj ∧ rj < C.gates.length ∧
        (gateAt C rj).op = GateOp.or ∧ a ∈ (gateAt C rj).inputs) →
      wire a = true → wire b = true := by
    rintro a b ⟨_, rj, rfl, hrj, hop, hmem⟩ ha
    rw [hwire_gate rj hrj, hop]
    apply List.any_eq_true.mpr
    exact ⟨wire a, List.mem_map_of_mem hmem, ha⟩
  have hwire_R : ∀ {a b : ℕ}, R a b → wire a = true → wire b = true := by
    intro a b hab ha
    rw [hR] at hab
    induction hab with
    | refl => exact ha
    | tail _ hstep ih => exact hstep_prop hstep ih
  rw [hT] at hTL
  have hbase : ∀ (qv qt : ℕ), qv < n → R qv qt →
      (∀ gv ∈ [(qt, qv)], wire gv.1 = true) → wire qt = true := by
    intro qv qt hqv hRqvqt hlabels
    simpa using hlabels (qt, qv) (by simp)
  have hstep : ∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)),
      qj < C.gates.length →
      (gateAt C qj).op = GateOp.and →
      R (n + qj) qt →
      ((∀ gv ∈ qL1, wire gv.1 = true) → wire ((gateAt C qj).inputs.getD 0 0) = true) →
      ((∀ gv ∈ qL2, wire gv.1 = true) → wire ((gateAt C qj).inputs.getD 1 0) = true) →
      (∀ gv ∈ qL1 ++ qL2, wire gv.1 = true) → wire qt = true := by
    intro qj qt L1 L2 hqj hAnd hRq hQ1 hQ2 hlabels
    have h1 : wire ((gateAt C qj).inputs.getD 0 0) = true :=
      hQ1 (fun gv hgv => hlabels gv (List.mem_append_left L2 hgv))
    have h2 : wire ((gateAt C qj).inputs.getD 1 0) = true :=
      hQ2 (fun gv hgv => hlabels gv (List.mem_append_right L1 hgv))
    have hlen2 : (gateAt C qj).inputs.length = 2 := by
      have hmem : gateAt C qj ∈ C.gates := by
        rw [hgateAt qj hqj]
        exact List.getElem_mem hqj
      exact hAO.2.2 _ hmem
    obtain ⟨a, b, hin⟩ := List.length_eq_two.mp hlen2
    simp [hin] at h1 h2
    have hgate : wire (n + qj) = true := by
      rw [hwire_gate qj hqj, hAnd, hin]
      simp [GateOp.eval, h1, h2]
    exact hwire_R hRq hgate
  exact hTL (fun tt tL => (∀ gv ∈ tL, wire gv.1 = true) → wire tt = true) hbase hstep hLtrue

end PEqualNP.Outside

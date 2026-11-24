import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4923_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma preserved (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma atEnd (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_out_of_bounds (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

def wireSet (n : ℕ) (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun k : Fin n =>
    (gs.foldl step (List.ofFn fun i : Fin n => decide (i = k))).getD w false = true

def prefSet (n : ℕ) (gs : List Gate) (m w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun k : Fin n =>
    ((gs.take m).foldl step (List.ofFn fun i : Fin n => decide (i = k))).getD w false = true

lemma foldl_take_append (gs : List Gate) (m : ℕ) (hm : m < gs.length) (w : List Bool) :
    (gs.take (m + 1)).foldl step w = step ((gs.take m).foldl step w) gs[m] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

lemma wire_val_at_gate (n : ℕ) (gs : List Gate) (m : ℕ) (hm : m < gs.length) (init : List Bool)
    (hlen : init.length = n) :
    (gs.foldl step init).getD (n + m) false =
      gs[m].op.eval (gs[m].inputs.map fun a => ((gs.take m).foldl step init).getD a false) := by
  have hsplit : gs = gs.take (m + 1) ++ gs.drop (m + 1) := (List.take_append_drop (m + 1) gs).symm
  conv_lhs => rw [hsplit, List.foldl_append]
  have hlen1 : ((gs.take (m + 1)).foldl step init).length = n + (m + 1) := by
    rw [foldl_step_len, hlen, List.length_take_of_le (by omega)]
  rw [preserved (gs.drop (m + 1)) _ (n + m) (by omega)]
  rw [foldl_take_append gs m hm init]
  have hlen0 : ((gs.take m).foldl step init).length = n + m := by
    rw [foldl_step_len, hlen, List.length_take_of_le (by omega)]
  rw [← hlen0]
  exact atEnd ((gs.take m).foldl step init) _

lemma card_le_one_of_lt (n : ℕ) (gs : List Gate) (w : ℕ) (hw : w < n) :
    (wireSet n gs w).card ≤ 1 := by
  have hsub : wireSet n gs w ⊆ {⟨w, hw⟩} := by
    intro k hk
    simp only [wireSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hlen : (List.ofFn fun i : Fin n => decide (i = k)).length = n := List.length_ofFn
    rw [preserved gs _ w (by omega)] at hk
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte,
      Option.getD_some, decide_eq_true_eq] at hk
    exact Finset.mem_singleton.mpr hk.symm
  exact (Finset.card_le_card hsub).trans (by simp)

lemma prefSet_mem_or_card (n : ℕ) (gs : List Gate) (m : ℕ) (hm : m ≤ gs.length) (a : ℕ)
    (outList : List (Finset (Fin n)))
    (hout : outList = List.ofFn fun j : Fin gs.length => wireSet n gs (n + j.val)) :
    (prefSet n gs m a).card ≤ 1 ∨ prefSet n gs m a ∈ outList.take m := by
  by_cases ha1 : a < n
  · left
    exact card_le_one_of_lt n (gs.take m) a ha1
  · by_cases ha2 : a < n + m
    · right
      have hidx : a - n < m := by omega
      have hlt : a - n < gs.length := by omega
      have hmem : outList[a - n]? = some (wireSet n gs (n + (a - n))) := by
        rw [hout, List.getElem?_ofFn]
        simp [hlt]
      have htake : wireSet n gs (n + (a - n)) ∈ outList.take m := by
        rw [List.mem_iff_getElem?]
        refine ⟨a - n, ?_⟩
        rw [List.getElem?_take_of_lt hidx, hmem]
      have heq : prefSet n gs m a = wireSet n gs (n + (a - n)) := by
        ext k
        simp only [prefSet, wireSet, Finset.mem_filter, Finset.mem_univ, true_and]
        have hsum : n + (a - n) = a := by omega
        rw [hsum]
        have hsplit : gs = gs.take m ++ gs.drop m := (List.take_append_drop m gs).symm
        conv_rhs => rw [hsplit, List.foldl_append]
        have hlenm : ((gs.take m).foldl step (List.ofFn fun i : Fin n => decide (i = k))).length = n + m := by
          rw [foldl_step_len, List.length_ofFn, List.length_take_of_le hm]
        rw [preserved (gs.drop m) _ a (by omega)]
      rw [heq]
      exact htake
    · left
      have h0 : prefSet n gs m a = ∅ := by
        ext k
        simp only [prefSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, Bool.not_eq_true]
        apply getD_out_of_bounds
        rw [foldl_step_len, List.length_ofFn, List.length_take_of_le hm]
        omega
      rw [h0]
      simp

end PEqualNP.Outside.L_meta_4923_aux

theorem PEqualNP.Outside.L_meta_4923 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x3 ∈ x2.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs.length ≤ (2 : ℕ)) →     ∃ (x4 : List (Finset (Fin x1))),       x4.length ≤ x2.size ∧         (∀ (x5 : ℕ),             have x6 : Finset (Fin x1) := {x6 : Fin x1 | (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 = x6))).getD x5 Bool.false = Bool.true};             x6.card ≤ (1 : ℕ) ∨ x6 ∈ x4) ∧           ∀ (x5 : ℕ) (x6 : Finset (Fin x1)), x4[x5]? = Option.some x6 → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x1)), x6 = x8 ∪ x9 ∧ (x8.card ≤ (1 : ℕ) ∨ x8 ∈ List.take x5 x4) ∧ (x9.card ≤ (1 : ℕ) ∨ x9 ∈ List.take x5 x4) := by
  intro x1 x2 hor
  let x4 : List (Finset (Fin x1)) :=
    List.ofFn fun j : Fin x2.gates.length =>
      PEqualNP.Outside.L_meta_4923_aux.wireSet x1 x2.gates (x1 + j.val)
  refine ⟨x4, ?_, ?_, ?_⟩
  · simp [x4, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x5
    dsimp only
    have hset :
        ({x6 : Fin x1 | (x2.wires (List.ofFn fun x7 : Fin x1 => decide (x7 = x6))).getD x5 false = true} :
          Finset (Fin x1)) =
          PEqualNP.Outside.L_meta_4923_aux.wireSet x1 x2.gates x5 := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        PEqualNP.Outside.L_meta_4923_aux.wireSet]
      rfl
    rw [hset]
    by_cases h1 : x5 < x1
    · left
      exact PEqualNP.Outside.L_meta_4923_aux.card_le_one_of_lt x1 x2.gates x5 h1
    · by_cases h2 : x5 < x1 + x2.gates.length
      · right
        have hlt : x5 - x1 < x2.gates.length := by omega
        rw [List.mem_iff_getElem?]
        refine ⟨x5 - x1, ?_⟩
        simp only [x4, List.getElem?_ofFn, hlt, ↓reduceDIte]
        congr 2
        omega
      · left
        have h0 : PEqualNP.Outside.L_meta_4923_aux.wireSet x1 x2.gates x5 = ∅ := by
          ext k
          simp only [PEqualNP.Outside.L_meta_4923_aux.wireSet, Finset.mem_filter,
            Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, Bool.not_eq_true]
          apply PEqualNP.Outside.L_meta_4923_aux.getD_out_of_bounds
          rw [PEqualNP.Outside.L_meta_4923_aux.foldl_step_len, List.length_ofFn]
          omega
        rw [h0]
        simp
  · intro x5 x6 hx6
    have hx5 : x5 < x2.gates.length := by
      by_contra hge
      have hnone : x4[x5]? = none := by
        simp [x4, show ¬ x5 < x2.gates.length from hge]
      rw [hx6] at hnone
      cases hnone
    have hx6eq : x6 = PEqualNP.Outside.L_meta_4923_aux.wireSet x1 x2.gates (x1 + x5) := by
      simp only [x4, List.getElem?_ofFn, hx5, ↓reduceDIte, Option.some.injEq] at hx6
      exact hx6.symm
    have hgmem : x2.gates[x5] ∈ x2.gates := List.getElem_mem hx5
    obtain ⟨hgop, hglen⟩ := hor x2.gates[x5] hgmem
    have hchar : ∀ k : Fin x1, k ∈ x6 ↔
        ((x2.gates[x5].inputs.map fun a =>
          ((x2.gates.take x5).foldl PEqualNP.Outside.L_meta_4923_aux.step
            (List.ofFn fun i : Fin x1 => decide (i = k))).getD a false).any id) = true := by
      intro k
      rw [hx6eq]
      simp only [PEqualNP.Outside.L_meta_4923_aux.wireSet, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [PEqualNP.Outside.L_meta_4923_aux.wire_val_at_gate x1 x2.gates x5 hx5 _ List.length_ofFn]
      rw [hgop]
      rfl
    have hp : ∀ a : ℕ,
        (PEqualNP.Outside.L_meta_4923_aux.prefSet x1 x2.gates x5 a).card ≤ 1 ∨
          PEqualNP.Outside.L_meta_4923_aux.prefSet x1 x2.gates x5 a ∈ List.take x5 x4 :=
      fun a => PEqualNP.Outside.L_meta_4923_aux.prefSet_mem_or_card x1 x2.gates x5
        (Nat.le_of_lt hx5) a x4 rfl
    rcases hins : x2.gates[x5].inputs with _ | ⟨a, _ | ⟨b, t⟩⟩
    · refine ⟨∅, ∅, ?_, Or.inl (by simp), Or.inl (by simp)⟩
      ext k
      simp only [Finset.union_empty, Finset.notMem_empty, iff_false]
      intro hk
      have h := (hchar k).mp hk
      simp [hins] at h
    · refine ⟨PEqualNP.Outside.L_meta_4923_aux.prefSet x1 x2.gates x5 a, ∅, ?_, hp a, Or.inl (by simp)⟩
      ext k
      simp only [Finset.union_empty, PEqualNP.Outside.L_meta_4923_aux.prefSet,
        Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hchar k, hins]
      simp
    · cases t with
      | nil =>
        refine ⟨PEqualNP.Outside.L_meta_4923_aux.prefSet x1 x2.gates x5 a,
          PEqualNP.Outside.L_meta_4923_aux.prefSet x1 x2.gates x5 b, ?_, hp a, hp b⟩
        ext k
        simp only [Finset.mem_union, PEqualNP.Outside.L_meta_4923_aux.prefSet,
          Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hchar k, hins]
        simp
      | cons c t' =>
        rw [hins] at hglen
        simp at hglen

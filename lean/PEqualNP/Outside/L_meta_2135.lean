import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2135

open PEqualNP.CircuitLowerBounds

private def run (gates : List Gate) (inputs : List Bool) : List Bool :=
  gates.foldl (fun wires gate =>
    wires ++ [gate.op.eval (gate.inputs.map fun i => wires.getD i false)]) inputs

private lemma run_length (gates : List Gate) (inputs : List Bool) :
    (run gates inputs).length = inputs.length + gates.length := by
  induction gates generalizing inputs with
  | nil => simp [run]
  | cons gate gates ih =>
    change (run gates (inputs ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private lemma run_snoc (gates : List Gate) (gate : Gate) (inputs : List Bool) :
    run (gates ++ [gate]) inputs =
      run gates inputs ++ [gate.op.eval (gate.inputs.map fun i => (run gates inputs).getD i false)] := by
  simp [run, List.foldl_append]

-- The support argument adapts L_meta_1942. Tracing a binary gate back adds at most one wire.
private lemma supports (n : ℕ) (gates : List Gate)
    (hfan : ∀ gate ∈ gates, gate.inputs.length ≤ 2) (frontier : Finset ℕ) :
    ∃ support : Finset ℕ, support.card ≤ frontier.card + gates.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ support, x.getD i false = y.getD i false) →
        ∀ i ∈ frontier, (run gates x).getD i false = (run gates y).getD i false := by
  induction gates using List.reverseRecOn generalizing frontier with
  | nil => exact ⟨frontier, by simp, fun _ _ _ _ agree => agree⟩
  | append_singleton gates gate ih =>
    let j := n + gates.length
    let reads := gate.inputs.toFinset
    let previous := if j ∈ frontier then frontier.erase j ∪ reads else frontier
    have hprevious : previous.card ≤ frontier.card + 1 := by
      by_cases hj : j ∈ frontier
      · have hunion := Finset.card_union_le (frontier.erase j) reads
        have herase := Finset.card_erase_add_one hj
        have hreads : reads.card ≤ 2 :=
          (List.toFinset_card_le gate.inputs).trans (hfan gate (by simp))
        simp only [previous, ite_eq_left hj]
        omega
      · simp [previous, hj]
    obtain ⟨support, hsize, hagree⟩ := ih (fun g hg => hfan g (List.mem_append_left _ hg)) previous
    refine ⟨support, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy agree i hi
    have hxlen : (run gates x).length = j := by simp [run_length, hx, j]
    have hylen : (run gates y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hagree x y hx hy agree i
      by_cases hj : j ∈ frontier
      · simpa [previous, hj] using
          Finset.mem_union_left reads (Finset.mem_erase.mpr ⟨hlt.ne, hi⟩)
      · simpa [previous, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [hxlen, hylen, Nat.sub_self, List.getD_cons_zero]
      apply congrArg gate.op.eval
      apply List.map_congr_left
      intro k hk
      apply hagree x y hx hy agree k
      simpa [previous, hi, reads] using
        Finset.mem_union_right (frontier.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma essential_bound {n : ℕ} (C : Circuit)
    (hfan : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2)
    (essential : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) : n ≤ C.size + 1 := by
  obtain ⟨support, hsize, hagree⟩ := supports n C.gates hfan {C.output}
  suffices hall : Finset.range n ⊆ support by
    have hcard := Finset.card_le_card hall
    simp only [Finset.card_range] at hcard
    simp only [Finset.card_singleton] at hsize
    unfold Circuit.size
    omega
  intro i hi
  by_contra hmissing
  let input : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨x, y, hxy, hne⟩ := essential input
  apply hne
  apply hagree (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro j hj
  by_cases hlt : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt),
      List.getD_eq_getElem _ _ (by simpa using hlt)]
    simp only [List.getElem_ofFn]
    apply hxy
    intro heq
    have hindex : j = i := congrArg Fin.val heq
    exact hmissing (hindex ▸ hj)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hlt),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hlt)]

private def edge (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
    (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4)

private def partner (i : Fin 5) : Fin 5 := if i.val < 2 then 2 else 0

private def without (i j : Fin 5) : Bool := decide (j = partner i)

private def withInput (i j : Fin 5) : Bool := without i j || decide (j = i)

private lemma edge_changes : ∀ i : Fin 5, edge (without i) ≠ edge (withInput i) := by
  decide

end PEqualNP.Outside.L_meta_2135

theorem PEqualNP.Outside.L_meta_2135 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun z : Fin 5 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 0 && z 4) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4)) x) → 4 ≤ C.size := by
  intro C hmono _ hcorrect
  have hsize : 5 ≤ C.size + 1 := by
    apply PEqualNP.Outside.L_meta_2135.essential_bound C (fun g hg => (hmono g hg).2)
    intro i
    refine ⟨PEqualNP.Outside.L_meta_2135.without i, PEqualNP.Outside.L_meta_2135.withInput i, ?_, ?_⟩
    · intro j hj
      simp [PEqualNP.Outside.L_meta_2135.withInput, hj]
    · rw [hcorrect, hcorrect]
      exact PEqualNP.Outside.L_meta_2135.edge_changes i
  omega

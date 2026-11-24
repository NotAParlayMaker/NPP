import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2058_773
    (small : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → q ≤ 222 → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, {p : Fin N | I p l}.ncard = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = decide
        (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      N * (q + 1) ≤ 112 * C.size)
    (star : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = decide
        (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      let clean := fun e : Fin N × Fin N =>
        ∃ u v : Fin (N + N), s(u, v) = s(Fin.castAdd N e.1, Fin.natAdd N e.2) ∧
          ((∃ w < N + N + C.size, let S := orIn (N + N) C w
            2 ≤ S.card ∧ v ∈ S ∧ ∀ z ∈ S, circuitFun (N + N) C (pairInput u z) = true) ∨
            ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ side C j 0 = {u} ∧ side C j 1 = {v})
      {e : Fin N × Fin N | I e.1 e.2 ∧ clean e}.ncard ≤ 3 * C.size)
    (remaining : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      222 < q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, {p : Fin N | I p l}.ncard = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = decide
        (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      PEqualNP.ReadK.IsReadK (N + N) C 2 →
      let clean := fun e : Fin N × Fin N =>
        ∃ u v : Fin (N + N), s(u, v) = s(Fin.castAdd N e.1, Fin.natAdd N e.2) ∧
          ((∃ w < N + N + C.size, let S := orIn (N + N) C w
            2 ≤ S.card ∧ v ∈ S ∧ ∀ z ∈ S, circuitFun (N + N) C (pairInput u z) = true) ∨
            ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ side C j 0 = {u} ∧ side C j 1 = {v})
      {e : Fin N × Fin N | I e.1 e.2 ∧ ¬ clean e}.ncard ≤ 109 * C.size) :
  ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * (q + 1) ≤ 112 * C.size := by
  intro q N I _ C qLower plane degrees uniqueLine circuitModel correct readTwo
  have setDegrees (l : Fin N) : {p : Fin N | I p l}.ncard = q + 1 := by
    have asFinset : ({p : Fin N | I p l} : Set (Fin N)) =
        ↑(Finset.univ.filter fun p : Fin N => I p l) := by
      ext p
      simp
    rw [asFinset, Set.ncard_coe_finset, degrees]
  by_cases qSmall : q ≤ 222
  · exact small q N I C qLower qSmall plane setDegrees uniqueLine circuitModel correct
  classical
  let clean := fun e : Fin N × Fin N =>
    ∃ u v : Fin (N + N), s(u, v) = s(Fin.castAdd N e.1, Fin.natAdd N e.2) ∧
      ((∃ w < N + N + C.size, let S := orIn (N + N) C w
        2 ≤ S.card ∧ v ∈ S ∧ ∀ z ∈ S, circuitFun (N + N) C (pairInput u z) = true) ∨
        ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ side C j 0 = {u} ∧ side C j 1 = {v})
  let incidences := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2
  have count : incidences.card = N * (q + 1) := by
    let columns := fun l : Fin N => (Finset.univ.filter fun p => I p l).image fun p => (p, l)
    have parts : incidences = Finset.univ.biUnion columns := by
      ext e
      obtain ⟨p, l⟩ := e
      simp only [incidences, columns, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro h
        exact ⟨l, p, h, rfl, rfl⟩
      · rintro ⟨a, b, h, rfl, rfl⟩
        exact h
    have columnCount (l : Fin N) : (columns l).card = q + 1 := by
      have injective : Function.Injective (fun p : Fin N => (p, l)) :=
        fun _ _ h => congrArg Prod.fst h
      dsimp [columns]
      rw [Finset.card_image_of_injective _ injective, degrees]
    rw [parts, Finset.card_biUnion]
    · simp [columnCount, nsmul_eq_mul]
    · intro a _ b _ hdiff
      apply Finset.disjoint_left.mpr
      intro e ha hb
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨_, _, he⟩ := Finset.mem_image.mp hb
      exact hdiff (congrArg Prod.snd he).symm
  have starCount := star N I C uniqueLine circuitModel correct
  have restCount := remaining q N I C (Nat.lt_of_not_ge qSmall) plane setDegrees uniqueLine circuitModel correct readTwo
  have coveredSet : (↑(incidences.filter clean) : Set (Fin N × Fin N)) =
      {e | I e.1 e.2 ∧ clean e} := by
    ext e
    simp [incidences]
  have restSet : (↑(incidences.filter fun e => ¬ clean e) : Set (Fin N × Fin N)) =
      {e | I e.1 e.2 ∧ ¬ clean e} := by
    ext e
    simp [incidences]
  change {e : Fin N × Fin N | I e.1 e.2 ∧ clean e}.ncard ≤ 3 * C.size at starCount
  change {e : Fin N × Fin N | I e.1 e.2 ∧ ¬ clean e}.ncard ≤ 109 * C.size at restCount
  rw [← coveredSet, Set.ncard_coe_finset] at starCount
  rw [← restSet, Set.ncard_coe_finset] at restCount
  have split := Finset.card_filter_add_card_filter_not (s := incidences) clean
  omega

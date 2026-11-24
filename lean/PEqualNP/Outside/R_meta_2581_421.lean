import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_2581_421
    (good : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
        readsAtMost C (N+N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 2 = true)).card ≤ 100 * C.size)
    (bad : ∃ k : ℕ, ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      IsReadK (N+N) C 3 →
      (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
        readsAtMost C (N+N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 2 = false)).card ≤ k * C.size) :
    ∃ c : ℕ, ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 3 → N * q ≤ c * C.size := by
  obtain ⟨k, hk⟩ := bad
  refine ⟨100+k, ?_⟩
  intro q N I inst C hq hN hL hU hAO hC hr
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  let G : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2 ∧
    readsAtMost C (N+N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 2 = true)
  let B : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2 ∧
    readsAtMost C (N+N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 2 = false)
  have hG : G.card ≤ 100*C.size := good q N I C hq hN hL hU hAO hC
  have hB : B.card ≤ k*C.size := hk q N I C hq hN hL hU hAO hC hr
  have hsplit : E ⊆ G ∪ B := by
    intro e he
    have hi : I e.1 e.2 := (Finset.mem_filter.mp he).2
    cases heq : readsAtMost C (N+N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 2
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, heq⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, heq⟩)
  let F (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter (fun p => I p l)).map ⟨fun p => (p,l), fun _ _ h => congrArg Prod.fst h⟩
  have hF (l : Fin N) (e : Fin N × Fin N) : e ∈ F l ↔ I e.1 l ∧ e.2 = l := by
    constructor
    · intro he
      obtain ⟨p,hp,ht⟩ := Finset.mem_map.mp he
      change (p,l) = e at ht
      rw [← ht]
      exact ⟨(Finset.mem_filter.mp hp).2,rfl⟩
    · rintro ⟨hi,hh⟩
      refine Finset.mem_map.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,?_⟩
      exact Prod.ext rfl hh.symm
  have heq : E = Finset.univ.biUnion F := by
    ext e
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,hF]
    exact ⟨fun h => ⟨e.2,h,rfl⟩, fun ⟨l,hi,he⟩ => he ▸ hi⟩
  have hE : E.card = N*(q+1) := by
    rw [heq, Finset.card_biUnion]
    · simp [F,hL]
    · intro l _ l' _ hne
      refine Finset.disjoint_left.mpr ?_
      intro e he he'
      exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)
  have hsum := (Finset.card_le_card hsplit).trans (Finset.card_union_le G B)
  have hqle : N*q ≤ N*(q+1) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.add_mul]
  omega

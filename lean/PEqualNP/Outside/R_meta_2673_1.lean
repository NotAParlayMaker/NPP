import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2673_1 (h1 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → (∀ p4 l4 : Fin N, I p4 l4 → PEqualNP.ReadK.readsAtMost C (N + N) [p4.val, N + l4.val] 2 = true) → ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 2 ∧ v.getD 1 0 ≤ 1))).card ≤ 10 * C.size + N) (h2 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → (∀ p4 l4 : Fin N, I p4 l4 → PEqualNP.ReadK.readsAtMost C (N + N) [p4.val, N + l4.val] 2 = true) → ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 1 ∧ v.getD 1 0 ≤ 2))).card ≤ 10 * C.size + N) (h3 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → (∀ p4 l4 : Fin N, I p4 l4 → PEqualNP.ReadK.readsAtMost C (N + N) [p4.val, N + l4.val] 2 = true) → ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ ¬ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 2 ∧ v.getD 1 0 ≤ 1) ∧ ¬ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 1 ∧ v.getD 1 0 ≤ 2))).card ≤ 79 * C.size) (h4 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → (∀ p4 l4 : Fin N, I p4 l4 → PEqualNP.ReadK.readsAtMost C (N + N) [p4.val, N + l4.val] 2 = true) → N + N ≤ C.size + 1) : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → (∀ p4 l4 : Fin N, I p4 l4 → PEqualNP.ReadK.readsAtMost C (N + N) [p4.val, N + l4.val] 2 = true) → N * q ≤ 100 * C.size := by
  intro q N I _ C hq hN hL hU hAO hacc hrej hread
  classical
  have e1 := h1 q N I C hq hN hL hU hAO hacc hrej hread
  have e2 := h2 q N I C hq hN hL hU hAO hacc hrej hread
  have e3 := h3 q N I C hq hN hL hU hAO hacc hrej hread
  have e4 := h4 q N I C hq hN hL hU hAO hacc hrej hread
  set E := (Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2) with hE
  have hcard : E.card = N * (q + 1) := by
    clear h1 h2 h3 h4 e1 e2 e3 e4 hacc hrej hread hAO hU
    rw [hE, Finset.card_eq_sum_card_fiberwise (f := fun e : Fin N × Fin N => e.2)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have hfib : ∀ l : Fin N, ((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun e : Fin N × Fin N => I e.1 e.2)).filter (fun e : Fin N × Fin N => e.2 = l) =
        ((Finset.univ : Finset (Fin N)).filter (fun p => I p l)).map
          ⟨fun p => (p, l), fun a b h => (Prod.mk.inj h).1⟩ := by
      intro l
      ext ⟨p, l'⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · rintro ⟨hi, rfl⟩
        exact ⟨p, hi, rfl⟩
      · rintro ⟨p', hi, he⟩
        cases he
        exact ⟨hi, rfl⟩
    simp only [hfib, Finset.card_map, hL, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  have hsub : E ⊆ ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 2 ∧ v.getD 1 0 ≤ 1))) ∪
      (((Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 1 ∧ v.getD 1 0 ≤ 2))) ∪
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ ¬ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 2 ∧ v.getD 1 0 ≤ 1) ∧ ¬ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 1 ∧ v.getD 1 0 ≤ 2)))) := by
    intro e he
    have hi := (Finset.mem_filter.mp he).2
    by_cases ha : (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 2 ∧ v.getD 1 0 ≤ 1)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ha⟩)
    · by_cases hb : (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 1 ∧ v.getD 1 0 ≤ 2)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hb⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ha, hb⟩))
  have hc0 := Finset.card_le_card hsub
  have hc1 := Finset.card_union_le ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 2 ∧ v.getD 1 0 ≤ 1))) (((Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 1 ∧ v.getD 1 0 ≤ 2))) ∪
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ ¬ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 2 ∧ v.getD 1 0 ≤ 1) ∧ ¬ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 1 ∧ v.getD 1 0 ≤ 2))))
  have hc2 := Finset.card_union_le ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 1 ∧ v.getD 1 0 ≤ 2))) ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ ¬ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 2 ∧ v.getD 1 0 ≤ 1) ∧ ¬ (∃ v ∈ ((PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []), v.getD 0 0 ≤ 1 ∧ v.getD 1 0 ≤ 2)))
  have hN7 : 7 ≤ N := by nlinarith
  have hexp : N * (q + 1) = N * q + N := by ring
  omega

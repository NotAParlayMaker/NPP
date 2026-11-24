import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1539

theorem main (K : Type) [Field K] [Fintype K] [DecidableEq K] (P : Finset (K × K)) (a m : K)
    (T : Finset K) (hP : 2 * P.card < Fintype.card K) (hT : 2 * T.card ≤ Fintype.card K) :
    ∃ b : K, (∀ pt ∈ P, pt.2 ≠ m * pt.1 + b) ∧ m * a + b ∉ T := by
  set B : Finset K := P.image (fun pt => pt.2 - m * pt.1) ∪ T.image (fun t => t - m * a) with hB
  have hcard : B.card < (Finset.univ : Finset K).card := by
    calc B.card ≤ (P.image (fun pt => pt.2 - m * pt.1)).card + (T.image (fun t => t - m * a)).card :=
          Finset.card_union_le _ _
      _ ≤ P.card + T.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ < Fintype.card K := by omega
      _ = (Finset.univ : Finset K).card := Finset.card_univ.symm
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨b, ?_, ?_⟩
  · intro pt hpt heq
    apply hb
    rw [hB, Finset.mem_union]
    left
    rw [Finset.mem_image]
    exact ⟨pt, hpt, by rw [heq]; ring⟩
  · intro hmem
    apply hb
    rw [hB, Finset.mem_union]
    right
    rw [Finset.mem_image]
    exact ⟨m * a + b, hmem, by ring⟩

end PEqualNP.Outside.L_meta_1539

theorem PEqualNP.Outside.L_meta_1539 : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (P : Finset (K × K)) (a m : K) (T : Finset K), 2 * P.card < Fintype.card K → 2 * T.card ≤ Fintype.card K → ∃ b : K, (∀ pt ∈ P, pt.2 ≠ m * pt.1 + b) ∧ m * a + b ∉ T := by
  intro K _ _ _ P a m T hP hT
  exact PEqualNP.Outside.L_meta_1539.main K P a m T hP hT

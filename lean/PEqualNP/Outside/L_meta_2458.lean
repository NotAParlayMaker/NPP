import Mathlib

open Configuration
open scoped LinearAlgebra.Projectivization

theorem PEqualNP.Outside.L_meta_2458 :
    ∃ (q N : ℕ) (I : Fin N → Fin N → Prop) (_ : DecidableRel I),
      201 ≤ q ∧ N = q^2 + q + 1 ∧
      (∀ l, Fintype.card {p // I p l} = q + 1) ∧
      ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l := by
  classical
  let _ : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  let K := ZMod 257
  let P := ℙ K (Fin 3 → K)
  let _ : Fintype P := Fintype.ofFinite P
  let q := ProjectivePlane.order P P
  have count : Fintype.card P = q^2 + q + 1 := ProjectivePlane.card_points P P
  have concrete : Fintype.card P = 66307 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (ℙ (ZMod 257) (Fin 3 → ZMod 257)) = _
    rw [Projectivization.card'']
    norm_num [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  have large : 201 ≤ q := by
    by_contra! small
    have sq := Nat.pow_le_pow_left (show q ≤ 200 by omega) 2
    omega
  let labels := (Fintype.equivFin P).symm
  let I (p l : Fin (Fintype.card P)) := labels p ∈ labels l
  refine ⟨q, Fintype.card P, I, Classical.decRel _, large, count, ?_, ?_⟩
  · intro l
    let fiber : {p // I p l} ≃ {p : P // p ∈ labels l} :=
      labels.subtypeEquiv fun _ => Iff.rfl
    rw [Fintype.card_congr fiber, ← Nat.card_eq_fintype_card]
    exact ProjectivePlane.pointCount_eq P (labels l)
  · intro p r ne
    obtain ⟨l, hl, unique⟩ := HasLines.existsUnique_line P P (labels p) (labels r)
      (fun h => ne (labels.injective h))
    refine ⟨labels.symm l, ?_, fun k hk => labels.injective ?_⟩
    · simpa only [I, Equiv.apply_symm_apply] using hl
    · simpa only [Equiv.apply_symm_apply] using unique (labels k) hk

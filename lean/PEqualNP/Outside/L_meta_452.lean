import Mathlib.Data.Fintype.Option
import Mathlib.LinearAlgebra.Dimension.Finite

namespace PEqualNP.Outside.L_meta_452

open scoped BigOperators

def Essential {k m : ℕ} (r : Fin k → Fin m → ℚ) (i : Fin k) : Prop :=
  r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})

-- A nonzero relation that includes an essential vector could be
-- solved for that vector. The one remaining vector is nonzero.
lemma independent_with_extra {k m : ℕ} (r : Fin k → Fin m → ℚ)
    (j : Fin k) (hj : ¬ Essential r j) (hne : r j ≠ 0) :
    let ix : Option {i : Fin k // Essential r i} → Fin k := fun x => x.elim j Subtype.val
    LinearIndependent ℚ (fun x => (⟨r (ix x), Submodule.subset_span ⟨ix x, rfl⟩⟩ :
      Submodule.span ℚ (Set.range r))) := by
  classical
  intro ix
  let S := Submodule.span ℚ (Set.range r)
  let b (x : Option {i : Fin k // Essential r i}) : S :=
    ⟨r (ix x), Submodule.subset_span ⟨ix x, rfl⟩⟩
  change LinearIndependent ℚ b
  have hinj : Function.Injective ix := by
    intro a c heq
    cases a with
    | none =>
      cases c with
      | none => rfl
      | some i =>
        change j = i.val at heq
        exact (hj (heq ▸ i.property)).elim
    | some i =>
      cases c with
      | none =>
        change i.val = j at heq
        exact (hj (heq ▸ i.property)).elim
      | some l =>
        exact congrArg some (Subtype.ext heq)
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hzero : ∑ x, c x • r (ix x) = 0 := by
    simpa [b] using congrArg S.subtype hc
  have hsome (i : {i : Fin k // Essential r i}) : c (some i) = 0 := by
    let T := Submodule.span ℚ (r '' {l | l ≠ i.val})
    have hs : (∑ x ∈ Finset.univ.erase (some i), c x • r (ix x)) ∈ T := by
      apply T.sum_mem
      intro x hx
      refine T.smul_mem _ (Submodule.subset_span ⟨ix x, ?_, rfl⟩)
      exact fun he => (Finset.mem_erase.mp hx).1 (hinj he)
    have hsum := Finset.sum_erase_add Finset.univ (fun x => c x • r (ix x))
      (Finset.mem_univ (some i))
    rw [hzero] at hsum
    have hm : c (some i) • r i.val ∈ T := by
      have he := eq_neg_of_add_eq_zero_right hsum
      change c (some i) • r i.val = _ at he
      rw [he]
      exact T.neg_mem hs
    by_contra hcoef
    exact i.property ((T.smul_mem_iff hcoef).mp hm)
  intro v
  cases v with
  | some i => exact hsome i
  | none =>
    have hz : c none • r j = 0 := by
      simpa [ix] using (Finset.sum_eq_single none (fun x _ hx => by
        cases x with
        | none => exact (hx rfl).elim
        | some i => simp [hsome i]) (by simp)).symm.trans hzero
    exact (smul_eq_zero.mp hz).resolve_right hne

end PEqualNP.Outside.L_meta_452

theorem PEqualNP.Outside.L_meta_452 :
    ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
      (∀ i, r i ≠ 0) →
      (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
      Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
        Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  classical
  intro k m r hn ⟨j, hj⟩
  let E := {i : Fin k // PEqualNP.Outside.L_meta_452.Essential r i}
  let instE : Fintype E := Fintype.ofFinite E
  have hi := PEqualNP.Outside.L_meta_452.independent_with_extra r j (fun h => h hj) (hn j)
  have h : Fintype.card (Option E) ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range r)) :=
    hi.fintype_card_le_finrank
  rw [Fintype.card_option] at h
  change Nat.card E + 1 ≤ _
  rw [Nat.card_eq_fintype_card]
  exact h

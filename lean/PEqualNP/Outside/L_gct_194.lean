import Mathlib
import PEqualNP.Defs

open Finset

lemma PEqualNP.Outside.L_gct_194_split {M : Type} [AddCommMonoid M] {n m : ℕ}
    (F : (Fin (n+1) → Fin m) → M) :
    ∑ f, F f = ∑ a, ∑ t : Fin n → Fin m, F (Fin.cons a t) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin m) _ _ (fun _ => rfl)).symm

lemma PEqualNP.Outside.L_gct_194_emb {M : Type} [AddCommMonoid M] (G : (Fin 4 → Fin 5) → M) :
    ∑ f : Fin 4 ↪ Fin 5, G f =
      ∑ f : Fin 4 → Fin 5, if Function.Injective f then G f else 0 := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (univ.filter Function.Injective) (p := Function.Injective) (by simp)]
  exact (Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding _ _) _ _ (fun _ => rfl)).symm

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  rw [PEqualNP.Outside.L_gct_194_emb (fun f => ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1))))]
  simp only [PEqualNP.Outside.L_gct_194_split, Fintype.sum_unique, Fin.sum_univ_five,
    Fin.prod_univ_four]
  simp (config := {decide := true})
  ring_nf
  simp [Complex.I_sq, Complex.I_pow_four]
  ring_nf

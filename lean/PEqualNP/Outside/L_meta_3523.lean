import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3523_aux

def G (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) : SimpleGraph (Fin (x1 + x2)) where
  Adj u v := ∃ e ∈ x3, u = Fin.castAdd x2 e.1 ∧ v = Fin.natAdd x1 e.2 ∨
    v = Fin.castAdd x2 e.1 ∧ u = Fin.natAdd x1 e.2
  symm := by
    constructor
    rintro u v ⟨e, he, h⟩
    exact ⟨e, he, h.symm⟩
  loopless := by
    constructor
    rintro u ⟨e, he, h | h⟩
    · have h1 := congrArg Fin.val h.1
      have h2 := congrArg Fin.val h.2
      have := e.1.isLt
      simp at h1 h2
      omega
    · have h1 := congrArg Fin.val h.1
      have h2 := congrArg Fin.val h.2
      have := e.1.isLt
      simp at h1 h2
      omega

def f (x1 x2 : ℕ) (e : Fin x1 × Fin x2) : Sym2 (Fin (x1 + x2)) :=
  s(Fin.castAdd x2 e.1, Fin.natAdd x1 e.2)

theorem f_inj (x1 x2 : ℕ) : Function.Injective (f x1 x2) := by
  intro e e' h
  unfold f at h
  rw [Sym2.eq_iff] at h
  have := e.1.isLt
  have := e'.1.isLt
  simp only [Fin.ext_iff] at h
  simp at h
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem edge_eq (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) :
    (G x1 x2 x3).edgeSet = ((x3.image (f x1 x2) : Finset _) : Set _) := by
  ext z
  induction z using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet]
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨e, he, h⟩
      refine ⟨e, he, ?_⟩
      unfold f
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
    · rintro ⟨e, he, h⟩
      unfold f at h
      rw [Sym2.eq_iff] at h
      refine ⟨e, he, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        exact ⟨h1.symm, h2.symm⟩
      · right
        exact ⟨h1.symm, h2.symm⟩

end PEqualNP.Outside.L_meta_3523_aux

open PEqualNP.Outside.L_meta_3523_aux in
theorem PEqualNP.Outside.L_meta_3523 : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)), x4 ⊆ x3 → (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6.1 = x8.1 → x6 = x8) → (∀ x7 ∈ x4, ∀ x9 ∈ x4, x7.2 = x9.2 → x7 = x9) → ∃ (x8 : SimpleGraph (Fin (x1 + x2))), (∀ (x9 x10 : Fin (x1 + x2)), x8.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) ∧ x8.edgeSet.ncard = x3.card ∧ ∀ (x9 : Finset (Fin (x1 + x2))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x8 x9 → x4.card ≤ x9.card := by
  classical
  intro x1 x2 x3 x4 hsub h6 h7
  refine ⟨G x1 x2 x3, fun _ _ => Iff.rfl, ?_, ?_⟩
  · rw [edge_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ (f_inj x1 x2)]
  · intro S hS
    refine Finset.card_le_card_of_injOn
      (fun e => if Fin.castAdd x2 e.1 ∈ S then Fin.castAdd x2 e.1 else Fin.natAdd x1 e.2) ?_ ?_
    · intro e he
      have hadj : (G x1 x2 x3).Adj (Fin.castAdd x2 e.1) (Fin.natAdd x1 e.2) :=
        ⟨e, hsub he, Or.inl ⟨rfl, rfl⟩⟩
      have hc := hS _ _ hadj
      simp only [Finset.mem_coe]
      split_ifs with hm
      · exact hm
      · exact hc.resolve_left hm
    · intro e he e' he' h
      simp only at h
      split_ifs at h <;>
      first
        | exact h6 _ he _ he' (Fin.castAdd_injective _ _ h)
        | exact h7 _ he _ he' (Fin.natAdd_injective _ _ h)
        | (exfalso
           have := e.1.isLt
           have := e'.1.isLt
           simp [Fin.ext_iff] at h
           omega)

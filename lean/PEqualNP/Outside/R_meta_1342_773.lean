import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_1342_773
    (search :
      let E : List (ℕ × ℕ) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      let G := edgeGraph 11 E
      let I := fun u v : Fin 11 => (u.val,v.val) ∈ E
      let independent := fun s : Finset (Fin 11) => ∀ u ∈ s, ∀ v ∈ s, ¬ I u v
      ∃ C : Circuit, IsAO2 11 C ∧ TopForm G C ∧ 3 ≤ (junk G C).card ∧ C.size ≤ 21 ∧
        (∀ u v, I u v → C.eval (List.ofFn (setInput {u,v})) = true) ∧
        (∀ S : Finset (Fin 11), independent S →
          (∀ T : Finset (Fin 11), S ⊆ T → independent T → T = S) →
          C.eval (List.ofFn (setInput S)) = false))
    (complete : ∀ (n : ℕ) (I : Fin n → Fin n → Prop) (C : Circuit), Monotone2 C →
      (∀ u v, I u v → C.eval (List.ofFn (setInput {u,v})) = true) →
      (∀ S : Finset (Fin n), (∀ u ∈ S, ∀ v ∈ S, ¬ I u v) →
        (∀ T : Finset (Fin n), S ⊆ T → (∀ u ∈ T, ∀ v ∈ T, ¬ I u v) → T = S) →
        C.eval (List.ofFn (setInput S)) = false) →
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v, I u v ∧ x u = true ∧ x v = true) :
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin 11 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧ C.size ≤ 21 := by
  obtain ⟨C, model, _, _, budget, pos, neg⟩ := search
  have mono : Monotone2 C := by
    intro g hg
    refine ⟨?_, (model.2.2 g hg).le⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using model.1 g hg
  exact ⟨C, mono, complete 11 _ C mono pos neg, budget⟩

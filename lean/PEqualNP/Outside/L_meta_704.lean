import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_704

open PEqualNP.AndCount

private lemma starCircuit_gateVal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T U : Finset (Fin n)) (j : Fin (AndCountCircuit.starCircuit G T).size) :
    (AndCountCircuit.starCircuit G T).gateVal U j = true ↔
      T.orderEmbOfFin rfl j ∈ U ∧ ∃ w ∈ U, G.Adj (T.orderEmbOfFin rfl j) w := by
  have hpos : 0 < (AndCountCircuit.starCircuit G T).size := Fin.pos j
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  unfold AndCountCircuit.gateVal
  rw [hd]
  rw [AndCountCircuit.gateValFuel, Bool.and_eq_true, AndCountCircuit.sideTrue, AndCountCircuit.sideTrue,
    decide_eq_true_eq, decide_eq_true_eq]
  simp only [AndCountCircuit.starCircuit, Finset.mem_singleton, exists_eq_left,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ht | ⟨_, hj, _⟩, ⟨w, hAdj, hw⟩ | ⟨_, hj, _⟩⟩
    · exact ⟨ht, w, hw, hAdj⟩
    · exact False.elim (Finset.notMem_empty _ hj)
    · exact False.elim (Finset.notMem_empty _ hj)
    · exact False.elim (Finset.notMem_empty _ hj)
  · rintro ⟨ht, ⟨w, hw, hAdj⟩⟩
    exact ⟨Or.inl ht, Or.inl ⟨w, hAdj, hw⟩⟩

private lemma main_proof (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (hcov : ∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) :
    (AndCountCircuit.starCircuit G T).WellFormed ∧
    (AndCountCircuit.starCircuit G T).size = T.card ∧
    ∀ I : Finset (Fin n),
      (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) →
      (∀ x : Fin n, x ∉ I → ∃ v ∈ I, G.Adj x v) →
      (AndCountCircuit.starCircuit G T).eval I = false ∧
      ∀ x : Fin n, x ∉ I → (AndCountCircuit.starCircuit G T).eval (insert x I) = true := by
  refine ⟨?_, rfl, ?_⟩
  · intro i
    exact ⟨fun j hj => False.elim (Finset.notMem_empty j hj),
      fun j hj => False.elim (Finset.notMem_empty j hj)⟩
  · intro I hind hmax
    constructor
    · rw [AndCountCircuit.eval, decide_eq_false_iff_not]
      rintro (⟨v, hv, _⟩ | ⟨j, _, hj⟩)
      · exact Finset.notMem_empty v hv
      · obtain ⟨ht, w, hw, hAdj⟩ := (starCircuit_gateVal G T I j).mp hj
        exact hind _ ht _ hw hAdj
    · intro x hx
      obtain ⟨v, hvI, hxv⟩ := hmax x hx
      have hpair : ∃ t ∈ T, t ∈ insert x I ∧ ∃ w ∈ insert x I, G.Adj t w := by
        rcases hcov x v hxv with hxT | hvT
        · exact ⟨x, hxT, Finset.mem_insert_self x I, v, Finset.mem_insert_of_mem hvI, hxv⟩
        · exact ⟨v, hvT, Finset.mem_insert_of_mem hvI, x, Finset.mem_insert_self x I, hxv.symm⟩
      rcases hpair with ⟨t, htT, htU, w, hwU, hAdj⟩
      have hmem_range : t ∈ Set.range (T.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact htT
      rcases hmem_range with ⟨j, hj⟩
      rw [AndCountCircuit.eval, decide_eq_true_eq]
      right
      refine ⟨j, Finset.mem_univ j, ?_⟩
      rw [starCircuit_gateVal G T (insert x I) j, hj]
      exact ⟨htU, w, hwU, hAdj⟩

end PEqualNP.Outside.L_meta_704

theorem PEqualNP.Outside.L_meta_704 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
    (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) →
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).WellFormed ∧
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).size = T.card ∧
      ∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ x : Fin n, x ∉ I → ∃ v ∈ I, G.Adj x v) →
        (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).eval I = false ∧
        ∀ x : Fin n, x ∉ I → (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).eval (insert x I) = true := by
  intro n G _ T hcov
  exact PEqualNP.Outside.L_meta_704.main_proof n G T hcov

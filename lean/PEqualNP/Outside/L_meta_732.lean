import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_732_aux
def E (u v : Fin 8) : Prop := (u.val,v.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4), (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)] ∨ (v.val,u.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4), (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)]
def D (u v : Fin 8) : Prop := (u.val,v.val) ∈ [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7), (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]
instance (u v : Fin 8) : Decidable (E u v) := inferInstanceAs (Decidable (_ ∨ _))
instance (u v : Fin 8) : Decidable (D u v) := inferInstanceAs (Decidable (_ ∈ (_ : List (Nat × Nat))))
theorem orient : (∀ u v, E u v ↔ (D u v ∨ D v u)) ∧ (∀ u v, D u v → ¬ D v u) := by decide +kernel
def Indep (W : Finset (Fin 8)) : Prop := ∀ u ∈ W, ∀ v ∈ W, ¬ E u v
instance (W : Finset (Fin 8)) : Decidable (Indep W) :=
  inferInstanceAs (Decidable (∀ u ∈ W, ∀ v ∈ W, ¬ E u v))
def indSets : List (Finset (Fin 8)) := [∅,{0},{1},{2},{0,2},{1,2},{3},{2,3},{4},{5},{1,5},{2,5},{1,2,5},{6},{3,6},{5,6},{7},{0,7},{1,7},{6,7}]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ind_complete : ∀ W : Finset (Fin 8), Indep W → W ∈ indSets := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 8192 in
theorem finite_list : ∀ W ∈ indSets, ∀ K ∈ indSets, Disjoint K W →
    ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D v k := by decide +kernel

theorem finite : ∀ W K : Finset (Fin 8), (∀ u ∈ W, ∀ v ∈ W, ¬ E u v) → Disjoint K W → (∀ u ∈ K, ∀ v ∈ K, ¬ E u v) → ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D v k := by
  intro W K hw hd hk
  exact finite_list W (ind_complete W hw) K (ind_complete K hk) hd
end PEqualNP.Outside.L_meta_732_aux
theorem PEqualNP.Outside.L_meta_732 :
∀ (E D : Fin 8 → Fin 8 → Prop),
  (∀ u v, E u v ↔ ((u.val, v.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
      (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)] ∨
    (v.val, u.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
      (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)])) →
  (∀ u v, D u v ↔ (u.val, v.val) ∈ [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
      (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]) →
  (∀ u v, E u v ↔ (D u v ∨ D v u)) ∧ (∀ u v, D u v → ¬ D v u) ∧
  ∀ W K : Set (Fin 8),
    (∀ u ∈ W, ∀ v ∈ W, ¬ E u v) → Disjoint K W → (∀ u ∈ K, ∀ v ∈ K, ¬ E u v) →
    ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D v k := by
  classical
  intro E D hE hD
  have he : E = L_meta_732_aux.E := by funext u v; exact propext (hE u v)
  have hd : D = L_meta_732_aux.D := by funext u v; exact propext (hD u v)
  subst E; subst D
  refine ⟨L_meta_732_aux.orient.1, L_meta_732_aux.orient.2, ?_⟩
  intro W K hw hdis hk
  have h := L_meta_732_aux.finite W.toFinset K.toFinset
  simp only [Set.mem_toFinset, Set.disjoint_toFinset] at h
  exact h hw hdis hk

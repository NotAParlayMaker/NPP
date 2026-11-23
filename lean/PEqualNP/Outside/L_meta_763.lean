import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_763

open SimpleGraph

abbrev G : SimpleGraph (Fin 6) := SimpleGraph.fromRel (fun a b =>
  (a = 0 ∧ (b = 1 ∨ b = 2)) ∨ (a = 1 ∧ b = 3) ∨ (a = 4 ∧ b = 5))

abbrev side (a b z : Fin 6) : Bool :=
  if min a b = 0 ∧ max a b = 1 then decide (z = 1 ∨ z = 3) else decide (z = max a b)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 512 in
lemma side_adj : ∀ a b x y : Fin 6, G.Adj a b →
    (G.deleteEdges {s(a, b)}).Adj x y → (side a b x = true ↔ side a b y = true) := by
  simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  decide

lemma side_sep : ∀ a b : Fin 6, G.Adj a b → ¬ (side a b a = true ↔ side a b b = true) := by
  decide

lemma walk_side {a b u v : Fin 6} (hab : G.Adj a b)
    (p : (G.deleteEdges {s(a, b)}).Walk u v) : side a b u = true ↔ side a b v = true := by
  induction p with
  | nil => exact Iff.rfl
  | cons hadj _ ih => exact (side_adj a b _ _ hab hadj).trans ih

lemma forest : G.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge]
  intro e he
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    rw [SimpleGraph.isBridge_iff]
    rintro ⟨p⟩
    exact side_sep a b he (walk_side he p)

lemma edge : G.Adj 0 1 := by decide

lemma edgeCount : G.edgeFinset.card = 4 := by decide

abbrev cover : Finset (Fin 6) := {0, 1, 4}

lemma covers : ∀ a b : Fin 6, G.Adj a b → a ∈ cover ∨ b ∈ cover := by decide

lemma coverLower (T : Finset (Fin 6))
    (hT : ∀ a b : Fin 6, G.Adj a b → a ∈ T ∨ b ∈ T) : 3 ≤ T.card := by
  have h02 := hT 0 2 (by decide)
  have h13 := hT 1 3 (by decide)
  have h45 := hT 4 5 (by decide)
  rcases h02 with h0 | h2 <;> rcases h13 with h1 | h3 <;> rcases h45 with h4 | h5
  · have hsub : ({0, 1, 4} : Finset (Fin 6)) ⊆ T := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    exact le_trans (by decide) (Finset.card_le_card hsub)
  · have hsub : ({0, 1, 5} : Finset (Fin 6)) ⊆ T := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    exact le_trans (by decide) (Finset.card_le_card hsub)
  · have hsub : ({0, 3, 4} : Finset (Fin 6)) ⊆ T := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    exact le_trans (by decide) (Finset.card_le_card hsub)
  · have hsub : ({0, 3, 5} : Finset (Fin 6)) ⊆ T := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    exact le_trans (by decide) (Finset.card_le_card hsub)
  · have hsub : ({2, 1, 4} : Finset (Fin 6)) ⊆ T := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    exact le_trans (by decide) (Finset.card_le_card hsub)
  · have hsub : ({2, 1, 5} : Finset (Fin 6)) ⊆ T := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    exact le_trans (by decide) (Finset.card_le_card hsub)
  · have hsub : ({2, 3, 4} : Finset (Fin 6)) ⊆ T := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    exact le_trans (by decide) (Finset.card_le_card hsub)
  · have hsub : ({2, 3, 5} : Finset (Fin 6)) ⊆ T := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    exact le_trans (by decide) (Finset.card_le_card hsub)

set_option maxRecDepth 10000 in
lemma eval_eq : ∀ x : Fin 6 → Bool,
    decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) := by
  decide

end PEqualNP.Outside.L_meta_763

open PEqualNP.Outside.L_meta_763

theorem PEqualNP.Outside.L_meta_763 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  intro s
  rw [← funext eval_eq]
  constructor
  · intro h
    have bound := PEqualNP.MetaComplexity.L104 6 3 s G forest ⟨0, 1, edge⟩ coverLower h
    rw [edgeCount] at bound
    omega
  · intro hs
    have upper := PEqualNP.MetaComplexity.L105 6 G cover ⟨0, 1, edge⟩ covers
    have coverCount : cover.card = 3 := by decide
    rw [edgeCount, coverCount] at upper
    obtain ⟨C, hC, hsize, heval⟩ := upper
    exact ⟨C, hC, by omega, heval⟩

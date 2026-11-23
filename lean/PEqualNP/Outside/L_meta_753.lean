import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_753_aux

def E (i j : Fin 5) : Bool :=
  (i.val = 0 && j.val = 1) || (i.val = 1 && j.val = 0) || (i.val = 0 && j.val = 2) ||
  (i.val = 2 && j.val = 0) || (i.val = 3 && j.val = 4) || (i.val = 4 && j.val = 3)

def G : SimpleGraph (Fin 5) where
  Adj i j := E i j = true
  symm := ⟨fun i j h => by fin_cases i <;> fin_cases j <;> simp_all [E]⟩
  loopless := ⟨fun i h => by fin_cases i <;> simp_all [E]⟩

def instG : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (E i j = true))

theorem sep {H : SimpleGraph (Fin 5)} (S : Fin 5 → Bool) (h : ∀ a b, H.Adj a b → S a = S b)
    {u v : Fin 5} (hr : H.Reachable u v) : S u = S v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons ha _ ih => exact (h _ _ ha).trans ih

theorem acyc : G.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  rw [SimpleGraph.isBridge_iff]
  intro hr
  have key : ∀ S : Fin 5 → Bool, (∀ x y, (G.deleteEdges {s(a, b)}).Adj x y → S x = S y) → S a = S b :=
    fun S h => sep S h hr
  simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at key
  change E a b = true at hab
  fin_cases a <;> fin_cases b <;> simp [E] at hab
  · have := key (fun w => decide (w = 0 ∨ w = 2)) (by intro x y; change E x y = true ∧ _ → _; fin_cases x <;> fin_cases y <;> simp [E])
    simp at this
  · have := key (fun w => decide (w = 0 ∨ w = 1)) (by intro x y; change E x y = true ∧ _ → _; fin_cases x <;> fin_cases y <;> simp [E])
    simp at this
  · have := key (fun w => decide (w = 1)) (by intro x y; change E x y = true ∧ _ → _; fin_cases x <;> fin_cases y <;> simp [E])
    simp at this
  · have := key (fun w => decide (w = 2)) (by intro x y; change E x y = true ∧ _ → _; fin_cases x <;> fin_cases y <;> simp [E])
    simp at this
  · have := key (fun w => decide (w = 3)) (by intro x y; change E x y = true ∧ _ → _; fin_cases x <;> fin_cases y <;> simp [E])
    simp at this
  · have := key (fun w => decide (w = 4)) (by intro x y; change E x y = true ∧ _ → _; fin_cases x <;> fin_cases y <;> simp [E])
    simp at this

theorem hP : ∀ x : Fin 5 → Bool, ((x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) = true ↔
    ∃ i j : Fin 5, G.Adj i j ∧ x i = true ∧ x j = true := by
  change ∀ x : Fin 5 → Bool, _ ↔ ∃ i j : Fin 5, E i j = true ∧ x i = true ∧ x j = true
  decide

theorem cover : ∀ T : Finset (Fin 5), (∀ i j : Fin 5, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  change ∀ T : Finset (Fin 5), (∀ i j : Fin 5, E i j = true → i ∈ T ∨ j ∈ T) → 2 ≤ T.card
  decide

end PEqualNP.Outside.L_meta_753_aux

open PEqualNP.Outside.L_meta_753_aux in
theorem PEqualNP.Outside.L_meta_753 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) s ↔ 4 ≤ s := by
  intro s
  letI : DecidableRel G.Adj := instG
  have hc : G.edgeFinset.card = 3 := by decide
  constructor
  · intro h
    obtain ⟨C, h1, h2, h3⟩ := h
    have := PEqualNP.MetaComplexity.L104 5 2 s G acyc ⟨0, 1, show E 0 1 = true by decide⟩ cover
      ⟨C, h1, h2, fun x => by rw [h3 x]; exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff]; exact hP x)⟩
    omega
  · intro hs
    obtain ⟨C, h1, h2, h3⟩ := PEqualNP.MetaComplexity.L105 5 G {0, 3} ⟨0, 1, show E 0 1 = true by decide⟩
      (by change ∀ i j : Fin 5, E i j = true → i ∈ ({0, 3} : Finset (Fin 5)) ∨ j ∈ ({0, 3} : Finset (Fin 5)); decide)
    have h4 : ({0, 3} : Finset (Fin 5)).card = 2 := by decide
    refine ⟨C, h1, by omega, fun x => ?_⟩
    rw [h3 x]
    exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff]; exact (hP x).symm)

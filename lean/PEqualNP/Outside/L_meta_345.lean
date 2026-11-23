import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Bowtie345

private abbrev edges : List (Fin 5 × Fin 5) := [(0,1),(0,2),(1,2),(0,3),(0,4),(3,4)]

private def works (S : Finset (Fin 5 × Fin 5)) (C : Finset (Fin 5)) : Prop :=
  (∀ A ∈ C.powerset, A.Nonempty → A ≠ C → ∃ e ∈ S,
    (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧
  (∀ a b : Fin 5, a ∉ C → b ∉ C →
    (∃ x ∈ C, (x,a) ∈ S ∨ (a,x) ∈ S) → (∃ y ∈ C, (y,b) ∈ S ∨ (b,y) ∈ S) →
    ¬ ((a,b) ∈ edges ∨ (b,a) ∈ edges)) ∧
  (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1

set_option synthInstance.maxSize 4096 in
private def decWorks (S : Finset (Fin 5 × Fin 5)) (C : Finset (Fin 5)) : Decidable (works S C) := by
  unfold works
  infer_instance

private def pick (b : Bool) (e : Fin 5 × Fin 5) : Finset (Fin 5 × Fin 5) :=
  if b then {e} else ∅

private def graph (a b c d e f : Bool) :=
  pick a (0,1) ∪ pick b (0,2) ∪ pick c (1,2) ∪ pick d (0,3) ∪ pick e (0,4) ∪ pick f (3,4)

private theorem represent (S : Finset (Fin 5 × Fin 5)) (hs : ∀ q ∈ S, q ∈ edges) :
    S = graph (decide ((0,1) ∈ S)) (decide ((0,2) ∈ S)) (decide ((1,2) ∈ S))
      (decide ((0,3) ∈ S)) (decide ((0,4) ∈ S)) (decide ((3,4) ∈ S)) := by
  classical
  have hp (q r : Fin 5 × Fin 5) : q ∈ pick (decide (r ∈ S)) r ↔ q = r ∧ r ∈ S := by
    by_cases h : r ∈ S <;> simp [pick,h]
  ext q
  simp only [graph, Finset.mem_union, hp]
  constructor
  · intro h
    have he := hs q h
    simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [h]
  · rintro (((((⟨rfl,h⟩ | ⟨rfl,h⟩) | ⟨rfl,h⟩) | ⟨rfl,h⟩) | ⟨rfl,h⟩) | ⟨rfl,h⟩) <;> exact h

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
private theorem checked (a b c d e f : Bool) :
    (graph a b c d e f).Nonempty → ∃ C : Finset (Fin 5), works (graph a b c d e f) C := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f
  · simp [graph, pick]
  · intro _
    exact ⟨{3}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{3}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0,3}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{0,1}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{3}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{4}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{3}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{3}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{4}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{3}, @of_decide_eq_true _ (decWorks _ _) rfl⟩
  · intro _
    exact ⟨{1,2}, @of_decide_eq_true _ (decWorks _ _) rfl⟩

end PEqualNP.Outside.Bowtie345

open PEqualNP.Outside.Bowtie345 in
theorem PEqualNP.Outside.L_meta_345 :
    ∀ E : List (Fin 5 × Fin 5), E = [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] → ∀ S : Finset (Fin 5 × Fin 5), (∀ e ∈ S, e ∈ E) → S.Nonempty → ∃ C : Finset (Fin 5), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 5, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  rintro _ rfl S hS hn
  have he := represent S hS
  have hg := he ▸ hn
  obtain ⟨C,h⟩ := checked _ _ _ _ _ _ hg
  rw [← he] at h
  obtain ⟨hc,hb,hp⟩ := h
  exact ⟨C, fun A hA => hc A (Finset.mem_powerset.mpr hA), hb, hp⟩

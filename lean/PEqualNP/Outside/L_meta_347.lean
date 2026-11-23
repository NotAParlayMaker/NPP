import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_347_aux

private def netEdges : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)]

private def vertices : List (Fin 6) := List.finRange 6

private def checkNetWitness (S : Finset (Fin 6 × Fin 6)) (C : Finset (Fin 6)) : Bool :=
  (vertices.sublists.all fun l =>
    let A := l.toFinset
    decide (A ⊆ C ∧ A.Nonempty ∧ A ≠ C) == false ||
    netEdges.any fun e => decide (e ∈ S ∧
      ((e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)))) &&
  (vertices.all fun a => vertices.all fun b =>
    decide (a ∈ C ∨ b ∈ C ∨ ¬ ((a, b) ∈ netEdges ∨ (b, a) ∈ netEdges)) ||
    !(vertices.any fun x => decide (x ∈ C ∧ ((x, a) ∈ S ∨ (a, x) ∈ S))) ||
    !(vertices.any fun y => decide (y ∈ C ∧ ((y, b) ∈ S ∨ (b, y) ∈ S)))) &&
  decide ((S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checkedNet :
    (netEdges.sublists.all fun l =>
      let S := l.toFinset
      decide (S = ∅) ||
      ([{0}, {1}, {2}, {3}, {4}, {5}, {0, 1}] : List (Finset (Fin 6))).any
        (checkNetWitness S)) = true := by
  decide

private theorem chooseSublist {α : Type} [DecidableEq α] (l : List α) (S : Finset α)
    (h : ∀ a ∈ S, a ∈ l) : ∃ l' ∈ l.sublists, l'.toFinset = S := by
  refine ⟨l.filter (fun a => decide (a ∈ S)), List.mem_sublists.mpr List.filter_sublist, ?_⟩
  ext a
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun ha => ⟨h a ha, ha⟩⟩

end PEqualNP.Outside.L_meta_347_aux

open PEqualNP.Outside.L_meta_347_aux in
theorem PEqualNP.Outside.L_meta_347 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] → ∀ S : Finset (Fin 6 × Fin 6), (∀ e ∈ S, e ∈ E) → S.Nonempty → ∃ C : Finset (Fin 6), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 6, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  intro E hE S hS hne
  subst E
  change (∀ e ∈ S, e ∈ netEdges) at hS
  obtain ⟨l, hl, hls⟩ := chooseSublist netEdges S hS
  have hc := List.all_eq_true.mp checkedNet l hl
  rw [hls] at hc
  have hns : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hne
  simp only [hns, decide_false, Bool.false_or, List.any_eq_true] at hc
  obtain ⟨C, -, hC⟩ := hc
  simp only [checkNetWitness, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    List.any_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨hconn, hind⟩, hodd⟩ := hC
  refine ⟨C, ?_, ?_, hodd⟩
  · intro A hA hAn hAC
    obtain ⟨la, hla, hlaA⟩ := chooseSublist vertices A (by
      intro a _
      simp [vertices])
    have hv := hconn la hla
    rw [hlaA] at hv
    have hgood : A ⊆ C ∧ A.Nonempty ∧ A ≠ C := ⟨hA, hAn, hAC⟩
    obtain ⟨e, -, he, hh⟩ := hv.resolve_left (by simp [hgood])
    exact ⟨e, he, hh⟩
  · intro a b ha hb hxa hyb he
    obtain ⟨x, hx, hxa⟩ := hxa
    obtain ⟨y, hy, hyb⟩ := hyb
    have hv := hind a (by simp [vertices]) b (by simp [vertices])
    have hx' : (vertices.any fun x => decide (x ∈ C ∧ ((x, a) ∈ S ∨ (a, x) ∈ S))) = true :=
      List.any_eq_true.mpr ⟨x, by simp [vertices], decide_eq_true ⟨hx, hxa⟩⟩
    have hy' : (vertices.any fun y => decide (y ∈ C ∧ ((y, b) ∈ S ∨ (b, y) ∈ S))) = true :=
      List.any_eq_true.mpr ⟨y, by simp [vertices], decide_eq_true ⟨hy, hyb⟩⟩
    change (a, b) ∈ netEdges ∨ (b, a) ∈ netEdges at he
    rcases hv with (h | h) | h
    · exact h.elim ha (fun h => h.elim hb (fun h => h he))
    · rw [hx'] at h
      contradiction
    · rw [hy'] at h
      contradiction

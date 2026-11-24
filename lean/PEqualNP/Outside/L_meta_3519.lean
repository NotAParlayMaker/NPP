import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3519

lemma sum_filterMap {α : Type} (l : List α) (f : α → Option (ℕ × List ℕ)) (g : α → ℕ)
    (h1 : ∀ a x, f a = some x → x.2.length = g a) (h0 : ∀ a, f a = none → g a = 0) :
    ((l.filterMap f).map (fun x => x.2.length)).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rcases hfa : f a with _ | x
    · simp [hfa, ih, h0 a hfa]
    · simp [hfa, ih, h1 a x hfa]

end PEqualNP.Outside.L_meta_3519

theorem PEqualNP.Outside.L_meta_3519 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : List (ℕ × List ℕ)), (∀ x8 ∈ x7, x8.2 ≠ [] ∧ ((x8.1 < x1 ∧ ∀ x10 ∈ x8.2, x1 ≤ x10 ∧ x10 < x1 + x2) ∨ x1 ≤ x8.1 ∧ x8.1 < x1 + x2 ∧ ∀ x10 ∈ x8.2, x10 < x1)) ∧ (∀ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ↔ ∃ x10 ∈ x7, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) ∧ (List.map (fun (x8 : ℕ × List ℕ) => x8.2.length) x7).sum + x7.length - (1 : ℕ) ≤ x3.card + x4.card + x5.card - (1 : ℕ) := by
  classical
  intro n m E A B hcov
  set sA : Fin n → Finset (Fin n × Fin m) := fun a => E.filter (fun e => e.1 = a) with hsA
  set sB : Fin m → Finset (Fin n × Fin m) :=
    fun b => (E.filter (fun e => e.1 ∉ A)).filter (fun e => e.2 = b) with hsB
  set fA : Fin n → Option (ℕ × List ℕ) := fun a =>
    if sA a = ∅ then none else some (a.val, (sA a).toList.map (fun e => n + e.2.val)) with hfA
  set fB : Fin m → Option (ℕ × List ℕ) := fun b =>
    if sB b = ∅ then none else some (n + b.val, (sB b).toList.map (fun e => e.1.val)) with hfB
  have memA : ∀ x, x ∈ A.toList.filterMap fA → ∃ a : Fin n, sA a ≠ ∅ ∧
      x = (a.val, (sA a).toList.map (fun e => n + e.2.val)) := by
    intro x hx
    obtain ⟨a, -, ha⟩ := List.mem_filterMap.1 hx
    by_cases h0 : sA a = ∅
    · simp [hfA, h0] at ha
    · refine ⟨a, h0, ?_⟩
      simp only [hfA, h0, ite_false, Option.some.injEq] at ha
      exact ha.symm
  have memB : ∀ x, x ∈ B.toList.filterMap fB → ∃ b : Fin m, sB b ≠ ∅ ∧
      x = (n + b.val, (sB b).toList.map (fun e => e.1.val)) := by
    intro x hx
    obtain ⟨b, -, hb⟩ := List.mem_filterMap.1 hx
    by_cases h0 : sB b = ∅
    · simp [hfB, h0] at hb
    · refine ⟨b, h0, ?_⟩
      simp only [hfB, h0, ite_false, Option.some.injEq] at hb
      exact hb.symm
  refine ⟨A.toList.filterMap fA ++ B.toList.filterMap fB, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨a, h0, rfl⟩ := memA x hx
      refine ⟨?_, Or.inl ⟨a.isLt, ?_⟩⟩
      · simpa [Finset.toList_eq_nil] using h0
      · intro y hy
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
        have := e.2.isLt
        omega
    · obtain ⟨b, h0, rfl⟩ := memB x hx
      refine ⟨?_, Or.inr ⟨by omega, by have := b.isLt; omega, ?_⟩⟩
      · simpa [Finset.toList_eq_nil] using h0
      · intro y hy
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
        exact e.1.isLt
  · intro p l
    constructor
    · intro hpl
      by_cases hp : p ∈ A
      · have hin : (p, l) ∈ sA p := Finset.mem_filter.2 ⟨hpl, rfl⟩
        have hne : sA p ≠ ∅ := Finset.ne_empty_of_mem hin
        refine ⟨(p.val, (sA p).toList.map (fun e => n + e.2.val)), ?_, Or.inl ⟨rfl, ?_⟩⟩
        · apply List.mem_append_left
          exact List.mem_filterMap.2 ⟨p, Finset.mem_toList.2 hp, by simp [hfA, hne]⟩
        · exact List.mem_map.2 ⟨(p, l), Finset.mem_toList.2 hin, rfl⟩
      · have hl : l ∈ B := by
          rcases hcov (p, l) hpl with h | h
          · exact absurd h hp
          · exact h
        have hin : (p, l) ∈ sB l := Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hpl, hp⟩, rfl⟩
        have hne : sB l ≠ ∅ := Finset.ne_empty_of_mem hin
        refine ⟨(n + l.val, (sB l).toList.map (fun e => e.1.val)), ?_, Or.inr ⟨rfl, ?_⟩⟩
        · apply List.mem_append_right
          exact List.mem_filterMap.2 ⟨l, Finset.mem_toList.2 hl, by simp [hfB, hne]⟩
        · exact List.mem_map.2 ⟨(p, l), Finset.mem_toList.2 hin, rfl⟩
    · rintro ⟨x, hx, h⟩
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨a, -, rfl⟩ := memA x hx
        rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩
        · have hap : a = p := Fin.ext h1
          obtain ⟨e, he, he2⟩ := List.mem_map.1 h2
          have he' : e ∈ sA a := Finset.mem_toList.1 he
          simp only [hsA, Finset.mem_filter] at he'
          have : e = (p, l) := by
            ext
            · simp [he'.2, hap]
            · first | omega | (apply Fin.ext; omega) | (simp only [Fin.ext_iff] at *; omega)
          rw [← this]; exact he'.1
        · have := a.isLt
          simp only at h1
          omega
      · obtain ⟨b, -, rfl⟩ := memB x hx
        rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
        · have := p.isLt
          simp only at h1
          omega
        · have hbl : b = l := by
            simp only at h1
            exact Fin.ext (by omega)
          obtain ⟨e, he, he2⟩ := List.mem_map.1 h2
          have he' : e ∈ sB b := Finset.mem_toList.1 he
          simp only [hsB, Finset.mem_filter] at he'
          have : e = (p, l) := by
            ext
            · first | omega | (apply Fin.ext; omega) | (simp only [Fin.ext_iff] at *; omega)
            · simp [he'.2, hbl]
          rw [← this]; exact he'.1.1
  · have hsumA : ((A.toList.filterMap fA).map (fun x => x.2.length)).sum =
        (A.toList.map (fun a => (sA a).card)).sum := by
      apply PEqualNP.Outside.L_meta_3519.sum_filterMap
      · intro a x hx
        by_cases h0 : sA a = ∅
        · simp [hfA, h0] at hx
        · simp only [hfA, h0, ite_false, Option.some.injEq] at hx
          subst hx
          simp
      · intro a hx
        by_cases h0 : sA a = ∅
        · simp [h0]
        · simp [hfA, h0] at hx
    have hsumB : ((B.toList.filterMap fB).map (fun x => x.2.length)).sum =
        (B.toList.map (fun b => (sB b).card)).sum := by
      apply PEqualNP.Outside.L_meta_3519.sum_filterMap
      · intro b x hx
        by_cases h0 : sB b = ∅
        · simp [hfB, h0] at hx
        · simp only [hfB, h0, ite_false, Option.some.injEq] at hx
          subst hx
          simp
      · intro b hx
        by_cases h0 : sB b = ∅
        · simp [h0]
        · simp [hfB, h0] at hx
    have hA : (A.toList.map (fun a => (sA a).card)).sum = (E.filter (fun e => e.1 ∈ A)).card := by
      rw [Finset.sum_map_toList]
      exact Finset.sum_card_fiberwise_eq_card_filter E A Prod.fst
    have hB : (B.toList.map (fun b => (sB b).card)).sum =
        ((E.filter (fun e => e.1 ∉ A)).filter (fun e => e.2 ∈ B)).card := by
      rw [Finset.sum_map_toList]
      exact Finset.sum_card_fiberwise_eq_card_filter _ B Prod.snd
    have hBle : ((E.filter (fun e => e.1 ∉ A)).filter (fun e => e.2 ∈ B)).card ≤
        (E.filter (fun e => e.1 ∉ A)).card := Finset.card_filter_le _ _
    have hsplit : (E.filter (fun e => e.1 ∈ A)).card + (E.filter (fun e => e.1 ∉ A)).card = E.card :=
      Finset.card_filter_add_card_filter_not _
    have hlA : (A.toList.filterMap fA).length ≤ A.card :=
      (List.length_filterMap_le _ _).trans (by simp)
    have hlB : (B.toList.filterMap fB).length ≤ B.card :=
      (List.length_filterMap_le _ _).trans (by simp)
    rw [List.map_append, List.sum_append, List.length_append, hsumA, hsumB, hA, hB]
    omega

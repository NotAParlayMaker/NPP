import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3519

-- Edges at a cover point, plus edges at a cover line whose point is not a cover point,
-- count each edge at most once.
theorem count (Np Nl : ℕ) (E : Finset (Fin Np × Fin Nl)) (A : Finset (Fin Np))
    (B : Finset (Fin Nl)) :
    ∑ p ∈ A, (Finset.univ.filter (fun l : Fin Nl => (p, l) ∈ E)).card +
      ∑ l ∈ B, (Finset.univ.filter (fun p : Fin Np => (p, l) ∈ E ∧ p ∉ A)).card ≤ E.card := by
  classical
  have hE : E.card = ∑ p : Fin Np, ∑ l : Fin Nl, (if (p, l) ∈ E then 1 else 0) := by
    rw [← Fintype.sum_prod_type (f := fun e => if e ∈ E then 1 else 0), ← Finset.card_filter]
    congr 1; ext e; simp
  have h1 : ∑ p ∈ A, (Finset.univ.filter (fun l : Fin Nl => (p, l) ∈ E)).card =
      ∑ p : Fin Np, ∑ l : Fin Nl, (if p ∈ A ∧ (p, l) ∈ E then 1 else 0) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ A)]
    have e0 : ∑ p ∈ Finset.univ.filter (fun p => ¬ p ∈ A), ∑ l : Fin Nl,
        (if p ∈ A ∧ (p, l) ∈ E then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero; intro p hp
      simp only [Finset.mem_filter] at hp
      simp [hp.2]
    rw [e0, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl; intro p hp
    rw [Finset.card_filter]; simp [hp]
  have h2 : ∑ l ∈ B, (Finset.univ.filter (fun p : Fin Np => (p, l) ∈ E ∧ p ∉ A)).card ≤
      ∑ p : Fin Np, ∑ l : Fin Nl, (if (p, l) ∈ E ∧ p ∉ A then 1 else 0) := by
    rw [Finset.sum_comm]
    calc _ = ∑ l ∈ B, ∑ p : Fin Np, (if (p, l) ∈ E ∧ p ∉ A then 1 else 0) :=
          Finset.sum_congr rfl (fun l _ => Finset.card_filter _ _)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
  rw [hE, h1]
  refine (Nat.add_le_add_left h2 _).trans ?_
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro l _
  by_cases hA : p ∈ A <;> by_cases hE' : (p, l) ∈ E <;> simp [hA, hE']

end PEqualNP.Outside.L_meta_3519

theorem PEqualNP.Outside.L_meta_3519 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : List (ℕ × List ℕ)), (∀ x8 ∈ x7, x8.2 ≠ [] ∧ ((x8.1 < x1 ∧ ∀ x10 ∈ x8.2, x1 ≤ x10 ∧ x10 < x1 + x2) ∨ x1 ≤ x8.1 ∧ x8.1 < x1 + x2 ∧ ∀ x10 ∈ x8.2, x10 < x1)) ∧ (∀ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ↔ ∃ x10 ∈ x7, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) ∧ (List.map (fun (x8 : ℕ × List ℕ) => x8.2.length) x7).sum + x7.length - (1 : ℕ) ≤ x3.card + x4.card + x5.card - (1 : ℕ) := by
  classical
  intro Np Nl E A B hcov
  let LP : Fin Np → List ℕ := fun p =>
    (Finset.univ.filter (fun l : Fin Nl => (p, l) ∈ E)).toList.map (fun l => Np + l.val)
  let LL : Fin Nl → List ℕ := fun l =>
    (Finset.univ.filter (fun p : Fin Np => (p, l) ∈ E ∧ p ∉ A)).toList.map (fun p => p.val)
  let S0 : List (ℕ × List ℕ) :=
    A.toList.map (fun p => (p.val, LP p)) ++ B.toList.map (fun l => (Np + l.val, LL l))
  have nz : ∀ s : ℕ × List ℕ, ∀ x ∈ s.2, (!s.2.isEmpty) = true := by
    intro s x hx; cases h : s.2 with
    | nil => rw [h] at hx; simp at hx
    | cons _ _ => rfl
  refine ⟨S0.filter (fun s => !s.2.isEmpty), ?_, ?_, ?_⟩
  · intro s hs
    rw [List.mem_filter] at hs
    obtain ⟨hs, hne⟩ := hs
    refine ⟨fun h => by rw [h] at hne; simp at hne, ?_⟩
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp h
      refine Or.inl ⟨p.isLt, fun x hx => ?_⟩
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
      have := l.isLt; omega
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp h
      have := l.isLt
      refine Or.inr ⟨by omega, by omega, fun x hx => ?_⟩
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
      exact p.isLt
  · intro p l
    constructor
    · intro he
      by_cases hp : p ∈ A
      · have hm : Np + l.val ∈ LP p :=
          List.mem_map.mpr ⟨l, Finset.mem_toList.mpr (by simp [he]), rfl⟩
        exact ⟨(p.val, LP p), List.mem_filter.mpr ⟨List.mem_append_left _
          (List.mem_map.mpr ⟨p, Finset.mem_toList.mpr hp, rfl⟩), nz _ _ hm⟩, Or.inl ⟨rfl, hm⟩⟩
      · have hl : l ∈ B := (hcov _ he).resolve_left hp
        have hm : p.val ∈ LL l :=
          List.mem_map.mpr ⟨p, Finset.mem_toList.mpr (by simp [he, hp]), rfl⟩
        exact ⟨(Np + l.val, LL l), List.mem_filter.mpr ⟨List.mem_append_right _
          (List.mem_map.mpr ⟨l, Finset.mem_toList.mpr hl, rfl⟩), nz _ _ hm⟩, Or.inr ⟨rfl, hm⟩⟩
    · rintro ⟨s, hs, h⟩
      rw [List.mem_filter] at hs
      rcases List.mem_append.mp hs.1 with h' | h'
      · obtain ⟨p', -, rfl⟩ := List.mem_map.mp h'
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · obtain rfl : p' = p := Fin.ext h1
          obtain ⟨l', hl', hx⟩ := List.mem_map.mp h2
          obtain rfl : l' = l := Fin.ext (by omega)
          simpa using hl'
        · exfalso; have := p'.isLt; simp only at h1; omega
      · obtain ⟨l', -, rfl⟩ := List.mem_map.mp h'
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exfalso; have := p.isLt; simp only at h1; omega
        · obtain rfl : l' = l := Fin.ext (by simp only at h1; omega)
          obtain ⟨p', hp', hx⟩ := List.mem_map.mp h2
          obtain rfl : p' = p := Fin.ext hx
          simp only [Finset.mem_toList, Finset.mem_filter] at hp'
          exact hp'.2.1
  · have hlen : (S0.filter (fun s => !s.2.isEmpty)).length ≤ A.card + B.card := by
      refine (List.length_filter_le _ _).trans ?_
      simp [S0]
    have hsum : ((S0.filter (fun s => !s.2.isEmpty)).map (fun s => s.2.length)).sum ≤ E.card := by
      refine le_trans (List.Sublist.sum_le_sum ((List.filter_sublist).map _) (by simp)) ?_
      simp only [S0, List.map_append, List.map_map, List.sum_append, Function.comp_def, LP, LL,
        List.length_map, Finset.length_toList, Finset.sum_map_toList]
      exact PEqualNP.Outside.L_meta_3519.count Np Nl E A B
    omega

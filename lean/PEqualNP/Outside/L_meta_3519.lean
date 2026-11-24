import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3519_aux

theorem sum_filter_le (P : ℕ × List ℕ → Bool) (l : List (ℕ × List ℕ)) :
    ((l.filter P).map (fun x => x.2.length)).sum ≤ (l.map (fun x => x.2.length)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases h : P a = true
    · simp [h]
      omega
    · simp [h]
      omega

theorem cnt1 (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) :
    ∑ p ∈ x4, (Finset.univ.filter (fun l : Fin x2 => (p, l) ∈ x3)).card
      ≤ (x3.filter (fun e => e.1 ∈ x4)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (s := x3.filter (fun e => e.1 ∈ x4)) (f := Prod.fst) (t := x4)
    (fun e he => (Finset.mem_filter.1 he).2)]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.card_le_card_of_injOn (fun l => (p, l))
  · intro l hl
    simp at hl ⊢
    exact ⟨hl, hp⟩
  · intro a _ b _ h
    simpa using h

theorem cnt2 (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1))
    (x5 : Finset (Fin x2)) (hc : ∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) :
    ∑ l ∈ x5, (Finset.univ.filter (fun p : Fin x1 => (p, l) ∈ x3 ∧ p ∉ x4)).card
      ≤ (x3.filter (fun e => e.1 ∉ x4)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (s := x3.filter (fun e => e.1 ∉ x4)) (f := Prod.snd) (t := x5)
    (fun e he => (hc e (Finset.mem_filter.1 he).1).resolve_left (Finset.mem_filter.1 he).2)]
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.card_le_card_of_injOn (fun p => (p, l))
  · intro p hp
    simp at hp ⊢
    exact hp
  · intro a _ b _ h
    simpa using h

end PEqualNP.Outside.L_meta_3519_aux

open PEqualNP.Outside.L_meta_3519_aux in
theorem PEqualNP.Outside.L_meta_3519 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : List (ℕ × List ℕ)), (∀ x8 ∈ x7, x8.2 ≠ [] ∧ ((x8.1 < x1 ∧ ∀ x10 ∈ x8.2, x1 ≤ x10 ∧ x10 < x1 + x2) ∨ x1 ≤ x8.1 ∧ x8.1 < x1 + x2 ∧ ∀ x10 ∈ x8.2, x10 < x1)) ∧ (∀ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ↔ ∃ x10 ∈ x7, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) ∧ (List.map (fun (x8 : ℕ × List ℕ) => x8.2.length) x7).sum + x7.length - (1 : ℕ) ≤ x3.card + x4.card + x5.card - (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hc
  refine ⟨((x4.toList.map (fun p : Fin x1 => ((p.val, (Finset.univ.filter (fun l : Fin x2 => (p, l) ∈ x3)).toList.map (fun l : Fin x2 => x1 + l.val)) : ℕ × List ℕ))) ++ (x5.toList.map (fun l : Fin x2 => ((x1 + l.val, (Finset.univ.filter (fun p : Fin x1 => (p, l) ∈ x3 ∧ p ∉ x4)).toList.map (fun p : Fin x1 => p.val)) : ℕ × List ℕ)))).filter (fun o => decide (o.2 ≠ [])), ?_, ?_, ?_⟩
  · intro o ho
    simp only [List.mem_filter, List.mem_append, List.mem_map, Finset.mem_toList] at ho
    obtain ⟨(⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩), hne⟩ := ho
    · refine ⟨of_decide_eq_true hne, Or.inl ⟨p.2, ?_⟩⟩
      intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨l, -, rfl⟩ := hy
      have := l.2
      omega
    · refine ⟨of_decide_eq_true hne, Or.inr ⟨by omega, by have := l.2; omega, ?_⟩⟩
      intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      exact p.2
  · intro p l
    constructor
    · intro h
      by_cases hp : p ∈ x4
      · have mem : x1 + l.val ∈ (Finset.univ.filter (fun l : Fin x2 => (p, l) ∈ x3)).toList.map (fun l : Fin x2 => x1 + l.val) :=
          List.mem_map.2 ⟨l, by simp [h], rfl⟩
        refine ⟨(p.val, (Finset.univ.filter (fun l : Fin x2 => (p, l) ∈ x3)).toList.map (fun l : Fin x2 => x1 + l.val)), ?_, Or.inl ⟨rfl, mem⟩⟩
        simp only [List.mem_filter, List.mem_append, List.mem_map, Finset.mem_toList]
        exact ⟨Or.inl ⟨p, hp, rfl⟩, decide_eq_true (List.ne_nil_of_mem mem)⟩
      · have hl : l ∈ x5 := (hc _ h).resolve_left hp
        have mem : p.val ∈ (Finset.univ.filter (fun q : Fin x1 => (q, l) ∈ x3 ∧ q ∉ x4)).toList.map (fun q : Fin x1 => q.val) :=
          List.mem_map.2 ⟨p, by simp [h, hp], rfl⟩
        refine ⟨(x1 + l.val, (Finset.univ.filter (fun q : Fin x1 => (q, l) ∈ x3 ∧ q ∉ x4)).toList.map (fun q : Fin x1 => q.val)), ?_, Or.inr ⟨rfl, mem⟩⟩
        simp only [List.mem_filter, List.mem_append, List.mem_map, Finset.mem_toList]
        exact ⟨Or.inr ⟨l, hl, rfl⟩, decide_eq_true (List.ne_nil_of_mem mem)⟩
    · rintro ⟨o, ho, h⟩
      simp only [List.mem_filter, List.mem_append, List.mem_map, Finset.mem_toList] at ho
      obtain ⟨(⟨p', hp', rfl⟩ | ⟨l', hl', rfl⟩), -⟩ := ho
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at h2
          obtain ⟨l'', hl'', e⟩ := h2
          have e1 : p' = p := Fin.ext h1
          have e2 : l'' = l := Fin.ext (by omega)
          subst e1 e2
          exact hl''
        · have := p'.2
          dsimp only at h1
          omega
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have := p.2
          dsimp only at h1
          omega
        · simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at h2
          obtain ⟨p'', hp'', e⟩ := h2
          have e1 : p'' = p := Fin.ext e
          have e2 : l' = l := Fin.ext (by dsimp only at h1; omega)
          subst e1 e2
          exact hp''.1
  · have hS := sum_filter_le (fun o => decide (o.2 ≠ [])) ((x4.toList.map (fun p : Fin x1 => ((p.val, (Finset.univ.filter (fun l : Fin x2 => (p, l) ∈ x3)).toList.map (fun l : Fin x2 => x1 + l.val)) : ℕ × List ℕ))) ++ (x5.toList.map (fun l : Fin x2 => ((x1 + l.val, (Finset.univ.filter (fun p : Fin x1 => (p, l) ∈ x3 ∧ p ∉ x4)).toList.map (fun p : Fin x1 => p.val)) : ℕ × List ℕ))))
    have hL := List.length_filter_le (fun o : ℕ × List ℕ => decide (o.2 ≠ [])) ((x4.toList.map (fun p : Fin x1 => ((p.val, (Finset.univ.filter (fun l : Fin x2 => (p, l) ∈ x3)).toList.map (fun l : Fin x2 => x1 + l.val)) : ℕ × List ℕ))) ++ (x5.toList.map (fun l : Fin x2 => ((x1 + l.val, (Finset.univ.filter (fun p : Fin x1 => (p, l) ∈ x3 ∧ p ∉ x4)).toList.map (fun p : Fin x1 => p.val)) : ℕ × List ℕ))))
    have c1 := cnt1 x1 x2 x3 x4
    have c2 := cnt2 x1 x2 x3 x4 x5 hc
    have c3 : (x3.filter (fun e => e.1 ∈ x4)).card + (x3.filter (fun e => e.1 ∉ x4)).card = x3.card := by
      first
        | exact Finset.card_filter_add_card_filter_not (s := x3) (fun e => e.1 ∈ x4)
    have d1 := Finset.sum_map_toList x4 (fun p : Fin x1 => (Finset.univ.filter (fun l : Fin x2 => (p, l) ∈ x3)).card)
    have d2 := Finset.sum_map_toList x5 (fun l : Fin x2 => (Finset.univ.filter (fun p : Fin x1 => (p, l) ∈ x3 ∧ p ∉ x4)).card)
    rw [Nat.add_assoc]
    refine Nat.sub_le_sub_right (Nat.add_le_add (le_trans hS ?_) (le_trans hL ?_)) 1
    · simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def, List.length_map, Finset.length_toList]
      omega
    · simp only [List.length_map, List.length_append, Finset.length_toList]
      omega

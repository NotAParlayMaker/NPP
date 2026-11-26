import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18270_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

theorem foldl_len (n : ℕ) (l : List Gate) (acc : List (List ℕ)) :
    (l.foldl (coneStep n) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons g l ih => rw [List.foldl_cons, ih]; simp [coneStep]; omega

theorem foldl_ext (n : ℕ) (l : List Gate) (acc : List (List ℕ)) :
    ∃ t, l.foldl (coneStep n) acc = acc ++ t := by
  induction l generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons g l ih =>
    obtain ⟨t, ht⟩ := ih (coneStep n acc g)
    refine ⟨(coneStep n acc g).drop acc.length ++ t, ?_⟩
    rw [List.foldl_cons, ht]; simp [coneStep]

theorem mem_cone (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔ ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  have hl : C.gates = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j+1)) := by simp
  obtain ⟨t, ht⟩ := foldl_ext n (C.gates.drop (j+1))
    (coneStep n ((C.gates.take j).foldl (coneStep n) []) C.gates[j])
  have hA : ((C.gates.take j).foldl (coneStep n) []).length = j := by
    rw [foldl_len]; simp; omega
  have hc : cones n C = ((C.gates.take j).foldl (coneStep n) []) ++
      ([((C.gates[j]).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: ((C.gates.take j).foldl (coneStep n) []).getD (w - n) [])] ++ t) := by
    unfold cones
    conv_lhs => rw [hl]
    rw [List.foldl_append, List.foldl_cons, ht]
    simp [coneStep, hA]
  have hg : gateAt C j = C.gates[j] := by
    unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
  have hlow : ∀ k < j, (cones n C).getD k [] =
      ((C.gates.take j).foldl (coneStep n) []).getD k [] := by
    intro k hk
    rw [hc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  unfold InCone
  rw [hg]
  conv_lhs => rw [hc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp only [hA, Nat.sub_self]
  simp only [List.cons_append, List.getElem?_cons_zero, Option.getD_some, List.mem_flatMap,
    List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, h1, h2⟩, h⟩
    refine ⟨w, hw, h1, h2, ?_⟩
    rw [hlow _ (by omega)]
    exact h
  · rintro ⟨w, hw, h1, h2, h⟩
    refine ⟨w, ⟨hw, h1, h2⟩, ?_⟩
    rw [← hlow _ (by omega)]
    exact h

theorem cone_lt (n : ℕ) (C : Circuit) (i j : ℕ) (h : InCone n C i j) : j < C.gates.length := by
  by_contra hc
  unfold InCone cones at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [foldl_len]; simp; omega)] at h
  simp at h

theorem cone_sub (n : ℕ) (C : Circuit) : ∀ b a k, InCone n C a b → InCone n C k a →
    InCone n C k b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a k hab hka
    have hb := cone_lt n C a b hab
    obtain ⟨w, hw, h1, h2, h⟩ := (mem_cone n C a b hb).1 hab
    refine (mem_cone n C k b hb).2 ⟨w, hw, h1, h2, Or.inr ?_⟩
    rcases h with h | h
    · subst h; exact hka
    · exact ih (w - n) (by omega) a k h hka

theorem step (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) (hij : i < j)
    (h : n + i ∈ (gateAt C j).inputs) : InCone n C i j :=
  (mem_cone n C i j hj).2 ⟨n + i, h, by omega, by omega, Or.inl (by omega)⟩

end PEqualNP.Outside.L_meta_18270_aux

open PEqualNP.Outside.L_meta_18270_aux in
theorem PEqualNP.Outside.L_meta_18270 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (ℕ × ℕ)), (∀ x4 < x2.size, (∃ x6 ∈ x3, x1 + x4 = x6.1 ∨ x1 + x4 = x6.2) ∨ ∃ x6 < x2.size, x4 < x6 ∧ x1 + x4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs) → ∀ x5 < x2.size, ∃ x7 ∈ x3, ∃ x8 ∈ [x7.1, x7.2], x8 = x1 + x5 ∨ x1 ≤ x8 ∧ PEqualNP.EdgeOwnership.InCone x1 x2 x5 (x8 - x1) := by
  intro n C L hP
  have hs : C.size = C.gates.length := rfl
  suffices H : ∀ k, ∀ i < C.size, C.size - i ≤ k → ∃ p ∈ L, ∃ w ∈ [p.1, p.2], w = n + i ∨
      n ≤ w ∧ PEqualNP.EdgeOwnership.InCone n C i (w - n) by
    intro i hi
    exact H _ i hi le_rfl
  intro k
  induction k with
  | zero => intro i hi hk; omega
  | succ k ih =>
    intro i hi hk
    rcases hP i hi with ⟨p, hp, h⟩ | ⟨j, hj, hij, hin⟩
    · rcases h with h | h
      · exact ⟨p, hp, p.1, by simp, Or.inl h.symm⟩
      · exact ⟨p, hp, p.2, by simp, Or.inl h.symm⟩
    · obtain ⟨p, hp, w, hw, h⟩ := ih j hj (by omega)
      have hc := step n C i j (by omega) hij hin
      refine ⟨p, hp, w, hw, Or.inr ?_⟩
      rcases h with h | h
      · subst h
        refine ⟨by omega, ?_⟩
        simpa using hc
      · exact ⟨h.1, cone_sub n C _ j i h.2 hc⟩

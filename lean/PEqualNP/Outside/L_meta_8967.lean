import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8967_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

theorem key (n m : ℕ) (G : List Gate)
    (H : ∀ j (hj : j < G.length), G[j].op = GateOp.and → ∀ w ∈ G[j].inputs, w < n + m) :
    ∀ k ≤ G.length, ((G.take k).foldl (coneStep n) []).length = k ∧
      ∀ j i, i ∈ ((G.take k).foldl (coneStep n) []).getD j [] →
        i < j ∧ (∀ hj : j < G.length, G[j].op = GateOp.and → i < m) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkG : k < G.length := by omega
    obtain ⟨hl, hc⟩ := ih (by omega)
    rw [List.take_add_one, List.getElem?_eq_getElem hkG]
    simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hcs : (List.take k G).foldl (coneStep n) [] = cs at hl hc
    unfold coneStep
    refine ⟨by simp [hl], ?_⟩
    intro j i hi
    rw [List.getD_eq_getElem?_getD] at hi
    rcases Nat.lt_trichotomy j k with h | h | h
    · rw [List.getElem?_append_left (by omega)] at hi
      rw [← List.getD_eq_getElem?_getD] at hi
      exact hc j i hi
    · subst h
      rw [List.getElem?_append_right (by omega)] at hi
      simp only [hl, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
      rw [List.mem_flatMap] at hi
      obtain ⟨w, hw, hiw⟩ := hi
      rw [List.mem_filter] at hw
      obtain ⟨hw1, hw2⟩ := hw
      simp only [decide_eq_true_eq] at hw2
      rcases List.mem_cons.mp hiw with h1 | h1
      · subst h1
        refine ⟨by omega, ?_⟩
        intro hj hand
        have := H j hj hand w hw1
        omega
      · obtain ⟨a1, a2⟩ := hc (w - n) i h1
        refine ⟨by omega, ?_⟩
        intro hj hand
        have := H j hj hand w hw1
        omega
    · rw [List.getElem?_eq_none (by simp [hl]; omega)] at hi
      simp at hi

end PEqualNP.Outside.L_meta_8967_aux

theorem PEqualNP.Outside.L_meta_8967 : ∀ (x1 x2 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x3 : List (Fin (32 : ℕ) × Fin (32 : ℕ))) (x4 : Fin (21 : ℕ) → Bool × Fin (32 : ℕ) × Fin (32 : ℕ)),   List.ofFn x4 = x1 ++ List.map (fun (x5 : Fin (32 : ℕ) × Fin (32 : ℕ)) => (Bool.true, x5)) x3 ++ x2 →     (∀ x6 ∈ x2, x6.1 = Bool.false) →       (∀ (x7 : Fin (21 : ℕ)), ↑(x4 x7).2.1 < (11 : ℕ) + ↑x7 ∧ ↑(x4 x7).2.2 < (11 : ℕ) + ↑x7) →         (∀ x8 ∈ x3, ↑x8.1 < (11 : ℕ) + x1.length ∧ ↑x8.2 < (11 : ℕ) + x1.length) →           have x9 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x9 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => { op := if x9.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x9.2.1, ↑x9.2.2] : PEqualNP.CircuitLowerBounds.Gate }) (List.ofFn x4), output := (31 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };           ∀ (x10 x11 : Fin (21 : ℕ)), x1.length ≤ ↑x10 → (x4 x11).1 = Bool.true → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x9 ↑x10 ↑x11 := by
  intro x1 x2 x3 x4 hlist hx2 h3 h4 x9 x10 x11 hm hand hin
  have hfin : ∀ jj : Fin 21, (x4 jj).1 = true →
      ((x4 jj).2.1 : ℕ) < 11 + x1.length ∧ ((x4 jj).2.2 : ℕ) < 11 + x1.length := by
    intro jj hjj
    have hmem : x4 jj ∈ x1 ++ List.map (fun (x5 : Fin 32 × Fin 32) => (true, x5)) x3 ++ x2 := by
      rw [← hlist]; exact List.mem_ofFn.2 ⟨jj, rfl⟩
    simp only [List.mem_append, List.mem_map] at hmem
    rcases hmem with (h | ⟨x8, hx8, he⟩) | h
    · have htake : (List.ofFn x4).take x1.length = x1 := by
        rw [hlist, List.append_assoc, List.take_left]
      rw [← htake, List.mem_iff_getElem] at h
      obtain ⟨i, hi, he⟩ := h
      have hi' : i < x1.length := by
        have := hi
        simp only [List.length_take, List.length_ofFn] at this
        omega
      simp only [List.getElem_take, List.getElem_ofFn] at he
      have := h3 ⟨i, by omega⟩
      rw [he] at this
      simp only at this
      omega
    · rw [← he]
      exact h4 x8 hx8
    · have := hx2 _ h
      rw [hjj] at this
      exact absurd this (by decide)
  have K := PEqualNP.Outside.L_meta_8967_aux.key 11 x1.length x9.gates (by
    intro j hj hop w hw
    simp only [x9, List.getElem_map, List.getElem_ofFn, List.length_map, List.length_ofFn] at hj hop hw
    split_ifs at hop with hh
    · have := hfin ⟨j, hj⟩ hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      omega) x9.gates.length le_rfl
  rw [List.take_length] at K
  have hj : (x11 : ℕ) < x9.gates.length := by
    simp only [x9, List.length_map, List.length_ofFn]; omega
  have := (K.2 x11 x10 hin).2 hj (by
    simp only [x9, List.getElem_map, List.getElem_ofFn, Fin.eta, hand, ite_true])
  omega

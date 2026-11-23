import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_732_aux

def db (u v : Fin 8) : Bool :=
  decide ((u.val, v.val) ∈ [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
      (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)])

def eb (u v : Fin 8) : Bool := db u v || db v u

theorem key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (∀ u v : Fin 8, ![b0, b1, b2, b3, b4, b5, b6, b7] u = true →
      ![b0, b1, b2, b3, b4, b5, b6, b7] v = true → eb u v = false) →
    ∃ a b : Fin 8, eb a b = true ∧ ![b0, b1, b2, b3, b4, b5, b6, b7] a = false ∧
      ![b0, b1, b2, b3, b4, b5, b6, b7] b = false ∧
      ∀ k : Fin 8, ![b0, b1, b2, b3, b4, b5, b6, b7] k = true → db a k = false ∧ db b k = false := by
  decide +kernel

theorem key2 (f : Fin 8 → Bool) (h : ∀ u v : Fin 8, f u = true → f v = true → eb u v = false) :
    ∃ a b : Fin 8, eb a b = true ∧ f a = false ∧ f b = false ∧
      ∀ k : Fin 8, f k = true → db a k = false ∧ db b k = false := by
  have hf : f = ![f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := by
    funext i; fin_cases i <;> rfl
  have := key (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  rw [← hf] at this
  exact this h

end PEqualNP.Outside.L_meta_732_aux

theorem PEqualNP.Outside.L_meta_732 : ∀ (E D : Fin 8 → Fin 8 → Prop),
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
  intro E D hE hD
  have hDb : ∀ u v, D u v ↔ PEqualNP.Outside.L_meta_732_aux.db u v = true := by
    intro u v; rw [hD]; simp only [PEqualNP.Outside.L_meta_732_aux.db, decide_eq_true_eq]
  have hED : ∀ u v, E u v ↔ (D u v ∨ D v u) := by
    intro u v; rw [hE, hD, hD]; revert u v; decide
  have hEb : ∀ u v, E u v ↔ PEqualNP.Outside.L_meta_732_aux.eb u v = true := by
    intro u v; rw [hED, hDb, hDb]; simp only [PEqualNP.Outside.L_meta_732_aux.eb, Bool.or_eq_true]
  refine ⟨hED, ?_, ?_⟩
  · intro u v; rw [hD, hD]; revert u v; decide
  · intro W K hW hKW hK
    classical
    obtain ⟨a, b, hab, ha, hb, hk⟩ := PEqualNP.Outside.L_meta_732_aux.key2 (fun i => decide (i ∈ K)) (by
      intro u v hu hv
      have h1 := hK u (of_decide_eq_true hu) v (of_decide_eq_true hv)
      rw [hEb] at h1
      simpa using h1)
    have ha' : a ∉ K := of_decide_eq_false ha
    have hb' : b ∉ K := of_decide_eq_false hb
    have hk' : ∀ k ∈ K, ¬ D a k ∧ ¬ D b k := by
      intro k hkK
      have h2 := hk k (decide_eq_true hkK)
      rw [hDb, hDb]
      simpa using h2
    by_cases haW : a ∈ W
    · have hbW : b ∉ W := fun hbW => hW a haW b hbW ((hEb a b).2 hab)
      exact ⟨b, hbW, hb', fun k hkK => (hk' k hkK).2⟩
    · exact ⟨a, haW, ha', fun k hkK => (hk' k hkK).1⟩

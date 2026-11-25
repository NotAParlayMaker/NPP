import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7473_aux

def E (i j : Fin 13) : Prop := (i.val + j.val) % 13 ∈ [0, 1, 3, 9]

def F (i j : ℕ) : Prop := (i + j) % 13 ∈ [0, 1, 3, 9]

def G (a b c d p : Fin 13) : Prop := ¬ F a.val p.val ∧ ¬ F b.val p.val ∧ ¬ F c.val p.val ∧ ¬ F d.val p.val

instance (i j : ℕ) : Decidable (F i j) := by unfold F; infer_instance

instance (a b c d p : Fin 13) : Decidable (G a b c d p) := by unfold G; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
theorem core : ∀ a b : Fin 13, a < b → ∀ c : Fin 13, b < c → ∀ d : Fin 13, c < d →
    ∀ p : Fin 13, G a b c d p → ∀ q : Fin 13, p < q → G a b c d q → ∀ r : Fin 13, q < r →
    G a b c d r → ∀ s : Fin 13, r < s → G a b c d s → False := by
  decide +kernel

theorem key (A B : Finset (Fin 13)) (h : ∀ i ∈ A, ∀ j ∈ B, ¬ E i j) :
    A.card ≤ 3 ∨ B.card ≤ 3 := by
  by_contra hc
  simp only [not_or, not_le] at hc
  obtain ⟨S, hSA, hS⟩ := Finset.exists_subset_card_eq (s := A) (n := 4) (by omega)
  obtain ⟨T, hTB, hT⟩ := Finset.exists_subset_card_eq (s := B) (n := 4) (by omega)
  have hf := (S.orderEmbOfFin hS).strictMono
  have hg := (T.orderEmbOfFin hT).strictMono
  have hG : ∀ l : Fin 4, G (S.orderEmbOfFin hS 0) (S.orderEmbOfFin hS 1)
      (S.orderEmbOfFin hS 2) (S.orderEmbOfFin hS 3) (T.orderEmbOfFin hT l) := by
    intro l
    have hj := hTB (Finset.orderEmbOfFin_mem T hT l)
    have hi : ∀ k : Fin 4, ¬ E (S.orderEmbOfFin hS k) (T.orderEmbOfFin hT l) :=
      fun k => h _ (hSA (Finset.orderEmbOfFin_mem S hS k)) _ hj
    exact ⟨hi 0, hi 1, hi 2, hi 3⟩
  exact core _ _ (hf (by decide : (0 : Fin 4) < 1)) _ (hf (by decide : (1 : Fin 4) < 2))
    _ (hf (by decide : (2 : Fin 4) < 3)) _ (hG 0) _ (hg (by decide : (0 : Fin 4) < 1)) (hG 1)
    _ (hg (by decide : (1 : Fin 4) < 2)) (hG 2) _ (hg (by decide : (2 : Fin 4) < 3)) (hG 3)

end PEqualNP.Outside.L_meta_7473_aux

open PEqualNP.Outside.L_meta_7473_aux in
theorem PEqualNP.Outside.L_meta_7473 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Fin (13 : ℕ) → Fin ((13 : ℕ) + (13 : ℕ)) := fun (x2 : Fin (13 : ℕ)) => Fin.castAdd (13 : ℕ) x2; have x3 : Fin (13 : ℕ) → Fin ((13 : ℕ) + (13 : ℕ)) := fun (x3 : Fin (13 : ℕ)) => Fin.natAdd (13 : ℕ) x3; have x4 : (Fin (13 : ℕ) → Fin (26 : ℕ)) → Finset (Fin (26 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Fin (13 : ℕ) → Fin (26 : ℕ)) (x5 : Finset (Fin (26 : ℕ))) => {x6 : Fin (13 : ℕ) | x4 x6 ∉ x5}; have x5 : Finset (Fin (26 : ℕ)) → Prop := fun (x5 : Finset (Fin (26 : ℕ))) => ∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 → x2 x6 ∈ x5 ∨ x3 x7 ∈ x5; ∀ (x6 : Finset (Fin (26 : ℕ))), x5 x6 → (x4 x2 x6).card ≤ (3 : ℕ) ∨ (x4 x3 x6).card ≤ (3 : ℕ) := by
  intro x1 x2 x3 x4 x5 C hC
  apply key
  intro i hi j hj hE
  simp only [x4, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  rcases hC i j hE with h | h
  · exact hi h
  · exact hj h

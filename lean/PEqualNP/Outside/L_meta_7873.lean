import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7873_aux

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

set_option maxRecDepth 100000 in
theorem bridge : ∀ i j : Fin 13,
    (i + j ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ↔ F i.val j.val := by
  decide

theorem key (A B : Finset (Fin 13)) (hA : A.card = 4)
    (h : ∀ i ∈ A, ∀ j ∈ B, ¬ F i.val j.val) : B.card ≤ 3 := by
  by_contra hc
  simp only [not_le] at hc
  obtain ⟨T, hTB, hT⟩ := Finset.exists_subset_card_eq (s := B) (n := 4) (by omega)
  have hf := (A.orderEmbOfFin hA).strictMono
  have hg := (T.orderEmbOfFin hT).strictMono
  have hG : ∀ l : Fin 4, G (A.orderEmbOfFin hA 0) (A.orderEmbOfFin hA 1)
      (A.orderEmbOfFin hA 2) (A.orderEmbOfFin hA 3) (T.orderEmbOfFin hT l) := by
    intro l
    have hj := hTB (Finset.orderEmbOfFin_mem T hT l)
    have hi : ∀ k : Fin 4, ¬ F (A.orderEmbOfFin hA k).val (T.orderEmbOfFin hT l).val :=
      fun k => h _ (Finset.orderEmbOfFin_mem A hA k) _ hj
    exact ⟨hi 0, hi 1, hi 2, hi 3⟩
  exact core _ _ (hf (by decide : (0 : Fin 4) < 1)) _ (hf (by decide : (1 : Fin 4) < 2))
    _ (hf (by decide : (2 : Fin 4) < 3)) _ (hG 0) _ (hg (by decide : (0 : Fin 4) < 1)) (hG 1)
    _ (hg (by decide : (1 : Fin 4) < 2)) (hG 2) _ (hg (by decide : (2 : Fin 4) < 3)) (hG 3)

end PEqualNP.Outside.L_meta_7873_aux

open PEqualNP.Outside.L_meta_7873_aux in
theorem PEqualNP.Outside.L_meta_7873 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 : Finset (Fin (13 : ℕ))),   x2.card = (4 : ℕ) →     have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x2, x5 + x4 ∉ x1};     x4.card ≤ (3 : ℕ) := by
  intro x1 A hA x4
  apply key A x4 hA
  intro i hi j hj hF
  simp only [x4, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact hj i hi ((bridge i j).2 hF)

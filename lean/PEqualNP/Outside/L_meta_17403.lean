import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17403_aux

def ncb (a y : Fin 13) : Bool := [(0 : Fin 13), 1, 3, 9].all (fun x4 => a != y + x4)

theorem ncb_iff (a y : Fin 13) : ncb a y = true ↔ ¬ ∃ x4 ∈ [(0 : Fin 13), 1, 3, 9], a = y + x4 := by
  simp [ncb]

def chk : Bool := (List.finRange 13).all fun a => (List.finRange 13).all fun b =>
  (List.finRange 13).all fun c => (List.finRange 13).all fun d =>
    (a == b || a == c || a == d || b == c || b == d || c == d ||
      decide (((Finset.univ : Finset (Fin 13)).filter (fun y : Fin 13 =>
        (ncb a y && ncb b y && ncb c y && ncb d y) = true)).card ≤ 3))

theorem chk_ok : chk = true := by
  set_option maxHeartbeats 0 in decide +kernel

theorem key (a b c d : Fin 13) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d) :
    ((Finset.univ : Finset (Fin 13)).filter (fun y : Fin 13 =>
      (ncb a y && ncb b y && ncb c y && ncb d y) = true)).card ≤ 3 := by
  have h := chk_ok
  simp only [chk, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have := h a b c d
  simp_all

end PEqualNP.Outside.L_meta_17403_aux

theorem PEqualNP.Outside.L_meta_17403 : have x1 : Finset (Fin (13 : ℕ)) := Finset.univ; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4; ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → {x5 ∈ x1 | ∀ x6 ∈ x3, ¬x2 x6 x5}.card ≤ (3 : ℕ) := by
  intro x1 x2 x3 hx3
  obtain ⟨a, T, haT, rfl, hT⟩ := Finset.card_eq_succ.mp hx3
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp hT
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at haT
  have h := PEqualNP.Outside.L_meta_17403_aux.key a b c d haT.1 haT.2.1 haT.2.2 hbc hbd hcd
  refine le_trans (Finset.card_le_card ?_) h
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at hy ⊢
  simp only [Bool.and_eq_true, PEqualNP.Outside.L_meta_17403_aux.ncb_iff, and_assoc]
  simp only [x2] at hy
  exact hy.2

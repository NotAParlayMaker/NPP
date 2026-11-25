import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7029

lemma flip_card (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun c => c u ≠ c v)).card =
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun c => ¬ c u ≠ c v)).card := by
  refine Finset.card_bij' (fun c _ => Function.update c u (!c u))
    (fun c _ => Function.update c u (!c u)) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [Function.update_self, Function.update_of_ne huv.symm]
    revert hc; cases c u <;> cases c v <;> simp
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [Function.update_self, Function.update_of_ne huv.symm]
    revert hc; cases c u <;> cases c v <;> simp
  · intro c _
    simp
  · intro c _
    simp

lemma cut_iff (n : ℕ) (u v : Fin n) (c : Fin n → Bool) :
    (∀ a b : Fin n, s(u, v) = s(a, b) → c a ≠ c b) ↔ c u ≠ c v := by
  constructor
  · intro h; exact h u v rfl
  · intro h a b hab
    rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact fun h' => h h'.symm

lemma cutHalf : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (T : Finset (Sym2 (Fin n))), T ⊆ G.edgeFinset →
        ∃ (U : Finset (Sym2 (Fin n))) (c : Fin n → Bool), U ⊆ T ∧ T.card ≤ 2 * U.card ∧
          ∀ u v : Fin n, s(u, v) ∈ U → c u ≠ c v := by
  classical
  intro n G _ T hT
  by_contra hcon
  have hall : ∀ c : Fin n → Bool,
      (T.filter (fun e => ∀ a b : Fin n, e = s(a, b) → c a ≠ c b)).card <
        (T.filter (fun e => ¬ ∀ a b : Fin n, e = s(a, b) → c a ≠ c b)).card := by
    intro c
    have hsum := Finset.card_filter_add_card_filter_not (s := T)
      (fun e => ∀ a b : Fin n, e = s(a, b) → c a ≠ c b)
    by_contra hlt
    apply hcon
    refine ⟨T.filter (fun e => ∀ a b : Fin n, e = s(a, b) → c a ≠ c b), c,
      Finset.filter_subset _ _, by omega, ?_⟩
    intro u v huv
    exact (Finset.mem_filter.mp huv).2 u v rfl
  have hlt := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ : Finset (Fin n → Bool))) Finset.univ_nonempty (fun c _ => hall c)
  simp only [Finset.card_filter] at hlt
  have h1 := Finset.sum_comm (s := (Finset.univ : Finset (Fin n → Bool))) (t := T)
    (f := fun c e => if (∀ a b : Fin n, e = s(a, b) → c a ≠ c b) then 1 else 0)
  have h2 := Finset.sum_comm (s := (Finset.univ : Finset (Fin n → Bool))) (t := T)
    (f := fun c e => if (¬ ∀ a b : Fin n, e = s(a, b) → c a ≠ c b) then 1 else 0)
  rw [h1, h2] at hlt
  refine absurd hlt (not_lt.mpr (le_of_eq ?_))
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hadj := hT he
  induction e using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := by
      have : G.Adj u v := by simpa using hadj
      exact this.ne
    simp only [cut_iff]
    rw [← Finset.card_filter, ← Finset.card_filter]
    exact (flip_card n u v huv).symm

end PEqualNP.Outside.L_meta_7029

theorem PEqualNP.Outside.L_meta_7029 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], ∀ x4 ⊆ x2.edgeFinset, ∃ (x6 : Finset (Sym2 (Fin x1))) (x7 : Fin x1 → Bool), x6 ⊆ x4 ∧ x4.card ≤ (2 : ℕ) * x6.card ∧ ∀ (x8 x9 : Fin x1), s(x8, x9) ∈ x6 → x7 x8 ≠ x7 x9 :=
  PEqualNP.Outside.L_meta_7029.cutHalf

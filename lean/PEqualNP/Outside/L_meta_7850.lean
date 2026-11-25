import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7850_aux

theorem half (n : ℕ) (a b : Fin n) (h : a ≠ b) :
    2 * (Finset.univ.filter (fun f : Fin n → Bool => f a ≠ f b)).card
      = Fintype.card (Fin n → Bool) := by
  have h1 : (Finset.univ.filter (fun f : Fin n → Bool => f a ≠ f b)).card
      = (Finset.univ.filter (fun f : Fin n → Bool => ¬ (f a ≠ f b))).card := by
    apply Finset.card_bij' (fun f _ => Function.update f a (!f a))
      (fun f _ => Function.update f a (!f a))
    all_goals
      intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      first
        | (simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           rw [Function.update_self, Function.update_of_ne (Ne.symm h)]
           cases hfa : f a <;> cases hfb : f b <;> simp_all)
        | simp
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun f : Fin n → Bool => f a ≠ f b)
  rw [← Finset.card_univ]
  omega

end PEqualNP.Outside.L_meta_7850_aux

theorem PEqualNP.Outside.L_meta_7850 : ∀ (x1 : ℕ) (x2 : Finset (Sym2 (Fin x1))), (∀ x3 ∈ x2, ¬x3.IsDiag) → ∃ (x4 : Fin x1 → Bool), x2.card ≤ (2 : ℕ) * {x5 ∈ x2 | ¬(Sym2.map x4 x5).IsDiag}.card := by
  intro n E hE
  by_contra hcon
  push Not at hcon
  have key : ∀ e ∈ E, 2 * (Finset.univ.filter
      (fun f : Fin n → Bool => ¬(Sym2.map f e).IsDiag)).card
      = Fintype.card (Fin n → Bool) := by
    intro e he
    have hd := hE e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : a ≠ b := by simpa using hd
      have := PEqualNP.Outside.L_meta_7850_aux.half n a b hab
      simpa using this
  have hsum : ∑ f : Fin n → Bool, 2 * (E.filter (fun e => ¬(Sym2.map f e).IsDiag)).card
      < ∑ f : Fin n → Bool, E.card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun f _ => hcon f)
  have hswap : ∑ f : Fin n → Bool, 2 * (E.filter (fun e => ¬(Sym2.map f e).IsDiag)).card
      = ∑ e ∈ E, 2 * (Finset.univ.filter
        (fun f : Fin n → Bool => ¬(Sym2.map f e).IsDiag)).card := by
    simp only [Finset.card_filter, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap, Finset.sum_congr rfl key] at hsum
  simp [mul_comm] at hsum

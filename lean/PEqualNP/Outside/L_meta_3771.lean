import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3771

lemma independent_bound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (order : N=q^2+q+1) (degree : ∀ l,(Finset.univ.filter (fun p => I p l)).card=q+1)
    (both : ∀ l m : Fin N, l ≠ m → (Finset.univ.filter (fun p => I p l ∧ I p m)).card ≤ 1)
    (P L : Finset (Fin N)) (empty : ∀ p∈P,∀ l∈L,¬I p l) :
    P.card*L.card+q*(P.card+L.card)≤N*q := by
  classical
  let a (l p : Fin N) : ℕ := if I p l then 1 else 0
  let d (p : Fin N) := ∑ l∈L,a l p
  have mass (l) : ∑ p,a l p=q+1 := by rw [←degree l,Finset.card_filter]
  have products (l m : Fin N) : ∑ p,a l p*a m p ≤ 1+(if l=m then q else 0) := by
    by_cases eq : l=m
    · subst m
      simp only [ite_true]
      rw [show (∑ p,a l p*a l p) = ∑ p,a l p by
        apply Finset.sum_congr rfl
        intro p _; by_cases h : I p l <;> simp [a,h],mass]
      omega
    · simp only [eq,ite_false,Nat.add_zero]
      have cb := both l m eq
      rw [Finset.card_filter] at cb
      convert cb using 1
      apply Finset.sum_congr rfl
      intro p _; by_cases h : I p l <;> by_cases k : I p m <;> simp [a,h,k]
  have first : ∑ p,d p=L.card*(q+1) := by
    dsimp [d]; rw [Finset.sum_comm]; simp [mass]
  have second : ∑ p,(d p)^2 ≤ L.card*(L.card+q) := by
    calc
      ∑ p,(d p)^2 = ∑ p,∑ l∈L,∑ m∈L,a l p*a m p := by
        apply Finset.sum_congr rfl; intro p _
        dsimp only [d]; rw [pow_two,Finset.sum_mul]
        exact Finset.sum_congr rfl (fun l _ => Finset.mul_sum ..)
      _ = ∑ l∈L,∑ m∈L,∑ p,a l p*a m p := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ ≤ ∑ l∈L,∑ m∈L,(1+(if l=m then q else 0)) :=
        Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun m _ => products l m))
      _ = _ := by
        apply Eq.trans (Finset.sum_congr rfl (fun l hl => show
          (∑ m∈L,(1+(if l=m then q else 0)))=L.card+q from by simp [Finset.sum_add_distrib,hl]))
        simp
  have zero (p) (hp : p∈P) : d p=0 := Finset.sum_eq_zero (fun l hl => by simp [a,empty p hp l hl])
  have mass' : ∑ p∈Pᶜ,d p=L.card*(q+1) := by
    have h := Finset.sum_add_sum_compl P d
    rw [Finset.sum_eq_zero zero,Nat.zero_add,first] at h
    exact h
  have sq := sq_sum_le_card_mul_sum_sq (s:=Pᶜ) (f:=d)
  rw [mass'] at sq
  have upper := (Finset.sum_le_univ_sum_of_nonneg (s:=Pᶜ) (f:=fun p => (d p)^2) (by simp)).trans second
  have ncard : Pᶜ.card+P.card=N := by simp
  by_cases nil : L.card=0
  · have hp : P.card≤N := by omega
    simpa [nil,Nat.mul_comm] using Nat.mul_le_mul_right q hp
  have t : L.card*(L.card*(q+1)^2) ≤ L.card*(Pᶜ.card*(L.card+q)) := by
    calc
      _ = (L.card*(q+1))^2 := by ring
      _ ≤ Pᶜ.card * (L.card*(L.card+q)) := sq.trans (Nat.mul_le_mul_left _ upper)
      _ = _ := by ring
  have cancel := Nat.le_of_mul_le_mul_left t (Nat.pos_of_ne_zero nil)
  generalize P.card=pp at *; generalize L.card=ll at *; generalize Pᶜ.card=rr at *
  nlinarith [congrArg (fun k : ℕ => k*ll) ncard,congrArg (fun k : ℕ => k*q) ncard,
    congrArg (fun k : ℕ => k*ll) order]

end PEqualNP.Outside.L_meta_3771

theorem PEqualNP.Outside.L_meta_3771 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 + x6 ∉ x1) → x2.card ≤ (3 : ℕ) ∨ x3.card ≤ (3 : ℕ) := by
  let support : Finset (Fin 13) := {0, 1, 3, 9}
  let incidence (p l : Fin 13) := p + l ∈ support
  have degree : ∀ l, (Finset.univ.filter (fun p => incidence p l)).card = 4 := by
    decide +kernel
  have overlap : ∀ l m : Fin 13, l ≠ m → (Finset.univ.filter (fun p => incidence p l ∧ incidence p m)).card ≤ 1 := by
    decide +kernel
  intro _ P L avoid
  have bound := PEqualNP.Outside.L_meta_3771.independent_bound 3 13 incidence
    (by decide) degree overlap P L avoid
  by_contra! large
  have product := Nat.mul_le_mul (show 4 ≤ P.card by omega) (show 4 ≤ L.card by omega)
  omega

/-
Toy finite statements behind research/front/generalize/relativization/gravity-from-entropy.md.

Everything here is elementary query complexity. Nothing here bears on P vs NP.

* `DTree N`            : a deterministic query algorithm on an oracle `Fin N → Bool`.
* `eval_eq_of_agree`   : "locality": the answer only depends on the oracle along the
                         path actually walked in the empty world (at most `depth` bits).
* `card_planted_le`    : at most `depth T` single-point "matter insertions" are felt by `T`.
* `not_computes_or`    : Baker–Gill–Solovay kernel: depth < N cannot compute OR.
* `mle_sensitive`      : the multilinear extension at a generic point feels *every*
                         oracle bit (the non-relativizing / algebrizing step is "volume law").
-/
import Mathlib

namespace Relativization

/-- A deterministic decision tree querying an oracle with `N` positions. -/
inductive DTree (N : ℕ) where
  | leaf : Bool → DTree N
  | node : Fin N → DTree N → DTree N → DTree N

namespace DTree
variable {N : ℕ}

/-- Run the tree on oracle `A` (`node i lo hi`: query `i`, go `hi` on a 1-answer). -/
def eval : DTree N → (Fin N → Bool) → Bool
  | leaf b, _ => b
  | node i lo hi, A => if A i then eval hi A else eval lo A

def depth : DTree N → ℕ
  | leaf _ => 0
  | node _ lo hi => max (depth lo) (depth hi) + 1

/-- Positions queried when every answer is 0: the "light cone" of the tree in the empty world. -/
def zeroPath : DTree N → Finset (Fin N)
  | leaf _ => ∅
  | node i lo _ => insert i (zeroPath lo)

/-- The empty oracle (the unrelativized world). -/
def empty : Fin N → Bool := fun _ => false

/-- The empty oracle with one planted 1 at `i`. -/
def planted (i : Fin N) : Fin N → Bool := fun j => decide (j = i)

theorem card_zeroPath_le (T : DTree N) : (zeroPath T).card ≤ depth T := by
  induction T with
  | leaf b => simp [zeroPath, depth]
  | node i lo hi ihlo _ =>
    simp only [zeroPath, depth]
    calc (insert i (zeroPath lo)).card ≤ (zeroPath lo).card + 1 := Finset.card_insert_le _ _
      _ ≤ max (depth lo) (depth hi) + 1 := by omega

/-- Locality: an oracle that vanishes on the zero-path is indistinguishable from the empty one. -/
theorem eval_eq_of_agree (T : DTree N) (A : Fin N → Bool)
    (h : ∀ i ∈ zeroPath T, A i = false) : eval T A = eval T empty := by
  induction T with
  | leaf b => rfl
  | node i lo hi ihlo _ =>
    have hi0 : A i = false := h i (by simp [zeroPath])
    have hlo : ∀ j ∈ zeroPath lo, A j = false := fun j hj => h j (by simp [zeroPath, hj])
    simp [eval, hi0, empty, ihlo hlo]

/-- A planted point off the zero-path is not felt. -/
theorem eval_planted_of_not_mem (T : DTree N) (i : Fin N) (hi : i ∉ zeroPath T) :
    eval T (planted i) = eval T empty := by
  apply eval_eq_of_agree
  intro j hj
  have : j ≠ i := fun e => hi (e ▸ hj)
  simp [planted, this]

/-- At most `depth T` of the `N` single-point insertions change the answer:
    `Pr_i [T(e_i) ≠ T(0)] ≤ depth T / N`. -/
theorem card_planted_le (T : DTree N) :
    (Finset.univ.filter (fun i : Fin N => eval T (planted i) ≠ eval T empty)).card ≤ depth T := by
  refine le_trans (Finset.card_le_card ?_) (card_zeroPath_le T)
  intro i hi
  by_contra hmem
  exact (Finset.mem_filter.mp hi).2 (eval_planted_of_not_mem T i hmem)

/-- Some planted world is invisible to any tree of depth `< N`. -/
theorem exists_planted_invisible (T : DTree N) (h : depth T < N) :
    ∃ i : Fin N, eval T (planted i) = eval T empty := by
  by_contra hne
  push Not at hne
  have hall : (Finset.univ.filter (fun i : Fin N => eval T (planted i) ≠ eval T empty))
      = Finset.univ := Finset.filter_true_of_mem (fun i _ => hne i)
  have := card_planted_le T
  rw [hall, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- OR of the oracle ("is the oracle non-empty", the BGS test language at one length). -/
def orFn (A : Fin N → Bool) : Bool := decide (∃ i, A i = true)

/-- Baker–Gill–Solovay kernel: no tree of depth `< N` computes OR on `N` bits. -/
theorem not_computes_or (T : DTree N) (h : depth T < N) :
    ¬ ∀ A, eval T A = orFn A := by
  intro hT
  obtain ⟨i, hi⟩ := exists_planted_invisible T h
  rw [hT, hT] at hi
  have h1 : orFn (planted i) = true := by
    simp only [orFn, decide_eq_true_eq]; exact ⟨i, by simp [planted]⟩
  have h0 : orFn (empty : Fin N → Bool) = false := by
    simp [orFn, empty]
  rw [h1, h0] at hi
  exact Bool.noConfusion hi

end DTree

/-! ### The algebrizing step feels the whole oracle -/

section MLE
variable {m : ℕ} {F : Type*} [Field F]

/-- Lagrange basis weight of the cube point `x` at `r`. -/
def chi (x : Fin m → Bool) (r : Fin m → F) : F :=
  ∏ i, (if x i then r i else 1 - r i)

/-- Multilinear extension of an `F`-valued oracle on `{0,1}^m`, evaluated at `r ∈ F^m`. -/
def mle (A : (Fin m → Bool) → F) (r : Fin m → F) : F :=
  ∑ x, A x * chi x r

theorem chi_ne_zero (x : Fin m → Bool) (r : Fin m → F)
    (hr : ∀ i, r i ≠ 0 ∧ r i ≠ 1) : chi x r ≠ 0 := by
  unfold chi
  rw [Finset.prod_ne_zero_iff]
  intro i _
  by_cases hx : x i
  · simp [hx, (hr i).1]
  · simp only [hx, Bool.false_eq_true, if_false]
    intro h0
    exact (hr i).2 (by linear_combination -h0)

/-- At a point with no coordinate in `{0,1}`, the multilinear extension is sensitive to
    every single oracle entry: changing the oracle at exactly one cube point changes the value. -/
theorem mle_sensitive (A B : (Fin m → Bool) → F) (r : Fin m → F)
    (hr : ∀ i, r i ≠ 0 ∧ r i ≠ 1) (x₀ : Fin m → Bool)
    (hx₀ : A x₀ ≠ B x₀) (hoff : ∀ x, x ≠ x₀ → A x = B x) :
    mle A r ≠ mle B r := by
  intro h
  have hdiff : mle A r - mle B r = (A x₀ - B x₀) * chi x₀ r := by
    unfold mle
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single x₀]
    · ring
    · intro x _ hx
      rw [hoff x hx]; ring
    · intro hx; exact absurd (Finset.mem_univ _) hx
  rw [h, sub_self] at hdiff
  rcases mul_eq_zero.mp hdiff.symm with h1 | h2
  · exact hx₀ (sub_eq_zero.mp h1)
  · exact chi_ne_zero x₀ r hr h2

end MLE

end Relativization

#print axioms Relativization.DTree.card_planted_le
#print axioms Relativization.DTree.not_computes_or
#print axioms Relativization.mle_sensitive

import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3835

private def firstValue (op : GateOp) (inputs : List ℕ) (x : List Bool) : Bool :=
  op.eval (inputs.map fun i => x.getD i false)

private def combine (b p q : Bool) : Bool :=
  if b = true then p || q else p && q

private def Form (n : ℕ) (f : List Bool → Bool) : Prop :=
  (∃ i : Fin (n + 1), ∃ b : Bool, ∀ x : List Bool, x.length = n →
    f x = (b != x.getD i.val false)) ∨
  (∃ i j : Fin n, ∃ b : Bool, i < j ∧ ∀ x : List Bool, x.length = n →
    f x = combine b (x.getD i.val false) (x.getD j.val false))

private lemma fit_eq {n : ℕ} {f g : List Bool → Bool} (h : Form n f)
    (e : ∀ x : List Bool, x.length = n → g x = f x) : Form n g := by
  rcases h with ⟨i,b,hi⟩ | ⟨i,j,b,hij,hi⟩
  · exact Or.inl ⟨i,b,fun x hx => (e x hx).trans (hi x hx)⟩
  · exact Or.inr ⟨i,j,b,hij,fun x hx => (e x hx).trans (hi x hx)⟩

private lemma false_flip (a : Bool) : (false != a) = a := by cases a <;> decide

private lemma constant_form (n : ℕ) (b : Bool) : Form n (fun _ => b) := by
  refine Or.inl ⟨⟨n, Nat.lt_succ_self n⟩, b, ?_⟩
  intro x hx
  rw [List.getD_eq_default _ _ (by simp [hx])]
  cases b <;> rfl

private lemma literal_form (n i : ℕ) (b : Bool) :
    Form n (fun x => b != x.getD i false) := by
  by_cases hi : i < n
  · exact Or.inl ⟨⟨i, by omega⟩, b, fun _ _ => rfl⟩
  · apply fit_eq (constant_form n b)
    intro x hx
    rw [List.getD_eq_default _ _ (by omega)]
    cases b <;> rfl

private lemma copy_form (n i : ℕ) : Form n (fun x => x.getD i false) := by
  simpa only [false_flip] using literal_form n i false

private lemma ordered_binary (n i j : ℕ) (b : Bool) (hi : i < n) (hj : j < n) :
    Form n (fun x => combine b (x.getD i false) (x.getD j false)) := by
  rcases lt_trichotomy i j with hij | e | hji
  · exact Or.inr ⟨⟨i,hi⟩,⟨j,hj⟩,b,hij,fun _ _ => rfl⟩
  · subst j
    apply fit_eq (copy_form n i)
    intro x hx
    cases b <;> simp [combine]
  · refine Or.inr ⟨⟨j,hj⟩,⟨i,hi⟩,b,hji,?_⟩
    intro x hx
    cases b <;> simp [combine, Bool.and_comm, Bool.or_comm]

private lemma binary_form (n i j : ℕ) (b : Bool) :
    Form n (fun x => combine b (x.getD i false) (x.getD j false)) := by
  by_cases hi : i < n
  · by_cases hj : j < n
    · exact ordered_binary n i j b hi hj
    · cases b
      · apply fit_eq (constant_form n false)
        intro x hx
        rw [List.getD_eq_default _ _ (by omega : x.length ≤ j)]; simp [combine]
      · apply fit_eq (copy_form n i)
        intro x hx
        rw [List.getD_eq_default _ _ (by omega : x.length ≤ j)]; simp [combine]
  · cases b
    · apply fit_eq (constant_form n false)
      intro x hx
      rw [List.getD_eq_default _ _ (by omega : x.length ≤ i)]; simp [combine]
    · apply fit_eq (copy_form n j)
      intro x hx
      rw [List.getD_eq_default _ _ (by omega : x.length ≤ i)]; simp [combine]

private lemma first_form (n : ℕ) (op : GateOp) (xs : List ℕ)
    (hop : op = .and ∨ op = .or ∨ op = .not) (hsize : xs.length ≤ 2) :
    Form n (firstValue op xs) := by
  rcases hop with rfl | rfl | rfl
  · cases xs with
    | nil => exact fit_eq (constant_form n true) (fun _ _ => rfl)
    | cons i xs =>
      cases xs with
      | nil =>
        apply fit_eq (copy_form n i)
        intro x _
        simp [firstValue, GateOp.eval]
      | cons j xs =>
        have hx : xs = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hsize
          omega
        subst xs
        apply fit_eq (binary_form n i j false)
        intro x _
        simp [firstValue, GateOp.eval, combine]
  · cases xs with
    | nil => exact fit_eq (constant_form n false) (fun _ _ => rfl)
    | cons i xs =>
      cases xs with
      | nil =>
        apply fit_eq (copy_form n i)
        intro x _
        simp [firstValue, GateOp.eval]
      | cons j xs =>
        have hx : xs = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hsize
          omega
        subst xs
        apply fit_eq (binary_form n i j true)
        intro x _
        simp [firstValue, GateOp.eval, combine]
  · cases xs with
    | nil => exact fit_eq (constant_form n true) (fun _ _ => rfl)
    | cons i xs =>
      apply fit_eq (literal_form n i true)
      intro x _
      simp [firstValue, GateOp.eval]

end PEqualNP.Outside.L_meta_3835

theorem PEqualNP.Outside.L_meta_3835 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (0 : ℕ) < x2.size →
      ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size + (1 : ℕ) = x2.size ∧
        ((∃ (x6 : Fin (x1 + (1 : ℕ))) (x7 : Bool),
          ∀ (x8 : List Bool), x8.length = x1 → x2.eval x8 = x5.eval (x8 ++ [x7 != x8.getD (↑x6) Bool.false])) ∨
        ∃ (x6 : Fin x1) (x7 : Fin x1) (x8 : Bool), x6 < x7 ∧
          ∀ (x9 : List Bool), x9.length = x1 → x2.eval x9 = x5.eval (x9 ++
            [if x8 = Bool.true then x9.getD (↑x6) Bool.false || x9.getD (↑x7) Bool.false
            else x9.getD (↑x6) Bool.false && x9.getD (↑x7) Bool.false])) := by
  intro n C hC hsize
  rcases C with ⟨gs, out⟩
  cases gs with
  | nil => simp [Circuit.size] at hsize
  | cons g gs =>
    have hg := hC g List.mem_cons_self
    have htail : FanInTwo ⟨gs, out⟩ :=
      fun h hm => hC h (List.mem_cons_of_mem g hm)
    have hgop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa using hg.1
    have form := PEqualNP.Outside.L_meta_3835.first_form n g.op g.inputs hgop hg.2
    refine ⟨⟨gs, out⟩, htail, by simp [Circuit.size], ?_⟩
    have step (x : List Bool) :
        (⟨g :: gs, out⟩ : Circuit).eval x =
          (⟨gs, out⟩ : Circuit).eval
            (x ++ [PEqualNP.Outside.L_meta_3835.firstValue g.op g.inputs x]) := rfl
    rcases form with ⟨i,b,hi⟩ | ⟨i,j,b,hij,hi⟩
    · exact Or.inl ⟨i,b,fun x hx => by rw [step, hi x hx]⟩
    · exact Or.inr ⟨i,j,b,hij,fun x hx => by
        rw [step, hi x hx]
        rfl⟩

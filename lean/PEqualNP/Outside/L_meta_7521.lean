import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7521

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7521

theorem PEqualNP.Outside.L_meta_7521 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 : Finset ℕ) (x3 : List (Bool × ℕ × ℕ)),   ∃ (x4 : List ℕ),     x4.length ≤ x3.length ∧       x1 x2.toList x4 ∧         ∀           x5 ∈             List.foldl               (fun (x6 : Finset ℕ) (x7 : Bool × ℕ × ℕ) =>                 have x8 : ℕ := x7.2.1;                 have x9 : ℕ := x7.2.2;                 if x8 ∈ x6 ∧ x9 ∈ x6 ∧ x8 ≠ x9 then Insert.insert (if x7.1 = Bool.true then x8 ||| x9 else x8 &&& x9) (if x2.card = (8 : ℕ) then (x6.erase x8).erase x9 else x6) else x6)               x2 x3,           x5 ∈ x2.toList ++ x4 := by
  intro Ok B ts
  classical
  have snoc : ∀ (X ys : List ℕ) (v : ℕ), Ok X ys → (∃ a ∈ X ++ ys, ∃ b ∈ X ++ ys, v = a &&& b ∨ v = a ||| b) → Ok X (ys ++ [v]) := by
    intro X ys v hy hv i
    have hi : (i : ℕ) < (ys ++ [v]).length := i.isLt
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i ys.length with hlt | hge
    · have := hy ⟨i, hlt⟩
      simp only [List.get_eq_getElem] at this ⊢
      rw [List.take_append_of_le_length (by omega), List.getElem_append_left hlt]
      exact this
    · have hh : (i : ℕ) = ys.length := by omega
      simp only [List.get_eq_getElem]
      have e1 : (ys ++ [v])[(i : ℕ)]'i.isLt = v := by
        rw [List.getElem_append_right (by omega)]; simp
      rw [e1, List.take_append_of_le_length (by omega), hh, List.take_length]
      exact hv
  have key : ∀ (ts : List (Bool × ℕ × ℕ)) (S : Finset ℕ) (ys : List ℕ), Ok B.toList ys → (∀ x ∈ S, x ∈ B.toList ++ ys) →
      ∃ zs : List ℕ, zs.length ≤ ys.length + ts.length ∧ Ok B.toList zs ∧ ∀ x ∈ List.foldl (fun (x6 : Finset ℕ) (x7 : Bool × ℕ × ℕ) => have x8 : ℕ := x7.2.1; have x9 : ℕ := x7.2.2; if x8 ∈ x6 ∧ x9 ∈ x6 ∧ x8 ≠ x9 then Insert.insert (if x7.1 = Bool.true then x8 ||| x9 else x8 &&& x9) (if B.card = 8 then (x6.erase x8).erase x9 else x6) else x6) S ts, x ∈ B.toList ++ zs := by
    intro ts
    induction ts with
    | nil => intro S ys h1 h2; exact ⟨ys, by simp, h1, by simpa using h2⟩
    | cons t ts ih =>
      intro S ys h1 h2
      rw [List.foldl_cons]
      by_cases hc : t.2.1 ∈ S ∧ t.2.2 ∈ S ∧ t.2.1 ≠ t.2.2
      · simp only [if_pos hc]
        obtain ⟨zs, l1, l2, l3⟩ := ih (Insert.insert (if t.1 = true then t.2.1 ||| t.2.2 else t.2.1 &&& t.2.2) (if B.card = 8 then (S.erase t.2.1).erase t.2.2 else S))
          (ys ++ [if t.1 = true then t.2.1 ||| t.2.2 else t.2.1 &&& t.2.2])
          (snoc _ ys _ h1 ⟨_, h2 _ hc.1, _, h2 _ hc.2.1, by split_ifs <;> simp⟩) (by
            intro x hx
            rcases Finset.mem_insert.1 hx with hx | hx
            · rw [hx]; simp
            · have hxS : x ∈ S := by
                split_ifs at hx
                · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
                · exact hx
              rw [← List.append_assoc]
              exact List.mem_append_left _ (h2 x hxS))
        refine ⟨zs, ?_, l2, l3⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at l1 ⊢
        omega
      · simp only [if_neg hc]
        obtain ⟨zs, l1, l2, l3⟩ := ih S ys h1 h2
        exact ⟨zs, by simp only [List.length_cons]; omega, l2, l3⟩
  obtain ⟨zs, l1, l2, l3⟩ := key ts B [] (fun i => i.elim0) (by simp)
  exact ⟨zs, by simpa using l1, l2, l3⟩

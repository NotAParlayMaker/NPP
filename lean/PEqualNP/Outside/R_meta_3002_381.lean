import Mathlib
import PEqualNP.Defs

-- Delete any certificate containing a smaller one from the same family.
-- The resulting gate families are antichains, and every required cover retains a subcover.
theorem PEqualNP.Outside.R_meta_3002_381
    (operations :     let M : Set (Finset ℕ) → Set (Finset ℕ) := fun S => {A | Minimal (· ∈ S) A}
    (∀ S A, A ∈ S → ∃ B ∈ M S, B ⊆ A) ∧
    ∀ U V, M (U ∪ V) = M (M U ∪ M V) ∧
      M (Set.image2 (· ∪ ·) U V) = M (Set.image2 (· ∪ ·) (M U) (M V)))
    (antichainBound :
      let M : Set (Finset ℕ) → Set (Finset ℕ) := fun S => {A | Minimal (· ∈ S) A}
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 200 ≤ q → N = q^2+q+1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l) →
      ∀ (s o : ℕ) (F : ℕ → Set (Finset ℕ)), o < N+N+s → (∀ v < N+N, F v = {{v}}) →
      (∀ g < s, ∃ a < N+N+g, ∃ b < N+N+g,
        F (N+N+g) = M (Set.image2 (· ∪ ·) (F a) (F b)) ∨ F (N+N+g) = F a ∨
        F (N+N+g) = {∅} ∨ F (N+N+g) = M (F a ∪ F b)) →
      (∀ A ∈ F o, ∀ B ∈ F o, A ⊆ B → A = B) →
      (∀ A ∈ F o, ∀ p l : Fin N, I p l → p.val ∈ A ∨ N+l.val ∈ A) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N,
        (p.val ∈ A → ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A → p ∉ T)) → N*q ≤ 100*s) : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q N I inst hq hN degrees unique s o F ho leaves steps cover saturated
  let M : Set (Finset ℕ) → Set (Finset ℕ) := fun S => {A | Minimal (· ∈ S) A}
  let D := fun i => M (F i)
  have singleton (A : Finset ℕ) : M {A} = {A} := by
    ext B
    change Minimal (fun U => U ∈ ({A} : Set (Finset ℕ))) B ↔ B ∈ ({A} : Set (Finset ℕ))
    simp only [Set.mem_singleton_iff,minimal_eq_iff]
  apply antichainBound q N I hq hN degrees unique s o D ho
  · intro v hv
    exact (congrArg M (leaves v hv)).trans (singleton {v})
  · intro g hg
    obtain ⟨a,ha,b,hb,law⟩ := steps g hg
    refine ⟨a,ha,b,hb,?_⟩
    rcases law with join | copy | empty | meet
    · exact Or.inl ((congrArg M join).trans ((operations.2 (F a) (F b)).2))
    · exact Or.inr (Or.inl (congrArg M copy))
    · exact Or.inr (Or.inr (Or.inl ((congrArg M empty).trans (singleton ∅))))
    · exact Or.inr (Or.inr (Or.inr ((congrArg M meet).trans ((operations.2 (F a) (F b)).1))))
  · intro A hA B hB hAB
    exact Finset.Subset.antisymm hAB (hB.2 hA.1 hAB)
  · intro A hA p l inc
    exact cover A hA.1 p l inc
  · intro T hT
    obtain ⟨A,hA,shape⟩ := saturated T hT
    obtain ⟨B,hB,hBA⟩ := operations.1 (F o) A hA
    exact ⟨B,hB,fun p => ⟨fun h => (shape p).1.mp (hBA h),fun h => (shape p).2.mp (hBA h)⟩⟩

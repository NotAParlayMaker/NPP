import Mathlib
import PEqualNP.Defs

-- Use the rejected assignment formed by deleting one line from a pencil.
-- The counting part is a rank bound for partitions of the flag-pair matrix.
theorem PEqualNP.Outside.R_meta_3002_947
    (pencil : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      0 < q → N = q^2 + q + 1 → (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → ∀ r k, I r k →
      ∃ T : Finset (Fin N), T.card = q ∧ (∀ l, l ∈ T ↔ I r l ∧ l ≠ k) ∧
        (∀ p, (¬ ∃ l ∈ T, I p l) ↔ I p k ∧ p ≠ r))
    (routing : ∀ (q N s o : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      200 ≤ q → N = q^2 + q + 1 → (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      let E := {e : Fin N × Fin N // I e.1 e.2}
      let pair : E → Fin N × Fin N := Subtype.val
      let on := fun (e : E) (v : Fin N ⊕ Fin N) => v = .inl (pair e).1 ∨ v = .inr (pair e).2
      let off := fun (e : E) => Sum.elim
        (fun p => ¬ (I p (pair e).2 ∧ p ≠ (pair e).1)) (fun l => ¬ (I (pair e).1 l ∧ l ≠ (pair e).2))
      ∀ W : ℕ → Set (Bool × E), o < N+N+s →
        (∀ p : Fin N, W p.val = { z | ite (z.1 = true) (off z.2 (.inl p)) (¬ on z.2 (.inl p)) } ∧
          W (N+p.val) = { z | ite (z.1 = true) (off z.2 (.inr p)) (¬ on z.2 (.inr p)) }) →
        (∀ g < s, ∃ a < N+N+g, ∃ b < N+N+g,
          W (N+N+g) = W a ∩ W b ∨ W (N+N+g) = W a ∨
          W (N+N+g) = Set.univ ∨ W (N+N+g) = W a ∪ W b) →
        W o = { z | z.1 = true } →
        ∃ (m : ℕ) (R C : Fin m → Set E) (v : Fin m → Fin N ⊕ Fin N),
          m ≤ 99*s ∧ (∀ a b, ∃! j, a ∈ R j ∧ b ∈ C j) ∧
          (∀ j a, a ∈ R j → on a (v j)) ∧ (∀ j b, b ∈ C j → off b (v j)))
    (rank : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      let E := {e : Fin N × Fin N // I e.1 e.2}
      let pair : E → Fin N × Fin N := Subtype.val
      ∀ (m : ℕ) (R C : Fin m → Set E) (v : Fin m → Fin N ⊕ Fin N),
        (∀ a b, ∃! j, a ∈ R j ∧ b ∈ C j) →
        (∀ j a, a ∈ R j → v j = .inl (pair a).1 ∨ v j = .inr (pair a).2) →
        (∀ j b, b ∈ C j → Sum.elim
          (fun p => ¬ (I p (pair b).2 ∧ p ≠ (pair b).1)) (fun l => ¬ (I (pair b).1 l ∧ l ≠ (pair b).2)) (v j)) →
        N * (q + 1) ≤ N + N + m) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q N I inst large order degree unique s o F ho leaves steps sound complete
  let E := {e : Fin N × Fin N // I e.1 e.2}
  let allowed (z : Bool × E) (i : ℕ) : Prop :=
    if z.1 then
      (∀ p : Fin N, i = p.val → ¬ (I p z.2.val.2 ∧ p ≠ z.2.val.1)) ∧
      (∀ l : Fin N, i = N+l.val → ¬ (I z.2.val.1 l ∧ l ≠ z.2.val.2))
    else i ≠ z.2.val.1.val ∧ i ≠ N+z.2.val.2.val
  let W (w : ℕ) : Set (Bool × E) := {z | ∃ A ∈ F w, ∀ i ∈ A, allowed z i}
  have inputs (p : Fin N) :
      W p.val = {z | if z.1 then ¬ (I p z.2.val.2 ∧ p ≠ z.2.val.1) else p ≠ z.2.val.1} ∧
      W (N+p.val) = {z | if z.1 then ¬ (I z.2.val.1 p ∧ p ≠ z.2.val.2) else p ≠ z.2.val.2} := by
    have single (i : ℕ) (hi : i < N+N) (z : Bool × E) : z ∈ W i ↔ allowed z i := by
      simp [W, leaves i hi]
    have separate (a b : Fin N) : a.val ≠ N + b.val := by have := a.isLt; omega
    constructor <;> ext z
    · rw [single p.val (by have := p.isLt; omega)]
      cases hb : z.1
      · simp [allowed, hb, separate, Fin.val_inj]
      · simp only [allowed, hb, ite_true, Set.mem_ofPred_eq]
        constructor
        · exact fun h => h.1 p rfl
        · intro h
          refine ⟨?_, fun l eq => (separate p l eq).elim⟩
          intro a eq
          cases Fin.ext eq
          exact h
    · rw [single (N+p.val) (by have := p.isLt; omega)]
      cases hb : z.1
      · have apart : N+p.val ≠ z.2.val.1.val := Ne.symm (separate z.2.val.1 p)
        simp [allowed, hb, apart, Fin.val_inj]
      · simp only [allowed, hb, ite_true, Set.mem_ofPred_eq]
        constructor
        · exact fun h => h.2 p rfl
        · intro h
          refine ⟨fun a eq => (separate a p eq.symm).elim, ?_⟩
          intro l eq
          have hl : p = l := Fin.ext (by omega)
          cases hl
          exact h
  have gates : ∀ g < s, ∃ a < N+N+g, ∃ b < N+N+g,
      W (N+N+g) = W a ∩ W b ∨ W (N+N+g) = W a ∨
      W (N+N+g) = Set.univ ∨ W (N+N+g) = W a ∪ W b := by
    intro g hg
    obtain ⟨a, ha, b, hb, step⟩ := steps g hg
    refine ⟨a, ha, b, hb, ?_⟩
    rcases step with product | copy | unit | union
    · left
      ext z
      simp only [W, product, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_image2]
      constructor
      · rintro ⟨_, ⟨A, Amem, B, Bmem, rfl⟩, h⟩
        exact ⟨⟨A, Amem, fun i hi => h i (Finset.mem_union_left B hi)⟩,
          ⟨B, Bmem, fun i hi => h i (Finset.mem_union_right A hi)⟩⟩
      · rintro ⟨⟨A, Amem, hA⟩, ⟨B, Bmem, hB⟩⟩
        exact ⟨_, ⟨A, Amem, B, Bmem, rfl⟩, fun i hi => (Finset.mem_union.mp hi).elim (hA i) (hB i)⟩
    · exact Or.inr (Or.inl (by simp [W, copy]))
    · exact Or.inr (Or.inr (Or.inl (by ext z; simp [W, unit])))
    · right; right; right
      ext z
      simp only [W, union, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨A, hA | hA, h⟩
        · exact Or.inl ⟨A, hA, h⟩
        · exact Or.inr ⟨A, hA, h⟩
      · rintro (⟨A, hA, h⟩ | ⟨A, hA, h⟩)
        · exact ⟨A, Or.inl hA, h⟩
        · exact ⟨A, Or.inr hA, h⟩
  have output : W o = { z | z.1 = true } := by
    ext z
    rcases z with ⟨b, e⟩
    let r := e.val.1
    let k := e.val.2
    cases b
    · simp only [Set.mem_ofPred_eq, Bool.false_eq_true, iff_false]
      rintro ⟨A, Amem, hA⟩
      rcases sound A Amem r k e.property with h | h
      · exact (hA r.val h).1 rfl
      · exact (hA (N+k.val) h).2 rfl
    · simp only [Set.mem_ofPred_eq, iff_true]
      obtain ⟨T, Tcard, lineMem, pointAvoid⟩ := pencil q N I (by omega) order degree unique r k e.property
      obtain ⟨A, Amem, spec⟩ := complete T Tcard.le
      refine ⟨A, Amem, fun i hi => ⟨?_, ?_⟩⟩
      · rintro p rfl off
        exact ((pointAvoid p).mpr off) ((spec p).1.mp hi)
      · rintro l rfl off
        exact ((spec l).2.mp hi) ((lineMem l).mpr off)
  obtain ⟨m, R, C, v, bound, partition, onRow, offCol⟩ :=
    routing q N s o I large order degree unique W ho (by simpa using inputs) gates output
  have count := rank q N I degree m R C v partition onRow offCol
  rw [Nat.mul_add, Nat.mul_one] at count
  have orderBound := Nat.mul_le_mul_left N large
  omega

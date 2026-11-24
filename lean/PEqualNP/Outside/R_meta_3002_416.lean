import Mathlib
import PEqualNP.Defs

-- A row is a point-line pair and a column is a set of lines.
-- Each gate gives a rectangle covered by its two predecessors. At an incident row,
-- every sparse column reaches the output. The geometric bound uses only rectangles.
theorem PEqualNP.Outside.R_meta_3002_416
    (extract : ∀ (X Y : Type) (m s : ℕ) (F : ℕ → Set (Finset ℕ))
      (P : X → Finset ℕ) (Q : Y → Finset ℕ),
      (∀ i < m, F i = {{i}}) →
      (∀ g < s, ∃ a < m+g, ∃ b < m+g,
        F (m+g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (m+g) = F a ∨
        F (m+g) = {∅} ∨ F (m+g) = F a ∪ F b) →
      ∃ R : ℕ → Set (X × Y), (∀ i, ∃ U V, R i = Set.prod U V) ∧
        (∀ i < m, ∀ z ∈ R i, i ∈ P z.1 ∧ i ∈ Q z.2) ∧
        (∀ g < s, ∃ a < m+g, ∃ b < m+g, R (m+g) ⊆ R a ∪ R b) ∧
        ∀ i x y, (∀ A ∈ F i, ∃ v ∈ A, v ∈ P x) → Q y ∈ F i → (x,y) ∈ R i)
    (packing : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      200 ≤ q → N = q^2+q+1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      ∀ (s o : ℕ) (R : ℕ → Set ((Fin N × Fin N) × Finset (Fin N))),
      o < N+N+s → (∀ i, ∃ U V, R i = Set.prod U V) →
      (∀ p : Fin N, (∀ z ∈ R p.val, z.1.1 = p ∧ ∃ l ∈ z.2, I p l) ∧
        (∀ z ∈ R (N+p.val), z.1.2 = p ∧ p ∉ z.2)) →
      (∀ g < s, ∃ a < N+N+g, ∃ b < N+N+g, R (N+N+g) ⊆ R a ∪ R b) →
      (∀ p l : Fin N, I p l → ∀ T : Finset (Fin N), T.card ≤ q → ((p,l),T) ∈ R o) → N*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I inst hq order degree join s o F ho leaves gates covers saturated
  let P := fun z : Fin N × Fin N => ({z.1.val, N+z.2.val} : Finset ℕ)
  let Q := fun T : Finset (Fin N) => if h : T.card ≤ q then (saturated T h).choose else ∅
  have spec (T : Finset (Fin N)) (h : T.card ≤ q) :
      Q T ∈ F o ∧ ∀ p : Fin N,
        (p.val ∈ Q T ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ Q T ↔ p ∉ T) := by
    simpa only [Q, dif_pos h] using (saturated T h).choose_spec
  have sparse (i : ℕ) (T : Finset (Fin N)) (h : i ∈ Q T) : T.card ≤ q := by
    by_contra large
    simpa [Q, large] using h
  obtain ⟨R, rectangles, terminals, parents, root⟩ :=
    extract _ _ (N+N) s F P Q leaves gates
  refine packing q N I hq order degree join s o R ho rectangles ?_ parents ?_
  · intro p
    constructor
    · intro z hz
      obtain ⟨hp, hq'⟩ := terminals p.val (by omega) z hz
      change p.val ∈ ({z.1.1.val, N+z.1.2.val} : Finset ℕ) at hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      exact ⟨Fin.ext (by have := p.isLt; omega), ((spec z.2 (sparse _ _ hq')).2 p).1.mp hq'⟩
    · intro z hz
      obtain ⟨hp, hq'⟩ := terminals (N+p.val) (by omega) z hz
      change N+p.val ∈ ({z.1.1.val, N+z.1.2.val} : Finset ℕ) at hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      exact ⟨Fin.ext (by have := z.1.1.isLt; omega), ((spec z.2 (sparse _ _ hq')).2 p).2.mp hq'⟩
  · intro p l inc T small
    refine root o (p,l) T ?_ (spec T small).1
    intro A hA
    rcases covers A hA p l inc with h | h
    · exact ⟨p.val, h, by simp [P]⟩
    · exact ⟨N+l.val, h, by simp [P]⟩

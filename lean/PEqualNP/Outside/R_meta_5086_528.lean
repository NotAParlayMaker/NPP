import Mathlib
import PEqualNP.Defs

-- The first case charges each flag to the first wire containing its empty and singleton columns.
-- The second prices selectors whose descendant paths use only point inputs.
theorem PEqualNP.Outside.R_meta_5086_528
    (boundedBirths :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        1 ≤ q →
        (∀ l, Fintype.card {p // I p l} = q+1) →
        ∀ (s o : ℕ) (R : ℕ → Set (Fin n × Fin n) × Set (Finset (Fin n))),
          let box (w : ℕ) := (R w).1 ×ˢ (R w).2
          let pair (w : ℕ) (e : Fin n × Fin n) :=
            (e,∅) ∈ box w ∧ (e,{e.2}) ∈ box w
          let starts (w : ℕ) := {e | I e.1 e.2 ∧ pair w e ∧ ∀ v < w, ¬ pair v e}
          o < n+n+s →
          (∀ (i : Fin (n+n)) p l T, ((p,l),T) ∈ box i →
            (i = Fin.castAdd n p ∧ ∃ t ∈ T, I p t) ∨ (i = Fin.natAdd n l ∧ l ∉ T)) →
          {e | I e.1 e.2} ×ˢ {T : Finset (Fin n) | T.card ≤ q} ⊆ box o →
          (∀ j<s, (starts (n+n+j)).ncard ≤ 100) →
          n*q ≤ 100*s)
    (pointSelectors :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        (∀ l, Fintype.card {p // I p l} = q+1) →
        (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
        ∀ (s : ℕ) (R : ℕ → Set (Fin n × Fin n) × Set (Finset (Fin n))),
          let box (w : ℕ) := (R w).1 ×ˢ (R w).2
          let pointPhase (P : ℕ → Prop) :=
            (∀ w < n+n, P w → w<n) ∧
            (∀ j<s, let w := n+n+j; P w → ∃ a b,
              a < b ∧ b < w ∧ P a ∧ P b ∧ box w ⊆ box a ∪ box b) ∧
            (∀ l : Fin n, ∃ w<n+n+s, P w ∧ ∀ p, I p l → ((p,l),{l}) ∈ box w)
          (∀ (i : Fin (n+n)) p l T, ((p,l),T) ∈ box i →
            (i = Fin.castAdd n p ∧ ∃ t ∈ T, I p t) ∨ (i = Fin.natAdd n l ∧ l ∉ T)) →
          (∃ P, pointPhase P) → n*q ≤ s)
    (remaining :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        250 ≤ q →
        n = q^2+q+1 →
        (∀ l, Fintype.card {p // I p l} = q+1) →
        (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
        ∀ (s o : ℕ) (R : ℕ → Set (Fin n × Fin n) × Set (Finset (Fin n))),
          let box (w : ℕ) := (R w).1 ×ˢ (R w).2
          let pair (w : ℕ) (e : Fin n × Fin n) :=
            (e,∅) ∈ box w ∧ (e,{e.2}) ∈ box w
          let starts (w : ℕ) := {e | I e.1 e.2 ∧ pair w e ∧ ∀ v < w, ¬ pair v e}
          let pointPhase (P : ℕ → Prop) :=
            (∀ w < n+n, P w → w<n) ∧
            (∀ j<s, let w := n+n+j; P w → ∃ a b,
              a < b ∧ b < w ∧ P a ∧ P b ∧ box w ⊆ box a ∪ box b) ∧
            (∀ l : Fin n, ∃ w<n+n+s, P w ∧ ∀ p, I p l → ((p,l),{l}) ∈ box w)
          o < n+n+s →
          (∀ (i : Fin (n+n)) p l T, ((p,l),T) ∈ box i →
            (i = Fin.castAdd n p ∧ ∃ t ∈ T, I p t) ∨ (i = Fin.natAdd n l ∧ l ∉ T)) →
          (∀ j < s, ∃ a b, a < b ∧ b < n+n+j ∧ box (n+n+j) ⊆ box a ∪ box b) →
          {e | I e.1 e.2} ×ˢ {T : Finset (Fin n) | T.card ≤ q} ⊆ box o →
          (∃ j<s, 100 < (starts (n+n+j)).ncard) →
          (¬ ∃ P, pointPhase P) →
          n*q ≤ 100*s) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (250 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Fin x2 × Fin x2) × Set (Finset (Fin x2))),             have x12 : ℕ → Set ((Fin x2 × Fin x2) × Finset (Fin x2)) := fun (x12 : ℕ) => (x11 x12).1 ×ˢ (x11 x12).2;             x10 < x2 + x2 + x9 → (∀ (x14 : Fin (x2 + x2)) (x15 x16 : Fin x2) (x17 : Finset (Fin x2)), ((x15, x16), x17) ∈ x12 ↑x14 → (x14 = Fin.castAdd x2 x15 ∧ ∃ x19 ∈ x17, x3 x15 x19) ∨ x14 = Fin.natAdd x2 x16 ∧ x16 ∉ x17) → (∀ x15 < x9, ∃ (x17 : ℕ) (x18 : ℕ), x17 < x18 ∧ x18 < x2 + x2 + x15 ∧ x12 (x2 + x2 + x15) ⊆ x12 x17 ∪ x12 x18) → {x16 : Fin x2 × Fin x2 | x3 x16.1 x16.2} ×ˢ {x16 : Finset (Fin x2) | x16.card ≤ x1} ⊆ x12 x10 → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q n I rel large size degree unique s o R
  dsimp only
  intro out raw splits cover
  let box (w : ℕ) := (R w).1 ×ˢ (R w).2
  let pair (w : ℕ) (e : Fin n × Fin n) :=
    (e,∅) ∈ box w ∧ (e,{e.2}) ∈ box w
  let starts (w : ℕ) := {e | I e.1 e.2 ∧ pair w e ∧ ∀ v < w, ¬ pair v e}
  let pointPhase (P : ℕ → Prop) :=
    (∀ w < n+n, P w → w<n) ∧
    (∀ j<s, let w := n+n+j; P w → ∃ a b,
      a < b ∧ b < w ∧ P a ∧ P b ∧ box w ⊆ box a ∪ box b) ∧
    (∀ l : Fin n, ∃ w<n+n+s, P w ∧ ∀ p, I p l → ((p,l),{l}) ∈ box w)
  by_cases cap : ∀ j<s, (starts (n+n+j)).ncard ≤ 100
  · exact boundedBirths q n I (by omega) degree s o R out raw cover cap
  by_cases selectors : ∃ P, pointPhase P
  · have enough := pointSelectors q n I degree unique s R raw selectors
    omega
  have peak : ∃ j<s, 100 < (starts (n+n+j)).ncard := by
    push Not at cap
    exact cap
  exact remaining q n I large size degree unique s o R out raw splits cover peak selectors

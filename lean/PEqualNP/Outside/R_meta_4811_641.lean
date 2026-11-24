import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Use explicit incident-pair and two-sided independent-set closure rows for the tail circuit.
-- The first child strengthens the six-point geometry in L-meta-1475's reduction PR #8204.
set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.R_meta_4811_641
  (boundary : have D : Finset (Fin 21) := {0,5,7,17,20}
    have f : (Fin (42 : ℕ) → Bool) → Prop := fun (x1 : Fin (42 : ℕ) → Bool) => ∃ (x2 : Fin (42 : ℕ)) (x3 : Fin (42 : ℕ)), (↑x2 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x3 ∧ (↑x3 + (21 : ℕ) - ↑x2) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true;
    ∀ E : (Fin 42 → Bool) → Bool,
      (      (∀ i j : Fin 21, j-i ∈ D → E (Fin.append (fun p => decide (p=i)) (fun l => decide (l=j))) = true) ∧
      (∀ P : Finset (Fin 21), (P.card ≤ 5 ∨ P.card = 6 ∧
        ∃ L : Finset (Fin 21), L.card = 6 ∧ ∀ p ∈ P, ∀ l ∈ L, l-p ∉ D) →
        E (Fin.append (fun p => decide (p ∈ P)) (fun l => decide (∀ p ∈ P, l-p ∉ D))) = false) ∧
      ∀ L : Finset (Fin 21), L.card ≤ 5 →
        E (Fin.append (fun p => decide (∀ l ∈ L, l-p ∉ D)) (fun l => decide (l ∈ L))) = false) →
      ∀ x : Fin 42 → Bool, ((f x ∧ ∀ (x7 : Fin (42 : ℕ) → Bool), (∀ (x8 : Fin (42 : ℕ)), x7 x8 = Bool.true → x x8 = Bool.true) → f x7 → x7 = x) ∨ ¬f x ∧ ∀ (x7 : Fin (42 : ℕ) → Bool), (∀ (x8 : Fin (42 : ℕ)), x x8 = Bool.true → x7 x8 = Bool.true) → ¬f x7 → x7 = x)  → (E x = true ↔ f x))
  (tested : have D : Finset (Fin 21) := {0, 5, 7, 17, 20}
    ∃ (v : Fin 42) (a b : Fin 43) (C : Circuit) (E : (Fin 42 → Bool) → Bool),
      (v = 1 ∨ v = 21 ∨ v = 22) ∧ a < b ∧ (a,b) ≠ (0,v.castSucc) ∧
      (b = Fin.last 42 → a ≠ 0 ∧ a ≠ v.castSucc) ∧
      (∀ i : Fin 42, List.count i.val [0,v.val,a.val,b.val] = 1 → ∃ g ∈ C.gates, i.val ∈ g.inputs) ∧
      Monotone2 C ∧ NestedCover.ReadsBack 44 C ∧ C.size ≤ 122 ∧
      E = (fun x =>
        have y : Fin 43 → Bool := fun s => Fin.lastCases (x 0 || x v) x s
        C.eval (List.ofFn fun s => Fin.lastCases (y a || y b) y s)) ∧
      (∀ i j : Fin 21, j-i ∈ D → E (Fin.append (fun p => decide (p=i)) (fun l => decide (l=j))) = true) ∧
      (∀ P : Finset (Fin 21), (P.card ≤ 5 ∨ P.card = 6 ∧
        ∃ L : Finset (Fin 21), L.card = 6 ∧ ∀ p ∈ P, ∀ l ∈ L, l-p ∉ D) →
        E (Fin.append (fun p => decide (p ∈ P)) (fun l => decide (∀ p ∈ P, l-p ∉ D))) = false) ∧
      ∀ L : Finset (Fin 21), L.card ≤ 5 →
        E (Fin.append (fun p => decide (∀ l ∈ L, l-p ∉ D)) (fun l => decide (l ∈ L))) = false) :
  have x1 : (Fin (42 : ℕ) → Bool) → Prop := fun (x1 : Fin (42 : ℕ) → Bool) => ∃ (x2 : Fin (42 : ℕ)) (x3 : Fin (42 : ℕ)), (↑x2 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x3 ∧ (↑x3 + (21 : ℕ) - ↑x2) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∃ (x2 : Fin (42 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : Fin (43 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (x2 = (1 : Fin (42 : ℕ)) ∨ x2 = (21 : Fin (42 : ℕ)) ∨ x2 = (22 : Fin (42 : ℕ))) ∧     x3 < x4 ∧       (x3, x4) ≠ ((0 : Fin (43 : ℕ)), x2.castSucc) ∧         (x4 = Fin.last (42 : ℕ) → x3 ≠ (0 : Fin (43 : ℕ)) ∧ x3 ≠ x2.castSucc) ∧           (∀ (x6 : Fin (42 : ℕ)), List.count ↑x6 [(0 : ℕ), ↑x2, ↑x3, ↑x4] = (1 : ℕ) → ∃ x8 ∈ x5.gates, ↑x6 ∈ x8.inputs) ∧             PEqualNP.MetaComplexity.Monotone2 x5 ∧               PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x5 ∧                 x5.size ≤ (122 : ℕ) ∧                   ∀ (x6 : Fin (42 : ℕ) → Bool),                     ((x1 x6 ∧ ∀ (x7 : Fin (42 : ℕ) → Bool), (∀ (x8 : Fin (42 : ℕ)), x7 x8 = Bool.true → x6 x8 = Bool.true) → x1 x7 → x7 = x6) ∨ ¬x1 x6 ∧ ∀ (x7 : Fin (42 : ℕ) → Bool), (∀ (x8 : Fin (42 : ℕ)), x6 x8 = Bool.true → x7 x8 = Bool.true) → ¬x1 x7 → x7 = x6) →                       have x8 : Fin (43 : ℕ) → Bool := fun (x8 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 (0 : Fin (42 : ℕ)) || x6 x2) x6 x8;                       x5.eval (List.ofFn fun (x9 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 x3 || x8 x4) x8 x9) = Bool.true ↔ x1 x6 := by
  intro f
  obtain ⟨v,a,b,C,E,hv,hab,hne,hlast,hread,hmono,hback,hsize,hE,tests⟩ := tested
  refine ⟨v,a,b,C,hv,hab,hne,hlast,hread,hmono,hback,hsize,?_⟩
  intro x hx
  have ans := boundary E tests x hx
  rw [hE] at ans
  exact ans

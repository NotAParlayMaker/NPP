import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Operations

-- The input count uses the circuit dependency argument of R_meta_2794_601.
-- Monotonicity extends the two test families to exactness on every sparse line input.
theorem PEqualNP.Outside.R_meta_3364_731
    (boundedSupport : ∀ {Z : Type} (m g o : ℕ) (X : ℕ → Set Z), o < m+g →
      (∀ i < g, ∃ a < m+i, ∃ b < m+i,
        X (m+i) = X a ∪ X b ∨ X (m+i) = X a ∨ X (m+i) = ∅ ∨ X (m+i) = X a ∩ X b) →
      ∃ S : Finset ℕ, S.card ≤ g+1 ∧ (∀ j ∈ S, j < m) ∧
        ∀ u v : Z, (∀ j ∈ S, u ∈ X j → v ∈ X j) → u ∈ X o → v ∈ X o)
    (large : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      199 ≤ q → N = q^2+q+1 →
      (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      let V := Fin N → Bool
      ∀ (g o : ℕ) (T : Finset ℕ) (X : ℕ → Set (V × V)), o < N+N+g →
      (∀ i : Fin N, X i.val = {z | z.1 i = true} ∧ X (N+i.val) = {z | z.2 i = true}) →
      (∀ i < g, ∃ a < N+N+i, ∃ b < N+N+i,
        let u := X a
        let v := X b
        let w := X (N+N+i)
        w = u ∪ v ∨ w = u ∨ w = ∅ ∨ w = u ∩ v ∧
          (i ∈ T ∨ ∃ P L : Set V, u = P ×ˢ Set.univ ∧ v = Set.univ ×ˢ L)) →
      100*T.card < N*q →
      (∀ x y : V, Fintype.card {l // y l = true} ≤ q →
        ((x,y) ∈ X o ↔ ∃ p l, x p = true ∧ y l = true ∧ I p l)) →
      N*(q+1) ≤ 100*g) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → ∃ (x19 : Fin x9 → Finset (Fin x2)) (x20 : Fin x9 → Finset (Fin x2)), (∀ (x21 : Fin x9), ∀ x22 ∈ x19 x21, ∀ x24 ∈ x20 x21, x3 x22 x24) ∧ (∀ (x21 x22 : Fin x2), x3 x21 x22 → ∃ (x24 : Fin x9), x21 ∈ x19 x24 ∧ x22 ∈ x20 x24) ∧ ∑ x21 : Fin x9, ((x19 x21).card + (x20 x21).card) ≤ (100 : ℕ) * x9 + x2 := by
  have inputCount (q N g o : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (hq : 0 < q) (pt : ∀ p, ∃ l, I p l) (ln : ∀ l, ∃ p, I p l)
      (X : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (ho : o < N+N+g)
      (inputs : ∀ i : Fin N,
        X i.val = {z | z.1 i = true} ∧ X (N+i.val) = {z | z.2 i = true})
      (steps : ∀ i < g, ∃ a < N+N+i, ∃ b < N+N+i,
        X (N+N+i) = X a ∪ X b ∨ X (N+N+i) = X a ∨ X (N+N+i) = ∅ ∨ X (N+N+i) = X a ∩ X b)
      (pos : ∀ p l, I p l → (fun i => decide (i=p), fun i => decide (i=l)) ∈ X o)
      (neg : ∀ y : Fin N → Bool, Fintype.card {i // y i = true} ≤ q →
        (fun p => decide (¬ ∃ l, I p l ∧ y l = true), y) ∉ X o) : N+N ≤ g+1 := by
    obtain ⟨S,card,bound,dep⟩ := boundedSupport (N+N) g o X ho steps
    have points (p : Fin N) : p.val ∈ S := by
      by_contra missing
      obtain ⟨l,hit⟩ := pt p
      let y := fun i : Fin N => decide (i=l)
      have small : Fintype.card {i // y i = true} ≤ q := by
        simpa [Fintype.card_subtype, y] using (show 1 ≤ q by omega)
      apply neg y small
      apply dep _ _ _ (pos p l hit)
      intro j hj truth
      by_cases first : j < N
      · let i : Fin N := ⟨j,first⟩
        rw [(inputs i).1] at truth
        change decide (i=p) = true at truth
        have eq : j = p.val := congrArg Fin.val (of_decide_eq_true truth)
        exact False.elim (missing (eq ▸ hj))
      · let i : Fin N := ⟨j-N,by have := bound j hj; omega⟩
        have eq : j = N+i.val := by dsimp [i]; omega
        rw [eq,(inputs i).2] at truth ⊢
        exact truth
    have lines (l : Fin N) : N+l.val ∈ S := by
      by_contra missing
      obtain ⟨p,hit⟩ := ln l
      let y := fun _ : Fin N => false
      have small : Fintype.card {i // y i = true} ≤ q := by simp [y]
      apply neg y small
      apply dep _ _ _ (pos p l hit)
      intro j hj truth
      by_cases first : j < N
      · let i : Fin N := ⟨j,first⟩
        rw [(inputs i).1]
        change decide (¬ ∃ l, I i l ∧ y l = true) = true
        simp [y]
      · let i : Fin N := ⟨j-N,by have := bound j hj; omega⟩
        have eq : j = N+i.val := by dsimp [i]; omega
        rw [eq,(inputs i).2] at truth
        change decide (i=l) = true at truth
        have e := congrArg (fun k : Fin N => N+k.val) (of_decide_eq_true truth)
        exact False.elim (missing ((eq.trans e) ▸ hj))
    have sub : Finset.range (N+N) ⊆ S := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      by_cases first : j < N
      · exact points ⟨j,first⟩
      · let i : Fin N := ⟨j-N,by omega⟩
        have eq : N+i.val = j := by dsimp [i]; omega
        exact eq ▸ lines i
    exact le_trans (by simpa using Finset.card_le_card sub) card
  have smallOrderBudget (q N g : ℕ) (hq : 100 < q) (hsmall : q ≤ 198)
      (order : N = q^2+q+1) (count : N+N ≤ g+1) :
      N ≤ g ∧ N*(q+2) ≤ 100*g+N := by
    have hn : 100 ≤ N := by omega
    have bound := Nat.mul_le_mul_left N (show q+1 ≤ 199 by omega)
    have step : N*(q+2) = N*(q+1)+N := Nat.mul_succ N (q+1)
    constructor <;> omega
  have nonisolated (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (hN : 2 ≤ N) (degree : ∀ l, Fintype.card {p // I p l} = q+1)
      (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) :
      (∀ p, ∃ l, I p l) ∧ (∀ l, ∃ p, I p l) := by
    constructor
    · intro p
      let r : Fin N := if p.val = 0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
      have ne : p ≠ r := by
        intro h
        have e := congrArg Fin.val h
        unfold r at e
        split at e
        · change p.val = 1 at e; omega
        · change p.val = 0 at e; contradiction
      obtain ⟨l,hl,_⟩ := unique p r ne
      exact ⟨l,hl.1⟩
    · intro l
      have h : 0 < Fintype.card {p // I p l} := by rw [degree]; omega
      obtain ⟨⟨p,hp⟩⟩ := Fintype.card_pos_iff.mp h
      exact ⟨p,hp⟩
  have columnStars {N g k B : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
      (hcard : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = k)
      (hslots : N ≤ g) (hbudget : N * (k + 1) ≤ B) :
      ∃ A C : Fin g → Finset (Fin N),
        (∀ j, ∀ p ∈ A j, ∀ l ∈ C j, I p l) ∧
        (∀ p l, I p l → ∃ j, p ∈ A j ∧ l ∈ C j) ∧
        ∑ j, ((A j).card + (C j).card) ≤ B := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hslots
    let star (l : Fin N) := Finset.univ.filter fun p => I p l
    have hstar (l : Fin N) : (star l).card = k := by
      exact (Fintype.card_subtype (fun p => I p l)).symm.trans (hcard l)
    let A : Fin (N + d) → Finset (Fin N) :=
      Fin.addCases (motive := fun _ => Finset (Fin N)) star (fun _ => ∅)
    let C : Fin (N + d) → Finset (Fin N) :=
      Fin.addCases (motive := fun _ => Finset (Fin N)) (fun l => {l}) (fun _ => ∅)
    refine ⟨A, C, ?_, ?_, ?_⟩
    · intro j
      refine Fin.addCases (motive := fun i => ∀ p ∈ A i, ∀ l ∈ C i, I p l) ?_ ?_ j
      · intro i p hp l hl
        have heq : l = i := by simpa [C] using hl
        subst l
        simpa [A, star] using hp
      · intro i p hp
        simp [A] at hp
    · intro p l hpl
      refine ⟨Fin.castAdd d l, ?_, ?_⟩
      · simpa [A, star] using hpl
      · simp [C]
    · rw [Fin.sum_univ_add]
      simpa [A, C, hstar, nsmul_eq_mul] using hbudget
  intro q N I inst hq order degree unique g o tags X out inputs steps pos neg marked
  have simple : ∀ i < g, ∃ a < N+N+i, ∃ b < N+N+i,
      X (N+N+i) = X a ∪ X b ∨ X (N+N+i) = X a ∨ X (N+N+i) = ∅ ∨ X (N+N+i) = X a ∩ X b := by
    intro i hi
    obtain ⟨a,ha,b,hb,law⟩ := steps i hi
    exact ⟨a,ha,b,hb,law.imp_right (Or.imp_right (Or.imp_right And.left))⟩
  obtain ⟨S,_,bound,dep⟩ := boundedSupport (N+N) g o X out simple
  have mono (x y x' y' : Fin N → Bool) (hx : ∀ i, x i = true → x' i = true)
      (hy : ∀ i, y i = true → y' i = true) : (x,y) ∈ X o → (x',y') ∈ X o := by
    apply dep
    intro j hj
    by_cases lo : j < N
    · let i : Fin N := ⟨j,lo⟩
      rw [(inputs i).1]
      exact hx i
    · let i : Fin N := ⟨j-N, by have := bound j hj; omega⟩
      have e : j = N+i.val := by dsimp [i]; omega
      rw [e, (inputs i).2]
      exact hy i
  have sparse (x y : Fin N → Bool) (hy : Fintype.card {l // y l = true} ≤ q) :
      (x,y) ∈ X o ↔ ∃ p l, x p = true ∧ y l = true ∧ I p l := by
    constructor
    · intro hacc
      by_contra no
      apply neg y hy
      apply mono _ _ _ _ _ (fun _ h => h) hacc
      intro p hp
      apply decide_eq_true
      rintro ⟨l,hit,hl⟩
      exact no ⟨p,l,hp,hl,hit⟩
    · rintro ⟨p,l,hp,hl,hit⟩
      apply mono _ _ _ _ _ _ (pos p l hit)
      · intro i hi
        have e : i = p := of_decide_eq_true hi
        simpa [e] using hp
      · intro i hi
        have e : i = l := of_decide_eq_true hi
        simpa [e] using hl
  have budget : N ≤ g ∧ N*(q+2) ≤ 100*g+N := by
    by_cases small : q ≤ 198
    · obtain ⟨pt,ln⟩ := nonisolated q N I (by omega) degree unique
      exact smallOrderBudget q N g hq small order
        (inputCount q N g o I (by omega) pt ln X out inputs simple pos neg)
    · have lower := large q N I (by omega) order degree unique g o tags X out inputs steps marked sparse
      have factor : N*100 ≤ N*(q+1) := Nat.mul_le_mul_left N (by omega)
      have e : N*(q+2) = N*(q+1)+N := Nat.mul_succ N (q+1)
      constructor <;> omega
  exact columnStars I degree budget.1 budget.2

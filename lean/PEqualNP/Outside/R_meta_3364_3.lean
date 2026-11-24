import PEqualNP.Defs

-- Discard a mark whenever its wire admits any allowed unmarked expression.
-- No wire value, input profile, or circuit budget changes.
theorem PEqualNP.Outside.R_meta_3364_3 :
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      100 < q → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      let U := Fin N → Bool
      let e := fun (p r : Fin N) => decide (r = p)
      ∀ (m o : ℕ) (W : ℕ → Set (U × U)),
      let n := N+N
      let easy := fun i => ∃ a < n+i, ∃ b < n+i,
        let z := W (n+i)
        z ∈ [W a ∪ W b, W a, ∅] ∨
        z = W a ∩ W b ∧ (∃ S T : Set U, W a = S ×ˢ Set.univ ∧ W b = Set.univ ×ˢ T)
      o < n+m →
      (∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true}) →
      (∀ p l, I p l → (e p,e l) ∈ W o) →
      (∀ y : U, Fintype.card {l : Fin N // y l = true} ≤ q →
        ((fun p => decide (¬∃ l, I p l ∧ y l = true)),y) ∉ W o) →
      (∀ i < m, easy i) →
      N*(q+1) ≤ 100*m) →
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      100 < q → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      let U := Fin N → Bool
      let e := fun (p r : Fin N) => decide (r = p)
      ∀ (m o : ℕ) (M : Finset ℕ) (W : ℕ → Set (U × U)),
      let n := N+N
      let easy := fun i => ∃ a < n+i, ∃ b < n+i,
        let z := W (n+i)
        z ∈ [W a ∪ W b, W a, ∅] ∨
        z = W a ∩ W b ∧ (∃ S T : Set U, W a = S ×ˢ Set.univ ∧ W b = Set.univ ×ˢ T)
      o < n+m →
      (∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true}) →
      (∀ p l, I p l → (e p,e l) ∈ W o) →
      (∀ y : U, Fintype.card {l : Fin N // y l = true} ≤ q →
        ((fun p => decide (¬∃ l, I p l ∧ y l = true)),y) ∉ W o) →
      (∀ i < m, easy i ∨ i ∈ M ∧ ∃ a < n+i, ∃ b < n+i, W (n+i) = W a ∩ W b) →
      (∀ i ∈ M, ¬easy i) → M.Nonempty → 100*M.card < N*q →
      N*(q+1) ≤ 100*m) →
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → ∃ (x19 : Fin x9 → Finset (Fin x2)) (x20 : Fin x9 → Finset (Fin x2)), (∀ (x21 : Fin x9), ∀ x22 ∈ x19 x21, ∀ x24 ∈ x20 x21, x3 x22 x24) ∧ (∀ (x21 x22 : Fin x2), x3 x21 x22 → ∃ (x24 : Fin x9), x21 ∈ x19 x24 ∧ x22 ∈ x20 x24) ∧ ∑ x21 : Fin x9, ((x19 x21).card + (x20 x21).card) ≤ (100 : ℕ) * x9 + x2 := by
  intro no_marks irreducible q N I inst hq hN degree unique m o M W hout base original positive negative hmark
  classical
  let U := Fin N → Bool
  let n := N+N
  let easy : ℕ → Prop := fun i => ∃ a < n+i, ∃ b < n+i,
    let z := W (n+i)
    z ∈ [W a ∪ W b, W a, ∅] ∨
    z = W a ∩ W b ∧ (∃ S T : Set U, W a = S ×ˢ Set.univ ∧ W b = Set.univ ×ˢ T)
  let kept := M.filter fun i => i < m ∧ ¬ easy i
  have hkeep (i : ℕ) (hi : i < m) :
      easy i ∨ i ∈ kept ∧ ∃ a < n+i, ∃ b < n+i, W (n+i) = W a ∩ W b := by
    by_cases h : easy i
    · exact Or.inl h
    obtain ⟨a,ha,b,hb,eq⟩ := original i hi
    rcases eq with eq | eq | eq | ⟨eq,marked | axis⟩
    · exact False.elim (h ⟨a,ha,b,hb,Or.inl (by simp [n,eq])⟩)
    · exact False.elim (h ⟨a,ha,b,hb,Or.inl (by simp [n,eq])⟩)
    · exact False.elim (h ⟨a,ha,b,hb,Or.inl (by simp [n,eq])⟩)
    · exact Or.inr ⟨Finset.mem_filter.mpr ⟨marked,hi,h⟩,a,ha,b,hb,eq⟩
    · exact False.elim (h ⟨a,ha,b,hb,Or.inr ⟨eq,axis⟩⟩)
  have density : N*(q+1) ≤ 100*m := by
    by_cases nonempty : kept.Nonempty
    · have hkept : 100 * kept.card < N*q := by
        have hle : kept.card ≤ M.card :=
          Finset.card_le_card (Finset.filter_subset (fun i => i < m ∧ ¬easy i) M)
        omega
      exact irreducible q N I hq hN degree unique m o kept W hout base positive negative hkeep
        (fun i h => (Finset.mem_filter.mp h).2.2) nonempty hkept
    · apply no_marks q N I hq hN degree unique m o W hout base positive negative
      intro i hi
      exact (hkeep i hi).resolve_right (fun h => nonempty ⟨i,h.1⟩)
  have enough : N ≤ m := by
    have h := Nat.mul_le_mul_left N (show 100 ≤ q+1 by omega)
    rw [Nat.mul_comm N 100] at h
    omega
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le enough
  let A : Fin (N+k) → Finset (Fin N) := Fin.addCases
    (fun l => Finset.univ.filter (fun p => I p l)) (fun _ => ∅)
  let B : Fin (N+k) → Finset (Fin N) := Fin.addCases (fun l => {l}) (fun _ => ∅)
  refine ⟨A,B,?_,?_,?_⟩
  · intro i
    induction i using Fin.addCases with
    | left l => simp [A,B]
    | right t => simp [A,B]
  · intro p l h
    exact ⟨Fin.castAdd k l, by simpa [A] using h, by simp [B]⟩
  · rw [Fin.sum_univ_add]
    simpa [A,B, ← Fintype.card_subtype, degree, Nat.mul_add] using
      (show N*(q+1)+N ≤ 100*(N+k)+N by omega)

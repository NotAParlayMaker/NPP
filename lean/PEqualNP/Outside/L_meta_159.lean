import Mathlib
import PEqualNP.Defs

private theorem L159_tag {k : ℕ} (A : Fin k → Finset (Sym2 (Fin 5)))
    (B : Fin k → Finset (Finset (Fin 5))) (t : Fin k → Fin 5)
    (hA : ∀ i, ∀ e ∈ A i, t i ∈ e) (hB : ∀ i, ∀ I ∈ B i, t i ∉ I)
    (x y : Fin 5) (I : Finset (Fin 5)) (hx : x ∈ I) (i : Fin k)
    (hi : s(x, y) ∈ A i ∧ I ∈ B i) : t i = y := by
  rcases Sym2.mem_iff.mp (hA i _ hi.1) with h | h
  · exact absurd (h ▸ hx) (hB i I hi.2)
  · exact h

private theorem L159_tag' {k : ℕ} (A : Fin k → Finset (Sym2 (Fin 5)))
    (B : Fin k → Finset (Finset (Fin 5))) (t : Fin k → Fin 5)
    (hA : ∀ i, ∀ e ∈ A i, t i ∈ e) (hB : ∀ i, ∀ I ∈ B i, t i ∉ I)
    (x y : Fin 5) (I : Finset (Fin 5)) (hy : y ∈ I) (i : Fin k)
    (hi : s(x, y) ∈ A i ∧ I ∈ B i) : t i = x := by
  rcases Sym2.mem_iff.mp (hA i _ hi.1) with h | h
  · exact h
  · exact absurd (h ▸ hy) (hB i I hi.2)

private theorem L159_tri {k : ℕ} (A : Fin k → Finset (Sym2 (Fin 5)))
    (B : Fin k → Finset (Finset (Fin 5))) (t : Fin k → Fin 5)
    (hA : ∀ i, ∀ e ∈ A i, t i ∈ e) (hB : ∀ i, ∀ I ∈ B i, t i ∉ I)
    (z a b : Fin 5) (Z Bc Bd Ac Ad : Finset (Fin 5))
    (hzZ : z ∈ Z) (hbBc : b ∈ Bc) (hbBd : b ∈ Bd) (haAc : a ∈ Ac) (haAd : a ∈ Ad) (hab : a ≠ b)
    (c1 : ∃! i, s(z, a) ∈ A i ∧ Z ∈ B i) (c2 : ∃! i, s(a, b) ∈ A i ∧ Bc ∈ B i)
    (c3 : ∃! i, s(a, b) ∈ A i ∧ Bd ∈ B i) (c4 : ∃! i, s(z, b) ∈ A i ∧ Z ∈ B i)
    (c5 : ∃! i, s(a, b) ∈ A i ∧ Ac ∈ B i) (c6 : ∃! i, s(a, b) ∈ A i ∧ Ad ∈ B i)
    (c7 : ∃! i, s(a, b) ∈ A i ∧ Z ∈ B i) (c8 : ∃! i, s(z, a) ∈ A i ∧ Bc ∈ B i)
    (c9 : ∃! i, s(z, a) ∈ A i ∧ Bd ∈ B i) (c10 : ∃! i, s(z, b) ∈ A i ∧ Ac ∈ B i)
    (c11 : ∃! i, s(z, b) ∈ A i ∧ Ad ∈ B i) :
    (2 ≤ (Finset.univ.filter (fun i => t i = a)).card ∧
        2 ≤ (Finset.univ.filter (fun i => t i = b)).card) ∨
      ((∀ i, (s(z, a) ∈ A i ∧ Bc ∈ B i → t i = a) ∧ (s(z, a) ∈ A i ∧ Bd ∈ B i → t i = a)) ∧
        1 ≤ (Finset.univ.filter (fun i => t i = a)).card ∧
        2 ≤ (Finset.univ.filter (fun i => t i = b)).card) ∨
      ((∀ i, (s(z, b) ∈ A i ∧ Ac ∈ B i → t i = b) ∧ (s(z, b) ∈ A i ∧ Ad ∈ B i → t i = b)) ∧
        2 ≤ (Finset.univ.filter (fun i => t i = a)).card ∧
        1 ≤ (Finset.univ.filter (fun i => t i = b)).card) := by
  obtain ⟨i0, hi0, _⟩ := c1
  obtain ⟨i3, hi3, _⟩ := c2
  obtain ⟨i4, hi4, _⟩ := c3
  obtain ⟨j0, hj0, _⟩ := c4
  obtain ⟨j3, hj3, _⟩ := c5
  obtain ⟨j4, hj4, _⟩ := c6
  have ti0 : t i0 = a := L159_tag A B t hA hB z a Z hzZ i0 hi0
  have ti3 : t i3 = a := L159_tag' A B t hA hB a b Bc hbBc i3 hi3
  have ti4 : t i4 = a := L159_tag' A B t hA hB a b Bd hbBd i4 hi4
  have tj0 : t j0 = b := L159_tag A B t hA hB z b Z hzZ j0 hj0
  have tj3 : t j3 = b := L159_tag A B t hA hB a b Ac haAc j3 hj3
  have tj4 : t j4 = b := L159_tag A B t hA hB a b Ad haAd j4 hj4
  have two : ∀ (v : Fin 5) (x y : Fin k), x ≠ y → t x = v → t y = v →
      2 ≤ (Finset.univ.filter (fun i => t i = v)).card := by
    intro v x y hxy hx hy
    exact Finset.one_lt_card.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
      y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, hxy⟩
  have one : ∀ (v : Fin 5) (x : Fin k), t x = v →
      1 ≤ (Finset.univ.filter (fun i => t i = v)).card := by
    intro v x hx
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have sideA : 2 ≤ (Finset.univ.filter (fun i => t i = a)).card ∨
      ((∀ i, (s(z, a) ∈ A i ∧ Bc ∈ B i → t i = a) ∧ (s(z, a) ∈ A i ∧ Bd ∈ B i → t i = a)) ∧
        (s(a, b) ∈ A i0 ∧ Z ∈ B i0)) := by
    by_cases e3 : i0 = i3
    · by_cases e4 : i0 = i4
      · right
        refine ⟨fun i => ⟨fun hi => ?_, fun hi => ?_⟩, ?_⟩
        · have h : i = i0 := c8.unique hi ⟨hi0.1, by rw [e3]; exact hi3.2⟩
          rw [h]
          exact ti0
        · have h : i = i0 := c9.unique hi ⟨hi0.1, by rw [e4]; exact hi4.2⟩
          rw [h]
          exact ti0
        · exact ⟨by rw [e3]; exact hi3.1, hi0.2⟩
      · exact Or.inl (two a i0 i4 e4 ti0 ti4)
    · exact Or.inl (two a i0 i3 e3 ti0 ti3)
  have sideB : 2 ≤ (Finset.univ.filter (fun i => t i = b)).card ∨
      ((∀ i, (s(z, b) ∈ A i ∧ Ac ∈ B i → t i = b) ∧ (s(z, b) ∈ A i ∧ Ad ∈ B i → t i = b)) ∧
        (s(a, b) ∈ A j0 ∧ Z ∈ B j0)) := by
    by_cases e3 : j0 = j3
    · by_cases e4 : j0 = j4
      · right
        refine ⟨fun i => ⟨fun hi => ?_, fun hi => ?_⟩, ?_⟩
        · have h : i = j0 := c10.unique hi ⟨hj0.1, by rw [e3]; exact hj3.2⟩
          rw [h]
          exact tj0
        · have h : i = j0 := c11.unique hi ⟨hj0.1, by rw [e4]; exact hj4.2⟩
          rw [h]
          exact tj0
        · exact ⟨by rw [e3]; exact hj3.1, hj0.2⟩
      · exact Or.inl (two b j0 j4 e4 tj0 tj4)
    · exact Or.inl (two b j0 j3 e3 tj0 tj3)
  rcases sideA with hA2 | ⟨hDa, hia⟩
  · rcases sideB with hB2 | ⟨hDb, _⟩
    · exact Or.inl ⟨hA2, hB2⟩
    · exact Or.inr (Or.inr ⟨hDb, hA2, one b j0 tj0⟩)
  · rcases sideB with hB2 | ⟨_, hjb⟩
    · exact Or.inr (Or.inl ⟨hDa, one a i0 ti0, hB2⟩)
    · exfalso
      have h : i0 = j0 := c7.unique hia hjb
      apply hab
      rw [← ti0, ← tj0, h]

private theorem L159_zero3 {k : ℕ} (A : Fin k → Finset (Sym2 (Fin 5)))
    (B : Fin k → Finset (Finset (Fin 5))) (t : Fin k → Fin 5)
    (hA : ∀ i, ∀ e ∈ A i, t i ∈ e) (hB : ∀ i, ∀ I ∈ B i, t i ∉ I)
    (z a b c : Fin 5) (P Q R : Finset (Fin 5))
    (haP : a ∈ P) (hcQ : c ∈ Q) (hbR : b ∈ R)
    (cp : ∃! i, s(z, a) ∈ A i ∧ P ∈ B i) (cq : ∃! i, s(z, c) ∈ A i ∧ Q ∈ B i)
    (cr : ∃! i, s(z, b) ∈ A i ∧ R ∈ B i)
    (n1 : ∀ i, s(z, a) ∈ A i ∧ Q ∈ B i → t i ≠ z)
    (n2 : ∀ i, s(z, a) ∈ A i ∧ R ∈ B i → t i ≠ z)
    (n3 : ∀ i, s(z, c) ∈ A i ∧ R ∈ B i → t i ≠ z) :
    3 ≤ (Finset.univ.filter (fun i => t i = z)).card := by
  obtain ⟨ip, hip, _⟩ := cp
  obtain ⟨iq, hiq, _⟩ := cq
  obtain ⟨ir, hir, _⟩ := cr
  have tp : t ip = z := L159_tag' A B t hA hB z a P haP ip hip
  have tq : t iq = z := L159_tag' A B t hA hB z c Q hcQ iq hiq
  have tr : t ir = z := L159_tag' A B t hA hB z b R hbR ir hir
  have hpq : ip ≠ iq := fun h => n1 ip ⟨hip.1, by rw [h]; exact hiq.2⟩ tp
  have hpr : ip ≠ ir := fun h => n2 ip ⟨hip.1, by rw [h]; exact hir.2⟩ tp
  have hqr : iq ≠ ir := fun h => n3 iq ⟨hiq.1, by rw [h]; exact hir.2⟩ tq
  exact Finset.two_lt_card.mpr ⟨ip, Finset.mem_filter.mpr ⟨Finset.mem_univ _, tp⟩,
    iq, Finset.mem_filter.mpr ⟨Finset.mem_univ _, tq⟩,
    ir, Finset.mem_filter.mpr ⟨Finset.mem_univ _, tr⟩, hpq, hpr, hqr⟩

private theorem L159_zero2 {k : ℕ} (A : Fin k → Finset (Sym2 (Fin 5)))
    (B : Fin k → Finset (Finset (Fin 5))) (t : Fin k → Fin 5)
    (hA : ∀ i, ∀ e ∈ A i, t i ∈ e) (hB : ∀ i, ∀ I ∈ B i, t i ∉ I)
    (z a b : Fin 5) (P R : Finset (Fin 5))
    (haP : a ∈ P) (hbR : b ∈ R)
    (cp : ∃! i, s(z, a) ∈ A i ∧ P ∈ B i)
    (cr : ∃! i, s(z, b) ∈ A i ∧ R ∈ B i)
    (n2 : ∀ i, s(z, a) ∈ A i ∧ R ∈ B i → t i ≠ z) :
    2 ≤ (Finset.univ.filter (fun i => t i = z)).card := by
  obtain ⟨ip, hip, _⟩ := cp
  obtain ⟨ir, hir, _⟩ := cr
  have tp : t ip = z := L159_tag' A B t hA hB z a P haP ip hip
  have tr : t ir = z := L159_tag' A B t hA hB z b R hbR ir hir
  have hpr : ip ≠ ir := fun h => n2 ip ⟨hip.1, by rw [h]; exact hir.2⟩ tp
  exact Finset.one_lt_card.mpr ⟨ip, Finset.mem_filter.mpr ⟨Finset.mem_univ _, tp⟩,
    ir, Finset.mem_filter.mpr ⟨Finset.mem_univ _, tr⟩, hpr⟩

theorem PEqualNP.Outside.L_meta_159 : ∀ (k : ℕ) (A : Fin k → Finset (Sym2 (Fin 5))) (B : Fin k → Finset (Finset (Fin 5)))
    (t : Fin k → Fin 5),
    (∀ i, ∀ e ∈ A i, e ∈ (SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))).edgeFinset ∧ t i ∈ e) →
    (∀ i, ∀ I ∈ B i, t i ∉ I) →
    (∀ e ∈ (SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))).edgeFinset,
      ∀ I : Finset (Fin 5), (∀ u ∈ I, ∀ w ∈ I, ¬ (SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))).Adj u w) →
        ∃! i : Fin k, e ∈ A i ∧ I ∈ B i) →
    9 ≤ k := by
  intro k A B t h1 h2 h3
  have hA : ∀ i, ∀ e ∈ A i, t i ∈ e := fun i e he => (h1 i e he).2
  have hE : ∀ x y : Fin 5, x ≠ y →
      ((x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 2) ∨
        (x = 0 ∧ y = 3) ∨ (x = 0 ∧ y = 4) ∨ (x = 3 ∧ y = 4)) →
      s(x, y) ∈ (SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))).edgeFinset := by
    intro x y hxy h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
    exact ⟨hxy, Or.inl h⟩
  have hI : ∀ I : Finset (Fin 5), (I = {0} ∨ I = {1} ∨ I = {1, 3} ∨ I = {1, 4} ∨ I = {2, 3} ∨
      I = {2, 4}) → ∀ u ∈ I, ∀ w ∈ I, ¬ (SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))).Adj u w := by
    intro I hI u hu w hw
    rw [SimpleGraph.fromRel_adj]
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl <;> revert u w <;> decide
  have cov : ∀ (x y : Fin 5) (I : Finset (Fin 5)), x ≠ y →
      ((x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 2) ∨
        (x = 0 ∧ y = 3) ∨ (x = 0 ∧ y = 4) ∨ (x = 3 ∧ y = 4)) →
      (I = {0} ∨ I = {1} ∨ I = {1, 3} ∨ I = {1, 4} ∨ I = {2, 3} ∨ I = {2, 4}) →
      ∃! i : Fin k, s(x, y) ∈ A i ∧ I ∈ B i :=
    fun x y I hxy he hi => h3 _ (hE x y hxy he) I (hI I hi)
  have hk : k = ∑ v : Fin 5, (Finset.univ.filter (fun i : Fin k => t i = v)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin k)))
      (t := (Finset.univ : Finset (Fin 5))) (f := t) (fun i _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  rw [Fin.sum_univ_five] at hk
  have triA := L159_tri A B t hA h2 0 1 2 {0} {2, 3} {2, 4} {1, 3} {1, 4}
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (cov 0 1 _ (by decide) (by decide) (by decide))
    (cov 1 2 _ (by decide) (by decide) (by decide))
    (cov 1 2 _ (by decide) (by decide) (by decide))
    (cov 0 2 _ (by decide) (by decide) (by decide))
    (cov 1 2 _ (by decide) (by decide) (by decide))
    (cov 1 2 _ (by decide) (by decide) (by decide))
    (cov 1 2 _ (by decide) (by decide) (by decide))
    (cov 0 1 _ (by decide) (by decide) (by decide))
    (cov 0 1 _ (by decide) (by decide) (by decide))
    (cov 0 2 _ (by decide) (by decide) (by decide))
    (cov 0 2 _ (by decide) (by decide) (by decide))
  have triB := L159_tri A B t hA h2 0 3 4 {0} {1, 4} {2, 4} {1, 3} {2, 3}
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (cov 0 3 _ (by decide) (by decide) (by decide))
    (cov 3 4 _ (by decide) (by decide) (by decide))
    (cov 3 4 _ (by decide) (by decide) (by decide))
    (cov 0 4 _ (by decide) (by decide) (by decide))
    (cov 3 4 _ (by decide) (by decide) (by decide))
    (cov 3 4 _ (by decide) (by decide) (by decide))
    (cov 3 4 _ (by decide) (by decide) (by decide))
    (cov 0 3 _ (by decide) (by decide) (by decide))
    (cov 0 3 _ (by decide) (by decide) (by decide))
    (cov 0 4 _ (by decide) (by decide) (by decide))
    (cov 0 4 _ (by decide) (by decide) (by decide))
  have z1 : 1 ≤ (Finset.univ.filter (fun i : Fin k => t i = 0)).card := by
    obtain ⟨i, hi, _⟩ := cov 0 1 {1} (by decide) (by decide) (by decide)
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      L159_tag' A B t hA h2 0 1 {1} (by decide) i hi⟩⟩
  have ne : ∀ (i : Fin k) (v : Fin 5), v ≠ 0 → t i = v → t i ≠ 0 := by
    intro i v hv h h0
    exact hv (h ▸ h0)
  rcases triA with ⟨a1, a2⟩ | ⟨D1, a1, a2⟩ | ⟨D2, a1, a2⟩
  · rcases triB with ⟨b1, b2⟩ | ⟨D3, b1, b2⟩ | ⟨D4, b1, b2⟩
    · omega
    · have z2 := L159_zero2 A B t hA h2 0 3 4 {2, 3} {2, 4} (by decide) (by decide)
        (cov 0 3 _ (by decide) (by decide) (by decide))
        (cov 0 4 _ (by decide) (by decide) (by decide))
        (fun i hi => ne i 3 (by decide) ((D3 i).2 hi))
      omega
    · have z2 := L159_zero2 A B t hA h2 0 4 3 {2, 4} {2, 3} (by decide) (by decide)
        (cov 0 4 _ (by decide) (by decide) (by decide))
        (cov 0 3 _ (by decide) (by decide) (by decide))
        (fun i hi => ne i 4 (by decide) ((D4 i).2 hi))
      omega
  · rcases triB with ⟨b1, b2⟩ | ⟨D3, b1, b2⟩ | ⟨D4, b1, b2⟩
    · have z2 := L159_zero2 A B t hA h2 0 1 2 {1, 4} {2, 4} (by decide) (by decide)
        (cov 0 1 _ (by decide) (by decide) (by decide))
        (cov 0 2 _ (by decide) (by decide) (by decide))
        (fun i hi => ne i 1 (by decide) ((D1 i).2 hi))
      omega
    · have z3 := L159_zero3 A B t hA h2 0 1 2 3 {1, 4} {2, 3} {2, 4}
        (by decide) (by decide) (by decide)
        (cov 0 1 _ (by decide) (by decide) (by decide))
        (cov 0 3 _ (by decide) (by decide) (by decide))
        (cov 0 2 _ (by decide) (by decide) (by decide))
        (fun i hi => ne i 1 (by decide) ((D1 i).1 hi))
        (fun i hi => ne i 1 (by decide) ((D1 i).2 hi))
        (fun i hi => ne i 3 (by decide) ((D3 i).2 hi))
      omega
    · have z3 := L159_zero3 A B t hA h2 0 1 2 4 {1, 3} {2, 4} {2, 3}
        (by decide) (by decide) (by decide)
        (cov 0 1 _ (by decide) (by decide) (by decide))
        (cov 0 4 _ (by decide) (by decide) (by decide))
        (cov 0 2 _ (by decide) (by decide) (by decide))
        (fun i hi => ne i 1 (by decide) ((D1 i).2 hi))
        (fun i hi => ne i 1 (by decide) ((D1 i).1 hi))
        (fun i hi => ne i 4 (by decide) ((D4 i).2 hi))
      omega
  · rcases triB with ⟨b1, b2⟩ | ⟨D3, b1, b2⟩ | ⟨D4, b1, b2⟩
    · have z2 := L159_zero2 A B t hA h2 0 2 1 {2, 4} {1, 4} (by decide) (by decide)
        (cov 0 2 _ (by decide) (by decide) (by decide))
        (cov 0 1 _ (by decide) (by decide) (by decide))
        (fun i hi => ne i 2 (by decide) ((D2 i).2 hi))
      omega
    · have z3 := L159_zero3 A B t hA h2 0 2 1 3 {2, 4} {1, 3} {1, 4}
        (by decide) (by decide) (by decide)
        (cov 0 2 _ (by decide) (by decide) (by decide))
        (cov 0 3 _ (by decide) (by decide) (by decide))
        (cov 0 1 _ (by decide) (by decide) (by decide))
        (fun i hi => ne i 2 (by decide) ((D2 i).1 hi))
        (fun i hi => ne i 2 (by decide) ((D2 i).2 hi))
        (fun i hi => ne i 3 (by decide) ((D3 i).1 hi))
      omega
    · have z3 := L159_zero3 A B t hA h2 0 2 1 4 {2, 3} {1, 4} {1, 3}
        (by decide) (by decide) (by decide)
        (cov 0 2 _ (by decide) (by decide) (by decide))
        (cov 0 4 _ (by decide) (by decide) (by decide))
        (cov 0 1 _ (by decide) (by decide) (by decide))
        (fun i hi => ne i 2 (by decide) ((D2 i).2 hi))
        (fun i hi => ne i 2 (by decide) ((D2 i).1 hi))
        (fun i hi => ne i 4 (by decide) ((D4 i).1 hi))
      omega

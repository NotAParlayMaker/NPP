import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2794_1
    (hSignature : ∀ (q N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R]
      (s o : ℕ) (bad : Finset ℕ)
      (wires : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
      0 < q → o < N + N + s →
      (∀ i : Fin N, wires i = {z | z.1 i = true} ∧
        wires (N + i) = {z | z.2 i = true}) →
      (∀ j < s, ∃ a < N + N + j, ∃ b < N + N + j,
        let z := wires (N + N + j)
        z = wires a ∪ wires b ∨ z = wires a ∨ z = ∅ ∨
          z = wires a ∩ wires b ∧
            (j ∈ bad ∨ ∃ X Y, wires a = X ×ˢ Set.univ ∧
              wires b = Set.univ ×ˢ Y)) →
      (∀ p l, R p l → (fun i => decide (i = p), fun i => decide (i = l)) ∈ wires o) →
      (∀ y : Fin N → Bool,
        Fintype.card {i : Fin N // y i = true} ≤ q →
        (fun p => decide (¬ ∃ l, R p l ∧ y l = true), y) ∉ wires o) →
      ∀ p l, ((fun i => decide (i = p), fun i => decide (i = l)) ∈ wires o ↔ R p l))
    (hLayerBound : ∀ (N d s : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R]
      (bad : Finset ℕ) (wires : ℕ → Finset (Fin N × Fin N)) (o : ℕ),
      o < N + N + s →
      (∀ l : Fin N, Fintype.card {p : Fin N // R p l} = d) →
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ (R p l ∧ R p l' ∧ R p' l ∧ R p' l')) →
      (∀ i : Fin N, wires i = ({i} : Finset (Fin N)) ×ˢ Finset.univ ∧
        wires (N + i) = Finset.univ ×ˢ ({i} : Finset (Fin N))) →
      (∀ j < s, ∃ a < N + N + j, ∃ b < N + N + j,
        let z := wires (N + N + j)
        z = wires a ∪ wires b ∨ z = wires a ∨ z = ∅ ∨
          z = wires a ∩ wires b ∧
            (j ∈ bad ∨ ∃ X Y, wires a = X ×ˢ Finset.univ ∧
              wires b = Finset.univ ×ˢ Y)) →
      wires o = Finset.univ.filter (fun e : Fin N × Fin N => R e.1 e.2) →
      (Finset.univ.filter (fun e : Fin N × Fin N => R e.1 e.2)).card ≤
        48 * (s + bad.card) + 2 * N) :
    ∀ (q N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R],
      100 < q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // R p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, R p l ∧ R p' l) →
      ∀ (s o : ℕ) (bad : Finset ℕ)
        (wires : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
        o < N + N + s →
        (∀ i : Fin N, wires i = {z | z.1 i = true} ∧
          wires (N + i) = {z | z.2 i = true}) →
        (∀ j < s, ∃ a < N + N + j, ∃ b < N + N + j,
          let z := wires (N + N + j)
          z = wires a ∪ wires b ∨ z = wires a ∨ z = ∅ ∨
            z = wires a ∩ wires b ∧
              (j ∈ bad ∨ ∃ X Y, wires a = X ×ˢ Set.univ ∧
                wires b = Set.univ ×ˢ Y)) →
        (∀ p l, R p l → (fun i => decide (i = p), fun i => decide (i = l)) ∈ wires o) →
        (∀ y : Fin N → Bool,
          Fintype.card {i : Fin N // y i = true} ≤ q →
          (fun p => decide (¬ ∃ l, R p l ∧ y l = true), y) ∉ wires o) →
        100 * bad.card < N * q → N * q ≤ 100 * s := by
  intro q N R _ hq hN hdeg huniq s o bad wires ho hbase hgate hinc hreject hbudget
  have hSig := hSignature q N R s o bad wires (by omega) ho hbase hgate hinc hreject
  classical
  let one (p : Fin N) : Fin N → Bool := fun i => decide (i = p)
  let W : ℕ → Finset (Fin N × Fin N) := fun w =>
    Finset.univ.filter (fun e => (one e.1, one e.2) ∈ wires w)
  have hWbase : ∀ i : Fin N,
      W i = ({i} : Finset (Fin N)) ×ˢ Finset.univ ∧
      W (N + i) = Finset.univ ×ˢ ({i} : Finset (Fin N)) := by
    intro i
    constructor
    · ext ⟨p, l⟩
      simp [W, one, hbase i]
    · ext ⟨p, l⟩
      simp [W, one, hbase i]
  have hWgate : ∀ j < s, ∃ a < N + N + j, ∃ b < N + N + j,
      let z := W (N + N + j)
      z = W a ∪ W b ∨ z = W a ∨ z = ∅ ∨
        z = W a ∩ W b ∧
          (j ∈ bad ∨ ∃ X Y, W a = X ×ˢ Finset.univ ∧
            W b = Finset.univ ×ˢ Y) := by
    intro j hj
    obtain ⟨a, ha, b, hb, hcases⟩ := hgate j hj
    refine ⟨a, ha, b, hb, ?_⟩
    change W (N + N + j) = W a ∪ W b ∨ W (N + N + j) = W a ∨
      W (N + N + j) = ∅ ∨ W (N + N + j) = W a ∩ W b ∧
        (j ∈ bad ∨ ∃ X Y, W a = X ×ˢ Finset.univ ∧
          W b = Finset.univ ×ˢ Y)
    rcases hcases with hu | hc | hz | ⟨hi, hspecial⟩
    · left
      ext ⟨p, l⟩
      simp [W, hu]
    · right; left
      ext ⟨p, l⟩
      simp [W, hc]
    · right; right; left
      ext ⟨p, l⟩
      simp [W, hz]
    · right; right; right
      constructor
      · ext ⟨p, l⟩
        simp [W, hi]
      · rcases hspecial with hm | ⟨X, Y, hX, hY⟩
        · exact Or.inl hm
        · right
          let A : Finset (Fin N) := Finset.univ.filter (fun p => one p ∈ X)
          let B : Finset (Fin N) := Finset.univ.filter (fun l => one l ∈ Y)
          refine ⟨A, B, ?_, ?_⟩
          · ext ⟨p, l⟩
            simp [W, A, one, hX]
          · ext ⟨p, l⟩
            simp [W, B, one, hY]
  have hWout : W o = Finset.univ.filter (fun e : Fin N × Fin N => R e.1 e.2) := by
    ext ⟨p, l⟩
    simp [W, one, hSig p l]
  have hNoRect : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (R p l ∧ R p l' ∧ R p' l ∧ R p' l') := by
    intro p p' l l' hpp hll h
    rcases h with ⟨hpl, hpl', hp'l, hp'l'⟩
    obtain ⟨u, hu, huniq'⟩ := huniq p p' hpp
    have hl : l = u := huniq' l ⟨hpl, hp'l⟩
    have hl' : l' = u := huniq' l' ⟨hpl', hp'l'⟩
    exact hll (hl.trans hl'.symm)
  have hLayer := hLayerBound N (q + 1) s R bad W o ho
    (by simpa using hdeg) hNoRect hWbase hWgate hWout
  have hEdge : (Finset.univ.filter (fun e : Fin N × Fin N => R e.1 e.2)).card =
      N * (q + 1) := by
    classical
    let E := Finset.univ.filter (fun e : Fin N × Fin N => R e.1 e.2)
    let fiber (l : Fin N) := Finset.univ.filter (fun p : Fin N => R p l)
    have hbi : E = Finset.univ.biUnion (fun l : Fin N => (fiber l).image (fun p => (p, l))) := by
      ext ⟨p, l⟩
      constructor
      · intro hp
        have hpR : R p l := (Finset.mem_filter.mp hp).2
        apply Finset.mem_biUnion.mpr
        refine ⟨l, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
        exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpR⟩, by simp⟩
      · intro he
        rcases Finset.mem_biUnion.mp he with ⟨l', _, hl'⟩
        rcases Finset.mem_image.mp hl' with ⟨p', hp', heq⟩
        cases heq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp').2⟩
    change E.card = N * (q + 1)
    have hFiberCard : ∀ l : Fin N, (fiber l).card = q + 1 := by
      intro l
      simpa only [fiber, Fintype.card_subtype] using hdeg l
    have hImage : ∀ l : Fin N,
        ((fiber l).image (fun p => (p, l))).card = (fiber l).card := by
      intro l
      exact Finset.card_image_of_injective (fiber l)
        (by intro p p' h; exact congrArg Prod.fst h)
    rw [hbi, Finset.card_biUnion]
    · calc
        ∑ l : Fin N, ((fiber l).image (fun p => (p, l))).card =
            ∑ l : Fin N, (fiber l).card := by
              apply Finset.sum_congr rfl
              intro l hl
              exact hImage l
        _ = N * (q + 1) := by simp [hFiberCard]
    · intro l hl l' hl' hne
      apply Finset.disjoint_left.mpr
      intro e he he'
      have he2 := Finset.mem_image.mp he
      have he2' := Finset.mem_image.mp he'
      rcases he2 with ⟨p, hp, rfl⟩
      rcases he2' with ⟨p', hp', hh⟩
      have hll : l = l' := (congrArg Prod.snd hh).symm
      exact hne hll
  have hK : N * (q + 1) = N * q + N := by simp [Nat.mul_add]
  have hBound : N * q + N ≤ 48 * (s + bad.card) + 2 * N := by
    rw [← hK, ← hEdge]
    exact hLayer
  have hBig : 0 < N := by rw [hN]; omega
  have hNq : 100 * N < N * q := by
    have hmul := Nat.mul_lt_mul_of_pos_left hq hBig
    nlinarith [hmul]
  have hScaled : 100 * (N * q + N) ≤ 4800 * s + 4800 * bad.card + 200 * N := by
    nlinarith
  have hBudgetScaled : 4800 * bad.card < 48 * (N * q) := by
    have := Nat.mul_lt_mul_of_pos_left hbudget (by decide : 0 < 48)
    nlinarith
  have hCoeff : 51 * (N * q) < 4800 * s := by
    nlinarith [hScaled, hBudgetScaled, hNq]
  nlinarith [hCoeff]

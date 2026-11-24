import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 300000 in
theorem PEqualNP.Outside.R_meta_3002_512
    (unionHeavy : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      ∀ (s o : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ) (isChoice : Fin s → Bool),
        o < N + N + s →
        (∀ z v, v < N + N → D z v = {v}) →
        (∀ j : Fin s, ∃ a < N + N + j.val, ∃ b < N + N + j.val,
          if isChoice j then ∀ z, D z (N + N + j.val) = if z j then D z a else D z b
          else (∀ z, D z (N + N + j.val) = D z a ∪ D z b) ∨ (∀ z, D z (N + N + j.val) = ∅)) →
        (∀ z, ∀ p l : Fin N, I p l → p.val ∈ D z o ∨ N + l.val ∈ D z o) →
        (∀ p : Fin N, p.val ∉ D (fun _ => false) o ∧ N + p.val ∈ D (fun _ => false) o) →
        (∀ T : Finset (Fin N), T.card ≤ q → ∃ z, ∀ p : Fin N,
          (p.val ∈ D z o ↔ ∃ l ∈ T, I p l) ∧ (N + p.val ∈ D z o ↔ p ∉ T)) →
        2 * (Finset.univ.filter fun j : Fin s => isChoice j = true).card ≤ s →
        N * q ≤ 100 * s)
    (choiceHeavy : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      ∀ (s o : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ) (isChoice : Fin s → Bool),
        o < N + N + s →
        (∀ z v, v < N + N → D z v = {v}) →
        (∀ j : Fin s, ∃ a < N + N + j.val, ∃ b < N + N + j.val,
          if isChoice j then ∀ z, D z (N + N + j.val) = if z j then D z a else D z b
          else (∀ z, D z (N + N + j.val) = D z a ∪ D z b) ∨ (∀ z, D z (N + N + j.val) = ∅)) →
        (∀ z, ∀ p l : Fin N, I p l → p.val ∈ D z o ∨ N + l.val ∈ D z o) →
        (∀ p : Fin N, p.val ∉ D (fun _ => false) o ∧ N + p.val ∈ D (fun _ => false) o) →
        (∀ T : Finset (Fin N), T.card ≤ q → ∃ z, ∀ p : Fin N,
          (p.val ∈ D z o ↔ ∃ l ∈ T, I p l) ∧ (N + p.val ∈ D z o ↔ p ∉ T)) →
        s < 2 * (Finset.univ.filter fun j : Fin s => isChoice j = true).card →
        N * q ≤ 100 * s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I decI hq hN hdeg hpl s o F ho hin hgate hcov hsat
  let m : ℕ := N + N
  have hgate' : ∀ j : Fin s, ∃ (a b : ℕ), a < m + j.val ∧ b < m + j.val ∧
      (F (m + j.val) = Set.image2 (fun u v => u ∪ v) (F a) (F b) ∨
       F (m + j.val) = F a ∨ F (m + j.val) = {∅} ∨ F (m + j.val) = F a ∪ F b) := by
    intro j
    obtain ⟨a, ha, b, hb, h⟩ := hgate j.val j.isLt
    exact ⟨a, b, ha, hb, h⟩
  let gA : Fin s → ℕ := fun j => (hgate' j).choose
  let gB : Fin s → ℕ := fun j => (hgate' j).choose_spec.choose
  have hgA : ∀ j : Fin s, gA j < m + j.val := fun j => (hgate' j).choose_spec.choose_spec.1
  have hgB : ∀ j : Fin s, gB j < m + j.val := fun j => (hgate' j).choose_spec.choose_spec.2.1
  have hgSpec : ∀ j : Fin s,
      F (m + j.val) = Set.image2 (fun u v => u ∪ v) (F (gA j)) (F (gB j)) ∨
      F (m + j.val) = F (gA j) ∨ F (m + j.val) = {∅} ∨ F (m + j.val) = F (gA j) ∪ F (gB j) :=
    fun j => (hgate' j).choose_spec.choose_spec.2.2
  -- Classify each gate j into union (0), copy (1), empty (2), choice (3)
  let kind : Fin s → ℕ := fun j =>
    if F (m + j.val) = Set.image2 (fun u v => u ∪ v) (F (gA j)) (F (gB j)) then 0
    else if F (m + j.val) = F (gA j) then 1
    else if F (m + j.val) = {∅} then 2
    else 3
  let isChoice : Fin s → Bool := fun j => decide (kind j = 3)
  -- Build D z by simple List.foldl over List.finRange s
  let evalStep : (Fin s → Bool) → List (Finset ℕ) → Fin s → List (Finset ℕ) := fun z ws j =>
    ws ++ [if kind j = 0 then ws.getD (gA j) ∅ ∪ ws.getD (gB j) ∅
           else if kind j = 1 then ws.getD (gA j) ∅
           else if kind j = 2 then ∅
           else if z j then ws.getD (gA j) ∅ else ws.getD (gB j) ∅]
  let initWires : List (Finset ℕ) := (List.range m).map fun v => {v}
  let evalAll : (Fin s → Bool) → List (Finset ℕ) := fun z =>
    (List.finRange s).foldl (evalStep z) initWires
  let evalWire : (Fin s → Bool) → ℕ → Finset ℕ := fun z w => (evalAll z).getD w ∅
  have fold_len : ∀ (z : Fin s → Bool) (js : List (Fin s)) (acc : List (Finset ℕ)),
      (js.foldl (evalStep z) acc).length = acc.length + js.length := by
    intro z js; induction js with
    | nil => intro acc; simp
    | cons j r ih => intro acc; simp only [List.foldl_cons, ih, evalStep, List.length_append, List.length_cons, List.length_nil]; omega
  have fold_prefix : ∀ (z : Fin s → Bool) (js : List (Fin s)) (acc : List (Finset ℕ)) (w : ℕ),
      w < acc.length → (js.foldl (evalStep z) acc).getD w ∅ = acc.getD w ∅ := by
    intro z js; induction js with
    | nil => intro acc w _; rfl
    | cons j r ih =>
      intro acc w hw; simp only [List.foldl_cons]
      rw [ih _ w (by dsimp only [evalStep]; simp; omega)]
      simp only [evalStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
  have evalWire_in : ∀ (z : Fin s → Bool) (v : ℕ), v < m → evalWire z v = {v} := by
    intro z v hv
    dsimp only [evalWire, evalAll]
    rw [fold_prefix z (List.finRange s) initWires v (by simp [initWires, hv])]
    simp [initWires, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv]
  have evalWire_gate : ∀ (z : Fin s → Bool) (j : Fin s),
      evalWire z (m + j.val) =
        if kind j = 0 then evalWire z (gA j) ∪ evalWire z (gB j)
        else if kind j = 1 then evalWire z (gA j)
        else if kind j = 2 then ∅
        else if z j then evalWire z (gA j) else evalWire z (gB j) := by
    intro z j
    have hsplit : List.finRange s = (List.finRange s).take j.val ++ [j] ++ (List.finRange s).drop (j.val + 1) := by
      have h1 : (List.finRange s).take j.val ++ (List.finRange s).drop j.val = List.finRange s := List.take_append_drop j.val _
      have hjlt : j.val < (List.finRange s).length := by simp
      have h2 : (List.finRange s).drop j.val = (List.finRange s)[j.val] :: (List.finRange s).drop (j.val + 1) := List.drop_eq_getElem_cons hjlt
      have h3 : (List.finRange s)[j.val] = j := by simp
      rw [h3] at h2
      calc List.finRange s = (List.finRange s).take j.val ++ (List.finRange s).drop j.val := h1.symm
        _ = (List.finRange s).take j.val ++ (j :: (List.finRange s).drop (j.val + 1)) := by rw [h2]
        _ = (List.finRange s).take j.val ++ [j] ++ (List.finRange s).drop (j.val + 1) := by simp
    let acc := ((List.finRange s).take j.val).foldl (evalStep z) initWires
    have haccLen : acc.length = m + j.val := by
      dsimp only [acc]; rw [fold_len, List.length_take]; simp [initWires]
    have haccAt : ∀ u < m + j.val, evalWire z u = acc.getD u ∅ := by
      intro u hu
      dsimp only [evalWire, evalAll]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (((List.finRange s).drop (j.val + 1)).foldl (evalStep z) (evalStep z acc j)).getD u ∅ = acc.getD u ∅
      rw [fold_prefix z ((List.finRange s).drop (j.val + 1)) _ u (by dsimp only [evalStep]; rw [List.length_append, haccLen]; simp; omega)]
      dsimp only [evalStep]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [haccLen]; omega)]
    have hmain : evalWire z (m + j.val) =
        (if kind j = 0 then acc.getD (gA j) ∅ ∪ acc.getD (gB j) ∅
         else if kind j = 1 then acc.getD (gA j) ∅
         else if kind j = 2 then ∅
         else if z j then acc.getD (gA j) ∅ else acc.getD (gB j) ∅) := by
      dsimp only [evalWire, evalAll]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (((List.finRange s).drop (j.val + 1)).foldl (evalStep z) (evalStep z acc j)).getD (m + j.val) ∅ = _
      rw [fold_prefix z ((List.finRange s).drop (j.val + 1)) _ (m + j.val) (by dsimp only [evalStep]; rw [List.length_append, haccLen]; simp)]
      dsimp only [evalStep]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [haccLen])]
      simp [haccLen]
    rw [hmain, haccAt (gA j) (hgA j), haccAt (gB j) (hgB j)]
  have evalWire_mem : ∀ (z : Fin s → Bool) (w : ℕ), w < m + s → evalWire z w ∈ F w := by
    intro z w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hlt : w < m
      · rw [evalWire_in z w hlt, hin w hlt]; rfl
      · let j : Fin s := ⟨w - m, by omega⟩
        have hwj : w = m + j.val := by dsimp only [j]; omega
        rw [hwj, evalWire_gate z j]
        have ha : evalWire z (gA j) ∈ F (gA j) := ih (gA j) (by have := hgA j; omega) (by have := hgA j; omega)
        have hb : evalWire z (gB j) ∈ F (gB j) := ih (gB j) (by have := hgB j; omega) (by have := hgB j; omega)
        by_cases hk0 : kind j = 0
        · rw [if_pos hk0]
          have hF : F (m + j.val) = Set.image2 (fun u v => u ∪ v) (F (gA j)) (F (gB j)) := by
            dsimp only [kind] at hk0; split_ifs at hk0 with h0 <;> first | exact h0 | omega
          rw [hF]; exact Set.mem_image2_of_mem ha hb
        · rw [if_neg hk0]
          by_cases hk1 : kind j = 1
          · rw [if_pos hk1]
            have hF : F (m + j.val) = F (gA j) := by
              dsimp only [kind] at hk1; split_ifs at hk1 with h0 h1 <;> first | exact h1 | omega
            rw [hF]; exact ha
          · rw [if_neg hk1]
            by_cases hk2 : kind j = 2
            · rw [if_pos hk2]
              have hF : F (m + j.val) = {∅} := by
                dsimp only [kind] at hk2; split_ifs at hk2 with h0 h1 h2 <;> first | exact h2 | omega
              rw [hF]; rfl
            · rw [if_neg hk2]
              have hF : F (m + j.val) = F (gA j) ∪ F (gB j) := by
                dsimp only [kind] at hk0 hk1 hk2
                split_ifs at hk0 hk1 hk2 with h0 h1 h2
                · exact False.elim (hk0 rfl)
                · exact False.elim (hk1 rfl)
                · exact False.elim (hk2 rfl)
                · rcases hgSpec j with ha0 | ha1 | ha2 | ha3
                  · exact False.elim (h0 ha0)
                  · exact False.elim (h1 ha1)
                  · exact False.elim (h2 ha2)
                  · exact ha3
              rw [hF]; cases z j
              · exact Or.inr hb
              · exact Or.inl ha
  have evalWire_realize : ∀ (A : Finset ℕ), A ∈ F o → ∃ z : Fin s → Bool, evalWire z o ⊆ A := by
    intro A hA
    let z : Fin s → Bool := fun j => decide (∃ B ∈ F (gA j), B ⊆ A)
    refine ⟨z, ?_⟩
    have hrec : ∀ w < m + s, (∃ B ∈ F w, B ⊆ A) → evalWire z w ⊆ A := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw ⟨B, hBw, hBA⟩
        by_cases hlt : w < m
        · rw [evalWire_in z w hlt]; rw [hin w hlt] at hBw; rw [Set.mem_singleton_iff] at hBw; rwa [← hBw]
        · let j : Fin s := ⟨w - m, by omega⟩
          have hwj : w = m + j.val := by dsimp only [j]; omega
          rw [hwj] at hBw ⊢; rw [evalWire_gate z j]
          have hgaLt : gA j < m + j.val := hgA j
          have hgbLt : gB j < m + j.val := hgB j
          by_cases hk0 : kind j = 0
          · rw [if_pos hk0]
            have hF : F (m + j.val) = Set.image2 (fun u v => u ∪ v) (F (gA j)) (F (gB j)) := by
              dsimp only [kind] at hk0; split_ifs at hk0 with h0 <;> first | exact h0 | omega
            rw [hF] at hBw
            obtain ⟨B1, hB1, B2, hB2, rfl⟩ := Set.mem_image2.mp hBw
            exact Finset.union_subset
              (ih (gA j) (by omega) (by omega) ⟨B1, hB1, Finset.Subset.trans Finset.subset_union_left hBA⟩)
              (ih (gB j) (by omega) (by omega) ⟨B2, hB2, Finset.Subset.trans Finset.subset_union_right hBA⟩)
          · rw [if_neg hk0]
            by_cases hk1 : kind j = 1
            · rw [if_pos hk1]
              have hF : F (m + j.val) = F (gA j) := by
                dsimp only [kind] at hk1; split_ifs at hk1 with h0 h1 <;> first | exact h1 | omega
              rw [hF] at hBw
              exact ih (gA j) (by omega) (by omega) ⟨B, hBw, hBA⟩
            · rw [if_neg hk1]
              by_cases hk2 : kind j = 2
              · rw [if_pos hk2]; exact Finset.empty_subset A
              · rw [if_neg hk2]
                have hF : F (m + j.val) = F (gA j) ∪ F (gB j) := by
                  dsimp only [kind] at hk0 hk1 hk2
                  split_ifs at hk0 hk1 hk2 with h0 h1 h2
                  · exact False.elim (hk0 rfl)
                  · exact False.elim (hk1 rfl)
                  · exact False.elim (hk2 rfl)
                  · rcases hgSpec j with ha0 | ha1 | ha2 | ha3
                    · exact False.elim (h0 ha0)
                    · exact False.elim (h1 ha1)
                    · exact False.elim (h2 ha2)
                    · exact ha3
                rw [hF] at hBw
                by_cases hexA : ∃ B' ∈ F (gA j), B' ⊆ A
                · have hzj : z j = true := by simp [z, hexA]
                  rw [hzj, if_pos rfl]
                  exact ih (gA j) (by omega) (by omega) hexA
                · have hzj : z j = false := by simp [z, hexA]
                  rw [hzj, if_neg (by decide)]
                  rcases hBw with h1 | h2
                  · exact False.elim (hexA ⟨B, h1, hBA⟩)
                  · exact ih (gB j) (by omega) (by omega) ⟨B, h2, hBA⟩
    exact hrec o ho ⟨A, hA, Finset.Subset.refl A⟩
  have hminimal : ∀ (T : Finset (Fin N)) (A B : Finset ℕ), T.card ≤ q → B ⊆ A →
      (∀ p l : Fin N, I p l → p.val ∈ B ∨ N + l.val ∈ B) →
      (∀ p : Fin N, (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N + p.val ∈ A ↔ p ∉ T)) →
      ∀ p : Fin N, (p.val ∈ B ↔ ∃ l ∈ T, I p l) ∧ (N + p.val ∈ B ↔ p ∉ T) := by
    intro T A B hT hBA hBcov hAspec p
    constructor
    · constructor
      · intro hpB; exact (hAspec p).1.mp (hBA hpB)
      · rintro ⟨l, hlT, hIpl⟩
        have hnlA : N + l.val ∉ A := by intro h; exact ((hAspec l).2.mp h) hlT
        have hnlB : N + l.val ∉ B := fun h => hnlA (hBA h)
        rcases hBcov p l hIpl with hp | hl
        · exact hp
        · exact False.elim (hnlB hl)
    · constructor
      · intro hlB; exact (hAspec p).2.mp (hBA hlB)
      · intro hpT
        -- Find a point x on line p not on any line l' ∈ T
        have hlinePts : (Finset.univ.filter fun x : Fin N => I x p).card = q + 1 := by
          have := hdeg p
          rw [Fintype.card_subtype] at this
          exact this
        have hinter_le1 : ∀ l' ∈ T, (Finset.univ.filter fun x : Fin N => I x p ∧ I x l').card ≤ 1 := by
          intro l' hl'
          have hne : p ≠ l' := fun heq => hpT (heq ▸ hl')
          rw [Finset.card_le_one]
          intro x1 hx1 x2 hx2
          by_contra hxne
          have h1 := (Finset.mem_filter.mp hx1).2
          have h2 := (Finset.mem_filter.mp hx2).2
          obtain ⟨l0, _, huniq⟩ := hpl x1 x2 hxne
          have hp0 : p = l0 := huniq p ⟨h1.1, h2.1⟩
          have hl0 : l' = l0 := huniq l' ⟨h1.2, h2.2⟩
          exact hne (hp0.trans hl0.symm)
        have hcovCard : (Finset.univ.filter fun x : Fin N => I x p ∧ ∃ l' ∈ T, I x l').card ≤ q := by
          have hsub : (Finset.univ.filter fun x : Fin N => I x p ∧ ∃ l' ∈ T, I x l') ⊆
              T.biUnion (fun l' => Finset.univ.filter fun x : Fin N => I x p ∧ I x l') := by
            intro x hx
            obtain ⟨_, hp', l', hl', hxl'⟩ := Finset.mem_filter.mp hx
            exact Finset.mem_biUnion.mpr ⟨l', hl', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp', hxl'⟩⟩
          calc (Finset.univ.filter fun x : Fin N => I x p ∧ ∃ l' ∈ T, I x l').card
              ≤ (T.biUnion (fun l' => Finset.univ.filter fun x : Fin N => I x p ∧ I x l')).card := Finset.card_le_card hsub
            _ ≤ ∑ l' ∈ T, (Finset.univ.filter fun x : Fin N => I x p ∧ I x l').card := Finset.card_biUnion_le
            _ ≤ ∑ _l' ∈ T, 1 := Finset.sum_le_sum hinter_le1
            _ = T.card := by simp
            _ ≤ q := hT
        have hexPt : ∃ x : Fin N, I x p ∧ ¬ ∃ l' ∈ T, I x l' := by
          by_contra! hall
          have hsub : (Finset.univ.filter fun x : Fin N => I x p) ⊆
              (Finset.univ.filter fun x : Fin N => I x p ∧ ∃ l' ∈ T, I x l') := by
            intro x hx
            have hxp := (Finset.mem_filter.mp hx).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxp, hall x hxp⟩
          have := Finset.card_le_card hsub
          omega
        obtain ⟨x, hxp, hxnot⟩ := hexPt
        have hnxA : x.val ∉ A := by intro h; exact hxnot ((hAspec x).1.mp h)
        have hnxB : x.val ∉ B := fun h => hnxA (hBA h)
        rcases hBcov x p hxp with hx | hp'
        · exact False.elim (hnxB hx)
        · exact hp'
  have hchosen : ∀ (T : Finset (Fin N)), T.card ≤ q →
      ∃ z : Fin s → Bool, ∀ p : Fin N, (p.val ∈ evalWire z o ↔ ∃ l ∈ T, I p l) ∧ (N + p.val ∈ evalWire z o ↔ p ∉ T) := by
    intro T hT
    obtain ⟨A, hAo, hAspec⟩ := hsat T hT
    obtain ⟨z, hzSub⟩ := evalWire_realize A hAo
    exact ⟨z, hminimal T A (evalWire z o) hT hzSub (hcov _ (evalWire_mem z o ho)) hAspec⟩
  obtain ⟨base, hbase⟩ := hchosen ∅ (by simp)
  let flip : (Fin s → Bool) → Fin s → Bool := fun z j => if base j then !z j else z j
  let D : (Fin s → Bool) → ℕ → Finset ℕ := fun z => evalWire (flip z)
  have hflip2 : ∀ z, flip (flip z) = z := by
    intro z; funext j; cases hb : base j <;> simp [flip, hb]
  have hflip0 : flip (fun _ => false) = base := by
    funext j; cases hb : base j <;> simp [flip, hb]
  have hDsteps : ∀ j : Fin s, ∃ a < N + N + j.val, ∃ b < N + N + j.val,
      if isChoice j then ∀ z, D z (N + N + j.val) = if z j then D z a else D z b
      else (∀ z, D z (N + N + j.val) = D z a ∪ D z b) ∨ (∀ z, D z (N + N + j.val) = ∅) := by
    intro j
    by_cases hc : isChoice j = true
    · have hk3 : kind j = 3 := by simpa [isChoice] using hc
      have hk0 : kind j ≠ 0 := by omega
      have hk1 : kind j ≠ 1 := by omega
      have hk2 : kind j ≠ 2 := by omega
      cases hbj : base j with
      | false =>
        refine ⟨gA j, hgA j, gB j, hgB j, ?_⟩
        rw [if_pos hc]; intro z
        dsimp only [D]; change evalWire (flip z) (m + j.val) = _
        rw [evalWire_gate (flip z) j, if_neg hk0, if_neg hk1, if_neg hk2]
        have hfj : flip z j = z j := by simp [flip, hbj]
        rw [hfj]
      | true =>
        refine ⟨gB j, hgB j, gA j, hgA j, ?_⟩
        rw [if_pos hc]; intro z
        dsimp only [D]; change evalWire (flip z) (m + j.val) = _
        rw [evalWire_gate (flip z) j, if_neg hk0, if_neg hk1, if_neg hk2]
        have hfj : flip z j = !z j := by simp [flip, hbj]
        rw [hfj]; cases z j <;> rfl
    · have hcf : isChoice j = false := by cases h : isChoice j <;> simp [h] at hc ⊢
      have hk3 : kind j ≠ 3 := by intro h; rw [show isChoice j = true by simp [isChoice, h]] at hcf; cases hcf
      by_cases hk0 : kind j = 0
      · refine ⟨gA j, hgA j, gB j, hgB j, ?_⟩
        rw [if_neg (by simp [hcf])]; left; intro z
        dsimp only [D]; change evalWire (flip z) (m + j.val) = _
        rw [evalWire_gate (flip z) j, if_pos hk0]
      · by_cases hk1 : kind j = 1
        · refine ⟨gA j, hgA j, gA j, hgA j, ?_⟩
          rw [if_neg (by simp [hcf])]; left; intro z
          dsimp only [D]; change evalWire (flip z) (m + j.val) = _
          rw [evalWire_gate (flip z) j, if_neg hk0, if_pos hk1, Finset.union_idempotent]
        · have hk2 : kind j = 2 := by
            dsimp only [kind] at hk0 hk1 hk3 ⊢
            split_ifs at hk0 hk1 hk3 ⊢ <;> omega
          refine ⟨gA j, hgA j, gB j, hgB j, ?_⟩
          rw [if_neg (by simp [hcf])]; right; intro z
          dsimp only [D]; change evalWire (flip z) (m + j.val) = _
          rw [evalWire_gate (flip z) j, if_neg hk0, if_neg hk1, if_pos hk2]
  have hDcov : ∀ z, ∀ p l : Fin N, I p l → p.val ∈ D z o ∨ N + l.val ∈ D z o :=
    fun z p l hpl' => hcov _ (evalWire_mem (flip z) o ho) p l hpl'
  have hDbase : ∀ p : Fin N, p.val ∉ D (fun _ => false) o ∧ N + p.val ∈ D (fun _ => false) o := by
    intro p; dsimp only [D]; rw [hflip0]; simpa using hbase p
  have hDsat : ∀ T : Finset (Fin N), T.card ≤ q → ∃ z, ∀ p : Fin N,
      (p.val ∈ D z o ↔ ∃ l ∈ T, I p l) ∧ (N + p.val ∈ D z o ↔ p ∉ T) := by
    intro T hT; obtain ⟨z, hz⟩ := hchosen T hT
    exact ⟨flip z, fun p => by dsimp only [D]; rw [hflip2]; exact hz p⟩
  by_cases hU : 2 * (Finset.univ.filter fun j : Fin s => isChoice j = true).card ≤ s
  · exact unionHeavy q N I hq hN hdeg hpl s o D isChoice ho (fun z v hv => evalWire_in (flip z) v hv) hDsteps hDcov hDbase hDsat hU
  · exact choiceHeavy q N I hq hN hdeg hpl s o D isChoice ho (fun z v hv => evalWire_in (flip z) v hv) hDsteps hDcov hDbase hDsat (by omega)

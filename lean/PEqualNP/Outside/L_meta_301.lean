import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_301 :
    ∀ (k : ℕ) (c : ℕ → Bool), (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) → k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤ ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  intro k c hc
  have hbase : ∀ (a m : ℕ),
      (∀ j : ℕ, a ≤ j → j + 1 < a + 2 * m → c j = true ∨ c (j + 1) = true) →
      m ≤ ((Finset.Ico a (a + 2 * m)).filter (fun j => c j = true)).card := by
    intro a m
    induction m with
    | zero =>
      intro _
      exact Nat.zero_le _
    | succ m ih =>
      intro h
      have hm : m ≤ ((Finset.Ico a (a + 2 * m)).filter (fun j => c j = true)).card :=
        ih (fun j hj1 hj2 => h j hj1 (by omega))
      have hpair : c (a + 2 * m) = true ∨ c (a + 2 * m + 1) = true :=
        h (a + 2 * m) (by omega) (by omega)
      have hpos : 1 ≤ ((Finset.Ico (a + 2 * m) (a + 2 * (m + 1))).filter (fun j => c j = true)).card := by
        apply Finset.card_pos.mpr
        rcases hpair with h1 | h2
        · exact ⟨a + 2 * m, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, h1⟩⟩
        · exact ⟨a + 2 * m + 1, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, h2⟩⟩
      have hdisj : Disjoint
          ((Finset.Ico a (a + 2 * m)).filter (fun j => c j = true))
          ((Finset.Ico (a + 2 * m) (a + 2 * (m + 1))).filter (fun j => c j = true)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx1).1).2
        have h2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx2).1).1
        omega
      have hsub :
          ((Finset.Ico a (a + 2 * m)).filter (fun j => c j = true)) ∪
          ((Finset.Ico (a + 2 * m) (a + 2 * (m + 1))).filter (fun j => c j = true)) ⊆
          (Finset.Ico a (a + 2 * (m + 1))).filter (fun j => c j = true) := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx1 | hx2
        · rcases Finset.mem_filter.mp hx1 with ⟨hI, hc'⟩
          rcases Finset.mem_Ico.mp hI with ⟨hlo, hhi⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlo, by omega⟩, hc'⟩
        · rcases Finset.mem_filter.mp hx2 with ⟨hI, hc'⟩
          rcases Finset.mem_Ico.mp hI with ⟨hlo, hhi⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hhi⟩, hc'⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at hcard
      omega
  split_ifs with hboth
  · rcases hboth with ⟨h0, hlast⟩
    cases k with
    | zero =>
      have := hc 0 (by omega)
      simp [h0, hlast] at this
    | succ m =>
      have h1 : c 1 = true := by
        have := hc 0 (by omega)
        simp [h0] at this
        exact this
      have h2 : c (2 * (m + 1)) = true := by
        have := hc (2 * (m + 1)) (by omega)
        simp [hlast] at this
        exact this
      have hmid : m ≤ ((Finset.Ico 2 (2 + 2 * m)).filter (fun j => c j = true)).card :=
        hbase 2 m (fun j hj1 hj2 => hc j (by omega))
      have hnot1 : (1 : ℕ) ∉ insert (2 * (m + 1)) ((Finset.Ico 2 (2 + 2 * m)).filter (fun j => c j = true)) := by
        intro hmem
        rcases Finset.mem_insert.mp hmem with heq | hmem'
        · omega
        · have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hmem').1).1
          omega
      have hnot2 : 2 * (m + 1) ∉ (Finset.Ico 2 (2 + 2 * m)).filter (fun j => c j = true) := by
        intro hmem
        have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hmem).1).2
        omega
      have hsub :
          insert 1 (insert (2 * (m + 1)) ((Finset.Ico 2 (2 + 2 * m)).filter (fun j => c j = true))) ⊆
          (Finset.Icc 1 (2 * (m + 1))).filter (fun j => c j = true) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx1
        · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h1⟩
        · rcases Finset.mem_insert.mp hx1 with rfl | hx2
          · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h2⟩
          · rcases Finset.mem_filter.mp hx2 with ⟨hI, hc'⟩
            rcases Finset.mem_Ico.mp hI with ⟨hlo, hhi⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hc'⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot1, Finset.card_insert_of_notMem hnot2] at hcard
      omega
  · rw [add_zero]
    have hmain : k ≤ ((Finset.Ico 1 (1 + 2 * k)).filter (fun j => c j = true)).card :=
      hbase 1 k (fun j hj1 hj2 => hc j (by omega))
    have hsub :
        (Finset.Ico 1 (1 + 2 * k)).filter (fun j => c j = true) ⊆
        (Finset.Icc 1 (2 * k)).filter (fun j => c j = true) := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hI, hc'⟩
      rcases Finset.mem_Ico.mp hI with ⟨hlo, hhi⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, by omega⟩, hc'⟩
    have hcard := Finset.card_le_card hsub
    omega

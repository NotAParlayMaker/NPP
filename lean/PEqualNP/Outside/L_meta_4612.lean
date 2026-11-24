import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4612

private def legal (A U : List ℕ) : Prop :=
  ∀ i : Fin U.length, ∃ a ∈ A ++ U.take i.val, ∃ b ∈ A ++ U.take i.val,
    U.get i = a &&& b ∨ U.get i = a ||| b

private lemma legal_append {A F K V : List ℕ} (hF : legal A F)
    (hK : ∀ k ∈ K, k ∈ A ++ F) (hV : legal K V) : legal A (F ++ V) := by
  intro i
  by_cases hi : i.val < F.length
  · have hget : (F ++ V).get i = F.get ⟨i.val, hi⟩ := by
      simp [List.get_eq_getElem, List.getElem_append_left hi]
    have htake : (F ++ V).take i.val = F.take i.val :=
      List.take_append_of_le_length (Nat.le_of_lt hi)
    rw [hget, htake]
    exact hF ⟨i.val, hi⟩
  · have hjlt : i.val - F.length < V.length := by
      have hlen := i.isLt
      simp only [List.length_append] at hlen
      omega
    have hge : F.length ≤ i.val := Nat.le_of_not_lt hi
    have hget : (F ++ V).get i = V.get ⟨i.val - F.length, hjlt⟩ := by
      simp [List.get_eq_getElem, List.getElem_append_right hge]
    have htake : (F ++ V).take i.val = F ++ V.take (i.val - F.length) := by
      rw [List.take_append, List.take_of_length_le hge]
    obtain ⟨a, ha, b, hb, hab⟩ := hV ⟨i.val - F.length, hjlt⟩
    have mem_conv : ∀ z, z ∈ K ++ V.take (i.val - F.length) →
        z ∈ A ++ (F ++ V.take (i.val - F.length)) := by
      intro z hz
      rcases List.mem_append.mp hz with hzK | hzV
      · rcases List.mem_append.mp (hK z hzK) with hzA | hzF
        · exact List.mem_append_left _ hzA
        · exact List.mem_append_right _ (List.mem_append_left _ hzF)
      · exact List.mem_append_right _ (List.mem_append_right _ hzV)
    rw [hget, htake]
    exact ⟨a, mem_conv a ha, b, mem_conv b hb, hab⟩

private lemma legal_cons_drop {A : List ℕ} {x : ℕ} {xs : List ℕ}
    (hx : x ∈ A) (h : legal A (x :: xs)) : legal A xs := by
  intro j
  obtain ⟨a, ha, b, hb, hab⟩ := h j.succ
  have htake : (x :: xs).take j.succ.val = x :: xs.take j.val := rfl
  have hget : (x :: xs).get j.succ = xs.get j := rfl
  rw [htake] at ha hb
  rw [hget] at hab
  have mem_sub : ∀ z, z ∈ A ++ x :: xs.take j.val → z ∈ A ++ xs.take j.val := by
    intro z hz
    rcases List.mem_append.mp hz with hzA | hzT
    · exact List.mem_append_left _ hzA
    · rcases List.mem_cons.mp hzT with rfl | hzT'
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ hzT'
  exact ⟨a, mem_sub a ha, b, mem_sub b hb, hab⟩

private lemma legal_cons_keep {A : List ℕ} {x : ℕ} {xs : List ℕ}
    (h : legal A (x :: xs)) :
    (∃ a ∈ A, ∃ b ∈ A, x = a &&& b ∨ x = a ||| b) ∧ legal (A ++ [x]) xs := by
  constructor
  · simpa [List.take] using h ⟨0, Nat.succ_pos _⟩
  · intro j
    obtain ⟨a, ha, b, hb, hab⟩ := h j.succ
    have htake : (x :: xs).take j.succ.val = x :: xs.take j.val := rfl
    have hget : (x :: xs).get j.succ = xs.get j := rfl
    rw [htake] at ha hb
    rw [hget] at hab
    have mem_sub : ∀ z, z ∈ A ++ x :: xs.take j.val → z ∈ (A ++ [x]) ++ xs.take j.val := by
      intro z hz
      rcases List.mem_append.mp hz with hzA | hzT
      · exact List.mem_append_left _ (List.mem_append_left _ hzA)
      · rcases List.mem_cons.mp hzT with rfl | hzT'
        · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self z))
        · exact List.mem_append_right _ hzT'
    exact ⟨a, mem_sub a ha, b, mem_sub b hb, hab⟩

private lemma legal_cons_of {A : List ℕ} {x : ℕ} {xs : List ℕ}
    (hx : ∃ a ∈ A, ∃ b ∈ A, x = a &&& b ∨ x = a ||| b)
    (hxs : legal (A ++ [x]) xs) : legal A (x :: xs) := by
  intro i
  cases hi : i.val with
  | zero =>
    have hget : (x :: xs).get i = x := by simp [List.get_eq_getElem, hi]
    rw [hget]
    simpa [List.take, List.append_nil] using hx
  | succ j =>
    have hjlt : j < xs.length := by
      have hlen := i.isLt
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := hxs ⟨j, hjlt⟩
    have hget : (x :: xs).get i = xs.get ⟨j, hjlt⟩ := by
      simp [List.get_eq_getElem, hi]
    have mem_sub : ∀ z, z ∈ (A ++ [x]) ++ xs.take j → z ∈ A ++ x :: xs.take j := by
      intro z hz
      rcases List.mem_append.mp hz with hzAx | hzT
      · rcases List.mem_append.mp hzAx with hzA | hzx
        · exact List.mem_append_left _ hzA
        · rw [List.mem_singleton.mp hzx]
          exact List.mem_append_right _ (List.mem_cons_self)
      · exact List.mem_append_right _ (List.mem_cons_of_mem x hzT)
    rw [hget]
    change ∃ a ∈ A ++ x :: xs.take j, ∃ b ∈ A ++ x :: xs.take j,
      xs.get ⟨j, hjlt⟩ = a &&& b ∨ xs.get ⟨j, hjlt⟩ = a ||| b
    exact ⟨a, mem_sub a ha, b, mem_sub b hb, hab⟩

private def clean (A : List ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => if x ∈ A then clean A xs else x :: clean (A ++ [x]) xs

private lemma clean_length (A U : List ℕ) : (clean A U).length ≤ U.length := by
  induction U generalizing A with
  | nil => simp [clean]
  | cons x xs ih =>
    unfold clean
    split
    · exact Nat.le_trans (ih A) (Nat.le_succ _)
    · exact Nat.succ_le_succ (ih (A ++ [x]))

private lemma clean_fresh (A U : List ℕ) : ∀ y ∈ clean A U, y ∉ A := by
  induction U generalizing A with
  | nil => intro y hy; simp [clean] at hy
  | cons x xs ih =>
    intro y hy
    unfold clean at hy
    split at hy
    · exact ih A y hy
    · rename_i hx
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hx
      · have hnot := ih (A ++ [x]) y hy'
        exact fun hm => hnot (List.mem_append_left _ hm)

private lemma clean_nodup (A U : List ℕ) : (clean A U).Nodup := by
  induction U generalizing A with
  | nil => simp [clean]
  | cons x xs ih =>
    unfold clean
    split
    · exact ih A
    · refine List.nodup_cons.mpr ⟨?_, ih (A ++ [x])⟩
      intro hx'
      exact clean_fresh (A ++ [x]) xs x hx' (List.mem_append_right _ (List.mem_singleton_self x))

private lemma clean_mem (A U : List ℕ) : ∀ z ∈ U, z ∈ A ∨ z ∈ clean A U := by
  induction U generalizing A with
  | nil => intro z hz; simp at hz
  | cons x xs ih =>
    intro z hz
    unfold clean
    split
    · rename_i hx
      rcases List.mem_cons.mp hz with rfl | hzs
      · exact Or.inl hx
      · exact ih A z hzs
    · rcases List.mem_cons.mp hz with rfl | hzs
      · exact Or.inr List.mem_cons_self
      · rcases ih (A ++ [x]) z hzs with hzAx | hzC
        · rcases List.mem_append.mp hzAx with hzA | hzx
          · exact Or.inl hzA
          · rw [List.mem_singleton.mp hzx]
            exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem x hzC)

private lemma clean_legal (A U : List ℕ) (h : legal A U) : legal A (clean A U) := by
  induction U generalizing A with
  | nil => intro i; exact Fin.elim0 i
  | cons x xs ih =>
    unfold clean
    split
    · rename_i hx
      exact ih A (legal_cons_drop hx h)
    · obtain ⟨hstep0, htail⟩ := legal_cons_keep h
      exact legal_cons_of hstep0 (ih (A ++ [x]) htail)

end PEqualNP.Outside.L_meta_4612

theorem PEqualNP.Outside.L_meta_4612 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 x4 x5 : List ℕ), ∀ x6 ∉ x2, x1 x2 x3 → (∀ x9 ∈ x4, x9 ∈ x2 ++ x3) → x1 x4 x5 → x6 ∈ x4 ++ x5 → ∃ (x12 : List ℕ), x12.length ≤ x3.length + x5.length ∧ x12.Nodup ∧ (∀ x13 ∈ x12, x13 ∉ x2) ∧ x6 ∈ x12 ∧ x1 x2 x12 := by
  dsimp only
  intro A F K V t ht hF hK hV htmem
  have hcat : PEqualNP.Outside.L_meta_4612.legal A (F ++ V) :=
    PEqualNP.Outside.L_meta_4612.legal_append hF hK hV
  have htcat : t ∈ F ++ V := by
    rcases List.mem_append.mp htmem with htK | htV
    · rcases List.mem_append.mp (hK t htK) with htA | htF
      · exact False.elim (ht htA)
      · exact List.mem_append_left _ htF
    · exact List.mem_append_right _ htV
  refine ⟨PEqualNP.Outside.L_meta_4612.clean A (F ++ V), ?_,
    PEqualNP.Outside.L_meta_4612.clean_nodup A (F ++ V),
    PEqualNP.Outside.L_meta_4612.clean_fresh A (F ++ V), ?_,
    PEqualNP.Outside.L_meta_4612.clean_legal A (F ++ V) hcat⟩
  · simpa only [List.length_append] using PEqualNP.Outside.L_meta_4612.clean_length A (F ++ V)
  · exact (PEqualNP.Outside.L_meta_4612.clean_mem A (F ++ V) t htcat).resolve_left ht

import Mathlib.Data.Nat.Notation

namespace PEqualNP.Outside.L_meta_4612

def valid (base l : List ℕ) : Prop :=
  ∀ (i : Fin l.length),
    ∃ u ∈ base ++ List.take (↑i) l,
    ∃ v ∈ base ++ List.take (↑i) l,
    l.get i = u &&& v ∨ l.get i = u ||| v

lemma valid_append (x1 x2 x3 x4 : List ℕ)
    (hx2 : valid x1 x2)
    (hsub : ∀ z ∈ x3, z ∈ x1 ++ x2)
    (hx4 : valid x3 x4) :
    valid x1 (x2 ++ x4) := by
  intro idx
  by_cases hlt : idx.val < x2.length
  · have ⟨a, ha, b, hb, hval⟩ := hx2 ⟨idx.val, hlt⟩
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact ha
    · rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hb
    · rw [List.get_eq_getElem, List.getElem_append_left hlt]
      simpa [List.get_eq_getElem] using hval
  · have hge : x2.length ≤ idx.val := Nat.le_of_not_lt hlt
    have hidx4 : idx.val - x2.length < x4.length := by
      have hlen : idx.val < x2.length + x4.length := by
        simpa [List.length_append] using idx.isLt
      omega
    have ⟨a, ha, b, hb, hval⟩ := hx4 ⟨idx.val - x2.length, hidx4⟩
    have hmem : ∀ z, z ∈ x3 ++ List.take (idx.val - x2.length) x4 → z ∈ x1 ++ List.take idx.val (x2 ++ x4) := by
      intro z hz
      rw [List.take_append, List.take_of_length_le hge, ← List.append_assoc]
      rw [List.mem_append] at hz ⊢
      rcases hz with hz3 | hz4
      · exact Or.inl (hsub z hz3)
      · exact Or.inr hz4
    refine ⟨a, hmem a ha, b, hmem b hb, ?_⟩
    rw [List.get_eq_getElem, List.getElem_append_right hge]
    simpa [List.get_eq_getElem] using hval

def cleanAux (base acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | a :: rest =>
    if a ∈ base ∨ a ∈ acc then
      cleanAux base acc rest
    else
      cleanAux base (acc ++ [a]) rest

lemma cleanAux_spec (base : List ℕ) :
    ∀ (rem acc : List ℕ),
      acc.Nodup →
      (∀ z ∈ acc, z ∉ base) →
      valid base acc →
      valid (base ++ acc) rem →
      let res := cleanAux base acc rem
      res.length ≤ acc.length + rem.length ∧
      res.Nodup ∧
      (∀ z ∈ res, z ∉ base) ∧
      (∀ z ∈ base ++ acc ++ rem, z ∈ base ++ res) ∧
      valid base res
  | [], acc, hnd, hdisj, hvacc, _ => by
    refine ⟨by simp [cleanAux], hnd, hdisj, ?_, hvacc⟩
    intro z hz
    simpa [cleanAux] using hz
  | a :: rest, acc, hnd, hdisj, hvacc, hvrem => by
    by_cases hmem : a ∈ base ∨ a ∈ acc
    · have hvrest : valid (base ++ acc) rest := by
        intro idx
        have ⟨u, hu, v, hv, hval⟩ := hvrem ⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩
        have hlift : ∀ z, z ∈ base ++ acc ++ List.take (idx.val + 1) (a :: rest) →
            z ∈ base ++ acc ++ List.take idx.val rest := by
          intro z hz
          simp only [List.take_succ_cons, List.mem_append, List.mem_cons] at hz ⊢
          rcases hz with (hb | ha) | (rfl | hr)
          · exact Or.inl (Or.inl hb)
          · exact Or.inl (Or.inr ha)
          · rcases hmem with hab | haa
            · exact Or.inl (Or.inl hab)
            · exact Or.inl (Or.inr haa)
          · exact Or.inr hr
        refine ⟨u, hlift u hu, v, hlift v hv, ?_⟩
        simpa [List.get_eq_getElem] using hval
      have ih := cleanAux_spec base rest acc hnd hdisj hvacc hvrest
      simp only [cleanAux, hmem, ↓reduceIte]
      refine ⟨Nat.le_trans ih.1 (by simp), ih.2.1, ih.2.2.1, ?_, ih.2.2.2.2⟩
      intro z hz
      apply ih.2.2.2.1
      simp only [List.mem_append, List.mem_cons] at hz ⊢
      rcases hz with (hb | ha) | (rfl | hr)
      · exact Or.inl (Or.inl hb)
      · exact Or.inl (Or.inr ha)
      · rcases hmem with hab | haa
        · exact Or.inl (Or.inl hab)
        · exact Or.inl (Or.inr haa)
      · exact Or.inr hr
    · have hnotbase : a ∉ base := fun h => hmem (Or.inl h)
      have hnotacc : a ∉ acc := fun h => hmem (Or.inr h)
      have hnd' : (acc ++ [a]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hnd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
        intro x hx y hy hxy
        simp only [List.mem_singleton] at hy
        subst hy
        subst hxy
        exact hnotacc hx
      have hdisj' : ∀ z ∈ acc ++ [a], z ∉ base := by
        intro z hz
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hza | rfl
        · exact hdisj z hza
        · exact hnotbase
      have hvacc' : valid base (acc ++ [a]) := by
        apply valid_append base acc (base ++ acc) [a] hvacc (fun z hz => hz)
        intro idx
        have h0 : idx.val = 0 := Nat.lt_one_iff.mp idx.isLt
        have ⟨u, hu, v, hv, hval⟩ := hvrem ⟨0, Nat.zero_lt_succ rest.length⟩
        refine ⟨u, ?_, v, ?_, ?_⟩
        · simpa [h0] using hu
        · simpa [h0] using hv
        · simp only [List.get_eq_getElem, h0] at hval ⊢
          exact hval
      have hvrest : valid (base ++ (acc ++ [a])) rest := by
        intro idx
        have ⟨u, hu, v, hv, hval⟩ := hvrem ⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩
        have hlift : ∀ z, z ∈ base ++ acc ++ List.take (idx.val + 1) (a :: rest) →
            z ∈ base ++ (acc ++ [a]) ++ List.take idx.val rest := by
          intro z hz
          simp only [List.take_succ_cons, List.mem_append, List.mem_cons] at hz ⊢
          rcases hz with (hb | ha) | (rfl | hr)
          · exact Or.inl (Or.inl hb)
          · exact Or.inl (Or.inr (Or.inl ha))
          · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr hr
        refine ⟨u, hlift u hu, v, hlift v hv, ?_⟩
        simpa [List.get_eq_getElem] using hval
      have ih := cleanAux_spec base rest (acc ++ [a]) hnd' hdisj' hvacc' hvrest
      simp only [cleanAux, hmem, ↓reduceIte]
      refine ⟨?_, ih.2.1, ih.2.2.1, ?_, ih.2.2.2.2⟩
      · have hlen := ih.1
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
        omega
      · intro z hz
        apply ih.2.2.2.1
        simp only [List.mem_append, List.mem_cons] at hz ⊢
        rcases hz with (hb | ha) | (rfl | hr)
        · exact Or.inl (Or.inl hb)
        · exact Or.inl (Or.inr (Or.inl ha))
        · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr hr

end PEqualNP.Outside.L_meta_4612

theorem PEqualNP.Outside.L_meta_4612 :
    have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 x4 x5 : List ℕ), ∀ x6 ∉ x2, x1 x2 x3 → (∀ x9 ∈ x4, x9 ∈ x2 ++ x3) → x1 x4 x5 → x6 ∈ x4 ++ x5 → ∃ (x12 : List ℕ), x12.length ≤ x3.length + x5.length ∧ x12.Nodup ∧ (∀ x13 ∈ x12, x13 ∉ x2) ∧ x6 ∈ x12 ∧ x1 x2 x12 := by
  dsimp only
  intro x2 x3 x4 x5 x6 hx6not hx3 hsub hx5 hx6mem
  have hvcomb : PEqualNP.Outside.L_meta_4612.valid x2 (x3 ++ x5) :=
    PEqualNP.Outside.L_meta_4612.valid_append x2 x3 x4 x5 hx3 hsub hx5
  have hspec := PEqualNP.Outside.L_meta_4612.cleanAux_spec x2 (x3 ++ x5) []
    List.nodup_nil
    (fun z hz => by cases hz)
    (fun idx => by cases idx.isLt)
    (by simpa using hvcomb)
  refine ⟨PEqualNP.Outside.L_meta_4612.cleanAux x2 [] (x3 ++ x5), ?_, hspec.2.1, hspec.2.2.1, ?_, hspec.2.2.2.2⟩
  · simpa [List.length_append] using hspec.1
  · have hx6in : x6 ∈ x2 ++ [] ++ (x3 ++ x5) := by
      simp only [List.append_nil, List.mem_append] at hx6mem ⊢
      rcases hx6mem with hx64 | hx65
      · have h := hsub x6 hx64
        rw [List.mem_append] at h
        rcases h with h2 | h3
        · exact Or.inl h2
        · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr hx65)
    have hres := hspec.2.2.2.1 x6 hx6in
    rw [List.mem_append] at hres
    rcases hres with h2 | h12
    · exact absurd h2 hx6not
    · exact h12

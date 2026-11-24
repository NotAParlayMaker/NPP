import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4612

def Good (B L : List ℕ) : Prop :=
  ∀ i (h : i < L.length), ∃ a ∈ B ++ L.take i, ∃ b ∈ B ++ L.take i, L[i] = a &&& b ∨ L[i] = a ||| b

theorem good_iff (B L : List ℕ) :
    (∀ (x3 : Fin L.length), ∃ x4 ∈ B ++ List.take (↑x3) L, ∃ x5 ∈ B ++ List.take (↑x3) L,
      L.get x3 = x4 &&& x5 ∨ L.get x3 = x4 ||| x5) ↔ Good B L := by
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h x
    exact h x.val x.isLt

theorem good_snoc (B L : List ℕ) (v : ℕ) :
    Good B (L ++ [v]) ↔ Good B L ∧ ∃ a ∈ B ++ L, ∃ b ∈ B ++ L, v = a &&& b ∨ v = a ||| b := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      have hi' : i < (L ++ [v]).length := by simp; omega
      obtain ⟨a, ha, b, hb, hab⟩ := h i hi'
      rw [List.take_append_of_le_length (by omega)] at ha hb
      rw [List.getElem_append_left hi] at hab
      exact ⟨a, ha, b, hb, hab⟩
    · have hi' : L.length < (L ++ [v]).length := by simp
      obtain ⟨a, ha, b, hb, hab⟩ := h L.length hi'
      rw [List.take_left' rfl] at ha hb
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero] at hab
      exact ⟨a, ha, b, hb, hab⟩
  · rintro ⟨hL, a, ha, b, hb, hab⟩ i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < L.length
    · obtain ⟨a', ha', b', hb', hab'⟩ := hL i hlt
      refine ⟨a', ?_, b', ?_, ?_⟩
      · rw [List.take_append_of_le_length (by omega)]; exact ha'
      · rw [List.take_append_of_le_length (by omega)]; exact hb'
      · rw [List.getElem_append_left hlt]; exact hab'
    · have hi2 : i = L.length := by omega
      subst hi2
      refine ⟨a, ?_, b, ?_, ?_⟩
      · rw [List.take_left' rfl]; exact ha
      · rw [List.take_left' rfl]; exact hb
      · simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
        exact hab

theorem good_append (B B2 L1 : List ℕ) (h1 : Good B L1) (hsub : ∀ y ∈ B2, y ∈ B ++ L1) :
    ∀ L2 : List ℕ, Good B2 L2 → Good B (L1 ++ L2) := by
  intro L2
  induction L2 using List.reverseRecOn with
  | nil => intro _; simpa using h1
  | append_singleton L v ih =>
    intro h
    rw [good_snoc] at h
    obtain ⟨hL, a, ha, b, hb, hab⟩ := h
    rw [← List.append_assoc, good_snoc]
    have hmem : ∀ c ∈ B2 ++ L, c ∈ B ++ (L1 ++ L) := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp (hsub c hc) with h' | h'
        · exact List.mem_append_left _ h'
        · exact List.mem_append_right _ (List.mem_append_left _ h')
      · exact List.mem_append_right _ (List.mem_append_right _ hc)
    exact ⟨ih hL, a, hmem a ha, b, hmem b hb, hab⟩

theorem prune (B : List ℕ) : ∀ L : List ℕ, Good B L → ∃ M : List ℕ, M.Nodup ∧ (∀ m ∈ M, m ∉ B) ∧
    (∀ v ∈ L, v ∉ B → v ∈ M) ∧ M.length ≤ L.length ∧ Good B M := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], by simp, by simp, by simp, by simp, ?_⟩
    intro i hi
    simp at hi
  | append_singleton L v ih =>
    intro h
    rw [good_snoc] at h
    obtain ⟨hL, a, ha, b, hb, hab⟩ := h
    obtain ⟨M0, hnd, hnb, hcov, hlen, hgood⟩ := ih hL
    by_cases hv : v ∈ B ∨ v ∈ M0
    · refine ⟨M0, hnd, hnb, ?_, by simp; omega, hgood⟩
      intro w hw hwB
      rcases List.mem_append.mp hw with hw | hw
      · exact hcov w hw hwB
      · simp only [List.mem_singleton] at hw
        subst hw
        rcases hv with hv | hv
        · exact absurd hv hwB
        · exact hv
    · push Not at hv
      refine ⟨M0 ++ [v], ?_, ?_, ?_, by simp; omega, ?_⟩
      · exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton v, by
          simp only [List.mem_singleton]
          intro a ha b hb h
          subst hb
          subst h
          exact hv.2 ha⟩
      · intro m hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hnb m hm
        · simp only [List.mem_singleton] at hm
          subst hm
          exact hv.1
      · intro w hw hwB
        rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_left _ (hcov w hw hwB)
        · exact List.mem_append_right _ hw
      · rw [good_snoc]
        have hmem : ∀ c ∈ B ++ L, c ∈ B ++ M0 := by
          intro c hc
          by_cases hcB : c ∈ B
          · exact List.mem_append_left _ hcB
          · rcases List.mem_append.mp hc with hc | hc
            · exact absurd hc hcB
            · exact List.mem_append_right _ (hcov c hc hcB)
        exact ⟨hgood, a, hmem a ha, b, hmem b hb, hab⟩

end PEqualNP.Outside.L_meta_4612

theorem PEqualNP.Outside.L_meta_4612 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 x4 x5 : List ℕ), ∀ x6 ∉ x2, x1 x2 x3 → (∀ x9 ∈ x4, x9 ∈ x2 ++ x3) → x1 x4 x5 → x6 ∈ x4 ++ x5 → ∃ (x12 : List ℕ), x12.length ≤ x3.length + x5.length ∧ x12.Nodup ∧ (∀ x13 ∈ x12, x13 ∉ x2) ∧ x6 ∈ x12 ∧ x1 x2 x12 := by
  dsimp only
  intro B L1 B2 L2 x6 hx6 h1 hsub h2 hin
  rw [PEqualNP.Outside.L_meta_4612.good_iff] at h1 h2
  have hall := PEqualNP.Outside.L_meta_4612.good_append B B2 L1 h1 hsub L2 h2
  obtain ⟨M, hnd, hnb, hcov, hlen, hgood⟩ := PEqualNP.Outside.L_meta_4612.prune B _ hall
  refine ⟨M, by simpa using hlen, hnd, hnb, ?_, ?_⟩
  · apply hcov x6 _ hx6
    rcases List.mem_append.mp hin with h | h
    · rcases List.mem_append.mp (hsub x6 h) with h' | h'
      · exact absurd h' hx6
      · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ h
  · exact (PEqualNP.Outside.L_meta_4612.good_iff B M).2 hgood

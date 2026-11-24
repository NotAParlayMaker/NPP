import Mathlib

namespace PEqualNP.Outside.L_meta_4612_aux

def Der (B L : List ℕ) : Prop :=
  ∀ (i : Fin L.length), ∃ a ∈ B ++ List.take (↑i) L, ∃ b ∈ B ++ List.take (↑i) L,
    L.get i = a &&& b ∨ L.get i = a ||| b

def step (B acc : List ℕ) (y : ℕ) : List ℕ := if y ∈ B ∨ y ∈ acc then acc else acc ++ [y]

def proc (B acc L : List ℕ) : List ℕ := L.foldl (step B) acc

theorem der_snoc {B acc : List ℕ} {y : ℕ} (h : Der B acc)
    (hy : ∃ a ∈ B ++ acc, ∃ b ∈ B ++ acc, y = a &&& b ∨ y = a ||| b) : Der B (acc ++ [y]) := by
  intro i
  have hi := i.isLt
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge (↑i) acc.length with hlt | hge
  · obtain ⟨a, ha, b, hb, hab⟩ := h ⟨i, hlt⟩
    have ht : List.take (↑i) (acc ++ [y]) = List.take (↑i) acc := by
      rw [List.take_append_of_le_length (by omega)]
    have hg : (acc ++ [y]).get i = acc.get ⟨i, hlt⟩ := by
      simp [List.getElem_append_left hlt]
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [ht]; exact ha
    · rw [ht]; exact hb
    · rw [hg]; exact hab
  · have hi' : (i : ℕ) = acc.length := by omega
    have ht : List.take (↑i) (acc ++ [y]) = acc := by
      rw [hi', List.take_left]
    have hg : (acc ++ [y]).get i = y := by
      simp [hi']
    obtain ⟨a, ha, b, hb, hab⟩ := hy
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [ht]; exact ha
    · rw [ht]; exact hb
    · rw [hg]; exact hab

def Avail (B acc : List ℕ) (z : ℕ) : Prop := z ∈ B ∨ z ∈ acc

theorem step_sub {B acc : List ℕ} {y z : ℕ} (h : z ∈ acc) : z ∈ step B acc y := by
  unfold step; split
  · exact h
  · exact List.mem_append_left _ h

theorem step_avail (B acc : List ℕ) (y : ℕ) : Avail B (step B acc y) y := by
  unfold step Avail; split
  · rename_i h; rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact Or.inr (by simp)

theorem proc_spec (B : List ℕ) : ∀ (L acc : List ℕ), Der B acc → acc.Nodup → (∀ z ∈ acc, z ∉ B) →
    (∀ (i : Fin L.length), ∃ a, (Avail B acc a ∨ a ∈ List.take (↑i) L) ∧
      ∃ b, (Avail B acc b ∨ b ∈ List.take (↑i) L) ∧ (L.get i = a &&& b ∨ L.get i = a ||| b)) →
    Der B (proc B acc L) ∧ (proc B acc L).Nodup ∧ (∀ z ∈ proc B acc L, z ∉ B) ∧
      (∀ z, Avail B acc z ∨ z ∈ L → Avail B (proc B acc L) z) ∧
      (proc B acc L).length ≤ acc.length + L.length
  | [], acc, hd, hn, hb, _ => by
    refine ⟨hd, hn, hb, ?_, by simp [proc]⟩
    intro z hz
    rcases hz with hz | hz
    · simpa [proc] using hz
    · simp at hz
  | y :: L, acc, hd, hn, hb, hL => by
    have h0 := hL ⟨0, by simp⟩
    obtain ⟨a, ha, b, hb', hab⟩ := h0
    simp only [List.take_zero, List.not_mem_nil, or_false, List.get_eq_getElem,
      List.getElem_cons_zero] at ha hb' hab
    set acc' := step B acc y with hacc'
    have hsub : ∀ z, Avail B acc z → Avail B acc' z := by
      intro z hz; rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (step_sub hz)
    have hd' : Der B acc' := by
      rw [hacc']; unfold step; split
      · exact hd
      · apply der_snoc hd
        refine ⟨a, ?_, b, ?_, hab⟩
        · rcases ha with ha | ha
          · exact List.mem_append_left _ ha
          · exact List.mem_append_right _ ha
        · rcases hb' with hb' | hb'
          · exact List.mem_append_left _ hb'
          · exact List.mem_append_right _ hb'
    have hn' : acc'.Nodup := by
      rw [hacc']; unfold step; split
      · exact hn
      · rename_i h
        push_neg at h
        exact List.nodup_append.2 ⟨hn, List.nodup_singleton y, by
          intro u hu v hv; simp at hv; subst hv; intro e; subst e; exact h.2 hu⟩
    have hb2 : ∀ z ∈ acc', z ∉ B := by
      rw [hacc']; unfold step; split
      · exact hb
      · rename_i h
        push_neg at h
        intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · exact hb z hz
        · simp at hz; subst hz; exact h.1
    have hL' : ∀ (i : Fin L.length), ∃ a, (Avail B acc' a ∨ a ∈ List.take (↑i) L) ∧
        ∃ b, (Avail B acc' b ∨ b ∈ List.take (↑i) L) ∧ (L.get i = a &&& b ∨ L.get i = a ||| b) := by
      intro i
      obtain ⟨a, ha, b, hb, hab⟩ := hL ⟨i + 1, by simp⟩
      have hget : (y :: L).get ⟨i + 1, by simp⟩ = L.get i := by simp
      have htake : List.take (↑i + 1) (y :: L) = y :: List.take (↑i) L := by simp
      simp only [Fin.val_mk] at ha hb
      rw [htake] at ha hb
      rw [hget] at hab
      have conv : ∀ z, (Avail B acc z ∨ z ∈ y :: List.take (↑i) L) →
          (Avail B acc' z ∨ z ∈ List.take (↑i) L) := by
        intro z hz
        rcases hz with hz | hz
        · exact Or.inl (hsub z hz)
        · rcases List.mem_cons.1 hz with hz | hz
          · subst hz; exact Or.inl (step_avail B acc z)
          · exact Or.inr hz
      exact ⟨a, conv a ha, b, conv b hb, hab⟩
    obtain ⟨r1, r2, r3, r4, r5⟩ := proc_spec B L acc' hd' hn' hb2 hL'
    have hlen : acc'.length ≤ acc.length + 1 := by
      rw [hacc']; unfold step; split <;> simp
    have hp : proc B acc (y :: L) = proc B acc' L := by simp [proc, hacc']
    rw [hp]
    refine ⟨r1, r2, r3, ?_, by simp; omega⟩
    intro z hz
    rcases hz with hz | hz
    · exact r4 z (Or.inl (hsub z hz))
    · rcases List.mem_cons.1 hz with hz | hz
      · subst hz; exact r4 z (Or.inl (step_avail B acc z))
      · exact r4 z (Or.inr hz)

end PEqualNP.Outside.L_meta_4612_aux

open PEqualNP.Outside.L_meta_4612_aux

theorem PEqualNP.Outside.L_meta_4612 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 x4 x5 : List ℕ), ∀ x6 ∉ x2, x1 x2 x3 → (∀ x9 ∈ x4, x9 ∈ x2 ++ x3) → x1 x4 x5 → x6 ∈ x4 ++ x5 → ∃ (x12 : List ℕ), x12.length ≤ x3.length + x5.length ∧ x12.Nodup ∧ (∀ x13 ∈ x12, x13 ∉ x2) ∧ x6 ∈ x12 ∧ x1 x2 x12 := by
  intro D B L1 B2 L2 x hx h1 hB2 h2 hmem
  have hD0 : Der B [] := fun i => absurd i.isLt (by simp)
  obtain ⟨p1, p2, p3, p4, p5⟩ := proc_spec B L1 [] hD0 List.nodup_nil (by simp) (by
    intro i
    obtain ⟨a, ha, b, hb, hab⟩ := h1 i
    refine ⟨a, ?_, b, ?_, hab⟩
    · rcases List.mem_append.1 ha with ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inr ha
    · rcases List.mem_append.1 hb with hb | hb
      · exact Or.inl (Or.inl hb)
      · exact Or.inr hb)
  set r1 := proc B [] L1
  have hB2a : ∀ z ∈ B2, Avail B r1 z := by
    intro z hz
    rcases List.mem_append.1 (hB2 z hz) with h | h
    · exact Or.inl h
    · exact p4 z (Or.inr h)
  obtain ⟨q1, q2, q3, q4, q5⟩ := proc_spec B L2 r1 p1 p2 p3 (by
    intro i
    obtain ⟨a, ha, b, hb, hab⟩ := h2 i
    refine ⟨a, ?_, b, ?_, hab⟩
    · rcases List.mem_append.1 ha with ha | ha
      · exact Or.inl (hB2a a ha)
      · exact Or.inr ha
    · rcases List.mem_append.1 hb with hb | hb
      · exact Or.inl (hB2a b hb)
      · exact Or.inr hb)
  refine ⟨proc B r1 L2, by simp at p5; omega, q2, q3, ?_, q1⟩
  have hav : Avail B (proc B r1 L2) x := by
    rcases List.mem_append.1 hmem with h | h
    · exact q4 x (Or.inl (hB2a x h))
    · exact q4 x (Or.inr h)
  rcases hav with h | h
  · exact absurd h hx
  · exact h

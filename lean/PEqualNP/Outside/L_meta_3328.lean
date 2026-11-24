import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328

def One (S : List ℕ) (v : ℕ) : Prop := ∃ a ∈ S, ∃ b ∈ S, v = a &&& b ∨ v = a ||| b

def Seq (S L : List ℕ) : Prop := ∀ i : Fin L.length, One (S ++ L.take i) (L.get i)

lemma one_mono {S T : List ℕ} {v : ℕ} (h : ∀ a ∈ S, a ∈ T) (hv : One S v) : One T v := by
  obtain ⟨a, ha, b, hb, e⟩ := hv
  exact ⟨a, h a ha, b, h b hb, e⟩

lemma seq_cons {S : List ℕ} {a : ℕ} {L : List ℕ} :
    Seq S (a :: L) ↔ One S a ∧ Seq (S ++ [a]) L := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h ⟨0, by simp⟩
    · intro i
      have := h ⟨i.1 + 1, by simp⟩
      simpa [List.take_succ_cons, List.append_assoc] using this
  · rintro ⟨h0, h1⟩ ⟨i, hi⟩
    cases i with
    | zero => simpa using h0
    | succ j =>
      have := h1 ⟨j, by simpa using hi⟩
      simpa [List.take_succ_cons, List.append_assoc] using this

lemma seq_mono : ∀ {L S T : List ℕ}, (∀ a ∈ S, a ∈ T) → Seq S L → Seq T L
  | [], _, _, _, _ => fun i => i.elim0
  | a :: l, S, T, h, hL => by
    rw [seq_cons] at hL ⊢
    obtain ⟨h0, h1⟩ := hL
    refine ⟨one_mono h h0, seq_mono ?_ h1⟩
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (h x hx)
    · exact Or.inr hx

lemma seq_snoc : ∀ {L S : List ℕ} {v : ℕ}, Seq S L → One (S ++ L) v → Seq S (L ++ [v])
  | [], S, v, _, hv => by
    rw [List.nil_append, seq_cons]
    exact ⟨by simpa using hv, fun i => i.elim0⟩
  | a :: l, S, v, hL, hv => by
    rw [List.cons_append, seq_cons]
    rw [seq_cons] at hL
    obtain ⟨h0, h1⟩ := hL
    exact ⟨h0, seq_snoc h1 (by simpa [List.append_assoc] using hv)⟩

def keep : List ℕ → List ℕ → List ℕ
  | _, [] => []
  | s, a :: l => if a ∈ s then keep s l else a :: keep (a :: s) l

lemma keep_seq : ∀ (L s : List ℕ), Seq s L → Seq s (keep s L)
  | [], _, _ => fun i => i.elim0
  | a :: l, s, h => by
    rw [seq_cons] at h
    obtain ⟨h0, h1⟩ := h
    by_cases ha : a ∈ s
    · rw [keep, if_pos ha]
      refine keep_seq l s (seq_mono ?_ h1)
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hx
      · exact ha
    · rw [keep, if_neg ha, seq_cons]
      refine ⟨h0, seq_mono ?_ (keep_seq l (a :: s) (seq_mono ?_ h1))⟩
      · intro x hx
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        tauto
      · intro x hx
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        tauto

lemma keep_out : ∀ (L s : List ℕ) (x : ℕ), x ∈ keep s L → x ∉ s
  | [], _, _, h => by simp [keep] at h
  | a :: l, s, x, h => by
    unfold keep at h
    split_ifs at h with ha
    · exact keep_out l s x h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ha
      · have := keep_out l (a :: s) x h
        simp only [List.mem_cons, not_or] at this
        exact this.2

lemma keep_nodup : ∀ (L s : List ℕ), (keep s L).Nodup
  | [], _ => by simp [keep]
  | a :: l, s => by
    unfold keep
    split_ifs with ha
    · exact keep_nodup l s
    · refine List.nodup_cons.mpr ⟨fun h => ?_, keep_nodup l (a :: s)⟩
      exact keep_out l (a :: s) a h (by simp)

lemma keep_len : ∀ (L s : List ℕ), (keep s L).length ≤ L.length
  | [], _ => by simp [keep]
  | a :: l, s => by
    unfold keep
    split_ifs with ha
    · have := keep_len l s
      simp only [List.length_cons]
      omega
    · have := keep_len l (a :: s)
      simp only [List.length_cons]
      omega

lemma keep_mem : ∀ (L s : List ℕ) (x : ℕ), x ∈ L → x ∉ s → x ∈ keep s L
  | [], _, _, h, _ => by simp at h
  | a :: l, s, x, h, hx => by
    unfold keep
    split_ifs with ha
    · rcases List.mem_cons.mp h with rfl | h
      · exact absurd ha hx
      · exact keep_mem l s x h hx
    · by_cases e : x = a
      · subst e
        exact List.mem_cons_self
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h e
        · exact List.mem_cons_of_mem _ (keep_mem l (a :: s) x h (by simp [e, hx]))

end PEqualNP.Outside.L_meta_3328

open PEqualNP.Outside.L_meta_3328

theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  show ∀ (B : List ℕ) (w t : ℕ) (L : List ℕ), t ∉ B → One B w → Seq (w :: B) L →
    One (w :: B ++ L) t → ∃ M : List ℕ, M.length ≤ L.length + 2 ∧ M.Nodup ∧
      (∀ x ∈ M, x ∉ B) ∧ t ∈ M ∧ Seq B M
  intro B w t L ht hw hL htL
  have hM : Seq B (w :: (L ++ [t])) := by
    rw [seq_cons]
    refine ⟨hw, seq_snoc (seq_mono ?_ hL) (one_mono ?_ htL)⟩
    · intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      tauto
    · intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      tauto
  refine ⟨keep B (w :: (L ++ [t])), ?_, keep_nodup _ _, fun x hx => keep_out _ _ x hx,
    keep_mem _ _ t (by simp) ht, keep_seq _ _ hM⟩
  have := keep_len (w :: (L ++ [t])) B
  simp only [List.length_cons, List.length_append] at this
  omega

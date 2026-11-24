import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328

def Step (L : List ℕ) (v : ℕ) : Prop := ∃ a ∈ L, ∃ b ∈ L, v = a &&& b ∨ v = a ||| b

def Prog (B P : List ℕ) : Prop := ∀ i : Fin P.length, Step (B ++ P.take i) (P.get i)

def SeqP : List ℕ → List ℕ → Prop
  | _, [] => True
  | B, e :: L => Step B e ∧ SeqP (B ++ [e]) L

theorem step_mono {L L' : List ℕ} {v : ℕ} (h : ∀ y ∈ L, y ∈ L') : Step L v → Step L' v := by
  rintro ⟨a, ha, b, hb, hv⟩
  exact ⟨a, h a ha, b, h b hb, hv⟩

theorem seq_mono : ∀ (L B B' : List ℕ), (∀ y ∈ B, y ∈ B') → SeqP B L → SeqP B' L
  | [], _, _, _, _ => trivial
  | e :: L, B, B', h, ⟨h1, h2⟩ => by
    refine ⟨step_mono h h1, seq_mono L (B ++ [e]) (B' ++ [e]) ?_ h2⟩
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact List.mem_append_left _ (h y hy)
    · exact List.mem_append_right _ hy

theorem seq_snoc : ∀ (l B : List ℕ) (e : ℕ), SeqP B (l ++ [e]) ↔ SeqP B l ∧ Step (B ++ l) e
  | [], B, e => by simp [SeqP]
  | x :: l, B, e => by
    show (Step B x ∧ SeqP (B ++ [x]) (l ++ [e])) ↔ (Step B x ∧ SeqP (B ++ [x]) l) ∧ Step (B ++ x :: l) e
    rw [seq_snoc l (B ++ [x]) e]
    simp only [List.append_assoc, List.singleton_append]
    tauto

theorem prog_iff : ∀ (P B : List ℕ), Prog B P ↔ SeqP B P
  | [], B => by
    simp only [SeqP, iff_true]
    intro i
    exact absurd i.isLt (by simp)
  | e :: P, B => by
    show Prog B (e :: P) ↔ Step B e ∧ SeqP (B ++ [e]) P
    rw [← prog_iff P (B ++ [e])]
    constructor
    · intro h
      refine ⟨by simpa using h ⟨0, by simp⟩, fun i => ?_⟩
      have := h ⟨i.val + 1, by simp⟩
      simpa [List.take_succ_cons, List.append_assoc] using this
    · rintro ⟨h0, h1⟩ i
      rcases i with ⟨_ | k, hk⟩
      · simpa using h0
      · have := h1 ⟨k, by simpa using hk⟩
        simpa [List.take_succ_cons, List.append_assoc] using this

theorem greedy (base : List ℕ) : ∀ (L acc : List ℕ), SeqP base acc → acc.Nodup →
    (∀ e ∈ acc, e ∉ base) → SeqP (base ++ acc) L →
    ∃ acc', SeqP base acc' ∧ acc'.Nodup ∧ (∀ e ∈ acc', e ∉ base) ∧
      acc'.length ≤ acc.length + L.length ∧ (∀ y ∈ acc, y ∈ acc') ∧
      ∀ e ∈ L, e ∈ base ∨ e ∈ acc'
  | [], acc, h1, h2, h3, _ => ⟨acc, h1, h2, h3, by simp, fun _ hy => hy, by simp⟩
  | e :: L, acc, h1, h2, h3, ⟨he, hL⟩ => by
    by_cases hin : e ∈ base ∨ e ∈ acc
    · have hL' : SeqP (base ++ acc) L := seq_mono L _ _ (by
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hy
        · simp only [List.mem_singleton] at hy
          subst hy
          rcases hin with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ h) hL
      obtain ⟨acc', a1, a2, a3, a4, a5, a6⟩ := greedy base L acc h1 h2 h3 hL'
      refine ⟨acc', a1, a2, a3, by simp; omega, a5, ?_⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rcases hin with h | h
        · exact Or.inl h
        · exact Or.inr (a5 _ h)
      · exact a6 y hy
    · push_neg at hin
      have s2 : SeqP base (acc ++ [e]) := (seq_snoc acc base e).2 ⟨h1, he⟩
      have n2 : (acc ++ [e]).Nodup := by
        rw [List.nodup_append]
        refine ⟨h2, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        intro hab
        subst hab
        exact hin.2 ha
      have b2 : ∀ x ∈ acc ++ [e], x ∉ base := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact h3 x hx
        · simp only [List.mem_singleton] at hx
          subst hx
          exact hin.1
      have hL2 : SeqP (base ++ (acc ++ [e])) L := by
        rw [← List.append_assoc]
        exact hL
      obtain ⟨acc', a1, a2, a3, a4, a5, a6⟩ := greedy base L (acc ++ [e]) s2 n2 b2 hL2
      refine ⟨acc', a1, a2, a3, by simp at a4 ⊢; omega, fun y hy => a5 y (List.mem_append_left _ hy), ?_⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact Or.inr (a5 _ (List.mem_append_right _ (List.mem_singleton_self _)))
      · exact a6 y hy

end PEqualNP.Outside.L_meta_3328

open PEqualNP.Outside.L_meta_3328 in
theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  intro S Pg base a v prog hv ha hprog hlast
  have ha' : Step base a := ha
  have hprog' : SeqP (a :: base) prog := (prog_iff prog (a :: base)).1 hprog
  have hlast' : Step (a :: base ++ prog) v := hlast
  have hseq : SeqP (base ++ []) (a :: (prog ++ [v])) := by
    refine ⟨by simpa using ha', ?_⟩
    rw [seq_snoc]
    refine ⟨seq_mono prog _ _ ?_ hprog', step_mono ?_ hlast'⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · simp
      · simp [hy]
    · intro y hy
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hy
      simp only [List.append_nil, List.mem_append, List.mem_singleton]
      tauto
  obtain ⟨acc', a1, a2, a3, a4, _, a6⟩ := greedy base (a :: (prog ++ [v])) [] trivial
    List.nodup_nil (by simp) hseq
  refine ⟨acc', by simp at a4; omega, a2, a3, ?_, (prog_iff acc' base).2 a1⟩
  rcases a6 v (by simp) with h | h
  · exact absurd h hv
  · exact h

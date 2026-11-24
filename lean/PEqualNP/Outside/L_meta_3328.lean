import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328_aux

def D (S : List ℕ) (v : ℕ) : Prop := ∃ a ∈ S, ∃ b ∈ S, v = a &&& b ∨ v = a ||| b

def Prog : List ℕ → List ℕ → Prop
  | _, [] => True
  | base, y :: ys => D base y ∧ Prog (base ++ [y]) ys

def clean (S : List ℕ) : List ℕ → List ℕ → List ℕ
  | _, [] => []
  | seen, y :: ys => if y ∈ S ∨ y ∈ seen then clean S seen ys else y :: clean S (y :: seen) ys

theorem D_mono {S1 S2 : List ℕ} (h : ∀ z ∈ S1, z ∈ S2) {v : ℕ} (hv : D S1 v) : D S2 v := by
  obtain ⟨a, ha, b, hb, h'⟩ := hv
  exact ⟨a, h a ha, b, h b hb, h'⟩

theorem Prog_mono (L : List ℕ) : ∀ (base base' : List ℕ), (∀ z ∈ base, z ∈ base') → Prog base L → Prog base' L := by
  induction L with
  | nil => intro _ _ _ _; trivial
  | cons y ys ih =>
    intro base base' h hP
    simp only [Prog] at hP ⊢
    refine ⟨D_mono h hP.1, ih (base ++ [y]) (base' ++ [y]) ?_ hP.2⟩
    intro z hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
    rcases hz with hz | hz
    · exact Or.inl (h z hz)
    · exact Or.inr hz

theorem Prog_append (L1 : List ℕ) : ∀ (L2 base : List ℕ), Prog base (L1 ++ L2) ↔ Prog base L1 ∧ Prog (base ++ L1) L2 := by
  induction L1 with
  | nil => intro L2 base; simp [Prog]
  | cons y ys ih =>
    intro L2 base
    simp only [List.cons_append, Prog, ih, and_assoc, List.append_assoc, List.nil_append]

theorem prog_iff (L : List ℕ) : ∀ (base : List ℕ), Prog base L ↔ ∀ i (h : i < L.length), D (base ++ L.take i) L[i] := by
  induction L with
  | nil => intro base; simp [Prog]
  | cons y ys ih =>
    intro base
    simp only [Prog, ih]
    constructor
    · rintro ⟨hD, hP⟩ i hi
      cases i with
      | zero => simpa using hD
      | succ j =>
        have := hP j (by simpa using hi)
        simpa using this
    · intro h
      refine ⟨?_, ?_⟩
      · have := h 0 (by simp)
        simp only [List.take_zero, List.append_nil, List.getElem_cons_zero] at this
        exact this
      intro j hj
      have := h (j + 1) (by simpa using hj)
      simpa using this

theorem clean_prog (S : List ℕ) (L : List ℕ) : ∀ (seen base B : List ℕ), (∀ z ∈ base, z ∈ B) → (∀ z, z ∈ S ∨ z ∈ seen → z ∈ B) → Prog base L → Prog B (clean S seen L) := by
  induction L with
  | nil => intro _ _ _ _ _ _; simp [clean, Prog]
  | cons y ys ih =>
    intro seen base B hb hs hP
    simp only [Prog] at hP
    simp only [clean]
    split_ifs with hy
    · refine ih seen (base ++ [y]) B ?_ hs hP.2
      intro z hz
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with hz | hz
      · exact hb z hz
      · subst hz; exact hs _ hy
    · simp only [Prog]
      refine ⟨D_mono hb hP.1, ih (y :: seen) (base ++ [y]) (B ++ [y]) ?_ ?_ hP.2⟩
      · intro z hz
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        rcases hz with hz | hz
        · exact Or.inl (hb z hz)
        · exact Or.inr hz
      · intro z hz
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_cons] at hz ⊢
        rcases hz with hz | hz | hz
        · exact Or.inl (hs z (Or.inl hz))
        · exact Or.inr hz
        · exact Or.inl (hs z (Or.inr hz))

theorem clean_mem_imp (S : List ℕ) (L : List ℕ) : ∀ (seen : List ℕ) (x : ℕ), x ∈ clean S seen L → x ∉ S ∧ x ∉ seen := by
  induction L with
  | nil => intro _ _ h; simp [clean] at h
  | cons y ys ih =>
    intro seen x hx
    simp only [clean] at hx
    split_ifs at hx with hy
    · exact ih seen x hx
    · rcases List.mem_cons.1 hx with h | h
      · subst h; exact not_or.1 hy
      · have := ih (y :: seen) x h
        exact ⟨this.1, fun h' => this.2 (List.mem_cons_of_mem _ h')⟩

theorem clean_nodup (S : List ℕ) (L : List ℕ) : ∀ (seen : List ℕ), (clean S seen L).Nodup := by
  induction L with
  | nil => intro _; simp [clean]
  | cons y ys ih =>
    intro seen
    simp only [clean]
    split_ifs with hy
    · exact ih seen
    · refine List.nodup_cons.2 ⟨?_, ih (y :: seen)⟩
      intro h
      exact (clean_mem_imp S ys (y :: seen) y h).2 (List.mem_cons_self ..)

theorem clean_length (S : List ℕ) (L : List ℕ) : ∀ (seen : List ℕ), (clean S seen L).length ≤ L.length := by
  induction L with
  | nil => intro _; simp [clean]
  | cons y ys ih =>
    intro seen
    simp only [clean]
    split_ifs with hy
    · have := ih seen; simp; omega
    · have := ih (y :: seen); simp; omega

theorem clean_mem (S : List ℕ) (L : List ℕ) : ∀ (seen : List ℕ) (x : ℕ), x ∈ L → x ∉ S → x ∉ seen → x ∈ clean S seen L := by
  induction L with
  | nil => intro _ _ h; simp at h
  | cons y ys ih =>
    intro seen x hx hS hseen
    simp only [clean]
    split_ifs with hy
    · rcases List.mem_cons.1 hx with h | h
      · subst h; exact absurd hy (not_or.2 ⟨hS, hseen⟩)
      · exact ih seen x h hS hseen
    · by_cases hxy : x = y
      · subst hxy; exact List.mem_cons_self ..
      · rcases List.mem_cons.1 hx with h | h
        · exact absurd h hxy
        · refine List.mem_cons_of_mem _ (ih (y :: seen) x h hS ?_)
          simp only [List.mem_cons, not_or]
          exact ⟨hxy, hseen⟩

end PEqualNP.Outside.L_meta_3328_aux

open PEqualNP.Outside.L_meta_3328_aux

theorem PEqualNP.Outside.L_meta_3328 :
    have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  intro x1 x2 S a b T hb ha hT hbD
  have hP : Prog (a :: S) T := by
    rw [prog_iff]
    intro i hi
    exact hT ⟨i, hi⟩
  have hL : Prog S (a :: (T ++ [b])) := by
    simp only [Prog]
    refine ⟨ha, ?_⟩
    rw [Prog_append]
    refine ⟨Prog_mono T _ _ ?_ hP, ?_⟩
    · intro z hz
      simp only [List.mem_append, List.mem_cons, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
      tauto
    · simp only [Prog, and_true]
      refine D_mono ?_ hbD
      intro z hz
      simp only [List.mem_append, List.mem_cons, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
      tauto
  refine ⟨clean S [] (a :: (T ++ [b])), ?_, clean_nodup S _ [], ?_, ?_, ?_⟩
  · have := clean_length S (a :: (T ++ [b])) []
    simp at this
    omega
  · intro z hz
    exact (clean_mem_imp S _ [] z hz).1
  · exact clean_mem S _ [] b (by simp) hb (by simp)
  · have h2 := clean_prog S (a :: (T ++ [b])) [] S S (fun z hz => hz) (fun z hz => by simpa using hz) hL
    rw [prog_iff] at h2
    intro i
    exact h2 i.1 i.2

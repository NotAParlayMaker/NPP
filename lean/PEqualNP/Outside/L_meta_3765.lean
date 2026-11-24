import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3765

def run (m n : ℕ) (a b op : Fin n → ℕ)
    (ha : ∀ j, a j < m + j.val) (hb : ∀ j, b j < m + j.val)
    (s : Fin n → Bool) (i : ℕ) : Finset ℕ :=
  if h : i < m then {i}
  else if hi : i < m + n then
    let j : Fin n := ⟨i - m, by omega⟩
    have hja : a j < i := by
      have h' := ha j
      change a j < m + (i - m) at h'
      omega
    have hjb : b j < i := by
      have h' := hb j
      change b j < m + (i - m) at h'
      omega
    if op j = 0 then run m n a b op ha hb s (a j) ∪ run m n a b op ha hb s (b j)
    else if op j = 1 then
      if s j = true then run m n a b op ha hb s (a j) else run m n a b op ha hb s (b j)
    else ∅
  else ∅
termination_by i

lemma run_input (m n : ℕ) (a b op : Fin n → ℕ)
    (ha : ∀ j, a j < m + j.val) (hb : ∀ j, b j < m + j.val)
    (s : Fin n → Bool) {i : ℕ} (hi : i < m) : run m n a b op ha hb s i = {i} := by
  rw [run, dite_eq_left hi]

lemma run_gate (m n : ℕ) (a b op : Fin n → ℕ)
    (ha : ∀ j, a j < m + j.val) (hb : ∀ j, b j < m + j.val)
    (s : Fin n → Bool) (j : Fin n) :
    run m n a b op ha hb s (m + j.val) =
      if op j = 0 then run m n a b op ha hb s (a j) ∪ run m n a b op ha hb s (b j)
      else if op j = 1 then
        if s j = true then run m n a b op ha hb s (a j) else run m n a b op ha hb s (b j)
      else ∅ := by
  have hlo : ¬ m + j.val < m := by omega
  have hhi : m + j.val < m + n := Nat.add_lt_add_left j.isLt m
  rw [run, dite_eq_right hlo, dite_eq_left hhi]
  have he : (⟨m + j.val - m, by omega⟩ : Fin n) = j := Fin.ext (show m + j.val - m = j.val by omega)
  simp only [he]

end PEqualNP.Outside.L_meta_3765

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_3765 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set (Finset ℕ)), x3 < x1 + x2 → (∀ x6 < x1, x4 x6 = {{x6}}) → (∀ x7 < x2, ∃ x9 < x1 + x7, ∃ x10 < x1 + x7, x4 (x1 + x7) = Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x4 x9) (x4 x10) ∨ x4 (x1 + x7) = x4 x9 ∨ x4 (x1 + x7) = {∅} ∨ x4 (x1 + x7) = x4 x9 ∪ x4 x10) → ∃ (x8 : (Fin x2 → Bool) → ℕ → Finset ℕ), (∀ (x9 : Fin x2 → Bool), ∀ x10 < x1, x8 x9 x10 = {x10}) ∧ (∀ (x9 : Fin x2), ∃ x10 < x1 + ↑x9, ∃ x11 < x1 + ↑x9, (∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = x8 x12 x10 ∪ x8 x12 x11) ∨ (∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = if x12 x9 = Bool.true then x8 x12 x10 else x8 x12 x11) ∨ ∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = ∅) ∧ (∀ (x9 : Fin x2 → Bool), x8 x9 x3 ∈ x4 x3) ∧ ∀ x9 ∈ x4 x3, ∃ (x11 : Fin x2 → Bool), x8 x11 x3 ⊆ x9 := by
  classical
  intro m n k S hk hinputs hgates
  have hnormal : ∀ j : Fin n, ∃ a b op : ℕ,
      a < m + j.val ∧ b < m + j.val ∧ S (m + j.val) =
        if op = 0 then Set.image2 (fun (A B : Finset ℕ) => A ∪ B) (S a) (S b)
        else if op = 1 then S a ∪ S b else {∅} := by
    intro j
    obtain ⟨a, ha, b, hb, h⟩ := hgates j.val j.isLt
    rcases h with h | h | h | h
    · exact ⟨a, b, 0, ha, hb, by simpa using h⟩
    · exact ⟨a, a, 1, ha, ha, by simpa using h⟩
    · exact ⟨a, b, 2, ha, hb, by simpa using h⟩
    · exact ⟨a, b, 1, ha, hb, by simpa using h⟩
  choose a b op ha hb hS using hnormal
  let F := PEqualNP.Outside.L_meta_3765.run m n a b op ha hb
  have Finput (s : Fin n → Bool) {i : ℕ} (hi : i < m) : F s i = {i} :=
    PEqualNP.Outside.L_meta_3765.run_input m n a b op ha hb s hi
  have Fgate (s : Fin n → Bool) (j : Fin n) : F s (m + j.val) =
      if op j = 0 then F s (a j) ∪ F s (b j)
      else if op j = 1 then if s j = true then F s (a j) else F s (b j)
      else ∅ := PEqualNP.Outside.L_meta_3765.run_gate m n a b op ha hb s j
  have Fmem (s : Fin n → Bool) : ∀ i < m + n, F s i ∈ S i := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi
      by_cases hinput : i < m
      · rw [Finput s hinput, hinputs i hinput]
        exact Set.mem_singleton _
      · let j : Fin n := ⟨i - m, by omega⟩
        have hj : m + j.val = i := by change m + (i - m) = i; omega
        have ha' : a j < i := hj ▸ ha j
        have hb' : b j < i := hj ▸ hb j
        have hma := ih (a j) ha' (ha'.trans hi)
        have hmb := ih (b j) hb' (hb'.trans hi)
        rw [← hj, Fgate, hS]
        by_cases h0 : op j = 0
        · simp only [ite_eq_left h0]
          exact ⟨F s (a j), hma, F s (b j), hmb, rfl⟩
        · by_cases h1 : op j = 1
          · simp only [ite_eq_right h0, ite_eq_left h1]
            by_cases hs : s j = true
            · rw [ite_eq_left hs]
              exact Or.inl hma
            · rw [ite_eq_right hs]
              exact Or.inr hmb
          · simp only [ite_eq_right h0, ite_eq_right h1]
            exact Set.mem_singleton _
  let Good (T : Finset ℕ) (i : ℕ) : Prop := ∃ U ∈ S i, U ⊆ T
  let select (T : Finset ℕ) (j : Fin n) : Bool := decide (Good T (a j))
  have Fsub (T : Finset ℕ) : ∀ i < m + n, Good T i → F (select T) i ⊆ T := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi hgood
      by_cases hinput : i < m
      · obtain ⟨U, hU, hUT⟩ := hgood
        have he : U = {i} := by simpa only [hinputs i hinput, Set.mem_singleton_iff] using hU
        simpa only [Finput (select T) hinput, ← he] using hUT
      · let j : Fin n := ⟨i - m, by omega⟩
        have hj : m + j.val = i := by change m + (i - m) = i; omega
        have ha' : a j < i := hj ▸ ha j
        have hb' : b j < i := hj ▸ hb j
        have hsa := ih (a j) ha' (ha'.trans hi)
        have hsb := ih (b j) hb' (hb'.trans hi)
        obtain ⟨U, hU, hUT⟩ := hgood
        rw [← hj, hS] at hU
        rw [← hj, Fgate]
        by_cases h0 : op j = 0
        · simp only [ite_eq_left h0] at hU ⊢
          obtain ⟨A, hA, B, hB, hAB⟩ := hU
          subst U
          have hAT : A ⊆ T := fun _ hx => hUT (Finset.mem_union.mpr (Or.inl hx))
          have hBT : B ⊆ T := fun _ hx => hUT (Finset.mem_union.mpr (Or.inr hx))
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact hsa ⟨A, hA, hAT⟩ hx
          · exact hsb ⟨B, hB, hBT⟩ hx
        · by_cases h1 : op j = 1
          · simp only [ite_eq_right h0, ite_eq_left h1] at hU ⊢
            by_cases hleft : Good T (a j)
            · have hs : select T j = true := by simp [select, hleft]
              rw [ite_eq_left hs]
              exact hsa hleft
            · have hs : ¬ select T j = true := by simp [select, hleft]
              rw [ite_eq_right hs]
              rcases hU with hU | hU
              · exact False.elim (hleft ⟨U, hU, hUT⟩)
              · exact hsb ⟨U, hU, hUT⟩
          · simp only [ite_eq_right h0, ite_eq_right h1]
            exact Finset.empty_subset _
  refine ⟨F, fun s i hi => Finput s hi, ?_, fun s => Fmem s k hk, ?_⟩
  · intro j
    refine ⟨a j, ha j, b j, hb j, ?_⟩
    by_cases h0 : op j = 0
    · exact Or.inl (fun s => by rw [Fgate, ite_eq_left h0])
    · by_cases h1 : op j = 1
      · exact Or.inr (Or.inl (fun s => by rw [Fgate, ite_eq_right h0, ite_eq_left h1]))
      · exact Or.inr (Or.inr (fun s => by rw [Fgate, ite_eq_right h0, ite_eq_right h1]))
  · intro T hT
    exact ⟨select T, Fsub T k hk ⟨T, hT, fun _ hx => hx⟩⟩

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1520

/-- The line number `s` of Z13. -/
def Lf (s : Fin 13) : Finset (Fin 13) := {s, s + 1, s + 3, s + 9}

/-- The set of points where `x` is false. -/
def phi (x : Fin 13 → Bool) : Finset (Fin 13) := Finset.univ.filter fun v => x v = false

theorem mem_phi (x : Fin 13 → Bool) (v : Fin 13) : v ∈ phi x ↔ x v = false := by simp [phi]

theorem phi_inj (x y : Fin 13 → Bool) (h : phi x = phi y) : x = y := by
  funext v
  have := congrArg (fun F => v ∈ F) h
  simp only [mem_phi, eq_iff_iff] at this
  cases hx : x v <;> cases hy : y v <;> simp_all

theorem phi_surj (F : Finset (Fin 13)) : phi (fun v => decide (v ∉ F)) = F := by
  ext v; simp [mem_phi]

theorem line_iff (x : Fin 13 → Bool) :
    (∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ Lf s) ↔ ∃ s : Fin 13, phi x ⊆ Lf s := by
  constructor
  · rintro ⟨s, h⟩; exact ⟨s, fun v hv => h v ((mem_phi x v).1 hv)⟩
  · rintro ⟨s, h⟩; exact ⟨s, fun v hv => h ((mem_phi x v).2 hv)⟩

theorem pt_iff (x : Fin 13 → Bool) :
    (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ↔
      ∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), v ∉ phi x := by
  constructor
  · rintro ⟨v, hv, h⟩; exact ⟨v, hv, by rw [mem_phi, h]; simp⟩
  · rintro ⟨v, hv, h⟩; exact ⟨v, hv, by rw [mem_phi] at h; simpa using h⟩

theorem card_transport (Q : Finset (Fin 13) → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun x : Fin 13 → Bool => Q (phi x)).card
      = (Finset.univ.filter fun F : Finset (Fin 13) => Q F).card := by
  apply Finset.card_bij (fun x _ => phi x)
  · intro x hx
    simpa using hx
  · intro x _ y _ h; exact phi_inj x y h
  · intro F hF
    refine ⟨fun v => decide (v ∉ F), ?_, phi_surj F⟩
    rw [Finset.mem_filter] at hF ⊢
    exact ⟨Finset.mem_univ _, by rw [phi_surj]; exact hF.2⟩

set_option maxRecDepth 100000 in
theorem count_lines : (Finset.univ.filter (fun F : Finset (Fin 13) =>
    ∃ s : Fin 13, F ⊆ Lf s)).card = 157 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem count_all : (Finset.univ.filter (fun F : Finset (Fin 13) =>
    (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), v ∉ F) ∨ ∃ s : Fin 13, F ⊆ Lf s)).card = 7170 := by
  decide +kernel

theorem only_zero : ∀ s : Fin 13, 0 ∈ Lf s → 1 ∈ Lf s → 3 ∈ Lf s → s = 0 := by decide

theorem in_zero : ∀ v : Fin 13, v ∈ ({0, 1, 3} : Finset (Fin 13)) → v ∈ Lf 0 ∧ v ≠ 9 := by decide

theorem zero_cases : ∀ v : Fin 13, v ∈ Lf 0 → v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 9 := by decide

end PEqualNP.Outside.L_meta_1520

open PEqualNP.Outside.L_meta_1520 in
theorem PEqualNP.Outside.L_meta_1520 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) ↔
      ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)))) ∧
    (∀ x : Fin 13 → Bool, (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) → x ≠ (fun v : Fin 13 => decide (v ∉ L 0)) ∧ x ≠ (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9))) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s))).card = 7170 ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s)).card = 157 ∧
    (∀ x y : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) → (∀ v : Fin 13, x v = true → y v = true) → ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), y v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, y v = false → v ∈ L s)) := by
  classical
  intro L hL
  have hLf : L = Lf := by funext t; rw [hL t]; rfl
  subst hLf
  have up : ∀ x y : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨
      ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ Lf s) →
      (∀ v : Fin 13, x v = true → y v = true) →
      ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), y v = true) ∨
        ∃ s : Fin 13, ∀ v : Fin 13, y v = false → v ∈ Lf s) := by
    intro x y h hxy
    rcases h with ⟨v, hv, h⟩ | ⟨s, h⟩
    · exact Or.inl ⟨v, hv, hxy v h⟩
    · refine Or.inr ⟨s, fun v hv => h v ?_⟩
      by_contra hne
      have : x v = true := by simpa using hne
      rw [hxy v this] at hv
      exact absurd hv (by simp)
  have sep : ∀ x : Fin 13 → Bool, (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) →
      x ≠ (fun v : Fin 13 => decide (v ∉ Lf 0)) ∧
      x ≠ (fun v : Fin 13 => decide (v ∉ Lf 0 ∨ v = 9)) := by
    rintro x ⟨v, hv, h⟩
    obtain ⟨h0, h9⟩ := in_zero v hv
    constructor
    · intro he; rw [he] at h; simp [h0] at h
    · intro he; rw [he] at h; simp [h0, h9] at h
  refine ⟨?_, sep, ?_, ?_, up⟩
  · intro x
    constructor
    · rintro (h | ⟨s, h⟩)
      · exact Or.inl h
      · by_cases hA : ∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true
        · exact Or.inl hA
        · right
          push_neg at hA
          have f0 : x 0 = false := by simpa using hA 0 (by decide)
          have f1 : x 1 = false := by simpa using hA 1 (by decide)
          have f3 : x 3 = false := by simpa using hA 3 (by decide)
          have hs : s = 0 := only_zero s (h 0 f0) (h 1 f1) (h 3 f3)
          subst hs
          cases h9 : x 9
          · left
            funext v
            by_cases hv : v ∈ Lf 0
            · rcases zero_cases v hv with rfl | rfl | rfl | rfl <;> simp [hv, f0, f1, f3, h9]
            · have : x v = true := by
                by_contra hne
                exact hv (h v (by simpa using hne))
              simp [hv, this]
          · right
            funext v
            by_cases hv : v ∈ Lf 0
            · rcases zero_cases v hv with rfl | rfl | rfl | rfl
              · simpa [hv] using f0
              · simpa [hv] using f1
              · simpa [hv] using f3
              · simp [h9]
            · have : x v = true := by
                by_contra hne
                exact hv (h v (by simpa using hne))
              simp [hv, this]
    · rintro (h | h | h)
      · exact Or.inl h
      · refine Or.inr ⟨0, fun v hv => ?_⟩
        rw [h] at hv; simpa using hv
      · refine Or.inr ⟨0, fun v hv => ?_⟩
        rw [h] at hv
        have := of_decide_eq_false hv
        push_neg at this
        exact this.1
  · have e : (Finset.univ.filter (fun x : Fin 13 → Bool =>
        ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨
          ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ Lf s)))
        = Finset.univ.filter (fun x : Fin 13 → Bool =>
          (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), v ∉ phi x) ∨ ∃ s : Fin 13, phi x ⊆ Lf s) := by
      apply Finset.filter_congr
      intro x _
      rw [pt_iff, line_iff]
    rw [e, card_transport (fun F => (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), v ∉ F) ∨
      ∃ s : Fin 13, F ⊆ Lf s)]
    exact count_all
  · have e : (Finset.univ.filter (fun x : Fin 13 → Bool =>
        ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ Lf s))
        = Finset.univ.filter (fun x : Fin 13 → Bool => ∃ s : Fin 13, phi x ⊆ Lf s) := by
      apply Finset.filter_congr
      intro x _
      rw [line_iff]
    rw [e, card_transport (fun F => ∃ s : Fin 13, F ⊆ Lf s)]
    exact count_lines

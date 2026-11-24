import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1520

def e (n : ℕ) : Fin 13 → Bool := fun v => n.testBit v

def f4 (n : ℕ) : Bool :=
  (List.finRange 13).any (fun s : Fin 13 => (List.finRange 13).all
    (fun v : Fin 13 => n.testBit v || decide (v ∈ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13)))))

def f3 (n : ℕ) : Bool := n.testBit 0 || n.testBit 1 || n.testBit 3 || f4 n

theorem e_inj : Set.InjOn e (Finset.range 8192 : Finset ℕ) := by
  intro a ha b hb hab
  have ha' : a < 2 ^ 13 := by simpa using ha
  have hb' : b < 2 ^ 13 := by simpa using hb
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 13
  · exact congrFun hab ⟨i, hi⟩
  · have h13 : 2 ^ 13 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha' h13),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb' h13)]

theorem e_img : (Finset.range 8192).image e = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn e_inj]
  simp

theorem range_count (f : ℕ → Bool) (N : ℕ) :
    ((Finset.range N).filter (fun n => f n = true)).card = ((List.range N).filter f).length := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.filter_append]
    by_cases h : f N = true
    · simp [h, ih]
    · simp [h, ih]

theorem transport (p : (Fin 13 → Bool) → Prop) [DecidablePred p] (f : ℕ → Bool)
    (h : ∀ n, p (e n) ↔ f n = true) :
    (Finset.univ.filter p).card = ((List.range 8192).filter f).length := by
  have h1 : Finset.univ.filter p = ((Finset.range 8192).filter (fun n => f n = true)).image e := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      have hx' : x ∈ (Finset.range 8192).image e := by rw [e_img]; exact Finset.mem_univ x
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx'
      exact ⟨n, ⟨hn, (h n).1 hx⟩, rfl⟩
    · rintro ⟨n, ⟨_, hn⟩, rfl⟩
      exact (h n).2 hn
  rw [h1, Finset.card_image_of_injOn, range_count]
  intro a ha b hb hab
  exact e_inj (Finset.mem_coe.2 (Finset.mem_of_mem_filter a (Finset.mem_coe.1 ha)))
    (Finset.mem_coe.2 (Finset.mem_of_mem_filter b (Finset.mem_coe.1 hb))) hab

set_option maxRecDepth 100000 in
theorem cnt4 : ((List.range 8192).filter f4).length = 157 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cnt3 : ((List.range 8192).filter f3).length = 7170 := by decide +kernel

theorem h4 (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) (n : ℕ) :
    (∃ s : Fin 13, ∀ v : Fin 13, e n v = false → v ∈ L s) ↔ f4 n = true := by
  simp only [f4, e, hL, List.any_eq_true, List.all_eq_true, List.mem_finRange, true_and,
    Bool.or_eq_true, decide_eq_true_eq, forall_const]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, fun v => ?_⟩
    by_cases hv : n.testBit v = true
    · exact Or.inl hv
    · exact Or.inr (hs v (by simpa using hv))
  · rintro ⟨s, hs⟩
    refine ⟨s, fun v hv => ?_⟩
    rcases hs v with h | h
    · rw [hv] at h; exact absurd h (by simp)
    · exact h

theorem hP (n : ℕ) : (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), e n v = true) ↔
    (n.testBit 0 || n.testBit 1 || n.testBit 3) = true := by
  simp [e, or_assoc]

theorem only0 : ∀ s : Fin 13, (0 : Fin 13) ∈ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13)) →
    (1 : Fin 13) ∈ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13)) →
    (3 : Fin 13) ∈ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13)) → s = 0 := by decide

theorem tabA : ∀ v : Fin 13, decide (v ∉ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13))) =
    !(v = 0 || v = 1 || v = 3 || v = 9) := by decide

theorem tabB : ∀ v : Fin 13, decide (v ∉ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)) ∨ v = 9) =
    !(v = 0 || v = 1 || v = 3) := by decide

theorem c1 (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) (x : Fin 13 → Bool) : ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) ↔
      ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9))) := by
  constructor
  · rintro (hp | ⟨s, hs⟩)
    · exact Or.inl hp
    · by_cases h0 : x 0 = true
      · exact Or.inl ⟨0, by decide, h0⟩
      by_cases h1 : x 1 = true
      · exact Or.inl ⟨1, by decide, h1⟩
      by_cases h3 : x 3 = true
      · exact Or.inl ⟨3, by decide, h3⟩
      right
      simp only [Bool.not_eq_true] at h0 h1 h3
      have hs0 : s = 0 := only0 s (hL s ▸ hs 0 h0) (hL s ▸ hs 1 h1) (hL s ▸ hs 3 h3)
      subst hs0
      have hout : ∀ v : Fin 13, (!(v = 0 || v = 1 || v = 3 || v = 9)) = true → x v = true := by
        intro v hv
        by_contra hx
        have hm := hs v (by simpa using hx)
        rw [hL] at hm
        rw [← tabA v] at hv
        exact (of_decide_eq_true hv) hm
      by_cases h9 : x 9 = true
      · right
        funext v
        show x v = decide (v ∉ L 0 ∨ v = 9)
        rw [hL, tabB v]
        by_cases a0 : v = 0
        · subst a0; rw [h0]; rfl
        by_cases a1 : v = 1
        · subst a1; rw [h1]; rfl
        by_cases a3 : v = 3
        · subst a3; rw [h3]; rfl
        by_cases a9 : v = 9
        · subst a9; rw [h9]; rfl
        rw [hout v (by simp [a0, a1, a3, a9])]
        simp [a0, a1, a3]
      · left
        simp only [Bool.not_eq_true] at h9
        funext v
        show x v = decide (v ∉ L 0)
        rw [hL, tabA v]
        by_cases a0 : v = 0
        · subst a0; rw [h0]; rfl
        by_cases a1 : v = 1
        · subst a1; rw [h1]; rfl
        by_cases a3 : v = 3
        · subst a3; rw [h3]; rfl
        by_cases a9 : v = 9
        · subst a9; rw [h9]; rfl
        rw [hout v (by simp [a0, a1, a3, a9])]
        simp [a0, a1, a3, a9]
  · rintro (hp | hx | hx)
    · exact Or.inl hp
    · refine Or.inr ⟨0, fun v hv => ?_⟩
      subst hx
      exact not_not.1 (of_decide_eq_false hv)
    · refine Or.inr ⟨0, fun v hv => ?_⟩
      subst hx
      exact not_not.1 (fun h => (of_decide_eq_false hv) (Or.inl h))

theorem c2 (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) (x : Fin 13 → Bool) : (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) → x ≠ (fun v : Fin 13 => decide (v ∉ L 0)) ∧ x ≠ (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) := by
  rintro ⟨v, hv, hxv⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  constructor
  · rintro rfl
    have h := of_decide_eq_true hxv
    rw [hL] at h
    rcases hv with rfl | rfl | rfl <;> exact h (by decide)
  · rintro rfl
    have h := of_decide_eq_true hxv
    rw [hL] at h
    rcases hv with rfl | rfl | rfl <;> exact absurd h (by decide)

theorem c3 (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) : (Finset.univ.filter (fun x : Fin 13 → Bool => ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s))).card = 7170 := by
  rw [transport _ f3]
  · exact cnt3
  · intro n
    rw [hP, h4 L hL]
    simp [f3, or_assoc]

theorem c4 (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) : (Finset.univ.filter (fun x : Fin 13 → Bool => ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s)).card = 157 := by
  rw [transport _ f4]
  · exact cnt4
  · intro n
    exact h4 L hL n

theorem c5 (L : Fin 13 → Finset (Fin 13)) (x y : Fin 13 → Bool) : ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) → (∀ v : Fin 13, x v = true → y v = true) → ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), y v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, y v = false → v ∈ L s) := by
  rintro (⟨v, hv, hxv⟩ | ⟨s, hs⟩) hxy
  · exact Or.inl ⟨v, hv, hxy v hxv⟩
  · refine Or.inr ⟨s, fun v hv => hs v ?_⟩
    by_contra hx
    have := hxy v (by simpa using hx)
    rw [hv] at this
    exact absurd this (by simp)

end PEqualNP.Outside.L_meta_1520

theorem PEqualNP.Outside.L_meta_1520 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) ↔
      ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)))) ∧
    (∀ x : Fin 13 → Bool, (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) → x ≠ (fun v : Fin 13 => decide (v ∉ L 0)) ∧ x ≠ (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9))) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s))).card = 7170 ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s)).card = 157 ∧
    (∀ x y : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) → (∀ v : Fin 13, x v = true → y v = true) → ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), y v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, y v = false → v ∈ L s)) := by
  intro L hL
  exact ⟨PEqualNP.Outside.L_meta_1520.c1 L hL, PEqualNP.Outside.L_meta_1520.c2 L hL, PEqualNP.Outside.L_meta_1520.c3 L hL, PEqualNP.Outside.L_meta_1520.c4 L hL, PEqualNP.Outside.L_meta_1520.c5 L⟩

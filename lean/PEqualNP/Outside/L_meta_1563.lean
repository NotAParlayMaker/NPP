import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1563

def line (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

lemma mem_line0 : ∀ v : Fin 13, v ∈ line 0 ↔ (v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 9) := by
  decide +kernel

lemma upset (x y : Fin 13 → Bool)
    (hx : x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ line 0 → x v = true)
    (hxy : ∀ v : Fin 13, x v = true → y v = true) :
    y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ line 0 → y v = true := by
  rcases hx with h | h | h
  · exact Or.inl (hxy 0 h)
  · exact Or.inr (Or.inl (hxy 1 h))
  · exact Or.inr (Or.inr fun v hv => hxy v (h v hv))

lemma colines : ∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ line t)) 0 = true ∨
    (fun v : Fin 13 => decide (v ∉ line t)) 1 = true ∨
    ∀ v : Fin 13, v ∉ line 0 → (fun v : Fin 13 => decide (v ∉ line t)) v = true) := by
  decide +kernel

lemma card_not01 :
    (Finset.univ.filter (fun x : Fin 13 → Bool => ¬ (x 0 = true ∨ x 1 = true))).card = 2048 := by
  have h : Finset.univ.filter (fun x : Fin 13 → Bool => ¬ (x 0 = true ∨ x 1 = true)) =
      Fintype.piFinset (fun a : Fin 13 =>
        if a = 0 ∨ a = 1 then ({false} : Finset Bool) else Finset.univ) := by
    ext x
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨_, h⟩ a
      by_cases ha : a = 0 ∨ a = 1
      · rw [ite_eq_left ha, Finset.mem_singleton]
        rcases ha with rfl | rfl
        · cases hx : x 0
          · rfl
          · exact absurd (Or.inl hx) h
        · cases hx : x 1
          · rfl
          · exact absurd (Or.inr hx) h
      · rw [ite_eq_right ha]
        exact Finset.mem_univ _
    · intro h
      refine ⟨Finset.mem_univ _, ?_⟩
      have h0 := h 0
      have h1 := h 1
      rw [ite_eq_left (Or.inl rfl), Finset.mem_singleton] at h0
      rw [ite_eq_left (Or.inr rfl), Finset.mem_singleton] at h1
      rintro (h' | h')
      · rw [h0] at h'
        exact Bool.false_ne_true h'
      · rw [h1] at h'
        exact Bool.false_ne_true h'
  rw [h, Fintype.card_piFinset]
  decide +kernel

lemma card_all : Fintype.card (Fin 13 → Bool) = 8192 := by
  simp

lemma card_01 :
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 13 → Bool)))
    (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)
  rw [card_not01, Finset.card_univ, card_all] at h
  have h6 : (6144 : ℕ) + 2048 = 8192 := by norm_num
  exact Nat.add_right_cancel (h.trans h6.symm)

lemma eq_fun (x : Fin 13 → Bool) (b3 b9 : Bool) (h0 : x 0 = false) (h1 : x 1 = false)
    (h3 : x 3 = b3) (h9 : x 9 = b9) (h : ∀ v : Fin 13, v ∉ line 0 → x v = true) :
    x = fun v : Fin 13 => decide (v ∉ line 0 ∨ (v = 3 ∧ b3 = true) ∨ (v = 9 ∧ b9 = true)) := by
  funext v
  by_cases hv : v ∈ line 0
  · rcases (mem_line0 v).mp hv with rfl | rfl | rfl | rfl
    · rw [h0]
      cases b3 <;> cases b9 <;> decide +kernel
    · rw [h1]
      cases b3 <;> cases b9 <;> decide +kernel
    · rw [h3]
      cases b3 <;> cases b9 <;> decide +kernel
    · rw [h9]
      cases b3 <;> cases b9 <;> decide +kernel
  · rw [h v hv]
    exact (decide_eq_true (Or.inl hv)).symm

lemma fn_ff : (fun v : Fin 13 => decide (v ∉ line 0 ∨ (v = 3 ∧ false = true) ∨ (v = 9 ∧ false = true))) =
    (fun v : Fin 13 => decide (v ∉ line 0)) := by
  decide +kernel

lemma fn_tf : (fun v : Fin 13 => decide (v ∉ line 0 ∨ (v = 3 ∧ true = true) ∨ (v = 9 ∧ false = true))) =
    (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 3)) := by
  decide +kernel

lemma fn_ft : (fun v : Fin 13 => decide (v ∉ line 0 ∨ (v = 3 ∧ false = true) ∨ (v = 9 ∧ true = true))) =
    (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 9)) := by
  decide +kernel

lemma fn_tt : (fun v : Fin 13 => decide (v ∉ line 0 ∨ (v = 3 ∧ true = true) ∨ (v = 9 ∧ true = true))) =
    (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 3 ∨ v = 9)) := by
  decide +kernel

lemma char5 (x : Fin 13 → Bool) :
    (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ line 0 → x v = true) ↔
      (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ line 0)) ∨
        x = (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 3)) ∨
        x = (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 9)) ∨
        x = (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 3 ∨ v = 9))) := by
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · by_cases h0 : x 0 = true
      · exact Or.inl h0
      · by_cases h1 : x 1 = true
        · exact Or.inr (Or.inl h1)
        · have h0' : x 0 = false := Bool.eq_false_iff.mpr h0
          have h1' : x 1 = false := Bool.eq_false_iff.mpr h1
          refine Or.inr (Or.inr ?_)
          by_cases h3 : x 3 = true
          · by_cases h9 : x 9 = true
            · exact Or.inr (Or.inr (Or.inr ((eq_fun x true true h0' h1' h3 h9 h).trans fn_tt)))
            · exact Or.inr (Or.inl ((eq_fun x true false h0' h1' h3
                (Bool.eq_false_iff.mpr h9) h).trans fn_tf))
          · by_cases h9 : x 9 = true
            · exact Or.inr (Or.inr (Or.inl ((eq_fun x false true h0' h1'
                (Bool.eq_false_iff.mpr h3) h9 h).trans fn_ft)))
            · exact Or.inl ((eq_fun x false false h0' h1' (Bool.eq_false_iff.mpr h3)
                (Bool.eq_false_iff.mpr h9) h).trans fn_ff)
  · rintro (h | h | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst h
      exact Or.inr (Or.inr fun v hv => decide_eq_true hv)
    · subst h
      exact Or.inr (Or.inr fun v hv => decide_eq_true (Or.inl hv))
    · subst h
      exact Or.inr (Or.inr fun v hv => decide_eq_true (Or.inl hv))
    · subst h
      exact Or.inr (Or.inr fun v hv => decide_eq_true (Or.inl hv))

def four : Finset (Fin 13 → Bool) :=
  {(fun v : Fin 13 => decide (v ∉ line 0)), (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 3)),
    (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 9)),
    (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 3 ∨ v = 9))}

lemma mem_four (x : Fin 13 → Bool) : x ∈ four ↔
    (x = (fun v : Fin 13 => decide (v ∉ line 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 3)) ∨
      x = (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ line 0 ∨ v = 3 ∨ v = 9))) := by
  unfold four
  simp only [Finset.mem_insert, Finset.mem_singleton]

lemma card_four : four.card = 4 := by
  decide +kernel

lemma four_01 (x : Fin 13 → Bool) (hx : x ∈ four) : x 0 = false ∧ x 1 = false := by
  rcases (mem_four x).mp hx with h | h | h | h <;> subst h <;> decide +kernel

lemma card_F :
    (Finset.univ.filter (fun x : Fin 13 → Bool =>
      (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ line 0 → x v = true))).card = 6148 := by
  have h : Finset.univ.filter (fun x : Fin 13 → Bool =>
      (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ line 0 → x v = true)) =
      Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true) ∪ four := by
    ext x
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, mem_four]
    constructor
    · rintro ⟨_, h⟩
      rcases (char5 x).mp h with h | h | h
      · exact Or.inl ⟨Finset.mem_univ _, Or.inl h⟩
      · exact Or.inl ⟨Finset.mem_univ _, Or.inr h⟩
      · exact Or.inr h
    · rintro (⟨_, h | h⟩ | h)
      · exact ⟨Finset.mem_univ _, (char5 x).mpr (Or.inl h)⟩
      · exact ⟨Finset.mem_univ _, (char5 x).mpr (Or.inr (Or.inl h))⟩
      · exact ⟨Finset.mem_univ _, (char5 x).mpr (Or.inr (Or.inr h))⟩
  have hd : Disjoint (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true))
      four := by
    rw [Finset.disjoint_left]
    intro x hx hx4
    have h01 := four_01 x hx4
    rcases (Finset.mem_filter.mp hx).2 with h' | h'
    · rw [h01.1] at h'
      exact Bool.false_ne_true h'
    · rw [h01.2] at h'
      exact Bool.false_ne_true h'
  rw [h, Finset.card_union_of_disjoint hd, card_01, card_four]

end PEqualNP.Outside.L_meta_1563

theorem PEqualNP.Outside.L_meta_1563 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)))) := by
  intro L hL
  obtain rfl : L = PEqualNP.Outside.L_meta_1563.line := funext hL
  exact ⟨PEqualNP.Outside.L_meta_1563.upset, PEqualNP.Outside.L_meta_1563.card_F,
    PEqualNP.Outside.L_meta_1563.colines, PEqualNP.Outside.L_meta_1563.card_01,
    PEqualNP.Outside.L_meta_1563.char5⟩

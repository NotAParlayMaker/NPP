import Mathlib
import PEqualNP.Defs

namespace Meta344Parity

private def parity {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => xor (p x) (parity p xs)

private theorem parity_filter {α : Type} (p : α → Bool) (xs : List α) :
    parity p xs = true ↔ (xs.filter p).length % 2 = 1 := by
  induction xs with
  | nil => simp [parity]
  | cons x xs ih =>
    cases h : p x <;> cases h' : parity p xs <;>
      simp [parity, h, h'] at ih ⊢ <;> omega

private theorem parity_card {α : Type} [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (xs : List α) (hn : xs.Nodup) :
    parity (fun x => decide (p x)) xs = true ↔ (xs.toFinset.filter p).card % 2 = 1 := by
  rw [parity_filter]
  have he : (xs.filter (fun x => decide (p x))).toFinset = xs.toFinset.filter p := by
    ext x
    simp
  rw [← he, List.toFinset_card_of_nodup (hn.filter _)]

end Meta344Parity

namespace Meta344

private def full : List (Fin 15 × Fin 15) := [(0, 1), (0, 4), (0, 5), (0, 6), (1, 2), (1, 6), (1, 7), (2, 3), (2, 7), (2, 8), (3, 4), (3, 8), (3, 9), (4, 5), (4, 9), (5, 10), (5, 13), (6, 11), (6, 14), (7, 10), (7, 12), (8, 11), (8, 13), (9, 12), (9, 14), (10, 12), (10, 13), (11, 13), (11, 14), (12, 14)]
private def selected : List (Fin 15 × Fin 15) := [(0, 1), (0, 5), (0, 6), (1, 2), (1, 7), (2, 3), (2, 7), (2, 8), (3, 8), (3, 9), (4, 5), (4, 9), (5, 13), (6, 11), (6, 14), (7, 10), (7, 12), (8, 11), (8, 13), (9, 12), (9, 14), (10, 12), (10, 13), (11, 13), (11, 14), (12, 14)]

private def forbidden (a b x y : Bool) : Bool := !a && !b && x && y

private def violated (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool) : Bool :=
    forbidden b1 b2 b7 b7 ||
    (forbidden b1 b7 b2 b2 ||
    (forbidden b2 b7 b1 b1 ||
    (forbidden b10 b12 b7 b7 ||
    (forbidden b11 b13 b8 b8 ||
    (forbidden b9 b14 b12 b12 ||
    (forbidden b7 b12 b10 b10 ||
    (forbidden b2 b8 b3 b3 ||
    (forbidden b5 b10 b13 b13 ||
    (forbidden b0 b4 b5 b5 ||
    (forbidden b8 b13 b11 b11 ||
    (forbidden b2 b3 b8 b8 ||
    (forbidden b6 b11 b14 b14 ||
    (forbidden b6 b14 b11 b11 ||
    (forbidden b11 b14 b6 b6 ||
    (forbidden b9 b12 b14 b14 ||
    (forbidden b10 b13 b12 b8 ||
    (forbidden b12 b14 b9 b9 ||
    (forbidden b8 b11 b2 b6 ||
    (forbidden b4 b5 b9 b13 ||
    (forbidden b7 b10 b12 b12 ||
    (forbidden b0 b5 b1 b13 ||
    (forbidden b6 b11 b0 b13 ||
    (forbidden b3 b9 b2 b12 ||
    (forbidden b1 b7 b0 b10 ||
    (forbidden b0 b6 b5 b11 ||
    (forbidden b0 b1 b5 b2 ||
    (forbidden b4 b9 b5 b12 ||
    (forbidden b9 b14 b3 b6 ||
    (forbidden b2 b3 b1 b9 ||
    (forbidden b0 b4 b6 b9 ||
    (forbidden b8 b11 b13 b13 ||
    (forbidden b1 b6 b2 b11 ||
    (forbidden b5 b13 b0 b8 ||
    (forbidden b1 b6 b0 b0 ||
    (forbidden b0 b5 b6 b13 ||
    (forbidden b12 b14 b7 b6 ||
    (forbidden b8 b13 b2 b5 ||
    (forbidden b3 b8 b9 b11 ||
    (forbidden b9 b12 b3 b7 ||
    (forbidden b11 b13 b6 b5 ||
    (forbidden b0 b6 b1 b11 ||
    (forbidden b3 b9 b2 b4 ||
    (forbidden b5 b10 b0 b7 ||
    (forbidden b1 b2 b0 b3 ||
    (forbidden b2 b7 b3 b10 ||
    (forbidden b3 b4 b9 b9 ||
    (forbidden b10 b12 b13 b9 ||
    (forbidden b11 b13 b6 b10 ||
    (forbidden b0 b1 b6 b2 ||
    (forbidden b0 b4 b1 b9 ||
    (forbidden b3 b4 b2 b5 ||
    (forbidden b5 b10 b4 b7 ||
    (forbidden b5 b13 b4 b8 ||
    (forbidden b8 b13 b2 b10 ||
    (forbidden b9 b12 b4 b7 ||
    (forbidden b9 b14 b4 b6))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def parityBits (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool) : Bool :=
    xor (b0 || b1) (xor (b0 || b5) (xor (b0 || b6) (xor (b1 || b2) (xor (b1 || b7) (xor (b2 || b3) (xor (b2 || b7) (xor (b2 || b8) (xor (b3 || b8) (xor (b3 || b9) (xor (b4 || b5) (xor (b4 || b9) (xor (b5 || b13) (xor (b6 || b11) (xor (b6 || b14) (xor (b7 || b10) (xor (b7 || b12) (xor (b8 || b11) (xor (b8 || b13) (xor (b9 || b12) (xor (b9 || b14) (xor (b10 || b12) (xor (b10 || b13) (xor (b11 || b13) (xor (b11 || b14) (xor (b12 || b14) (false))))))))))))))))))))))))))

-- A disjoint adjacent boundary pair is forced by each listed configuration.
-- A truth table on the fifteen membership bits checks that these cover odd parity.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cover : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool,
    (violated b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 || !parityBits b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14) = true := by
  decide +kernel

private abbrev Adj (G : List (Fin 15 × Fin 15)) (a b : Fin 15) :=
    (a,b) ∈ G.toFinset ∨ (b,a) ∈ G.toFinset

end Meta344

theorem PEqualNP.Outside.L_meta_344 : ∀ E : List (Fin 15 × Fin 15), E = [(0, 1), (0, 4), (0, 5), (0, 6), (1, 2), (1, 6), (1, 7), (2, 3), (2, 7), (2, 8), (3, 4), (3, 8), (3, 9), (4, 5), (4, 9), (5, 10), (5, 13), (6, 11), (6, 14), (7, 10), (7, 12), (8, 11), (8, 13), (9, 12), (9, 14), (10, 12), (10, 13), (11, 13), (11, 14), (12, 14)] → ∃ S : Finset (Fin 15 × Fin 15), (∀ e ∈ S, e ∈ E) ∧ S.Nonempty ∧ ¬ ∃ C : Finset (Fin 15), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 15, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  intro G hG
  change G = Meta344.full at hG
  subst G
  refine ⟨Meta344.selected.toFinset, ?_, ?_, ?_⟩
  · have hs : Meta344.selected.toFinset ⊆ Meta344.full.toFinset := by decide
    exact fun e he => List.mem_toFinset.mp (hs he)
  · decide
  rintro ⟨C, _, hb, hp⟩
  let f (i : Fin 15) := decide (i ∈ C)
  have hf (a b x y : Fin 15) (hg : Meta344.Adj Meta344.selected x a ∧
      Meta344.Adj Meta344.selected y b ∧ Meta344.Adj Meta344.full a b) :
      Meta344.forbidden (f a) (f b) (f x) (f y) = false := by
    by_cases ha : a ∈ C
    · simp [Meta344.forbidden, f, ha]
    by_cases hbb : b ∈ C
    · simp [Meta344.forbidden, f, hbb]
    by_cases hx : x ∈ C
    · by_cases hy : y ∈ C
      · exact False.elim (hb a b ha hbb ⟨x,hx,hg.1⟩ ⟨y,hy,hg.2.1⟩ (by simpa [Meta344.Adj] using hg.2.2))
      · simp [Meta344.forbidden, f, hy]
    · simp [Meta344.forbidden, f, hx]
  have hv : Meta344.violated (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) (f 11) (f 12) (f 13) (f 14) = false := by
    unfold Meta344.violated
    have q0 := hf 1 2 7 7 (by decide)
    have q1 := hf 1 7 2 2 (by decide)
    have q2 := hf 2 7 1 1 (by decide)
    have q3 := hf 10 12 7 7 (by decide)
    have q4 := hf 11 13 8 8 (by decide)
    have q5 := hf 9 14 12 12 (by decide)
    have q6 := hf 7 12 10 10 (by decide)
    have q7 := hf 2 8 3 3 (by decide)
    have q8 := hf 5 10 13 13 (by decide)
    have q9 := hf 0 4 5 5 (by decide)
    have q10 := hf 8 13 11 11 (by decide)
    have q11 := hf 2 3 8 8 (by decide)
    have q12 := hf 6 11 14 14 (by decide)
    have q13 := hf 6 14 11 11 (by decide)
    have q14 := hf 11 14 6 6 (by decide)
    have q15 := hf 9 12 14 14 (by decide)
    have q16 := hf 10 13 12 8 (by decide)
    have q17 := hf 12 14 9 9 (by decide)
    have q18 := hf 8 11 2 6 (by decide)
    have q19 := hf 4 5 9 13 (by decide)
    have q20 := hf 7 10 12 12 (by decide)
    have q21 := hf 0 5 1 13 (by decide)
    have q22 := hf 6 11 0 13 (by decide)
    have q23 := hf 3 9 2 12 (by decide)
    have q24 := hf 1 7 0 10 (by decide)
    have q25 := hf 0 6 5 11 (by decide)
    have q26 := hf 0 1 5 2 (by decide)
    have q27 := hf 4 9 5 12 (by decide)
    have q28 := hf 9 14 3 6 (by decide)
    have q29 := hf 2 3 1 9 (by decide)
    have q30 := hf 0 4 6 9 (by decide)
    have q31 := hf 8 11 13 13 (by decide)
    have q32 := hf 1 6 2 11 (by decide)
    have q33 := hf 5 13 0 8 (by decide)
    have q34 := hf 1 6 0 0 (by decide)
    have q35 := hf 0 5 6 13 (by decide)
    have q36 := hf 12 14 7 6 (by decide)
    have q37 := hf 8 13 2 5 (by decide)
    have q38 := hf 3 8 9 11 (by decide)
    have q39 := hf 9 12 3 7 (by decide)
    have q40 := hf 11 13 6 5 (by decide)
    have q41 := hf 0 6 1 11 (by decide)
    have q42 := hf 3 9 2 4 (by decide)
    have q43 := hf 5 10 0 7 (by decide)
    have q44 := hf 1 2 0 3 (by decide)
    have q45 := hf 2 7 3 10 (by decide)
    have q46 := hf 3 4 9 9 (by decide)
    have q47 := hf 10 12 13 9 (by decide)
    have q48 := hf 11 13 6 10 (by decide)
    have q49 := hf 0 1 6 2 (by decide)
    have q50 := hf 0 4 1 9 (by decide)
    have q51 := hf 3 4 2 5 (by decide)
    have q52 := hf 5 10 4 7 (by decide)
    have q53 := hf 5 13 4 8 (by decide)
    have q54 := hf 8 13 2 10 (by decide)
    have q55 := hf 9 12 4 7 (by decide)
    have q56 := hf 9 14 4 6 (by decide)
    simp only [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, q34, q35, q36, q37, q38, q39, q40, q41, q42, q43, q44, q45, q46, q47, q48, q49, q50, q51, q52, q53, q54, q55, q56, Bool.false_or]
  have hp' := (Meta344Parity.parity_card (fun e : Fin 15 × Fin 15 => e.1 ∈ C ∨ e.2 ∈ C)
    Meta344.selected (by decide)).2 hp
  have he : Meta344.parityBits (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) (f 11) (f 12) (f 13) (f 14) = true := by
    simpa only [Meta344.selected, Meta344Parity.parity, Bool.decide_or, Meta344.parityBits, f] using hp'
  have hc := Meta344.cover (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) (f 11) (f 12) (f 13) (f 14)
  simp [hv, he] at hc

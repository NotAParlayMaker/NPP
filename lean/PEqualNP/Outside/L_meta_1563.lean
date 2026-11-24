import Mathlib.Data.Fintype.BigOperators
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1563

abbrev Point := Fin 13
abbrev Input := Point → Bool

def line (t : Point) : Finset Point := {t, t + 1, t + 3, t + 9}
def pairOn (x : Input) : Prop := x 0 = true ∨ x 1 = true
def outsideOn (x : Input) : Prop := ∀ v, v ∉ line 0 → x v = true

def extra (a b : Bool) : Input := fun v =>
  decide (v ∉ line 0 ∨ (v = 3 ∧ a = true) ∨ (v = 9 ∧ b = true))

theorem recover (x : Input) (hpair : ¬ pairOn x) (hout : outsideOn x) :
    x = extra (x 3) (x 9) := by
  have hz : x 0 = false := by simpa [pairOn] using (show x 0 ≠ true from fun h => hpair (Or.inl h))
  have ho : x 1 = false := by simpa using (show x 1 ≠ true from fun h => hpair (Or.inr h))
  funext v
  by_cases hv : v ∈ line 0
  · have choices : v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 9 := by simpa [line] using hv
    rcases choices with rfl | rfl | rfl | rfl <;> simp [extra, line, hz, ho]
  · simp [extra, hv, hout v hv]

def special : Finset Input := {extra false false, extra true false, extra false true, extra true true}

theorem description (x : Input) : (pairOn x ∨ outsideOn x) ↔ pairOn x ∨ x ∈ special := by
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hp : pairOn x
      · exact Or.inl hp
      · right
        have he := recover x hp h
        cases ha : x 3 <;> cases hb : x 9 <;> rw [ha, hb] at he <;> rw [he] <;> simp [special]
  · rintro (h | h)
    · exact Or.inl h
    · right
      simp only [special, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl <;> intro v hv <;> simp [extra, hv]

theorem pair_count : (Finset.univ.filter fun x : Input => x 0 = true ∨ x 1 = true).card = 6144 := by
  let choices (v : Point) : Finset Bool := if v = 0 ∨ v = 1 then {false} else Finset.univ
  have box : (Finset.univ.filter fun x : Input => ¬ (x 0 = true ∨ x 1 = true)) =
      Fintype.piFinset choices := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h v
      by_cases hv : v = 0 ∨ v = 1
      · rcases hv with rfl | rfl <;> simp_all [choices]
      · simp [choices, hv]
    · intro h
      have hz := h 0
      have ho := h 1
      simp [choices] at hz ho
      simp [hz, ho]
  have n := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Input)) (p := fun x : Input => x 0 = true ∨ x 1 = true)
  rw [box, Fintype.card_piFinset] at n
  have a : (∏ v : Point, (choices v).card) = 2048 := by decide
  have b : (Finset.univ : Finset Input).card = 8192 := by simp [Input, Point]
  omega

end PEqualNP.Outside.L_meta_1563

open PEqualNP.Outside.L_meta_1563 in
theorem PEqualNP.Outside.L_meta_1563 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)))) := by
  intro L hL
  have eqL : L = line := funext hL
  subst L
  refine ⟨?_, ?_, ?_, pair_count, ?_⟩
  · intro x y hx hxy
    rcases hx with h | h | h
    · exact Or.inl (hxy 0 h)
    · exact Or.inr (Or.inl (hxy 1 h))
    · exact Or.inr (Or.inr (fun v hv => hxy v (h v hv)))
  · let A := Finset.univ.filter fun x : Input => x 0 = true ∨ x 1 = true
    have eq : (Finset.univ.filter fun x : Input =>
        x 0 = true ∨ x 1 = true ∨ ∀ v, v ∉ line 0 → x v = true) = A ∪ special := by
      ext x
      simpa only [A, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        pairOn, outsideOn, or_assoc] using description x
    have disj : Disjoint A special := by
      rw [Finset.disjoint_left]
      intro x hx hs
      simp only [special, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> simp [A, extra, line] at hx
    rw [eq, Finset.card_union_of_disjoint disj, show A.card = 6144 from pair_count]
    have card : special.card = 4 := by decide
    rw [card]
  · decide
  · intro x
    have h00 : extra false false = fun v => decide (v ∉ line 0) := by
      funext v
      simp [extra]
    have h10 : extra true false = fun v => decide (v ∉ line 0 ∨ v = 3) := by
      funext v
      simp [extra]
    have h01 : extra false true = fun v => decide (v ∉ line 0 ∨ v = 9) := by
      funext v
      simp [extra]
    have h11 : extra true true = fun v => decide (v ∉ line 0 ∨ v = 3 ∨ v = 9) := by
      funext v
      simp [extra]
    simpa only [special, Finset.mem_insert, Finset.mem_singleton, pairOn, outsideOn,
      h00, h10, h01, h11, or_assoc] using description x

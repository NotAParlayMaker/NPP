import Mathlib.Data.Nat.Bitwise
import PEqualNP.Defs

private def pairedBits (xs : List Bool) : List Bool :=
  xs.flatMap (fun b => [true, b])

private theorem pairedBits_injective : Function.Injective pairedBits := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys <;> simp_all [pairedBits]
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => simp [pairedBits] at h
      | cons y ys =>
          change true :: x :: pairedBits xs = true :: y :: pairedBits ys at h
          obtain ⟨rfl, ht⟩ := List.cons.inj (List.cons.inj h).2
          exact congrArg (List.cons x) (ih ht)

theorem PEqualNP.Outside.L_meta_368 : ∀ l l' : PEqualNP.Search.Literal,
    (PEqualNP.Search.encodeLiteral l).tail.tail =
      (PEqualNP.Search.encodeLiteral l').tail.tail ↔ l.1 = l'.1 := by
  intro l l'
  change pairedBits l.1.bits ++ [false, true] = pairedBits l'.1.bits ++ [false, true] ↔
    l.1 = l'.1
  rw [List.append_cancel_right_eq]
  constructor
  · intro h
    have hb := pairedBits_injective h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, hb]
  · intro h
    rw [h]

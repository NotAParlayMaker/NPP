import Mathlib
import PEqualNP.Defs

lemma PEqualNP.Outside.L_meta_368_bits_inj : ∀ m n : ℕ, m.bits = n.bits → m = n := by
  intro m
  induction m using Nat.binaryRec' with
  | zero =>
    intro n h
    induction n using Nat.binaryRec' with
    | zero => rfl
    | bit b k hk _ =>
      rw [Nat.zero_bits, Nat.bits_append_bit _ _ hk] at h
      exact absurd h (List.cons_ne_nil _ _).symm
  | bit b k hk ih =>
    intro n h
    induction n using Nat.binaryRec' with
    | zero =>
      rw [Nat.zero_bits, Nat.bits_append_bit _ _ hk] at h
      exact absurd h (List.cons_ne_nil _ _)
    | bit b' k' hk' _ =>
      rw [Nat.bits_append_bit _ _ hk, Nat.bits_append_bit _ _ hk'] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      rw [h1, ih k' h2]

lemma PEqualNP.Outside.L_meta_368_enc_inj : ∀ bs cs : List Bool,
    bs.flatMap (fun d => [true, d]) ++ [false, true] =
      cs.flatMap (fun d => [true, d]) ++ [false, true] → bs = cs
  | [], [], _ => rfl
  | [], c :: cs, h => by simp at h
  | b :: bs, [], h => by simp at h
  | b :: bs, c :: cs, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
      true_and] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1, PEqualNP.Outside.L_meta_368_enc_inj bs cs (by simpa only [List.append_assoc] using h2)]

theorem PEqualNP.Outside.L_meta_368 : ∀ l l' : PEqualNP.Search.Literal, (PEqualNP.Search.encodeLiteral l).tail.tail = (PEqualNP.Search.encodeLiteral l').tail.tail ↔ l.1 = l'.1 := by
  intro l l'
  simp only [PEqualNP.Search.encodeLiteral, List.cons_append, List.nil_append, List.tail_cons]
  constructor
  · intro h
    exact PEqualNP.Outside.L_meta_368_bits_inj _ _
      (PEqualNP.Outside.L_meta_368_enc_inj _ _ h)
  · intro h
    rw [h]

import PEqualNP.Defs

-- Use the shorter bound up to seven gates. In both remaining cases the
-- first gate is supplied, leaving a search with seven to nine gates.
-- Equal input phases give AND or OR. Mixed phases give directed differences.
theorem PEqualNP.Outside.R_meta_4425_391
    (short :
      have x1 : List (BitVec (512 : ℕ)) := List.map (fun (x1 : ℕ) => BitVec.ofNat (512 : ℕ) (((2 : ℕ) ^ (128 : ℕ) - (1 : ℕ)) / ((2 : ℕ) ^ (2 : ℕ) ^ x1 + (1 : ℕ)) * (2 : ℕ) ^ (2 : ℕ) ^ x1)) (List.range (7 : ℕ)); have x2 : Bool → Bool → BitVec (512 : ℕ) → BitVec (512 : ℕ) → BitVec (512 : ℕ) := fun (x2 x3 : Bool) (x4 x5 : BitVec (512 : ℕ)) =>   have x6 : BitVec (512 : ℕ) := (if x2 = Bool.true then x4 else ~~~x4) &&& if x3 = Bool.true then x5 else ~~~x5;   if x6.getLsbD (0 : ℕ) = Bool.true then ~~~x6 else x6; ∀ (x3 : List (BitVec (512 : ℕ))),   x3.length ≤ (7 : ℕ) →     (∀ (x5 : Fin x3.length),         have x6 : List (BitVec (512 : ℕ)) := x1 ++ List.take (↑x5) x3;         ∃ x7 ∈ x6, ∃ x8 ∈ x6, ∃ (x9 : Bool) (x10 : Bool), x3.get x5 = x2 x9 x10 x7 x8) →       BitVec.ofNat (512 : ℕ) ((18446744060824649720 : ℕ) * (2 : ℕ) ^ (64 : ℕ) + (18441958779708426440 : ℕ)) ∉ x1 ++ x3)
    (samePhase :
      let input := (List.range 7).map fun i => BitVec.ofNat 512 ((2^128-1) / (2^(2^i)+1) * 2^(2^i))
      let gate := fun (p q : Bool) (a b : BitVec 512) =>
        let z := (if p = true then a else ~~~a) &&& (if q = true then b else ~~~b)
        if z.getLsbD 0 = true then ~~~z else z
      ∀ a ∈ input, ∀ b ∈ input, ∀ p : Bool,
        let seed := input ++ [gate p p a b]
        ∀ xs : List (BitVec 512), 7 ≤ xs.length → xs.length ≤ 9 →
          (∀ i : Fin xs.length, let old := seed ++ xs.take i.val
            ∃ u ∈ old, ∃ v ∈ old, ∃ d e, xs.get i = gate d e u v) →
          BitVec.ofNat 512 (18446744060824649720 * 2^64 + 18441958779708426440) ∉ seed ++ xs)
    (mixedPhase :
      let input := (List.range 7).map fun i => BitVec.ofNat 512 ((2^128-1) / (2^(2^i)+1) * 2^(2^i))
      let gate := fun (p q : Bool) (a b : BitVec 512) =>
        let z := (if p = true then a else ~~~a) &&& (if q = true then b else ~~~b)
        if z.getLsbD 0 = true then ~~~z else z
      ∀ a ∈ input, ∀ b ∈ input, ∀ p : Bool,
        let seed := input ++ [gate p (!p) a b]
        ∀ xs : List (BitVec 512), 7 ≤ xs.length → xs.length ≤ 9 →
          (∀ i : Fin xs.length, let old := seed ++ xs.take i.val
            ∃ u ∈ old, ∃ v ∈ old, ∃ d e, xs.get i = gate d e u v) →
          BitVec.ofNat 512 (18446744060824649720 * 2^64 + 18441958779708426440) ∉ seed ++ xs) :
  have x1 : List (BitVec (512 : ℕ)) := List.map (fun (x1 : ℕ) => BitVec.ofNat (512 : ℕ) (((2 : ℕ) ^ (128 : ℕ) - (1 : ℕ)) / ((2 : ℕ) ^ (2 : ℕ) ^ x1 + (1 : ℕ)) * (2 : ℕ) ^ (2 : ℕ) ^ x1)) (List.range (7 : ℕ)); have x2 : Bool → Bool → BitVec (512 : ℕ) → BitVec (512 : ℕ) → BitVec (512 : ℕ) := fun (x2 x3 : Bool) (x4 x5 : BitVec (512 : ℕ)) =>   have x6 : BitVec (512 : ℕ) := (if x2 = Bool.true then x4 else ~~~x4) &&& if x3 = Bool.true then x5 else ~~~x5;   if x6.getLsbD (0 : ℕ) = Bool.true then ~~~x6 else x6; ∀ (x3 : List (BitVec (512 : ℕ))),   x3.length ≤ (10 : ℕ) →     (∀ (x5 : Fin x3.length),         have x6 : List (BitVec (512 : ℕ)) := x1 ++ List.take (↑x5) x3;         ∃ x7 ∈ x6, ∃ x8 ∈ x6, ∃ (x9 : Bool) (x10 : Bool), x3.get x5 = x2 x9 x10 x7 x8) →       BitVec.ofNat (512 : ℕ) ((18446744060824649720 : ℕ) * (2 : ℕ) ^ (64 : ℕ) + (18441958779708426440 : ℕ)) ∉ x1 ++ x3 := by
  dsimp only
  intro xs budget legal
  by_cases small : xs.length ≤ 7
  · exact short xs small legal
  cases xs with
  | nil => simp at small
  | cons f rest =>
    let input := (List.range 7).map fun i => BitVec.ofNat 512 ((2^128-1) / (2^(2^i)+1) * 2^(2^i))
    let gate := fun (p q : Bool) (a b : BitVec 512) =>
      let z := (if p = true then a else ~~~a) &&& (if q = true then b else ~~~b)
      if z.getLsbD 0 = true then ~~~z else z
    let t := BitVec.ofNat 512 (18446744060824649720 * 2^64 + 18441958779708426440)
    let first : Fin (f :: rest).length := ⟨0, by simp⟩
    obtain ⟨a, ha, b, hb, p, q, hf⟩ := legal first
    change a ∈ input at ha
    change b ∈ input at hb
    change f = gate p q a b at hf
    have lower : 7 ≤ rest.length := by simp only [List.length_cons] at small; omega
    have upper : rest.length ≤ 9 := by simp only [List.length_cons] at budget; omega
    have tail : ∀ i : Fin rest.length, let old := (input ++ [f]) ++ rest.take i.val
        ∃ u ∈ old, ∃ v ∈ old, ∃ d e, rest.get i = gate d e u v := by
      intro i
      let index : Fin (f :: rest).length := ⟨i.val + 1, by simp only [List.length_cons]; omega⟩
      obtain ⟨u, hu, v, hv, d, e, h⟩ := legal index
      change u ∈ input ++ (f :: rest).take (i.val+1) at hu
      change v ∈ input ++ (f :: rest).take (i.val+1) at hv
      change rest.get i = gate d e u v at h
      simp only [List.take_succ_cons, List.append_assoc, List.singleton_append] at hu hv ⊢
      exact ⟨u, hu, v, hv, d, e, h⟩
    change t ∉ input ++ f :: rest
    rw [show input ++ f :: rest = (input ++ [f]) ++ rest by simp only [List.append_assoc, List.singleton_append]]
    by_cases sign : p = q
    · subst q
      have result := samePhase a ha b hb p rest lower upper
      rw [hf] at tail ⊢
      exact result tail
    · have opposite : q = !p := by
        revert sign
        cases p <;> cases q <;> decide
      subst q
      have result := mixedPhase a ha b hb p rest lower upper
      rw [hf] at tail ⊢
      exact result tail

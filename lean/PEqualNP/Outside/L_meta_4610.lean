import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4610

/-- The `x1` predicate of the statement: `gates` is a list of AND/OR gates over the
seed wires `seeds`. -/
def IsList (seeds gates : List ℕ) : Prop :=
  ∀ (x3 : Fin gates.length), ∃ x4 ∈ seeds ++ List.take (↑x3) gates,
    ∃ x5 ∈ seeds ++ List.take (↑x3) gates,
      gates.get x3 = x4 &&& x5 ∨ gates.get x3 = x4 ||| x5

/-- The `x2` predicate of the statement: bit-position-wise coverage of the target mask
`m5` by the row masks in `rows`, witnessed inside the allowed mask `m4`. -/
def Covers (rows : List ℕ) (m4 m5 : ℕ) : Prop :=
  ∀ (b : ℕ), ∃ (w : ℕ), m4.testBit w = true ∧ m5.testBit w = m5.testBit b ∧
    ∀ r ∈ rows, if m5.testBit b = true then r.testBit w = true → r.testBit b = true
      else r.testBit b = true → r.testBit w = true

/-- The witness family extracted from `Covers`: `wf b` is a bit allowed by `x4` whose
`x5`-value equals `x5.b`, and every row respects the per-bit implication. -/
abbrev Wf (x3 : List ℕ) (x4 x5 : ℕ) (wf : ℕ → ℕ) : Prop :=
  ∀ (b : ℕ), x4.testBit (wf b) = true ∧ x5.testBit (wf b) = x5.testBit b ∧
    ∀ r ∈ x3, if x5.testBit b = true then r.testBit (wf b) = true → r.testBit b = true
      else r.testBit b = true → r.testBit (wf b) = true

/-- The coverage implications carried from rows to computed wires: for bit `b` with
`x5.b`, the forward implication `m.wf_b → m.b`; for `¬x5.b`, the backward one. -/
def Sat (x5 : ℕ) (wf : ℕ → ℕ) (m : ℕ) : Prop := ∀ b,
  (x5.testBit b = true → m.testBit (wf b) = true → m.testBit b = true) ∧
  (x5.testBit b = false → m.testBit b = true → m.testBit (wf b) = true)

variable {x3 : List ℕ} {x4 x5 : ℕ} {wf : ℕ → ℕ}

lemma sat_row (hwf : Wf x3 x4 x5 wf) (r : ℕ) (hr : r ∈ x3) : Sat x5 wf r := by
  intro b
  obtain ⟨_, _, hrows⟩ := hwf b
  have h := hrows r hr
  by_cases hb : x5.testBit b
  · simp only [hb, ite_true] at h
    exact ⟨fun _ => h, fun hnb => by rw [hb] at hnb; exact Bool.noConfusion hnb⟩
  · have hbf : x5.testBit b = false := by simp at hb; exact hb
    simp only [hbf] at h
    refine ⟨fun hb5 => by rw [hb5] at hbf; exact Bool.noConfusion hbf, ?_⟩
    intro _; exact h

lemma sat_and {a b : ℕ} (ha : Sat x5 wf a) (hb : Sat x5 wf b) :
    Sat x5 wf (a &&& b) := by
  intro i
  obtain ⟨ha1, ha2⟩ := ha i
  obtain ⟨hb1, hb2⟩ := hb i
  constructor
  · intro h5 h
    rw [Nat.testBit_and] at h ⊢; simp only [Bool.and_eq_true] at h ⊢
    exact ⟨ha1 h5 h.1, hb1 h5 h.2⟩
  · intro h5 h
    rw [Nat.testBit_and] at h ⊢; simp only [Bool.and_eq_true] at h ⊢
    exact ⟨ha2 h5 h.1, hb2 h5 h.2⟩

lemma sat_or {a b : ℕ} (ha : Sat x5 wf a) (hb : Sat x5 wf b) :
    Sat x5 wf (a ||| b) := by
  intro i
  obtain ⟨ha1, ha2⟩ := ha i
  obtain ⟨hb1, hb2⟩ := hb i
  constructor
  · intro h5 h
    rw [Nat.testBit_or] at h ⊢; simp only [Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (ha1 h5 h)
    · exact Or.inr (hb1 h5 h)
  · intro h5 h
    rw [Nat.testBit_or] at h ⊢; simp only [Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (ha2 h5 h)
    · exact Or.inr (hb2 h5 h)

/-- A wire satisfying `Sat` whose restriction to `x4` equals `x5`'s IS `x5`. -/
lemma sat_eq (hwf : Wf x3 x4 x5 wf) {m : ℕ} (hSat : Sat x5 wf m)
    (heq : m &&& x4 = x5 &&& x4) : m = x5 := by
  apply Nat.eq_of_testBit_eq
  intro b
  obtain ⟨hf, hb⟩ := hSat b
  obtain ⟨hw4, hw5, _⟩ := hwf b
  by_cases h : x5.testBit b
  · -- b ∈ x5 ⇒ b ∈ m via the forward implication at witness wf b
    have hw : (x5 &&& x4).testBit (wf b) = true := by
      rw [Nat.testBit_and]; simp only [Bool.and_eq_true]
      exact ⟨by rw [hw5]; exact h, hw4⟩
    rw [← heq, Nat.testBit_and] at hw
    simp only [Bool.and_eq_true] at hw
    rw [hf h hw.1]
    exact h.symm
  · have hnb : x5.testBit b = false := by simp at h; exact h
    rw [hnb]
    by_contra hmb
    have hmbt : m.testBit b = true := by simp at hmb; exact hmb
    have hmwb := hb hnb hmbt
    have hw : (m &&& x4).testBit (wf b) = true := by
      rw [Nat.testBit_and]; simp only [Bool.and_eq_true]
      exact ⟨hmwb, hw4⟩
    rw [heq, Nat.testBit_and] at hw
    simp only [Bool.and_eq_true] at hw
    rw [hw5, hnb] at hw
    exact absurd hw.1 (by decide)

/-- `x8` of the statement, the row masks restricted to `x4`. -/
def rest (rows : List ℕ) (m4 : ℕ) : List ℕ := rows.map (· &&& m4)

/-- Restricting a mask to `x4` commutes with the gate operations. -/
lemma rest_and (a b : ℕ) : (a &&& b) &&& x4 = (a &&& x4) &&& (b &&& x4) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> cases x4.testBit i <;> rfl
lemma rest_or (a b : ℕ) : (a ||| b) &&& x4 = (a &&& x4) ||| (b &&& x4) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> cases x4.testBit i <;> rfl

/-- The lifting construction: every gate list over the restricted seeds lifts to one
over the full seeds, with `Sat` preserved. -/
theorem lift (hwf : Wf x3 x4 x5 wf) (x6 : List ℕ) (hg : IsList (rest x3 x4) x6) :
    ∃ (ys : List ℕ), ys.length = x6.length ∧ IsList x3 ys ∧
      ys.map (· &&& x4) = x6 ∧ ∀ m ∈ ys, Sat x5 wf m := by
  -- index induction on the prefix length
  have step : ∀ j ≤ x6.length, ∃ (ys : List ℕ), ys.length = j ∧ IsList x3 ys ∧
      ys.map (· &&& x4) = x6.take j ∧ ∀ m ∈ ys, Sat x5 wf m := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨[], rfl, fun i => absurd i.isLt (Nat.not_lt_zero _), by simp, by simp⟩
    | succ j ih =>
      intro hj
      have hj' : j ≤ x6.length := by omega
      obtain ⟨ys, hylen, hylist, hymap, hysat⟩ := ih hj'
      have hlt : j < x6.length := by omega
      obtain ⟨a, ha, b, hb, hop⟩ := hg ⟨j, hlt⟩
      -- the seeds for gate j : rest ++ x6.take j = (x3 ++ ys).map (· &&& x4)
      have hseeds : rest x3 x4 ++ x6.take j = (x3 ++ ys).map (· &&& x4) := by
        show x3.map (· &&& x4) ++ x6.take j = (x3 ++ ys).map (· &&& x4)
        rw [List.map_append, hymap]
      rw [hseeds, List.mem_map] at ha hb
      obtain ⟨A, hA, hAe⟩ := ha
      obtain ⟨B, hB, hBe⟩ := hb
      have hAs : Sat x5 wf A := by
        rcases List.mem_append.1 hA with h | h
        · exact sat_row hwf A h
        · exact hysat A h
      have hBs : Sat x5 wf B := by
        rcases List.mem_append.1 hB with h | h
        · exact sat_row hwf B h
        · exact hysat B h
      have htake : x6.take (j + 1) = x6.take j ++ [x6[j]] := by
        rw [List.take_append_getElem hlt]
      -- the lifted gate
      rcases hop with hAB | hAB
      · refine ⟨ys ++ [A &&& B], by simp [hylen], ?_, ?_, ?_⟩
        · intro i
          have hi2 := i.isLt
          simp only [List.length_append, List.length_singleton] at hi2
          by_cases hi : (i : ℕ) < ys.length
          · obtain ⟨a', ha', b', hb', hop'⟩ := hylist ⟨i, hi⟩
            have hget : (ys ++ [A &&& B]).get i = ys.get ⟨i, hi⟩ := by
              rw [List.get_eq_getElem, List.get_eq_getElem]
              exact List.getElem_append_left hi
            refine ⟨a', ?_, b', ?_, ?_⟩
            · rw [List.take_append_of_le_length (by omega : (i : ℕ) ≤ ys.length)]
              exact ha'
            · rw [List.take_append_of_le_length (by omega : (i : ℕ) ≤ ys.length)]
              exact hb'
            · rw [hget]; exact hop'
          · have hi' : (i : ℕ) = ys.length := by omega
            have hget : (ys ++ [A &&& B]).get i = A &&& B := by
              rw [List.get_eq_getElem]
              rw [List.getElem_append_right (by omega : ys.length ≤ (i : ℕ))]
              simp only [hi', Nat.sub_self]
              simp
            refine ⟨A, ?_, B, ?_, Or.inl hget⟩
            · rw [List.take_append_of_le_length (by omega : (i : ℕ) ≤ ys.length),
                hi', List.take_length]
              exact hA
            · rw [List.take_append_of_le_length (by omega : (i : ℕ) ≤ ys.length),
                hi', List.take_length]
              exact hB
        · rw [List.map_append, List.map_cons, List.map_nil, hymap]
          rw [rest_and, hAe, hBe, ← hAB, htake]
          rfl
        · intro m hm
          rcases List.mem_append.1 hm with h | h
          · exact hysat m h
          · rw [List.mem_singleton.1 h]
            exact sat_and hAs hBs
      · refine ⟨ys ++ [A ||| B], by simp [hylen], ?_, ?_, ?_⟩
        · intro i
          have hi2 := i.isLt
          simp only [List.length_append, List.length_singleton] at hi2
          by_cases hi : (i : ℕ) < ys.length
          · obtain ⟨a', ha', b', hb', hop'⟩ := hylist ⟨i, hi⟩
            have hget : (ys ++ [A ||| B]).get i = ys.get ⟨i, hi⟩ := by
              rw [List.get_eq_getElem, List.get_eq_getElem]
              exact List.getElem_append_left hi
            refine ⟨a', ?_, b', ?_, ?_⟩
            · rw [List.take_append_of_le_length (by omega : (i : ℕ) ≤ ys.length)]
              exact ha'
            · rw [List.take_append_of_le_length (by omega : (i : ℕ) ≤ ys.length)]
              exact hb'
            · rw [hget]; exact hop'
          · have hi' : (i : ℕ) = ys.length := by omega
            have hget : (ys ++ [A ||| B]).get i = A ||| B := by
              rw [List.get_eq_getElem]
              rw [List.getElem_append_right (by omega : ys.length ≤ (i : ℕ))]
              simp only [hi', Nat.sub_self]
              simp
            refine ⟨A, ?_, B, ?_, Or.inr hget⟩
            · rw [List.take_append_of_le_length (by omega : (i : ℕ) ≤ ys.length),
                hi', List.take_length]
              exact hA
            · rw [List.take_append_of_le_length (by omega : (i : ℕ) ≤ ys.length),
                hi', List.take_length]
              exact hB
        · rw [List.map_append, List.map_cons, List.map_nil, hymap]
          rw [rest_or, hAe, hBe, ← hAB, htake]
          rfl
        · intro m hm
          rcases List.mem_append.1 hm with h | h
          · exact hysat m h
          · rw [List.mem_singleton.1 h]
            exact sat_or hAs hBs
  obtain ⟨ys, hylen, hylist, hymap, hysat⟩ := step x6.length (le_refl _)
  rw [List.take_length] at hymap
  exact ⟨ys, hylen, hylist, hymap, hysat⟩

theorem PEqualNP.Outside.L_meta_4610 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 : ℕ) => ∀ (x5 : ℕ), ∃ (x6 : ℕ), x3.testBit x6 = Bool.true ∧ x4.testBit x6 = x4.testBit x5 ∧ ∀ x7 ∈ x2, if x4.testBit x5 = Bool.true then x7.testBit x6 = Bool.true → x7.testBit x5 = Bool.true else x7.testBit x5 = Bool.true → x7.testBit x6 = Bool.true; ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ),   x2 x3 x4 x5 →     have x8 : List ℕ := List.map (fun (x8 : ℕ) => x8 &&& x4) x3;     x1 x8 x6 → x5 &&& x4 ∈ x8 ++ x6 → ∃ (x11 : List ℕ), x11.length ≤ x6.length ∧ x1 x3 x11 ∧ x5 ∈ x3 ++ x11 := by
  intro x1' x2' x3' x4' x5' x6' hcov x8' hgl hmem
  have hx8 : x8' = rest x3' x4' := rfl
  have hcov' : Covers x3' x4' x5' := hcov
  choose wf hwf using hcov'
  have hgl' : IsList (rest x3' x4') x6' := hx8 ▸ hgl
  obtain ⟨ys, hylen, hylist, hymap, hysat⟩ := lift hwf x6' hgl'
  rcases List.mem_append.1 hmem with h | h
  · -- restricted target is a restricted row ⇒ x5 IS that row
    rw [hx8] at h
    obtain ⟨r, hr, hrE⟩ := List.mem_map.1 h
    have hEq : x5' = r := (sat_eq hwf (sat_row hwf r hr) hrE).symm
    exact ⟨ys, le_of_eq hylen, hylist, List.mem_append_left _ (hEq ▸ hr)⟩
  · -- restricted target is a computed wire ⇒ its lift is x5
    rw [← hymap] at h
    obtain ⟨m, hm, hmE⟩ := List.mem_map.1 h
    have hEq : m = x5' := sat_eq hwf (hysat m hm) hmE
    exact ⟨ys, le_of_eq hylen, hylist, List.mem_append_right _ (hEq ▸ hm)⟩

end PEqualNP.Outside.L_meta_4610

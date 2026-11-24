import PEqualNP.Defs

-- A list of semantic gate values can forget a repeated value: later gates
-- use membership among earlier values, so an earlier copy suffices.
theorem PEqualNP.Outside.L_meta_4612 :
  have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 x4 x5 : List ℕ), ∀ x6 ∉ x2, x1 x2 x3 → (∀ x9 ∈ x4, x9 ∈ x2 ++ x3) → x1 x4 x5 → x6 ∈ x4 ++ x5 → ∃ (x12 : List ℕ), x12.length ≤ x3.length + x5.length ∧ x12.Nodup ∧ (∀ x13 ∈ x12, x13 ∉ x2) ∧ x6 ∈ x12 ∧ x1 x2 x12 := by
  dsimp only
  intro base first inputs second target fresh hFirst hInputs hSecond hTarget
  let Step (available : List ℕ) (value : ℕ) : Prop :=
    ∃ a ∈ available, ∃ b ∈ available, value = a &&& b ∨ value = a ||| b
  let Valid (available gates : List ℕ) : Prop :=
    ∀ i : Fin gates.length, Step (available ++ gates.take i.val) (gates.get i)
  change Valid base first at hFirst
  change Valid inputs second at hSecond
  have weaken (old new gates : List ℕ) (contained : ∀ a ∈ old, a ∈ new)
      (valid : Valid old gates) : Valid new gates := by
    intro i
    obtain ⟨a, ha, b, hb, h⟩ := valid i
    have keep (v : ℕ) (hv : v ∈ old ++ gates.take i.val) : v ∈ new ++ gates.take i.val := by
      rw [List.mem_append] at hv ⊢
      exact hv.imp (contained v) id
    exact ⟨a, keep a ha, b, keep b hb, h⟩
  have consValid (available : List ℕ) (g : ℕ) (rest : List ℕ) :
      Valid available (g :: rest) ↔ Step available g ∧ Valid (available ++ [g]) rest := by
    constructor
    · intro valid
      refine ⟨?_, ?_⟩
      · simpa using valid (0 : Fin (g :: rest).length)
      · intro i
        simpa [List.append_assoc] using valid (i.succ : Fin (g :: rest).length)
    · rintro ⟨firstStep, restValid⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using firstStep
      · simpa [List.append_assoc] using restValid j
  have appendValid : ∀ (a left right : List ℕ), Valid a left → Valid (a ++ left) right →
      Valid a (left ++ right) := by
    intro a left
    induction left generalizing a with
    | nil =>
      intro right _ h
      simpa using h
    | cons g rest ih =>
      intro right leftValid rightValid
      obtain ⟨firstStep, restValid⟩ := (consValid a g rest).mp leftValid
      refine (consValid a g (rest ++ right)).mpr ⟨firstStep, ?_⟩
      exact ih (a ++ [g]) right restValid (by simpa [List.append_assoc] using rightValid)
  have prune : ∀ (a gates : List ℕ), Valid a gates → ∃ kept : List ℕ,
      kept.length ≤ gates.length ∧ kept.Nodup ∧ (∀ v ∈ kept, v ∉ a) ∧
      (∀ v ∈ a ++ gates, v ∈ a ++ kept) ∧ Valid a kept := by
    intro a gates
    induction gates generalizing a with
    | nil =>
      intro valid
      exact ⟨[], le_rfl, List.nodup_nil, by simp, fun _ hv => hv, valid⟩
    | cons g rest ih =>
      intro valid
      obtain ⟨firstStep, restValid⟩ := (consValid a g rest).mp valid
      by_cases existing : g ∈ a
      · have contained (v : ℕ) (hv : v ∈ a ++ [g]) : v ∈ a := by
          rw [List.mem_append, List.mem_singleton] at hv
          exact hv.elim id (fun h => h.symm ▸ existing)
        obtain ⟨kept, lengthKept, nodup, outside, covers, keptValid⟩ :=
          ih a (weaken (a ++ [g]) a rest contained restValid)
        refine ⟨kept, lengthKept.trans (Nat.le_succ _), nodup, outside, ?_, keptValid⟩
        intro v hv
        apply covers v
        rw [List.mem_append, List.mem_cons] at hv
        rw [List.mem_append]
        rcases hv with ha | eq | hr
        · exact Or.inl ha
        · exact Or.inl (eq.symm ▸ existing)
        · exact Or.inr hr
      · obtain ⟨kept, lengthKept, nodup, outside, covers, keptValid⟩ := ih (a ++ [g]) restValid
        have gNotKept : g ∉ kept := fun hg =>
          outside g hg (List.mem_append_right _ (List.mem_singleton_self g))
        refine ⟨g :: kept, Nat.succ_le_succ lengthKept, List.nodup_cons.mpr ⟨gNotKept, nodup⟩,
          ?_, ?_, (consValid a g kept).mpr ⟨firstStep, keptValid⟩⟩
        · intro v hv
          rcases List.mem_cons.mp hv with eq | ht
          · exact eq.symm ▸ existing
          · exact fun ha => outside v ht (List.mem_append_left _ ha)
        · intro v hv
          have h : v ∈ (a ++ [g]) ++ rest := by simpa [List.append_assoc] using hv
          simpa [List.append_assoc] using covers v h
  have combined := appendValid base first second hFirst (weaken inputs (base ++ first) second hInputs hSecond)
  obtain ⟨kept, lengthKept, nodup, outside, covers, valid⟩ := prune base (first ++ second) combined
  have computed : target ∈ base ++ (first ++ second) := by
    rcases List.mem_append.mp hTarget with hi | hs
    · simpa only [← List.append_assoc] using List.mem_append_left second (hInputs target hi)
    · exact List.mem_append_right base (List.mem_append_right first hs)
  have inKept : target ∈ kept := (List.mem_append.mp (covers target computed)).resolve_left fresh
  exact ⟨kept, by simpa using lengthKept, nodup, outside, inKept, valid⟩

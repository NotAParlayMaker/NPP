import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

/-- Copied from `L_meta_1528` (self-contained): length of the OR-closure fold. -/
lemma l2233_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

/-- Copied from `L_meta_1528` (self-contained): membership characterisation of OR closures. -/
lemma l2233_orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [l2233_orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

/-- Copied from `L_meta_1528` (self-contained): `OrReaches` unfolding at a gate wire. -/
lemma l2233_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := l2233_orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

/-- Copied from `L_meta_1490`: `gateAt` agrees with list indexing in range. -/
lemma l2233_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

/-- Copied from `L_meta_1490`: `gateAt` in range is a gate of the circuit. -/
lemma l2233_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [l2233_gateAt_eq hj]; exact List.getElem_mem hj

/-- Every gate in an OR closure is a gate of the circuit. -/
lemma l2233_mem_lt {n : ℕ} {C : Circuit} :
    ∀ k j, j ∈ (orSets n C).getD k [] → j < C.gates.length := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hj
    have hj' : j ∈ (C.gates.foldl (orStep n) []).getD k [] := hj
    have h := (l2233_orSets_char n C.gates j k).mp hj'
    obtain ⟨hk, hjk | ⟨hop, w, hw, h1, h2, h3⟩⟩ := h
    · omega
    · exact ih (w - n) (by omega) j h3

/-- Chain lemma (desk sketch for L-meta-2233): a gate `j ≠ k` in the OR closure of gate `k`
is read, through the lowest step of its OR-path, by an OR gate `h` that is itself in the
OR closure of `k`. Proved by strong induction on `k`, peeling the first OR step. -/
lemma l2233_chain {n : ℕ} {C : Circuit} :
    ∀ k j, OrReaches n C (n + k) j → j ≠ k →
      ∃ h, (gateAt C h).op = GateOp.or ∧ n + j ∈ (gateAt C h).inputs ∧
        OrReaches n C (n + k) h := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hr hne
    obtain ⟨hk, hjk | ⟨hop, i, hi, hlt, hri⟩⟩ := (l2233_orReaches_iff n C k j).mp hr
    · exact absurd hjk hne
    · have hni : n ≤ i := hri.1
      obtain ⟨m, rfl⟩ : ∃ m, i = n + m := ⟨i - n, by omega⟩
      have hm : m < k := by omega
      by_cases hmj : m = j
      · subst hmj
        exact ⟨k, hop, hi, (l2233_orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩⟩
      · obtain ⟨h, hop', hin', hrh⟩ := ih m hm j hri (Ne.symm hmj)
        exact ⟨h, hop', hin',
          (l2233_orReaches_iff n C k h).mpr ⟨hk, Or.inr ⟨hop, n + m, hi, hlt, hrh⟩⟩⟩

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hAO2 hF
  obtain ⟨-, -, hlen2⟩ := hAO2
  classical
  -- The finset of OR gates OR-reaching the output.
  set D : Finset ℕ := (Finset.range C.gates.length).filter
    fun i => (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i with hDdef
  have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = ↑D := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.mem_coe, hDdef, Finset.mem_filter, Finset.mem_range]
  rw [hset, Set.ncard_coe_finset]
  -- If the output wire is an input wire, no gate OR-reaches it, so `F` is empty.
  by_cases hlt : C.output < n
  · have hFe : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact absurd (hF j hj).2.2.1 (by omega)
    rw [hFe]; simp
  · push_neg at hlt
    set o := C.output - n with hodef
    have hout : C.output = n + o := by omega
    -- If the output gate index is out of range, again no gate OR-reaches it.
    by_cases holen : o < C.gates.length
    swap
    · have hFe : F = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        have hr := (hF j hj).2.2
        rw [hout] at hr
        have hmem : j ∈ (orSets n C).getD o [] := by
          have h2 := hr.2
          rwa [Nat.add_sub_cancel_left] at h2
        have h := (l2233_orSets_char n C.gates j o).mp hmem
        omega
      rw [hFe]; simp
    · -- Main case: the output is gate `o`.
      have hmem : ∀ x ∈ F ∪ D, OrReaches n C (n + o) x := by
        intro x hx
        have hr : OrReaches n C C.output x := by
          rcases Finset.mem_union.mp hx with hxF | hxD
          · exact (hF x hxF).2.2
          · exact (Finset.mem_filter.mp hxD).2.2
        rwa [hout] at hr
      -- Choice of a lowest-step OR gate for every `x ≠ o` in `F ∪ D`.
      -- (Membership is inside the existential so `choose` yields `φ : ℕ → ℕ`.)
      have hex : ∀ x, ∃ h, x ∈ (F ∪ D).erase o →
          (gateAt C h).op = GateOp.or ∧ n + x ∈ (gateAt C h).inputs ∧
            OrReaches n C (n + o) h := by
        intro x
        by_cases hx : x ∈ (F ∪ D).erase o
        · obtain ⟨h, hop, hin, hrh⟩ := l2233_chain o x
            (hmem x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
          exact ⟨h, fun _ => ⟨hop, hin, hrh⟩⟩
        · exact ⟨0, fun h => absurd h hx⟩
      choose φ hφ using hex
      -- Every chosen gate lies in `D`.
      have hφD : ∀ x ∈ (F ∪ D).erase o, φ x ∈ D := by
        intro x hx
        obtain ⟨hop, -, hrh⟩ := hφ x hx
        have hmem2 : φ x ∈ (orSets n C).getD o [] := by
          have h2 := hrh.2
          rwa [Nat.add_sub_cancel_left] at h2
        have hlt' : φ x < C.gates.length := l2233_mem_lt o (φ x) hmem2
        rw [hDdef, Finset.mem_filter, Finset.mem_range]
        refine ⟨hlt', hop, ?_⟩
        rw [← hout] at hrh
        exact hrh
      -- Each OR gate is hit by at most two `x`'s (its inputs have length 2).
      have hfiber : ∀ h ∈ D,
          (((F ∪ D).erase o).filter fun x => φ x = h).card ≤ 2 := by
        intro h hh
        have hhD : h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧
            OrReaches n C C.output h := by
          rw [hDdef] at hh
          obtain ⟨hrange, hop, hr⟩ := Finset.mem_filter.mp hh
          exact ⟨Finset.mem_range.mp hrange, hop, hr⟩
        have hlenh : (gateAt C h).inputs.length = 2 :=
          hlen2 (gateAt C h) (l2233_gateAt_mem hhD.1)
        have hinj : Set.InjOn (fun x => n + x)
            (((F ∪ D).erase o).filter fun x => φ x = h) := by
          intro a _ b _ hab
          exact Nat.add_left_cancel hab
        have hmap : ∀ x ∈ ((F ∪ D).erase o).filter (fun x => φ x = h),
            n + x ∈ (gateAt C h).inputs.toFinset := by
          intro x hx
          have hxφ : φ x = h := (Finset.mem_filter.mp hx).2
          have hxx : x ∈ (F ∪ D).erase o := (Finset.mem_filter.mp hx).1
          obtain ⟨-, hin, -⟩ := hφ x hxx
          rw [hxφ] at hin
          exact List.mem_toFinset.mpr hin
        calc (((F ∪ D).erase o).filter fun x => φ x = h).card
            ≤ (gateAt C h).inputs.toFinset.card :=
              Finset.card_le_card_of_injOn (fun x => n + x) hmap hinj
          _ ≤ (gateAt C h).inputs.length := List.toFinset_card_le _
          _ = 2 := hlenh
      -- Counting: `|X ∖ {o}| ≤ 2|D|` where `X = F ∪ D`.
      have hcount : ((F ∪ D).erase o).card ≤ 2 * D.card := by
        have h1 := Finset.card_le_mul_card_image ((F ∪ D).erase o) 2 (f := φ)
          (fun b hb => by
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
            exact hfiber (φ x) (hφD x hx))
        have himg : ((F ∪ D).erase o).image φ ⊆ D := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          exact hφD x hx
        have h2 := Finset.card_le_card himg
        omega
      have hdisj : Disjoint F D := by
        rw [Finset.disjoint_left]
        intro j hjF hjD
        have hopF := (hF j hjF).2.1
        have hopD : (gateAt C j).op = GateOp.or := by
          rw [hDdef] at hjD
          exact (Finset.mem_filter.mp hjD).2.1
        rw [hopF] at hopD
        exact GateOp.noConfusion hopD
      have hXcard : (F ∪ D).card = F.card + D.card :=
        Finset.card_union_of_disjoint hdisj
      have herase : (F ∪ D).card - 1 ≤ ((F ∪ D).erase o).card := by
        by_cases ho : o ∈ F ∪ D
        · have h := Finset.card_erase_add_one ho
          omega
        · rw [Finset.erase_eq_of_notMem ho]
          omega
      omega

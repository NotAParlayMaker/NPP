import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_251 :
    ∀ (n j a h : ℕ) (C C2 : Circuit),
      C.gates[j]? = some ⟨GateOp.or, [a, h]⟩ →
      ¬ (∃ (l : ℕ) (u : ℕ → ℕ), u 0 = C.output ∧ u l = n + j ∧
        ∀ i : ℕ, i < l → ∃ (m : ℕ) (g : Gate),
          u i = n + m ∧ C.gates[m]? = some g ∧ g.op = GateOp.or ∧
            u (i + 1) ∈ g.inputs ∧ u (i + 1) < n + m) →
      C2 = ⟨C.gates.set j ⟨GateOp.or, [a]⟩ ++ [⟨GateOp.or, [C.output, h]⟩], n + C.size⟩ →
      {m : ℕ | ∃ g : Gate, C.gates[m]? = some g ∧ g.op = GateOp.or ∧
        (∃ (l : ℕ) (u : ℕ → ℕ), u 0 = C.output ∧ u l = n + m ∧
          ∀ i : ℕ, i < l → ∃ (m : ℕ) (g : Gate),
            u i = n + m ∧ C.gates[m]? = some g ∧ g.op = GateOp.or ∧
              u (i + 1) ∈ g.inputs ∧ u (i + 1) < n + m)}.ncard + 1 ≤
      {m : ℕ | ∃ g : Gate, C2.gates[m]? = some g ∧ g.op = GateOp.or ∧
        (∃ (l : ℕ) (u : ℕ → ℕ), u 0 = C2.output ∧ u l = n + m ∧
          ∀ i : ℕ, i < l → ∃ (m : ℕ) (g : Gate),
            u i = n + m ∧ C2.gates[m]? = some g ∧ g.op = GateOp.or ∧
              u (i + 1) ∈ g.inputs ∧ u (i + 1) < n + m)}.ncard := by
  intro n j a h C C2 _ avoidGate hc
  let walk (D : Circuit) (target : ℕ) : Prop :=
    ∃ (l : ℕ) (u : ℕ → ℕ), u 0 = D.output ∧ u l = target ∧
      ∀ i : ℕ, i < l → ∃ (m : ℕ) (g : Gate),
        u i = n + m ∧ D.gates[m]? = some g ∧ g.op = GateOp.or ∧
          u (i + 1) ∈ g.inputs ∧ u (i + 1) < n + m
  let top (D : Circuit) : Set ℕ :=
    {m | ∃ g : Gate, D.gates[m]? = some g ∧ g.op = GateOp.or ∧ walk D (n + m)}
  change ¬ walk C (n + j) at avoidGate
  change (top C).ncard + 1 ≤ (top C2).ncard

  let size := C.gates.length
  let newGate : Gate := ⟨GateOp.or, [C.output, h]⟩
  let edited := C.gates.set j ⟨GateOp.or, [a]⟩
  have editedLength : edited.length = size := List.length_set
  have newGates : C2.gates = edited ++ [newGate] := congrArg Circuit.gates hc
  have newOutput : C2.output = n + size := congrArg Circuit.output hc
  have getNew : C2.gates[size]? = some newGate := by
    rw [newGates, List.getElem?_append_right (Nat.le_of_eq editedLength), editedLength]
    simp
  have getOld {i : ℕ} (hi : i < size) (hne : i ≠ j) :
      C2.gates[i]? = C.gates[i]? := by
    rw [newGates, List.getElem?_append_left (editedLength.symm ▸ hi)]
    exact List.getElem?_set_ne hne.symm

  have topFinite (D : Circuit) : (top D).Finite := by
    apply (Set.finite_lt_nat D.gates.length).subset
    intro i hi
    obtain ⟨g, hg, _, _⟩ := hi
    exact (List.getElem?_eq_some_iff.mp hg).choose

  have preserves : top C ⊆ top C2 := by
    intro m hm
    obtain ⟨g, hg, hor, l, u, hstart, hend, hsteps⟩ := hm
    have hmBound : m < size := (List.getElem?_eq_some_iff.mp hg).choose
    have avoids (t : ℕ) (ht : t ≤ l) : u t ≠ n + j := by
      intro he
      exact avoidGate ⟨t, u, hstart, he, fun i hi => hsteps i (Nat.lt_of_lt_of_le hi ht)⟩
    have hmj : m ≠ j := by
      intro he
      exact avoids l (Nat.le_refl l) (by simpa [he] using hend)
    have outputBound : C.output < n + size := by
      cases l with
      | zero =>
        rw [hstart.symm.trans hend]
        exact Nat.add_lt_add_left hmBound n
      | succ l =>
        obtain ⟨r, f, hr, hf, _, _, _⟩ := hsteps 0 (Nat.zero_lt_succ l)
        have hrBound : r < size := (List.getElem?_eq_some_iff.mp hf).choose
        rw [← hstart, hr]
        exact Nat.add_lt_add_left hrBound n
    refine ⟨g, (getOld hmBound hmj).trans hg, hor, l + 1,
      fun i => if i = 0 then n + size else u (i - 1), by simpa using newOutput.symm,
      ?_, ?_⟩
    · simpa using hend
    · intro i hi
      cases i with
      | zero =>
        refine ⟨size, newGate, by simp, getNew, rfl, ?_, ?_⟩
        · simp [newGate, hstart]
        · simpa [hstart] using outputBound
      | succ i =>
        have hil : i < l := by omega
        obtain ⟨r, f, hr, hf, ho, hmem, hlt⟩ := hsteps i hil
        have hrBound : r < size := (List.getElem?_eq_some_iff.mp hf).choose
        have hrj : r ≠ j := by
          intro he
          exact avoids i (Nat.le_of_lt hil) (by simpa [he] using hr)
        refine ⟨r, f, ?_, (getOld hrBound hrj).trans hf, ho, ?_, ?_⟩
        · simpa using hr
        · simpa using hmem
        · simpa using hlt

  have root : size ∈ top C2 := by
    refine ⟨newGate, getNew, rfl, 0, fun _ => n + size, newOutput.symm, rfl, ?_⟩
    intro i hi
    exact (Nat.not_lt_zero i hi).elim
  have fresh : size ∉ top C := by
    rintro ⟨g, hg, _, _⟩
    exact (Nat.lt_irrefl size) (List.getElem?_eq_some_iff.mp hg).choose
  rw [← Set.ncard_insert_of_notMem fresh (topFinite C)]
  exact Set.ncard_le_ncard (Set.insert_subset root preserves) (topFinite C2)

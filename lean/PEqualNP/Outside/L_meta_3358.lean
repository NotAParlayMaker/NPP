import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3358_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

def isBinary (g : Gate) : Bool := !isNot g

def pins (g : Gate) : List ℕ :=
  if isNot g then g.inputs.take 1 else g.inputs

def writeGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def needed (n : ℕ) (g : Gate) : Finset ℕ :=
  (pins g).toFinset.filter fun i => i < n

def pull (n : ℕ) (g : Gate) (T : Finset ℕ) : Finset ℕ :=
  if n ∈ T then T.erase n ∪ needed n g else T

def deps (n : ℕ) : List Gate → Finset ℕ → Finset ℕ
  | [], S => S.filter fun i => i < n
  | g :: gs, S => pull n g (deps (n + 1) gs S)

theorem bounded (n : ℕ) (gs : List Gate) (S : Finset ℕ) :
    ∀ i ∈ deps n gs S, i < n := by
  induction gs generalizing n with
  | nil => intro i hi; exact (Finset.mem_filter.mp hi).2
  | cons g gs ih =>
    intro i hi
    simp only [deps, pull] at hi
    split at hi
    · rcases Finset.mem_union.mp hi with old | input
      · obtain ⟨hne, htail⟩ := Finset.mem_erase.mp old
        have h := ih (n + 1) i htail
        omega
      · exact (Finset.mem_filter.mp input).2
    · rename_i missing
      have h := ih (n + 1) i hi
      have ne : i ≠ n := fun eq => missing (eq ▸ hi)
      omega

theorem cost (n : ℕ) (gs : List Gate) (S : Finset ℕ)
    (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (deps n gs S).card ≤ S.card + gs.countP isBinary := by
  induction gs generalizing n with
  | nil => exact Finset.card_le_card (Finset.filter_subset _ _)
  | cons g gs ih =>
    let T := deps (n + 1) gs S
    have bounds := ih (n + 1) (fun h hh => fanin h (List.mem_cons_of_mem _ hh))
    have gateBound := fanin g (by simp)
    have portBound : (needed n g).card ≤ (pins g).length :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (List.toFinset_card_le (pins g))
    change (pull n g T).card ≤ _
    by_cases hn : n ∈ T
    · have erase := Finset.card_erase_add_one hn
      have joined : (pull n g T).card ≤ (T.erase n).card + (needed n g).card := by
        simpa [pull, hn] using Finset.card_union_le (T.erase n) (needed n g)
      change T.card ≤ _ at bounds
      cases ng : isNot g with
      | false =>
        have hp : (needed n g).card ≤ 2 := portBound.trans (by simpa [pins, ng] using gateBound)
        have hb : isBinary g = true := by simp [isBinary, ng]
        rw [List.countP_cons_of_pos hb]
        omega
      | true =>
        have hp : (needed n g).card ≤ 1 := portBound.trans (by simp [pins, ng])
        have hb : ¬ isBinary g := by simp [isBinary, ng]
        rw [List.countP_cons_of_neg hb]
        omega
    · change T.card ≤ _ at bounds
      simp only [pull, ite_eq_right hn, List.countP_cons]
      split <;> omega

theorem agreeGate (g : Gate) (u v : List Bool)
    (same : ∀ i ∈ pins g, u.getD i false = v.getD i false) :
    g.op.eval (g.inputs.map fun i => u.getD i false) =
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  rcases g with ⟨op, ps⟩
  cases op with
  | not =>
    cases ps with
    | nil => rfl
    | cons i rest =>
      have h := same i (by simp [pins, isNot])
      exact congrArg Bool.not h
  | and | or | mod | maj =>
    congr 1
    apply List.map_congr_left
    intro i hi
    exact same i (by simpa [pins, isNot] using hi)

theorem sound (n : ℕ) (gs : List Gate) (S : Finset ℕ) (u v : List Bool)
    (hu : u.length = n) (hv : v.length = n)
    (same : ∀ i ∈ deps n gs S, u.getD i false = v.getD i false) :
    ∀ i ∈ S, (gs.foldl writeGate u).getD i false = (gs.foldl writeGate v).getD i false := by
  induction gs generalizing n u v with
  | nil =>
    intro i hi
    have hn : deps n [] S = S.filter (fun j => j < n) := rfl
    by_cases lt : i < n
    · exact same i (hn ▸ Finset.mem_filter.mpr ⟨hi, lt⟩)
    · simp [hu, hv, Nat.le_of_not_gt lt]
  | cons g gs ih =>
    let T := deps (n + 1) gs S
    simp only [List.foldl_cons]
    apply ih (n + 1) (writeGate u g) (writeGate v g)
    · simp [writeGate, hu]
    · simp [writeGate, hv]
    · intro i hi
      change i ∈ T at hi
      have lt : i < n + 1 := bounded _ _ _ i hi
      by_cases eq : i = n
      · subst i
        have evalSame := agreeGate g u v (by
          intro j hj
          by_cases hjn : j < n
          · have neededMem : j ∈ needed n g := Finset.mem_filter.mpr ⟨by simpa using hj, hjn⟩
            apply same j
            change j ∈ pull n g T
            simpa [pull, hi] using Finset.mem_union_right (T.erase n) neededMem
          · rw [List.getD_eq_default _ _ (by omega : u.length ≤ j),
                List.getD_eq_default _ _ (by omega : v.length ≤ j)])
        change (u ++ [_]).getD n false = (v ++ [_]).getD n false
        rw [List.getD_append_right _ _ _ _ (by omega : u.length ≤ n),
            List.getD_append_right _ _ _ _ (by omega : v.length ≤ n)]
        rw [hu, hv, Nat.sub_self]
        exact evalSame
      · have lt' : i < n := by omega
        have orig : i ∈ deps n (g :: gs) S := by
          change i ∈ pull n g T
          by_cases h : n ∈ T
          · simp [pull, h, Finset.mem_erase.mpr ⟨eq, hi⟩]
          · simp [pull, h, hi]
        simpa only [writeGate, List.getD_append _ _ _ _ (by omega : i < u.length),
          List.getD_append _ _ _ _ (by omega : i < v.length)] using same i orig

theorem countTwo (gs : List Gate) (i j : ℕ) (hij : i < j) (hj : j < gs.length)
    (hiNot : isNot (gs[i]'(by omega)) = true) (hjNot : isNot (gs[j]'hj) = true) :
    2 ≤ gs.countP isNot := by
  induction gs generalizing i j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => omega
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have hn' : isNot gs[j] = true := by simpa using hjNot
      cases i with
      | zero =>
        have head : isNot g = true := by simpa using hiNot
        have tail : 0 < gs.countP isNot := List.countP_pos_iff.mpr
          ⟨gs[j], List.getElem_mem hj', hn'⟩
        rw [List.countP_cons_of_pos head]
        omega
      | succ i =>
        have hlo : i < j := by omega
        have two := ih i j hlo hj' (by simpa using hiNot) hn'
        simp only [List.countP_cons]
        split <;> omega

end PEqualNP.Outside.L_meta_3358_aux


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3358_aux in
theorem PEqualNP.Outside.L_meta_3358 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (7 : ℕ) → ∀ (x4 x5 : Fin x1.gates.length), x4 < x5 → (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ x9 ⊆ Finset.range (17 : ℕ), x9.card ≤ (6 : ℕ) ∧ ∀ (x10 x11 : List Bool), x10.length = (17 : ℕ) → x11.length = (17 : ℕ) → (∀ x14 ∈ x9, x10.getD x14 Bool.false = x11.getD x14 Bool.false) → x1.eval x10 = x1.eval x11 := by
  intro C fan small i j before firstNot secondNot
  have hi : isNot C.gates[i.val] = true := by
    change isNot (C.gates.get i) = true
    simp only [isNot, firstNot]
  have hj : isNot C.gates[j.val] = true := by
    change isNot (C.gates.get j) = true
    simp only [isNot, secondNot]
  have saved := countTwo C.gates i.val j.val before j.isLt hi hj
  have counted := List.length_eq_countP_add_countP isNot (l := C.gates)
  have complementary : (fun g : Gate => decide (¬ isNot g)) = isBinary := by
    funext g
    unfold isBinary
    cases isNot g <;> rfl
  rw [complementary] at counted
  change C.gates.length ≤ 7 at small
  let S := deps 17 C.gates {C.output}
  refine ⟨S, ?_, ?_, ?_⟩
  · intro k hk
    exact Finset.mem_range.mpr (bounded _ _ _ k hk)
  · have cap := cost 17 C.gates {C.output} (fun g hg => (fan g hg).2)
    change S.card ≤ _ at cap
    rw [Finset.card_singleton] at cap
    omega
  · intro x y hx hy agreement
    exact sound 17 C.gates {C.output} x y hx hy agreement C.output (by simp)


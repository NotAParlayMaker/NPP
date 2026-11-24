import Mathlib.Data.List.Forall2
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Count the AND and OR gates by evaluating their operations on one true bit.
-- The first child follows by specializing the branch groups of L_meta_2165 to all ten vertices.
-- The adjacency masks are 50, 69, 138, 276, 521, 385, 770, 548, 104, 208.
-- Five rounds of removing twin classes and isolates do not finish, giving at least 10 - 1 + 6 gates of these two kinds.
-- Cut the last inverter and run its monotone suffix with each possible bit.
-- Where the two outputs differ, the input to the inverter must equal the complement of the target.
-- In the second child each edge from u to v is encoded as the number 10 * u + v.
theorem PEqualNP.Outside.R_meta_2592_15
    (binaryBound : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = (fun (x : Fin 10 → Bool) =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
    (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) →
      15 ≤ C.gates.countP (fun g => g.op.eval [true]))
    (separate :
      let f := (fun (x : Fin 10 → Bool) =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any (fun e =>
          x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))))
      ∀ P M : Circuit, FanInTwo P → Monotone2 M → P.size + M.size ≤ 18 →
      P.gates.countP (fun g => !(g.op.eval [true])) ≤ 3 →
      let value := fun (x : Fin 10 → Bool) (b : Bool) => M.eval (P.wires (List.ofFn x) ++ [b])
      (∀ x, value x false ≤ f x ∧ f x ≤ value x true) →
      ∃ x, value x false ≠ value x true ∧ P.eval (List.ofFn x) = f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (19 : ℕ) → (∃ x4 ∈ x1.gates, x4.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ¬∀ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) = (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C fan budget hasNot computes
  let f := fun (x : Fin 10 → Bool) =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
    (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  change ∀ x, C.eval (List.ofFn x) = f x at computes
  have binary := binaryBound C fan computes
  let hit := fun g : Gate => g.op.eval [true]
  have total : C.gates.countP hit + C.gates.countP (fun g => !(hit g)) = C.gates.length := by
    simpa using (List.length_eq_countP_add_countP (l := C.gates) hit).symm
  change 15 ≤ C.gates.countP hit at binary
  change C.gates.length ≤ 19 at budget
  have splitLast (gs : List Gate) (seen : ∃ g ∈ gs, g.op = .not) :
      ∃ (pre : List Gate) (g : Gate) (post : List Gate),
        gs = pre ++ g :: post ∧ g.op = .not ∧ ∀ h ∈ post, h.op ≠ .not := by
    induction gs using List.reverseRecOn with
    | nil => simp at seen
    | append_singleton gs last ih =>
      by_cases hn : last.op = .not
      · exact ⟨gs, last, [], rfl, hn, by simp⟩
      · obtain ⟨w, hw, hop⟩ := seen
        have inGs : w ∈ gs := by
          rcases List.mem_append.mp hw with h | h
          · exact h
          · simp only [List.mem_singleton] at h
            exact (hn (h ▸ hop)).elim
        obtain ⟨pre, g, post, split, op, clear⟩ := ih ⟨w, inGs, hop⟩
        refine ⟨pre, g, post ++ [last], by simp [split, List.append_assoc], op, ?_⟩
        intro h mem
        rcases List.mem_append.mp mem with hpre | hend
        · exact clear h hpre
        · simp only [List.mem_singleton] at hend
          simpa only [hend] using hn
  obtain ⟨pre, g, post, parts, op, clear⟩ := splitLast C.gates hasNot
  let P : Circuit := ⟨pre, g.inputs.headD (10 + pre.length)⟩
  let M : Circuit := ⟨post, C.output⟩
  have prefixOK : FanInTwo P := fun h hmem => fan h (by rw [parts]; exact List.mem_append_left _ hmem)
  have suffixOK : Monotone2 M := by
    intro h hmem
    have ok := fan h (by rw [parts]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hmem))
    obtain ⟨basis, arity⟩ := ok
    refine ⟨?_, arity⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at basis ⊢
    exact basis.elim Or.inl (fun alt => alt.elim Or.inr (fun hn => (clear h hmem hn).elim))
  have short : P.size + M.size ≤ 18 := by
    rw [parts, List.length_append, List.length_cons] at budget
    change pre.length + post.length ≤ 18
    omega
  have few : P.gates.countP (fun h => !(h.op.eval [true])) ≤ 3 := by
    have notch : hit g = false := by
      change g.op.eval [true] = false
      rw [op]
      rfl
    have partCount : C.gates.countP (fun h => !(hit h)) =
        pre.countP (fun h => !(hit h)) + (post.countP (fun h => !(hit h)) + 1) := by
      simp [parts, List.countP_append, notch]
    change pre.countP (fun h => !(hit h)) ≤ 3
    omega
  let step := fun (w : List Bool) (h : Gate) =>
    w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
  have width (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons h gs ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  let value := fun (x : Fin 10 → Bool) (b : Bool) => M.eval (P.wires (List.ofFn x) ++ [b])
  have actual (x : Fin 10 → Bool) : value x (!(P.eval (List.ofFn x))) = f x := by
    rw [← computes x]
    let w := P.wires (List.ofFn x)
    have len : w.length = 10 + pre.length := by
      change (pre.foldl step (List.ofFn x)).length = _
      simp [width]
    have inverted : g.op.eval (g.inputs.map fun i => w.getD i false) = !(P.eval (List.ofFn x)) := by
      change g.op.eval (g.inputs.map fun i => w.getD i false) = !(w.getD (g.inputs.headD _) false)
      rw [op]
      cases eqn : g.inputs with
      | nil =>
        change (!false) = !(w.getD (10 + pre.length) false)
        rw [List.getD_eq_default _ _ (by omega)]
      | cons i tail => rfl
    change (post.foldl step (w ++ [!(P.eval (List.ofFn x))])).getD C.output false =
      (C.gates.foldl step (List.ofFn x)).getD C.output false
    rw [parts, List.foldl_append, List.foldl_cons, ← inverted]
    rfl
  have lookup {a b : List Bool} (ordered : List.Forall₂ (· ≤ ·) a b) (i : ℕ) :
      a.getD i false ≤ b.getD i false := by
    induction ordered generalizing i with
    | nil => exact le_rfl
    | cons h _ ih => cases i with
      | zero => exact h
      | succ i => exact ih i
  have gateOrder (op' : GateOp) (basis : op' = .and ∨ op' = .or) (pins : List ℕ)
      {a b : List Bool} (ordered : List.Forall₂ (· ≤ ·) a b) :
      op'.eval (pins.map fun i => a.getD i false) ≤ op'.eval (pins.map fun i => b.getD i false) := by
    induction pins with
    | nil => exact le_rfl
    | cons i rest ih =>
      have head := lookup ordered i
      rcases basis with rfl | rfl
      · exact (by decide : ∀ p q r s : Bool, p ≤ q → r ≤ s → (p && r) ≤ (q && s)) _ _ _ _ head ih
      · exact (by decide : ∀ p q r s : Bool, p ≤ q → r ≤ s → (p || r) ≤ (q || s)) _ _ _ _ head ih
  have runOrder (gs : List Gate) (basis : ∀ h ∈ gs, h.op = .and ∨ h.op = .or)
      {a b : List Bool} (ordered : List.Forall₂ (· ≤ ·) a b) :
      List.Forall₂ (· ≤ ·) (gs.foldl step a) (gs.foldl step b) := by
    induction gs generalizing a b with
    | nil => exact ordered
    | cons h tail ih =>
      apply ih (fun t ht => basis t (List.mem_cons_of_mem _ ht))
      exact List.rel_append ordered (.cons (gateOrder _ (basis h List.mem_cons_self) _ ordered) .nil)
  have mono (x : Fin 10 → Bool) : value x false ≤ value x true := by
    have basis (h : Gate) (mem : h ∈ post) : h.op = .and ∨ h.op = .or := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (suffixOK h mem).1
    exact lookup (runOrder post basis
      (List.rel_append (List.forall₂_refl _) (.cons (by decide : false ≤ true) .nil))) M.output
  have sandwich (x : Fin 10 → Bool) : value x false ≤ f x ∧ f x ≤ value x true := by
    have eqn := actual x
    cases bit : P.eval (List.ofFn x) <;> simp only [bit, Bool.not_false, Bool.not_true] at eqn
    · rw [← eqn]; exact ⟨mono x, le_rfl⟩
    · rw [← eqn]; exact ⟨le_rfl, mono x⟩
  let compact := fun (x : Fin 10 → Bool) =>
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
        (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  have same (x : Fin 10 → Bool) : compact x = f x := by
    simp only [compact, f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  obtain ⟨x, distinct, inputEq⟩ := separate P M prefixOK suffixOK short few
    (fun x => by change value x false ≤ compact x ∧ compact x ≤ value x true; simpa only [same] using sandwich x)
  change value x false ≠ value x true at distinct
  change P.eval (List.ofFn x) = compact x at inputEq
  rw [same] at inputEq
  have eqn := actual x
  have bounds := sandwich x
  rw [inputEq] at eqn
  cases hf : f x <;> simp only [hf, Bool.not_false, Bool.not_true] at eqn bounds <;>
    exact distinct (le_antisymm (mono x) (by simp_all))

import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The live expansion budget charges 21 at a NOT gate; otherwise it sums the two
-- operand budgets. The signed nine-input reduction by steveDOTdigital in PR 6197
-- uses a related fold.
-- Here the positive case uses one unit per input occurrence, and the complemented
-- case detects reachable negations by starting every input at zero.
theorem PEqualNP.Outside.R_meta_2371_21
    (lower : ∀ f : DMFormula 10, DMFormula.rec (motive := fun _ : DMFormula 10 => Prop) (fun _ s => s = true) (fun _ _ l r => l ∧ r) (fun _ _ l r => l ∧ r) f → (∀ x, f.eval x = (fun x : Fin 10 → Bool => x 1 && (x 0 || x 2 || x 6) || x 3 && (x 2 || x 4 || x 8) || x 4 && (x 0 || x 9) || x 5 && (x 0 || x 7 || x 8) || x 6 && (x 9 || x 8) || x 7 && (x 2 || x 9)) x) → 21 ≤ f.leaves)
    (shared : ∀ (C : Circuit) (b : Bool), FanInTwo C → C.size ≤ 18 → 21 ≤ (C.gates.foldl (fun (w : List Nat) (g : Gate) => w ++ [if g.op.eval [false] then 21 else (g.inputs.map fun i => w.getD i 0).sum]) (List.replicate 10 (if b then 0 else 1))).getD C.output 0 → ∃ x : Fin 10 → Bool, (if b then !C.eval (List.ofFn x) else C.eval (List.ofFn x)) ≠ (fun x : Fin 10 → Bool => x 1 && (x 0 || x 2 || x 6) || x 3 && (x 2 || x 4 || x 8) || x 4 && (x 0 || x 9) || x 5 && (x 0 || x 7 || x 8) || x 6 && (x 9 || x 8) || x 7 && (x 2 || x 9)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         ∃ (x10 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x9 x10 x3 else x9 x10 x3) ≠ x8 x10 := by
  intro g D i b hg hD size
  dsimp only
  let F := fun x : Fin 10 → Bool => x 1 && (x 0 || x 2 || x 6) || x 3 && (x 2 || x 4 || x 8) || x 4 && (x 0 || x 9) || x 5 && (x 0 || x 7 || x 8) || x 6 && (x 9 || x 8) || x 7 && (x 2 || x 9)
  let positive : DMFormula 10 → Prop := DMFormula.rec (motive := fun _ : DMFormula 10 => Prop) (fun _ s => s = true) (fun _ _ l r => l ∧ r) (fun _ _ l r => l ∧ r)
  let weight := fun (w : List Nat) (g : Gate) => w ++ [if g.op.eval [false] then 21 else (g.inputs.map fun i => w.getD i 0).sum]
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  let C : Circuit := ⟨g :: D.gates, i⟩
  have fan : FanInTwo C := by
    intro z hz
    obtain rfl | hz := List.mem_cons.mp hz
    · exact hg _ (by simp)
    · exact hD _ hz
  have nodes : C.size ≤ 18 := by change D.gates.length + 1 ≤ 18; exact Nat.succ_le_succ size
  have edgeForm (x : Fin 10 → Bool) : F x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
       x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    dsimp only [F]
    generalize x 0 = a0
    generalize x 1 = a1
    generalize x 2 = a2
    generalize x 3 = a3
    generalize x 4 = a4
    generalize x 5 = a5
    generalize x 6 = a6
    generalize x 7 = a7
    generalize x 8 = a8
    generalize x 9 = a9
    decide +revert
  by_contra! agrees
  have computes (x : Fin 10 → Bool) : (if b then !C.eval (List.ofFn x) else C.eval (List.ofFn x)) = F x :=
    (agrees x).trans (edgeForm x).symm
  let base := List.replicate 10 (if b then 0 else 1 : Nat)
  by_cases large : 21 ≤ (C.gates.foldl weight base).getD C.output 0
  · obtain ⟨x, hx⟩ := shared C b fan nodes large
    exact hx (computes x)
  have evalLit (v : Fin 10) (x : Fin 10 → Bool) : (DMFormula.lit v true).eval x = x v := rfl
  have evalAnd (f h : DMFormula 10) (x : Fin 10 → Bool) : (f.and h).eval x = (f.eval x && h.eval x) := rfl
  have evalOr (f h : DMFormula 10) (x : Fin 10 → Bool) : (f.or h).eval x = (f.eval x || h.eval x) := rfl
  have leavesAnd (f h : DMFormula 10) : (f.and h).leaves = f.leaves + h.leaves := rfl
  have leavesOr (f h : DMFormula 10) : (f.or h).leaves = f.leaves + h.leaves := rfl
  let Rep (k : Nat) (t : (Fin 10 → Bool) → Bool) :=
    (∃ c : Bool, ∀ x, t x = c) ∨
      ∃ f : DMFormula 10, positive f ∧ (b = false → f.leaves ≤ k) ∧ ∀ x, f.eval x = t x
  have both (d : Bool) (k l : Nat) (A B : (Fin 10 → Bool) → Bool) (ha : Rep k A) (hb : Rep l B) :
      Rep (k + l) (fun x => if d then A x && B x else A x || B x) := by
    have add (u : Nat) (hu : u ≤ k+l) (t : (Fin 10 → Bool) → Bool) (r : Rep u t) : Rep (k+l) t := by
      rcases r with h | ⟨f, p, bound, eqn⟩
      · exact Or.inl h
      · exact Or.inr ⟨f, p, fun s => (bound s).trans hu, eqn⟩
    rcases ha with ⟨a, ha⟩ | ⟨f, pf, hf, ef⟩
    · cases a <;> cases d <;> simp only [ha, ite_true, Bool.false_eq_true, ite_false,
        Bool.false_and, Bool.true_and, Bool.false_or, Bool.true_or]
      · exact add l (by omega) B hb
      · exact Or.inl ⟨false, fun _ => rfl⟩
      · exact Or.inl ⟨true, fun _ => rfl⟩
      · exact add l (by omega) B hb
    · rcases hb with ⟨c, ec⟩ | ⟨h, ph, hh, eh⟩
      · have self : Rep (k+l) A := add k (by omega) _ (Or.inr ⟨f, pf, hf, ef⟩)
        cases c <;> cases d <;> simp only [ec, ite_true, Bool.false_eq_true, ite_false,
          Bool.and_false, Bool.and_true, Bool.or_false, Bool.or_true]
        · exact self
        · exact Or.inl ⟨false, fun _ => rfl⟩
        · exact Or.inl ⟨true, fun _ => rfl⟩
        · exact self
      · cases d
        · exact Or.inr ⟨f.or h, ⟨pf, ph⟩, fun s => (leavesOr ..).le.trans (Nat.add_le_add (hf s) (hh s)),
            fun x => by rw [evalOr, ef, eh]; rfl⟩
        · exact Or.inr ⟨f.and h, ⟨pf, ph⟩, fun s => (leavesAnd ..).le.trans (Nat.add_le_add (hf s) (hh s)),
            fun x => by rw [evalAnd, ef, eh]; rfl⟩
  -- A zero-input gate produces a constant. A unary gate relays its operand.
  have binary (d : Bool) (ls : List Nat) (arity : ls.length ≤ 2)
      (w : List Nat) (rows : (Fin 10 → Bool) → List Bool)
      (old : ∀ i, w.getD i 0 < 21 → Rep (w.getD i 0) (fun x => (rows x).getD i false))
      (low : (ls.map fun j => w.getD j 0).sum < 21) :
      Rep (ls.map fun j => w.getD j 0).sum (fun x =>
        if d then (ls.map fun j => (rows x).getD j false).all id
        else (ls.map fun j => (rows x).getD j false).any id) := by
    cases ls with
    | nil => exact Or.inl ⟨d, fun _ => by cases d <;> rfl⟩
    | cons i ls =>
      cases ls with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at low ⊢
        simpa using old i low
      | cons j ls =>
        cases ls with
        | nil =>
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at low ⊢
          simpa using both d _ _ _ _ (old i (by omega)) (old j (by omega))
        | cons k ks => simp at arity
  have gate (z : Gate) (op : z.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (arity : z.inputs.length ≤ 2) (w : List Nat) (rows : (Fin 10 → Bool) → List Bool)
      (old : ∀ i, w.getD i 0 < 21 → Rep (w.getD i 0) (fun x => (rows x).getD i false)) :
      let k := if z.op.eval [false] then 21 else (z.inputs.map fun j => w.getD j 0).sum
      k < 21 → Rep k (fun x => z.op.eval (z.inputs.map fun j => (rows x).getD j false)) := by
    obtain ⟨o, ls⟩ := z
    rcases op with rfl | rfl | h
    · exact binary true ls arity w rows old
    · exact binary false ls arity w rows old
    · obtain rfl : o = GateOp.not := h
      change 21 < 21 → _
      omega
  -- Track a constant or a positive formula at each wire whose expansion stays below 21.
  have expand (gs : List Gate)
      (ops : ∀ z ∈ gs, z.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ z.inputs.length ≤ 2)
      (w : List Nat) (rows : (Fin 10 → Bool) → List Bool) (lens : ∀ x, (rows x).length = w.length)
      (old : ∀ i, w.getD i 0 < 21 → Rep (w.getD i 0) (fun x => (rows x).getD i false))
      (i : Nat) : (gs.foldl weight w).getD i 0 < 21 →
      Rep ((gs.foldl weight w).getD i 0) (fun x => (gs.foldl step (rows x)).getD i false) := by
    induction gs generalizing w rows with
    | nil => exact old i
    | cons z gs ih =>
      have hz := ops z List.mem_cons_self
      apply ih (fun g hg => ops g (List.mem_cons_of_mem z hg)) (weight w z) (fun x => step (rows x) z)
      · intro x
        simp [step, weight, lens]
      · intro j hj
        by_cases earlier : j < w.length
        · have e : (weight w z).getD j 0 = w.getD j 0 := List.getD_append _ _ _ _ earlier
          have v (x) : (step (rows x) z).getD j false = (rows x).getD j false :=
            List.getD_append _ _ _ _ (by simpa [lens] using earlier)
          simpa only [e, v] using old j (e ▸ hj)
        · by_cases now : j = w.length
          · subst j
            have e : (weight w z).getD w.length 0 =
                (if z.op.eval [false] then 21 else (z.inputs.map fun j => w.getD j 0).sum) := by
              dsimp only [weight]
              rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
              rfl
            have v (x) : (step (rows x) z).getD w.length false =
                z.op.eval (z.inputs.map fun j => (rows x).getD j false) := by
              dsimp only [step]
              rw [List.getD_append_right _ _ _ _ (by rw [lens]), lens, Nat.sub_self]
              rfl
            rw [e] at hj ⊢
            simp only [v]
            exact gate z hz.1 hz.2 w rows old hj
          · exact Or.inl ⟨false, fun x => List.getD_eq_default _ _ (by simp [step, lens]; omega)⟩
  have init (j : Nat) (_ : base.getD j 0 < 21) :
      Rep (base.getD j 0) (fun x => (List.ofFn x).getD j false) := by
    by_cases small : j < 10
    · refine Or.inr ⟨DMFormula.lit ⟨j, small⟩ true, rfl, ?_, ?_⟩
      · intro hb
        change 1 ≤ _
        dsimp only [base]
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_replicate] using small), List.getElem_replicate, hb]
        decide
      · intro x
        change (DMFormula.lit ⟨j, small⟩ true).eval x = (List.ofFn x).getD j false
        rw [evalLit, List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using small), List.getElem_ofFn]
    · exact Or.inl ⟨false, fun x => List.getD_eq_default _ _ (by simp; omega)⟩
  have repr := expand C.gates fan base List.ofFn (fun x => by simp [base]) init C.output (by omega)
  change Rep ((C.gates.foldl weight base).getD C.output 0) (fun x => C.eval (List.ofFn x)) at repr
  rcases repr with ⟨c, constant⟩ | ⟨f, pos, bound, eval⟩
  · change ∀ x, C.eval (List.ofFn x) = c at constant
    have no := computes (fun _ => false)
    have yes := computes (fun _ => true)
    rw [constant] at no yes
    exact Bool.false_ne_true (no.symm.trans yes)
  · change ∀ x, f.eval x = C.eval (List.ofFn x) at eval
    cases cb : b
    · have agreesF (x) := (eval x).trans (by simpa [cb] using computes x)
      have many := lower f pos agreesF
      have few := bound cb
      omega
    · have allFalse : ∀ a : DMFormula 10, positive a → a.eval (fun _ => false) = false := by
        intro a
        induction a with
        | lit i sign =>
          intro p
          obtain rfl : sign = true := p
          rfl
        | and l r ih jh => intro p; rw [evalAnd, ih p.1, jh p.2]; rfl
        | or l r ih jh => intro p; rw [evalOr, ih p.1, jh p.2]; rfl
      have no := computes (fun _ => false)
      rw [cb, ← eval, allFalse f pos] at no
      exact Bool.false_ne_true no.symm

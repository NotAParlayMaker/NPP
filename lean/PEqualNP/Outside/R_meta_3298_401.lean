import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3298_401
    (c6_lb :
      ¬PEqualNP.MetaComplexity.HasCircuitSize (6 : ℕ)
        (fun (x1 : Fin (6 : ℕ) → Bool) =>
          x1 (0 : Fin (6 : ℕ)) && x1 (1 : Fin (6 : ℕ)) ||
          x1 (1 : Fin (6 : ℕ)) && x1 (2 : Fin (6 : ℕ)) ||
          x1 (2 : Fin (6 : ℕ)) && x1 (3 : Fin (6 : ℕ)) ||
          x1 (3 : Fin (6 : ℕ)) && x1 (4 : Fin (6 : ℕ)) ||
          x1 (4 : Fin (6 : ℕ)) && x1 (5 : Fin (6 : ℕ)) ||
          x1 (5 : Fin (6 : ℕ)) && x1 (0 : Fin (6 : ℕ)))
        (7 : ℕ))
    (case_r1 :
      have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) =>
        x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) ||
        x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) ||
        x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) ||
        x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) ||
        x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ));
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x2 →
        PEqualNP.MetaComplexity.FanInTwo x3 →
        (1 : ℕ) ≤ x2.size →
        x2.size ≤ (4 : ℕ) →
        x2.size + x3.size ≤ (13 : ℕ) →
        x3.gates.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
          (if g.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) g.inputs else g.inputs).any
            (fun (i : ℕ) => i == (8 : ℕ) + x2.size)) = (1 : ℕ) →
        have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x);
        have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x : Fin (8 : ℕ) → Bool) => (x11 x).getD ((7 : ℕ) + x2.size) Bool.false;
        (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.false) →
        (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) →
        ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.true]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))))
    (case_r2 :
      have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) =>
        x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) ||
        x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) ||
        x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) ||
        x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) ||
        x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ));
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x2 →
        PEqualNP.MetaComplexity.FanInTwo x3 →
        (1 : ℕ) ≤ x2.size →
        x2.size ≤ (4 : ℕ) →
        x2.size + x3.size ≤ (13 : ℕ) →
        x3.gates.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
          (if g.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) g.inputs else g.inputs).any
            (fun (i : ℕ) => i == (8 : ℕ) + x2.size)) = (2 : ℕ) →
        have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x);
        have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x : Fin (8 : ℕ) → Bool) => (x11 x).getD ((7 : ℕ) + x2.size) Bool.false;
        (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.false) →
        (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) →
        ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.true]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))))
    (case_r3 :
      have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) =>
        x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) ||
        x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) ||
        x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) ||
        x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) ||
        x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ));
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x2 →
        PEqualNP.MetaComplexity.FanInTwo x3 →
        (1 : ℕ) ≤ x2.size →
        x2.size ≤ (4 : ℕ) →
        x2.size + x3.size = (13 : ℕ) →
        x3.gates.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
          (if g.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) g.inputs else g.inputs).any
            (fun (i : ℕ) => i == (8 : ℕ) + x2.size)) = (3 : ℕ) →
        (∀ g ∈ x3.gates,
          (if g.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) g.inputs else g.inputs).any
            (fun (i : ℕ) => i == (8 : ℕ) + x2.size) = Bool.true →
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (∃ g ∈ x3.gates, (7 : ℕ) + x2.size ∈ g.inputs) →
        have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x);
        have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x : Fin (8 : ℕ) → Bool) => (x11 x).getD ((7 : ℕ) + x2.size) Bool.false;
        (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.false) →
        (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) →
        ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.true]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ)))) :
  have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size ≤ (4 : ℕ) →         x2.size + x3.size ≤ (13 : ℕ) →           (8 : ℕ) ≤ x4 →             x4 < (8 : ℕ) + x2.size →               have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);               have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;               (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.false) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.true]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))) := by
  intro edgeF P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0
  let hiF : (Fin 8 → Bool) → Bool := fun x => edgeF x || x 0 || x 3
  let c6F : (Fin 6 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 5 || x 5 && x 0
  let reads : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun n g =>
    (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).any (fun i => i == n)
  let wiresFrom : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  let Ok : PEqualNP.CircuitLowerBounds.Gate → Prop := fun g =>
    g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
    g.inputs.length ≤ 2
  let NOk : PEqualNP.CircuitLowerBounds.Gate → Prop := fun g =>
    Ok g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length ≤ 1)
  let normGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g =>
    PEqualNP.CircuitLowerBounds.GateOp.rec g g ⟨PEqualNP.CircuitLowerBounds.GateOp.not, g.inputs.take 1⟩ (fun _ => g) g g.op
  let statVal : List Bool → Bool ⊕ ℕ → Bool := fun w s =>
    Sum.elim id (fun j => w.getD j false) s
  let statValid : ℕ → Bool ⊕ ℕ → Prop := fun m s =>
    Sum.elim (fun _ => True) (fun j => j < m) s
  let simpNot : ℕ → List (Bool ⊕ ℕ) → Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ) := fun m ins =>
    List.rec (none, Sum.inl true)
      (fun a _ _ => Sum.elim (fun c => (none, Sum.inl (!c)))
        (fun j => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [j]⟩, Sum.inr m)) a) ins
  let simpAnd : ℕ → List (Bool ⊕ ℕ) → Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ) := fun m ins =>
    List.rec (none, Sum.inl true)
      (fun a t _ => List.rec
        (none, a)
        (fun b t2 _ => List.rec
          (Sum.elim
            (fun c => Sum.elim (fun d => (none, Sum.inl (c && d)))
              (fun j => (none, bif c then Sum.inr j else Sum.inl false)) b)
            (fun j => Sum.elim (fun d => (none, bif d then Sum.inr j else Sum.inl false))
              (fun k => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [j, k]⟩, Sum.inr m)) b) a)
          (fun _ _ _ => (none, Sum.inl false)) t2) t) ins
  let simpOr : ℕ → List (Bool ⊕ ℕ) → Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ) := fun m ins =>
    List.rec (none, Sum.inl false)
      (fun a t _ => List.rec
        (none, a)
        (fun b t2 _ => List.rec
          (Sum.elim
            (fun c => Sum.elim (fun d => (none, Sum.inl (c || d)))
              (fun j => (none, bif c then Sum.inl true else Sum.inr j)) b)
            (fun j => Sum.elim (fun d => (none, bif d then Sum.inl true else Sum.inr j))
              (fun k => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [j, k]⟩, Sum.inr m)) b) a)
          (fun _ _ _ => (none, Sum.inl false)) t2) t) ins
  let simplify : PEqualNP.CircuitLowerBounds.GateOp → ℕ → List (Bool ⊕ ℕ) → Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ) := fun op m ins =>
    PEqualNP.CircuitLowerBounds.GateOp.rec (simpAnd m ins) (simpOr m ins) (simpNot m ins)
      (fun _ => (none, Sum.inl false)) (none, Sum.inl false) op
  let elimStep : ℕ → List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate → List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate := fun n acc g =>
    (acc.1 ++ [(simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
     acc.2 ++ (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
  let elim : ℕ → List PEqualNP.CircuitLowerBounds.Gate → List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate → List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate := fun n gs acc =>
    gs.foldl (elimStep n) acc
  let Inv : ℕ → List Bool → List Bool → List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate → Prop := fun n x w acc =>
    x.length = n ∧ acc.1.length = w.length ∧
    ∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
      statVal (wiresFrom acc.2 x) (acc.1.getD i (Sum.inl false)) = w.getD i false
  have wiresFrom_append : ∀ (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
    intro gs1 gs2 w
    exact List.foldl_append
  have wiresFrom_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (wiresFrom gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact (Nat.add_zero _).symm
    | cons g gs ih =>
      intro w
      change (wiresFrom gs (w ++ [_])).length = _
      rw [ih, List.length_append, List.length_singleton, List.length_cons]
      omega
  have getD_snoc_lt : ∀ {α : Type} (l : List α) (a d : α) (i : ℕ), i < l.length →
      (l ++ [a]).getD i d = l.getD i d := by
    intro α l a d i hi
    exact List.getD_append l [a] d i hi
  have getD_snoc_eq : ∀ {α : Type} (l : List α) (a d : α) (i : ℕ), i = l.length →
      (l ++ [a]).getD i d = a := by
    intro α l a d i hi
    subst hi
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  have getD_snoc_ne : ∀ {α : Type} (l : List α) (a d : α) (i : ℕ), i ≠ l.length →
      (l ++ [a]).getD i d = l.getD i d := by
    intro α l a d i hi
    by_cases hlt : i < l.length
    · exact getD_snoc_lt l a d i hlt
    · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega),
          List.getD_eq_default _ _ (by omega)]
  have wiresFrom_getD_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (wiresFrom gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      change (wiresFrom gs (w ++ [_])).getD i false = _
      rw [ih _ _ (by rw [List.length_append, List.length_singleton]; omega), getD_snoc_lt _ _ _ _ hi]
  have normGate_eval : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (F : ℕ → Bool),
      (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
    intro g F
    obtain ⟨op, ins⟩ := g
    cases op <;> simp only [normGate]
    cases ins <;> rfl
  have normGate_nok : ∀ (g : PEqualNP.CircuitLowerBounds.Gate), Ok g → NOk (normGate g) := by
    intro g h
    obtain ⟨op, ins⟩ := g
    obtain ⟨hop, hlen⟩ := h
    rcases hop with h | h | h
    · change op = _ at h; subst h; exact ⟨⟨Or.inl rfl, hlen⟩, fun hn => by cases hn⟩
    · change op = _ at h; subst h; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, fun hn => by cases hn⟩
    · change op = _ at h; subst h
      refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
      · change (ins.take 1).length ≤ 2; rw [List.length_take]; omega
      · change (ins.take 1).length ≤ 1; rw [List.length_take]; omega
  have wiresFrom_norm : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      wiresFrom (gs.map normGate) w = wiresFrom gs w := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      change wiresFrom (gs.map normGate) (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      rw [normGate_eval, ih]
  have reads_iff : ∀ (n : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), Ok g →
      (reads n g = true ↔ n ∈ (normGate g).inputs) := by
    intro n g hok
    obtain ⟨op, ins⟩ := g
    obtain ⟨hop, _⟩ := hok
    rcases hop with h | h | h <;> change op = _ at h <;> subst h
    · change (ins.any fun i => i == n) = true ↔ n ∈ ins
      rw [List.any_eq_true]
      exact ⟨fun h => by obtain ⟨a, ha, he⟩ := h; exact (beq_iff_eq.mp he) ▸ ha, fun hn => ⟨n, hn, beq_self_eq_true n⟩⟩
    · change (ins.any fun i => i == n) = true ↔ n ∈ ins
      rw [List.any_eq_true]
      exact ⟨fun h => by obtain ⟨a, ha, he⟩ := h; exact (beq_iff_eq.mp he) ▸ ha, fun hn => ⟨n, hn, beq_self_eq_true n⟩⟩
    · change ((ins.take 1).any fun i => i == n) = true ↔ n ∈ ins.take 1
      rw [List.any_eq_true]
      exact ⟨fun h => by obtain ⟨a, ha, he⟩ := h; exact (beq_iff_eq.mp he) ▸ ha, fun hn => ⟨n, hn, beq_self_eq_true n⟩⟩
  have cut_agree : ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, n ∉ g.inputs) → ∀ (v w : List Bool), v.length = w.length →
      (∀ i, i ≠ n → v.getD i false = w.getD i false) →
      ∀ i, i ≠ n → (wiresFrom gs v).getD i false = (wiresFrom gs w).getD i false := by
    intro n gs
    induction gs with
    | nil => intro _ v w _ h i hi; exact h i hi
    | cons g gs ih =>
      intro hno v w hlen hag
      change ∀ i, i ≠ n → (wiresFrom gs (v ++ [_])).getD i false = (wiresFrom gs (w ++ [_])).getD i false
      have hmap : g.inputs.map (fun i => v.getD i false) = g.inputs.map (fun i => w.getD i false) :=
        List.map_congr_left (fun i hi => hag i (fun heq => hno g List.mem_cons_self (heq ▸ hi)))
      rw [hmap]
      apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) _ _ (by rw [List.length_append, List.length_append, hlen])
      intro i hi
      by_cases h : i = v.length
      · rw [getD_snoc_eq _ _ _ _ h, getD_snoc_eq _ _ _ _ (h.trans hlen)]
      · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (by omega)]
        exact hag i hi
  have simplify_ok : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)),
      ∀ g ∈ (simplify op m ins).1, Ok g := by
    clear c6_lb case_r1 case_r2 case_r3 P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0
    intro op m ins g hg
    cases op
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · cases hg
      · cases a <;> cases hg
      · cases a <;> cases b <;> cases hg
        exact ⟨Or.inl rfl, Nat.le_refl 2⟩
      · simp only [simplify, simpAnd] at hg; cases hg
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · cases hg
      · cases a <;> cases hg
      · cases a <;> cases b <;> cases hg
        exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
      · simp only [simplify, simpOr] at hg; cases hg
    · rcases ins with _ | ⟨a, l⟩
      · cases hg
      · cases a <;> cases hg
        exact ⟨Or.inr (Or.inr rfl), Nat.le_succ 1⟩
    · cases hg
    · cases hg
  have simplify_count : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)),
      (op = .and ∨ op = .or ∨ op = .not) → ins.length ≤ 2 → (op = .not → ins.length ≤ 1) →
      (∃ c, Sum.inl c ∈ ins) → (simplify op m ins).1 = none := by
    clear c6_lb case_r1 case_r2 case_r3 P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0
    intro op m ins hop hlen hnot h
    obtain ⟨c, hc⟩ := h
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · cases hc
      · cases a <;> rfl
      · cases a with
        | inl _ => cases b <;> rfl
        | inr _ =>
          cases b with
          | inl _ => rfl
          | inr _ =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with h | h <;> cases h
      · simp only [List.length_cons] at hlen; omega
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · cases hc
      · cases a <;> rfl
      · cases a with
        | inl _ => cases b <;> rfl
        | inr _ =>
          cases b with
          | inl _ => rfl
          | inr _ =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with h | h <;> cases h
      · simp only [List.length_cons] at hlen; omega
    · have h1 := hnot rfl
      rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
      · cases hc
      · cases a with
        | inl _ => rfl
        | inr _ =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          cases hc
      · simp only [List.length_cons] at h1; omega
  have simplify_or_true : ∀ (m : ℕ) (ins : List (Bool ⊕ ℕ)),
      ins.length ≤ 2 → Sum.inl true ∈ ins → ∃ c, (simplify .or m ins).2 = Sum.inl c := by
    clear c6_lb case_r1 case_r2 case_r3 P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0
    intro m ins hlen hc
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · cases hc
    · cases a with
      | inl c => exact ⟨c, rfl⟩
      | inr _ => simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; cases hc
    · cases a with
      | inl c =>
        cases b with
        | inl d => exact ⟨c || d, rfl⟩
        | inr _ =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with h | h
          · cases h; exact ⟨true, rfl⟩
          · cases h
      | inr _ =>
        cases b with
        | inl d =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with h | h
          · cases h
          · cases h; exact ⟨true, rfl⟩
        | inr _ =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with h | h <;> cases h
    · simp only [List.length_cons] at hlen; omega
  have simplify_not_const : ∀ (m : ℕ) (ins : List (Bool ⊕ ℕ)) (b : Bool),
      ins.length ≤ 1 → Sum.inl b ∈ ins → ∃ c, (simplify .not m ins).2 = Sum.inl c := by
    clear c6_lb case_r1 case_r2 case_r3 P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0
    intro m ins b hlen hc
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩
    · cases hc
    · cases a with
      | inl c => exact ⟨!c, rfl⟩
      | inr _ => simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; cases hc
    · simp only [List.length_cons] at hlen; omega
  have simplify_all_const : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)),
      (op = .and ∨ op = .or ∨ op = .not) → ins.length ≤ 2 →
      (∀ s ∈ ins, ∃ c, s = Sum.inl c) → ∃ c, (simplify op m ins).2 = Sum.inl c := by
    clear c6_lb case_r1 case_r2 case_r3 P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0
    intro op m ins hop hlen hall
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · exact ⟨true, rfl⟩
      · obtain ⟨c, rfl⟩ := hall a List.mem_cons_self; exact ⟨c, rfl⟩
      · obtain ⟨c, rfl⟩ := hall a List.mem_cons_self
        obtain ⟨d, rfl⟩ := hall b (List.mem_cons_of_mem _ List.mem_cons_self)
        exact ⟨c && d, rfl⟩
      · simp only [List.length_cons] at hlen; omega
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · exact ⟨false, rfl⟩
      · obtain ⟨c, rfl⟩ := hall a List.mem_cons_self; exact ⟨c, rfl⟩
      · obtain ⟨c, rfl⟩ := hall a List.mem_cons_self
        obtain ⟨d, rfl⟩ := hall b (List.mem_cons_of_mem _ List.mem_cons_self)
        exact ⟨c || d, rfl⟩
      · simp only [List.length_cons] at hlen; omega
    · rcases ins with _ | ⟨a, l⟩
      · exact ⟨true, rfl⟩
      · obtain ⟨c, rfl⟩ := hall a List.mem_cons_self; exact ⟨!c, rfl⟩
  have simplify_sound : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp),
      (op = .and ∨ op = .or ∨ op = .not) → ∀ (w : List Bool) (ins : List (Bool ⊕ ℕ)),
      ins.length ≤ 2 → (∀ s ∈ ins, statValid w.length s) →
      statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
      statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2 =
        op.eval (ins.map (statVal w)) := by
    clear c6_lb case_r1 case_r2 case_r3 P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0
    intro op hop w ins hlen hv
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · exact ⟨trivial, rfl⟩
      · cases a with
        | inl c => exact ⟨trivial, by change c = (c && true); rw [Bool.and_true]⟩
        | inr j =>
          have hj : j < w.length := hv (Sum.inr j) List.mem_cons_self
          exact ⟨by change j < w.length + 0; omega, by change w.getD j false = (w.getD j false && true); rw [Bool.and_true]⟩
      · cases a with
        | inl c =>
          cases b with
          | inl d => exact ⟨trivial, by change (c && d) = (c && (d && true)); rw [Bool.and_true]⟩
          | inr j =>
            have hj : j < w.length := hv (Sum.inr j) (List.mem_cons_of_mem _ List.mem_cons_self)
            cases c
            · exact ⟨trivial, by change false = (false && (w.getD j false && true)); rfl⟩
            · exact ⟨by change j < w.length + 0; omega, by change w.getD j false = (true && (w.getD j false && true)); rw [Bool.true_and, Bool.and_true]⟩
        | inr i =>
          have hi : i < w.length := hv (Sum.inr i) List.mem_cons_self
          cases b with
          | inl d =>
            cases d
            · exact ⟨trivial, by change false = (w.getD i false && (false && true)); rw [Bool.and_true, Bool.and_false]⟩
            · exact ⟨by change i < w.length + 0; omega, by change w.getD i false = (w.getD i false && (true && true)); rw [Bool.and_true, Bool.and_true]⟩
          | inr j =>
            refine ⟨by change w.length < w.length + 1; omega, ?_⟩
            change (w ++ [(w.getD i false && (w.getD j false && true))]).getD w.length false = _
            rw [getD_snoc_eq _ _ _ _ rfl]
            rfl
      · simp only [List.length_cons] at hlen; omega
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · exact ⟨trivial, rfl⟩
      · cases a with
        | inl c => exact ⟨trivial, by change c = (c || false); rw [Bool.or_false]⟩
        | inr j =>
          have hj : j < w.length := hv (Sum.inr j) List.mem_cons_self
          exact ⟨by change j < w.length + 0; omega, by change w.getD j false = (w.getD j false || false); rw [Bool.or_false]⟩
      · cases a with
        | inl c =>
          cases b with
          | inl d => exact ⟨trivial, by change (c || d) = (c || (d || false)); rw [Bool.or_false]⟩
          | inr j =>
            have hj : j < w.length := hv (Sum.inr j) (List.mem_cons_of_mem _ List.mem_cons_self)
            cases c
            · exact ⟨by change j < w.length + 0; omega, by change w.getD j false = (false || (w.getD j false || false)); rw [Bool.false_or, Bool.or_false]⟩
            · exact ⟨trivial, by change true = (true || (w.getD j false || false)); rfl⟩
        | inr i =>
          have hi : i < w.length := hv (Sum.inr i) List.mem_cons_self
          cases b with
          | inl d =>
            cases d
            · exact ⟨by change i < w.length + 0; omega, by change w.getD i false = (w.getD i false || (false || false)); rw [Bool.or_false, Bool.or_false]⟩
            · exact ⟨trivial, by change true = (w.getD i false || (true || false)); rw [Bool.or_false, Bool.or_true]⟩
          | inr j =>
            refine ⟨by change w.length < w.length + 1; omega, ?_⟩
            change (w ++ [(w.getD i false || (w.getD j false || false))]).getD w.length false = _
            rw [getD_snoc_eq _ _ _ _ rfl]
            rfl
      · simp only [List.length_cons] at hlen; omega
    · rcases ins with _ | ⟨a, l⟩
      · exact ⟨trivial, rfl⟩
      · cases a with
        | inl c => exact ⟨trivial, rfl⟩
        | inr j =>
          refine ⟨by change w.length < w.length + 1; omega, ?_⟩
          change (w ++ [!(w.getD j false)]).getD w.length false = _
          rw [getD_snoc_eq _ _ _ _ rfl]
          rfl
  have elim_append : ∀ (n : ℕ) (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate),
      elim n (gs1 ++ gs2) acc = elim n gs2 (elim n gs1 acc) := by
    intro n gs1 gs2 acc; exact List.foldl_append
  have elim_fst_len : ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate),
      (elim n gs acc).1.length = acc.1.length + gs.length := by
    intro n gs
    induction gs with
    | nil => intro acc; exact (Nat.add_zero _).symm
    | cons g gs ih =>
      intro acc
      change (elim n gs (elimStep n acc g)).1.length = _
      rw [ih]
      change (acc.1 ++ [_]).length + gs.length = _
      rw [List.length_append, List.length_singleton, List.length_cons]; omega
  have elim_getD : ∀ (n k : ℕ) (d : Bool ⊕ ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate),
      k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
    intro n k d gs
    induction gs with
    | nil => intro acc _; rfl
    | cons g gs ih =>
      intro acc hk
      change (elim n gs (elimStep n acc g)).1.getD k d = _
      rw [ih _ (by change k < (acc.1 ++ [_]).length; rw [List.length_append, List.length_singleton]; omega)]
      exact getD_snoc_ne _ _ _ _ (by omega)
  have elim_ok : ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
    intro n gs
    induction gs with
    | nil => intro acc h; exact h
    | cons g gs ih =>
      intro acc h
      apply ih (elimStep n acc g)
      intro g' hg'
      rcases List.mem_append.mp hg' with h1 | h2
      · exact h g' h1
      · exact simplify_ok _ _ _ g' (Option.mem_toList.mp h2)
  have elim_inv : ∀ (n : ℕ) (x : List Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
      (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, Ok g) → Inv n x w acc → Inv n x (wiresFrom gs w) (elim n gs acc) := by
    clear c6_lb case_r1 case_r2 case_r3 P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0
    intro n x gs
    induction gs with
    | nil => intro w acc _ hi; exact hi
    | cons g gs ih =>
      intro w acc hok h
      obtain ⟨hx, hlen, hget⟩ := h
      have hgok : Ok g := hok g List.mem_cons_self
      let ins := g.inputs.map (fun i => acc.1.getD i (Sum.inl false))
      let res := simplify g.op (n + acc.2.length) ins
      let w' := wiresFrom acc.2 x
      have hw'len : w'.length = n + acc.2.length := by
        rw [wiresFrom_len, hx]
      have hvalid : ∀ s ∈ ins, statValid w'.length s := by
        intro s hs
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
        rw [hw'len]
        exact (hget i).1
      have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
        rcases hgok.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      have hsound := simplify_sound g.op hop w' ins (by rw [List.length_map]; exact hgok.2) hvalid
      rw [hw'len] at hsound
      have heval : g.op.eval (ins.map (statVal w')) = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        congr 1
        simp only [ins, List.map_map]
        apply List.map_congr_left
        intro i _
        exact (hget i).2
      apply ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      refine ⟨hx, by change (acc.1 ++ [_]).length = (w ++ [_]).length; rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton, hlen], ?_⟩
      intro i
      by_cases hi : i < w.length
      · rw [getD_snoc_lt _ _ _ _ (by omega : i < acc.1.length), getD_snoc_lt _ _ _ _ hi]
        obtain ⟨hv1, hv2⟩ := hget i
        refine ⟨?_, ?_⟩
        · cases hs : acc.1.getD i (Sum.inl false) with
          | inl c => trivial
          | inr j =>
            rw [hs] at hv1
            change j < n + acc.2.length at hv1
            change j < n + (acc.2 ++ res.1.toList).length
            rw [List.length_append]; omega
        · cases hs : acc.1.getD i (Sum.inl false) with
          | inl c => rw [hs] at hv2; exact hv2
          | inr j =>
            rw [hs] at hv1 hv2
            change (wiresFrom (acc.2 ++ res.1.toList) x).getD j false = _
            rw [wiresFrom_append, wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_len, hx]; exact hv1)]
            exact hv2
      · by_cases heq : i = w.length
        · rw [getD_snoc_eq _ _ _ _ (by omega : i = acc.1.length), getD_snoc_eq _ _ _ _ heq]
          refine ⟨?_, ?_⟩
          · change statValid (n + (acc.2 ++ res.1.toList).length) res.2
            rw [List.length_append, ← Nat.add_assoc]
            exact hsound.1
          · change statVal (wiresFrom (acc.2 ++ res.1.toList) x) res.2 = _
            rw [wiresFrom_append, ← heval]
            exact hsound.2
        · rw [List.getD_eq_default _ _ (by change (acc.1 ++ [_]).length ≤ i; rw [List.length_append, List.length_singleton]; omega),
              List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)]
          exact ⟨trivial, rfl⟩
  have elimStep_none : ∀ (n : ℕ) (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate),
      NOk g → ∀ a ∈ g.inputs, ∀ c, acc.1.getD a (Sum.inl false) = Sum.inl c →
      (elimStep n acc g).2.length = acc.2.length := by
    clear c6_lb case_r1 case_r2 case_r3 P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0
    intro n acc g hnok a ha c hc
    have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      rcases hnok.1.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hnone : (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none :=
      simplify_count _ _ _ hop (by rw [List.length_map]; exact hnok.1.2)
        (fun h => by rw [List.length_map]; exact hnok.2 h) ⟨c, List.mem_map.mpr ⟨a, ha, hc⟩⟩
    change (acc.2 ++ _).length = acc.2.length
    rw [hnone, Option.toList_none, List.append_nil]
  have elim_count : ∀ (n : ℕ) (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
      (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
    clear c6_lb case_r1 case_r2 case_r3 P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0
    intro n acc gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _ S hS
      have hE : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨g, hg, _⟩ := hS p hp
        simp only [List.getElem?_nil, reduceCtorEq] at hg
      subst hE
      rw [Finset.card_empty, Nat.add_zero]
      exact Nat.le_refl _
    | append_singleton gs g ih =>
      intro hok S hS
      have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
        rw [elim_append]; rfl
      have hpre : ∀ (a : ℕ) (d : Bool ⊕ ℕ), a < acc.1.length + gs.length →
          (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d := by
        intro a d hlt
        rw [hstep]
        exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)
      have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
      have ih' := ih hok' (S.erase gs.length) (by
        intro p hp
        obtain ⟨hne, hpS⟩ := Finset.mem_erase.mp hp
        obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
        have hpl : p < gs.length := by
          obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.mp hg'
          rw [List.length_append, List.length_singleton] at h1; omega
        rw [List.getElem?_append_left hpl] at hg'
        rw [hpre a _ (by omega)] at hc
        exact ⟨g', hg', a, ha, hlt, c, hc⟩)
      rw [hstep]
      have hlen_rhs : (gs ++ [g]).length = gs.length + 1 := by
        rw [List.length_append, List.length_singleton]
      rw [hlen_rhs]
      by_cases hin : gs.length ∈ S
      · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
        have hgg : g' = g := by
          rw [List.getElem?_concat_length] at hg'
          exact (Option.some.inj hg').symm
        subst hgg
        rw [hpre a _ hlt] at hc
        have h2 := elimStep_none n (elim n gs acc) g' (hok g' (List.mem_append_right _ List.mem_cons_self)) a ha c hc
        have hcard := Finset.card_erase_of_mem hin
        have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨_, hin⟩
        omega
      · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
          change ((elim n gs acc).2 ++ _).length ≤ _
          rw [List.length_append]
          cases (simplify g.op (n + (elim n gs acc).2.length)
            (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1 <;> simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_singleton] <;> omega
        rw [Finset.erase_eq_of_notMem hin] at ih'
        omega
  have hi_lb : ¬PEqualNP.MetaComplexity.HasCircuitSize 8 hiF 9 := by
    clear case_r1 case_r2 case_r3 P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0
    rintro ⟨C, hCfan, hCsize, hCeval⟩
    let gs := C.gates.map normGate
    have hnok : ∀ g ∈ gs, NOk g := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact normGate_nok g0 (hCfan g0 hg0)
    let init : List (Bool ⊕ ℕ) :=
      [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inl false, Sum.inr 3, Sum.inr 5, Sum.inr 2, Sum.inr 4]
    let lift : (Fin 6 → Bool) → (Fin 8 → Bool) := fun y i =>
      if i.val = 0 then false
      else if i.val = 1 then y 0
      else if i.val = 2 then y 1
      else if i.val = 3 then false
      else if i.val = 4 then y 3
      else if i.val = 5 then y 5
      else if i.val = 6 then y 2
      else y 4
    have hlift_eq : ∀ y : Fin 6 → Bool, hiF (lift y) = c6F y := by
      intro y
      dsimp only [hiF, edgeF, c6F, lift]
      cases y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;> cases y 4 <;> cases y 5 <;> rfl
    let acc := elim 6 gs (init, [])
    have hinv : ∀ y : Fin 6 → Bool, Inv 6 (List.ofFn y) (wiresFrom gs (List.ofFn (lift y))) acc := by
      intro y
      apply elim_inv 6 (List.ofFn y) gs (List.ofFn (lift y)) (init, []) (fun g hg => (hnok g hg).1)
      refine ⟨List.length_ofFn, by rw [List.length_ofFn]; rfl, ?_⟩
      intro i
      by_cases hi : i < 8
      · interval_cases i
        · exact ⟨trivial, rfl⟩
        · exact ⟨by change 0 < 6; omega, rfl⟩
        · exact ⟨by change 1 < 6; omega, rfl⟩
        · exact ⟨trivial, rfl⟩
        · exact ⟨by change 3 < 6; omega, rfl⟩
        · exact ⟨by change 5 < 6; omega, rfl⟩
        · exact ⟨by change 2 < 6; omega, rfl⟩
        · exact ⟨by change 4 < 6; omega, rfl⟩
      · rw [List.getD_eq_default _ _ (by change 8 ≤ i; omega), List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
        exact ⟨trivial, rfl⟩
    have hval : ∀ y : Fin 6 → Bool,
        statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false)) = c6F y := by
      intro y
      have h1 := ((hinv y).2.2 C.output).2
      rw [wiresFrom_norm] at h1
      exact h1.trans ((hCeval (lift y)).trans (hlift_eq y))
    have hgs_eval : ∀ x : Fin 8 → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = hiF x := by
      intro x
      rw [wiresFrom_norm]
      exact hCeval x
    have hout0 : C.output ≠ 0 := by
      intro heq
      have h1 := hgs_eval (fun i => decide (i = 3))
      rw [heq, wiresFrom_getD_lt _ _ _ (by rw [List.length_ofFn]; omega)] at h1
      have h2 : hiF (fun i => decide (i = 3)) = true := rfl
      rw [h2] at h1
      have h3 : (List.ofFn (fun i : Fin 8 => decide (i = 3))).getD 0 false = false := rfl
      rw [h3] at h1; exact Bool.noConfusion h1
    have hout3 : C.output ≠ 3 := by
      intro heq
      have h1 := hgs_eval (fun i => decide (i = 0))
      rw [heq, wiresFrom_getD_lt _ _ _ (by rw [List.length_ofFn]; omega)] at h1
      have h2 : hiF (fun i => decide (i = 0)) = true := rfl
      rw [h2] at h1
      have h3 : (List.ofFn (fun i : Fin 8 => decide (i = 0))).getD 3 false = false := rfl
      rw [h3] at h1; exact Bool.noConfusion h1
    have hhit0 : ∃ (p : ℕ) (hp : p < gs.length), 0 ∈ gs[p].inputs := by
      by_contra! hno
      have hno' : ∀ g ∈ gs, 0 ∉ g.inputs := by
        intro g hg
        obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hg
        exact hno p hp
      have heq := cut_agree 0 gs hno' (List.ofFn (fun i : Fin 8 => decide (i = 0)))
        (List.ofFn (fun _ : Fin 8 => false)) (by rw [List.length_ofFn, List.length_ofFn]) (by
          intro i hi
          by_cases hlt : i < 8
          · interval_cases i
            · exact (hi rfl).elim
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
          · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega),
                List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)])
        C.output hout0
      rw [hgs_eval, hgs_eval] at heq
      have h1 : hiF (fun i : Fin 8 => decide (i = 0)) = true := rfl
      have h2 : hiF (fun _ : Fin 8 => false) = false := rfl
      rw [h1, h2] at heq
      exact Bool.noConfusion heq
    have hhit3 : ∃ (p : ℕ) (hp : p < gs.length), 3 ∈ gs[p].inputs := by
      by_contra! hno
      have hno' : ∀ g ∈ gs, 3 ∉ g.inputs := by
        intro g hg
        obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hg
        exact hno p hp
      have heq := cut_agree 3 gs hno' (List.ofFn (fun i : Fin 8 => decide (i = 3)))
        (List.ofFn (fun _ : Fin 8 => false)) (by rw [List.length_ofFn, List.length_ofFn]) (by
          intro i hi
          by_cases hlt : i < 8
          · interval_cases i
            · rfl
            · rfl
            · rfl
            · exact (hi rfl).elim
            · rfl
            · rfl
            · rfl
            · rfl
          · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega),
                List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)])
        C.output hout3
      rw [hgs_eval, hgs_eval] at heq
      have h1 : hiF (fun i : Fin 8 => decide (i = 3)) = true := rfl
      have h2 : hiF (fun _ : Fin 8 => false) = false := rfl
      rw [h1, h2] at heq
      exact Bool.noConfusion heq
    have hstat0 : acc.1.getD 0 (Sum.inl false) = Sum.inl false := by
      rw [elim_getD 6 0 _ gs (init, []) (by decide)]; rfl
    have hstat3 : acc.1.getD 3 (Sum.inl false) = Sum.inl false := by
      rw [elim_getD 6 3 _ gs (init, []) (by decide)]; rfl
    have htwo : ∃ S : Finset ℕ, S.card = 2 ∧
        ∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < init.length + p ∧
          ∃ c, acc.1.getD a (Sum.inl false) = Sum.inl c := by
      obtain ⟨p0, hp0, h0in⟩ := hhit0
      obtain ⟨p3, hp3, h3in⟩ := hhit3
      by_cases hne : p0 ≠ p3
      · refine ⟨{p0, p3}, Finset.card_pair hne, ?_⟩
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact ⟨gs[p], List.getElem?_eq_getElem hp0, 0, h0in, by change 0 < 8 + p; omega, false, hstat0⟩
        · have rflp : p = p3 := Finset.mem_singleton.mp hp'
          subst rflp
          exact ⟨gs[p], List.getElem?_eq_getElem hp3, 3, h3in, by change 3 < 8 + p; omega, false, hstat3⟩
      · push Not at hne
        subst hne
        by_cases hother0 : ∃ (q : ℕ) (hq : q < gs.length), q ≠ p0 ∧ 0 ∈ gs[q].inputs
        · obtain ⟨q, hq, hqp, h0q⟩ := hother0
          refine ⟨{p0, q}, Finset.card_pair hqp.symm, ?_⟩
          intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hp'
          · exact ⟨gs[p], List.getElem?_eq_getElem hp0, 0, h0in, by change 0 < 8 + p; omega, false, hstat0⟩
          · have rflp : p = q := Finset.mem_singleton.mp hp'
            subst rflp
            exact ⟨gs[p], List.getElem?_eq_getElem hq, 0, h0q, by change 0 < 8 + p; omega, false, hstat0⟩
        · push Not at hother0
          have hgp0_all : ∀ a ∈ gs[p0].inputs, a = 0 ∨ a = 3 := by
            have hlen2 : gs[p0].inputs.length ≤ 2 := (hnok gs[p0] (List.getElem_mem hp0)).1.2
            rcases h : gs[p0].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
            · rw [h] at h0in; cases h0in
            · rw [h] at h0in h3in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h0in h3in
              omega
            · rw [h] at h0in h3in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h0in h3in
              intro x hx
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases h0in with rfl | rfl <;> rcases h3in with h3a | h3b <;> omega
            · rw [h] at hlen2; simp only [List.length_cons] at hlen2; omega
          have hsplit : gs = gs.take p0 ++ gs[p0] :: gs.drop (p0 + 1) := by
            have h1 := List.take_append_drop p0 gs
            have h2 : gs.drop p0 = gs[p0] :: gs.drop (p0 + 1) := List.drop_eq_getElem_cons hp0
            rw [h2] at h1; exact h1.symm
          have hstat_p0 : ∃ c, acc.1.getD (8 + p0) (Sum.inl false) = Sum.inl c := by
            have hstep_acc : acc = elim 6 (gs.drop (p0 + 1)) (elimStep 6 (elim 6 (gs.take p0) (init, [])) gs[p0]) := by
              change elim 6 gs (init, []) = _
              conv_lhs => rw [hsplit]
              rw [elim_append]; rfl
            rw [hstep_acc]
            have hlen_pre : (elim 6 (gs.take p0) (init, [])).1.length = 8 + p0 := by
              rw [elim_fst_len, List.length_take_of_le (Nat.le_of_lt hp0)]; rfl
            rw [elim_getD 6 (8 + p0) _ _ _ (by change 8 + p0 < ((elim 6 (gs.take p0) (init, [])).1 ++ [_]).length; rw [List.length_append, List.length_singleton, hlen_pre]; omega)]
            dsimp only [elimStep]
            rw [getD_snoc_eq _ _ _ _ hlen_pre.symm]
            have hop : gs[p0].op = .and ∨ gs[p0].op = .or ∨ gs[p0].op = .not := by
              rcases (hnok _ (List.getElem_mem hp0)).1.1 with h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)
            apply simplify_all_const _ _ _ hop (by rw [List.length_map]; exact (hnok _ (List.getElem_mem hp0)).1.2)
            intro s hs
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
            rcases hgp0_all a ha with rfl | rfl
            · rw [elim_getD 6 0 _ _ _ (by decide)]; exact ⟨false, rfl⟩
            · rw [elim_getD 6 3 _ _ _ (by decide)]; exact ⟨false, rfl⟩
          obtain ⟨cp0, hcp0⟩ := hstat_p0
          have hout_p0 : C.output ≠ 8 + p0 := by
            intro heq
            have hf0 := hval (fun _ => false)
            have hf1 := hval (fun _ => true)
            rw [heq, hcp0] at hf0 hf1
            have hc0 : c6F (fun _ => false) = false := rfl
            have hc1 : c6F (fun _ => true) = true := rfl
            rw [hc0] at hf0; rw [hc1] at hf1
            exact Bool.noConfusion (hf0.symm.trans hf1)
          have hhit_wp0 : ∃ (q : ℕ) (_ : p0 < q) (hq : q < gs.length), (8 + p0) ∈ gs[q].inputs := by
            by_contra! hno_wp0
            let xA : Fin 8 → Bool := fun i => decide (i = 0)
            let xB : Fin 8 → Bool := fun _ => false
            have hpre_ag : ∀ i, i ≠ 0 →
                (wiresFrom (gs.take p0) (List.ofFn xA)).getD i false =
                (wiresFrom (gs.take p0) (List.ofFn xB)).getD i false := by
              apply cut_agree 0 (gs.take p0)
              · intro g hg
                obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
                have hklt : k < p0 := by rw [List.length_take_of_le (Nat.le_of_lt hp0)] at hk; exact hk
                rw [List.getElem_take]
                exact hother0 k (by omega) (by omega)
              · rw [List.length_ofFn, List.length_ofFn]
              · intro i hi
                by_cases hlt : i < 8
                · interval_cases i
                  · exact (hi rfl).elim
                  · rfl
                  · rfl
                  · rfl
                  · rfl
                  · rfl
                  · rfl
                  · rfl
                · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega),
                      List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
            have hpre_lenA : (wiresFrom (gs.take p0) (List.ofFn xA)).length = 8 + p0 := by
              rw [wiresFrom_len, List.length_ofFn, List.length_take_of_le (Nat.le_of_lt hp0)]
            have hpre_lenB : (wiresFrom (gs.take p0) (List.ofFn xB)).length = 8 + p0 := by
              rw [wiresFrom_len, List.length_ofFn, List.length_take_of_le (Nat.le_of_lt hp0)]
            have hpost_no : ∀ g ∈ gs.drop (p0 + 1), 0 ∉ g.inputs ∧ (8 + p0) ∉ g.inputs := by
              intro g hg
              obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
              rw [List.getElem_drop]
              have hklt : p0 + 1 + k < gs.length := by rw [List.length_drop] at hk; omega
              exact ⟨hother0 (p0 + 1 + k) hklt (by omega), hno_wp0 (p0 + 1 + k) (by omega) hklt⟩
            have hpost_ag : ∀ (l : List PEqualNP.CircuitLowerBounds.Gate),
                (∀ g ∈ l, 0 ∉ g.inputs ∧ (8 + p0) ∉ g.inputs) →
                ∀ (v w : List Bool), v.length = w.length →
                (∀ i, i ≠ 0 → i ≠ 8 + p0 → v.getD i false = w.getD i false) →
                ∀ i, i ≠ 0 → i ≠ 8 + p0 → (wiresFrom l v).getD i false = (wiresFrom l w).getD i false := by
              intro l
              induction l with
              | nil => intro _ v w _ h i h0 hp; exact h i h0 hp
              | cons g l ih =>
                intro hno v w hlen hag
                change ∀ i, i ≠ 0 → i ≠ 8 + p0 → (wiresFrom l (v ++ [_])).getD i false = (wiresFrom l (w ++ [_])).getD i false
                have hmap : g.inputs.map (fun i => v.getD i false) = g.inputs.map (fun i => w.getD i false) :=
                  List.map_congr_left (fun i hi => hag i (fun h0 => (hno g List.mem_cons_self).1 (h0 ▸ hi))
                    (fun hp => (hno g List.mem_cons_self).2 (hp ▸ hi)))
                rw [hmap]
                apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) _ _ (by rw [List.length_append, List.length_append, hlen])
                intro i h0 hp
                by_cases h : i = v.length
                · rw [getD_snoc_eq _ _ _ _ h, getD_snoc_eq _ _ _ _ (h.trans hlen)]
                · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (by omega)]
                  exact hag i h0 hp
            have hmid_ag : ∀ i, i ≠ 0 → i ≠ 8 + p0 →
                (wiresFrom (gs.take p0 ++ [gs[p0]]) (List.ofFn xA)).getD i false =
                (wiresFrom (gs.take p0 ++ [gs[p0]]) (List.ofFn xB)).getD i false := by
              intro i hi0 hip0
              rw [wiresFrom_append, wiresFrom_append]
              change (wiresFrom (gs.take p0) (List.ofFn xA) ++ [_]).getD i false =
                (wiresFrom (gs.take p0) (List.ofFn xB) ++ [_]).getD i false
              rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
              exact hpre_ag i hi0
            have hfin := hpost_ag (gs.drop (p0 + 1)) hpost_no
              (wiresFrom (gs.take p0 ++ [gs[p0]]) (List.ofFn xA))
              (wiresFrom (gs.take p0 ++ [gs[p0]]) (List.ofFn xB))
              (by rw [wiresFrom_len, wiresFrom_len, List.length_ofFn, List.length_ofFn]) hmid_ag C.output hout0 hout_p0
            rw [← wiresFrom_append, ← wiresFrom_append] at hfin
            have hcat : gs.take p0 ++ [gs[p0]] ++ gs.drop (p0 + 1) = gs := by
              rw [List.append_assoc]; exact hsplit.symm
            rw [hcat, hgs_eval, hgs_eval] at hfin
            have h1 : hiF xA = true := rfl
            have h2 : hiF xB = false := rfl
            rw [h1, h2] at hfin
            exact Bool.noConfusion hfin
          obtain ⟨q, hpq, hqlt, hqin⟩ := hhit_wp0
          refine ⟨{p0, q}, Finset.card_pair (by omega), ?_⟩
          intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hp'
          · exact ⟨gs[p], List.getElem?_eq_getElem hp0, 0, h0in, by change 0 < 8 + p; omega, false, hstat0⟩
          · have rflp : p = q := Finset.mem_singleton.mp hp'
            subst rflp
            exact ⟨gs[p], List.getElem?_eq_getElem hqlt, 8 + p0, hqin, by change 8 + p0 < 8 + p; omega, cp0, hcp0⟩
    obtain ⟨S, hScard, hS⟩ := htwo
    have hcnt := elim_count 6 (init, []) gs hnok S hS
    have hsz7 : acc.2.length ≤ 7 := by
      have hgslen : gs.length = C.size := List.length_map _
      change acc.2.length + S.card ≤ 0 + gs.length at hcnt
      omega
    cases ho : acc.1.getD C.output (Sum.inl false) with
    | inr k =>
      apply c6_lb
      refine ⟨⟨acc.2, k⟩, elim_ok 6 gs (init, []) (fun _ h => by cases h), hsz7, ?_⟩
      intro y
      have hy := hval y
      rw [ho] at hy
      exact hy
    | inl b =>
      have h0 := hval (fun _ => false)
      have h1 := hval (fun _ => true)
      rw [ho] at h0 h1
      have hc0 : c6F (fun _ => false) = false := rfl
      have hc1 : c6F (fun _ => true) = true := rfl
      rw [hc0] at h0; rw [hc1] at h1
      exact Bool.noConfusion (h0.symm.trans h1)
  let mapGate : (ℕ → ℕ) → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun f g => ⟨g.op, g.inputs.map f⟩
  have mapGate_ok : ∀ (f : ℕ → ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), Ok g → Ok (mapGate f g) := by
    intro f g h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, by change (g.inputs.map f).length ≤ 2; rw [List.length_map]; exact h2⟩
  have trim_prefix :
      ∃ (P Q : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo P ∧
        PEqualNP.MetaComplexity.FanInTwo Q ∧
        1 ≤ P.size ∧ P.size ≤ 4 ∧ P.size + Q.size ≤ 13 ∧
        (∀ x : Fin 8 → Bool, (P.wires (List.ofFn x)).getD (7 + P.size) false = u0 x) ∧
        (∀ (x : Fin 8 → Bool) (b : Bool), Q.eval (P.wires (List.ofFn x) ++ [b]) = Q0.eval (w0 x ++ [b])) := by
    clear c6_lb case_r1 case_r2 case_r3 hi_lb
    let k := wire4 - 7
    have hk1 : 1 ≤ k := by omega
    have hkP0 : k ≤ P0.gates.length := by change wire4 < 8 + P0.gates.length at hw4hi; omega
    have hk4 : k ≤ 4 := by change P0.gates.length ≤ 4 at hP0le; omega
    let pre := P0.gates.take k
    let mid := P0.gates.drop k
    have hpre_len : pre.length = k := List.length_take_of_le hkP0
    have hmid_len : mid.length = P0.gates.length - k := List.length_drop
    let d := mid.length
    let remapMid : ℕ → ℕ := fun i => if i < 8 + k then i else i + 1
    let perm : ℕ → ℕ := fun i =>
      if i < 8 + k then i
      else if i < 8 + k + d then i + 1
      else if i = 8 + k + d then 8 + k
      else i
    let P : PEqualNP.CircuitLowerBounds.Circuit := ⟨pre, 0⟩
    let Q : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨mid.map (mapGate remapMid) ++ Q0.gates.map (mapGate perm), perm Q0.output⟩
    have hPfan : PEqualNP.MetaComplexity.FanInTwo P := fun g hg => hP0 g (List.mem_of_mem_take hg)
    have hQfan : PEqualNP.MetaComplexity.FanInTwo Q := by
      intro g hg
      rcases List.mem_append.mp hg with hm | hq
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hm
        exact mapGate_ok remapMid g0 (hP0 g0 (List.mem_of_mem_drop hg0))
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hq
        exact mapGate_ok perm g0 (hQ0 g0 hg0)
    have hmid_run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v1 v2 : List Bool) (b : Bool),
        v1.length = 8 + k →
        wiresFrom (gs.map (mapGate remapMid)) (v1 ++ [b] ++ v2) =
          v1 ++ [b] ++ (wiresFrom gs (v1 ++ v2)).drop (8 + k) ∧
        (wiresFrom gs (v1 ++ v2)).take (8 + k) = v1 := by
      intro gs
      induction gs with
      | nil =>
        intro v1 v2 b hv1
        exact ⟨by change v1 ++ [b] ++ v2 = v1 ++ [b] ++ (v1 ++ v2).drop (8 + k); rw [← hv1, List.drop_left],
               by change (v1 ++ v2).take (8 + k) = v1; rw [← hv1, List.take_left]⟩
      | cons g gs ih =>
        intro v1 v2 b hv1
        have hstep_val :
            (mapGate remapMid g).op.eval ((mapGate remapMid g).inputs.map fun i => (v1 ++ [b] ++ v2).getD i false) =
            g.op.eval (g.inputs.map fun i => (v1 ++ v2).getD i false) := by
          change g.op.eval ((g.inputs.map remapMid).map _) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          change (v1 ++ [b] ++ v2).getD (remapMid i) false = (v1 ++ v2).getD i false
          by_cases hlt : i < 8 + k
          · simp only [remapMid, ite_eq_left hlt, List.append_assoc]
            rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          · simp only [remapMid, ite_eq_right hlt]
            rw [List.append_assoc, List.getD_append_right v1 ([b] ++ v2) false (i + 1) (by omega),
                List.getD_append_right v1 v2 false i (by omega)]
            have hsub : i + 1 - v1.length = (i - v1.length) + 1 := by omega
            rw [hsub]
            rfl
        change wiresFrom (gs.map (mapGate remapMid)) ((v1 ++ [b] ++ v2) ++ [_]) = _ ∧ _
        rw [hstep_val]
        have h1 : (v1 ++ [b] ++ v2) ++ [g.op.eval (g.inputs.map fun i => (v1 ++ v2).getD i false)] =
            v1 ++ [b] ++ (v2 ++ [g.op.eval (g.inputs.map fun i => (v1 ++ v2).getD i false)]) := by
          rw [List.append_assoc]
        have h2 : (v1 ++ v2) ++ [g.op.eval (g.inputs.map fun i => (v1 ++ v2).getD i false)] =
            v1 ++ (v2 ++ [g.op.eval (g.inputs.map fun i => (v1 ++ v2).getD i false)]) := by
          rw [List.append_assoc]
        rw [h1]
        have res := ih v1 (v2 ++ [g.op.eval (g.inputs.map fun i => (v1 ++ v2).getD i false)]) b hv1
        rw [← h2] at res
        exact res
    have hperm_run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (vNew vOld : List Bool),
        vNew.length = vOld.length → 8 + k + d < vOld.length →
        (∀ i, vNew.getD (perm i) false = vOld.getD i false) →
        ∀ i, (wiresFrom (gs.map (mapGate perm)) vNew).getD (perm i) false = (wiresFrom gs vOld).getD i false := by
      intro gs
      induction gs with
      | nil => intro vNew vOld _ _ hag i; exact hag i
      | cons g gs ih =>
        intro vNew vOld hlen hbig hag
        have hval :
            (mapGate perm g).op.eval ((mapGate perm g).inputs.map fun i => vNew.getD i false) =
            g.op.eval (g.inputs.map fun i => vOld.getD i false) := by
          change g.op.eval ((g.inputs.map perm).map _) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hag i
        change ∀ i, (wiresFrom (gs.map (mapGate perm)) (vNew ++ [_])).getD (perm i) false =
          (wiresFrom gs (vOld ++ [_])).getD i false
        rw [hval]
        apply ih _ _ (by rw [List.length_append, List.length_append, hlen])
          (by rw [List.length_append, List.length_singleton]; omega)
        intro i
        by_cases hlt : i < vOld.length
        · have hplt : perm i < vNew.length := by
            simp only [perm]; split_ifs <;> omega
          rw [getD_snoc_lt _ _ _ _ hplt, getD_snoc_lt _ _ _ _ hlt]
          exact hag i
        · have hpi : perm i = i := by
            simp only [perm]
            rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
          rw [hpi]
          by_cases heq : i = vOld.length
          · rw [getD_snoc_eq _ _ _ _ (heq.trans hlen.symm), getD_snoc_eq _ _ _ _ heq]
          · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega),
                List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)]
    refine ⟨P, Q, hPfan, hQfan,
      by change 1 ≤ pre.length; rw [hpre_len]; omega,
      by change pre.length ≤ 4; rw [hpre_len]; omega,
      by change pre.length + (mid.map (mapGate remapMid) ++ Q0.gates.map (mapGate perm)).length ≤ 13
         rw [List.length_append, List.length_map, List.length_map, hpre_len, hmid_len]
         change P0.gates.length + Q0.gates.length ≤ 13 at hsum0; omega, ?_, ?_⟩
    · intro x
      have hP0sp : P0.gates = pre ++ mid := (List.take_append_drop k P0.gates).symm
      change (wiresFrom pre (List.ofFn x)).getD (7 + pre.length) false =
        (wiresFrom P0.gates (List.ofFn x)).getD wire4 false
      rw [hP0sp, wiresFrom_append, wiresFrom_getD_lt mid _ _ (by rw [wiresFrom_len, List.length_ofFn, hpre_len]; omega)]
      have hidx : 7 + pre.length = wire4 := by rw [hpre_len]; omega
      rw [hidx]
    · intro x b
      have hP0sp : P0.gates = pre ++ mid := (List.take_append_drop k P0.gates).symm
      have hpre_wlen : (wiresFrom pre (List.ofFn x)).length = 8 + k := by
        rw [wiresFrom_len, List.length_ofFn, hpre_len]
      change (wiresFrom (mid.map (mapGate remapMid) ++ Q0.gates.map (mapGate perm)) (wiresFrom pre (List.ofFn x) ++ [b])).getD (perm Q0.output) false =
        (wiresFrom Q0.gates (wiresFrom P0.gates (List.ofFn x) ++ [b])).getD Q0.output false
      rw [wiresFrom_append]
      have hm := hmid_run mid (wiresFrom pre (List.ofFn x)) [] b hpre_wlen
      simp only [List.append_nil] at hm
      rw [hm.1]
      have hP0w : wiresFrom P0.gates (List.ofFn x) = wiresFrom mid (wiresFrom pre (List.ofFn x)) := by
        rw [hP0sp, wiresFrom_append]
      rw [hP0w]
      let vPre := wiresFrom pre (List.ofFn x)
      let vAll := wiresFrom mid vPre
      have hvPre_len : vPre.length = 8 + k := hpre_wlen
      have hvAll_len : vAll.length = 8 + k + d := by
        rw [wiresFrom_len, hvPre_len]
      have hvAll_eq : vAll = vPre ++ vAll.drop (8 + k) := by
        conv_lhs => rw [← List.take_append_drop (8 + k) vAll]
        rw [hm.2]
      apply hperm_run Q0.gates (vPre ++ [b] ++ vAll.drop (8 + k)) (vAll ++ [b])
      · rw [List.length_append, List.length_append, List.length_append, List.length_singleton,
            List.length_drop, hvPre_len, hvAll_len]; omega
      · rw [List.length_append, List.length_singleton, hvAll_len]; omega
      · intro i
        by_cases h1 : i < 8 + k
        · simp only [perm, ite_eq_left h1, List.append_assoc]
          rw [List.getD_append _ _ _ _ (by omega)]
          conv_rhs => rw [hvAll_eq, List.append_assoc]
          rw [List.getD_append _ _ _ _ (by omega)]
        · by_cases h2 : i < 8 + k + d
          · simp only [perm, ite_eq_right h1, ite_eq_left h2]
            rw [List.append_assoc, List.getD_append_right vPre ([b] ++ vAll.drop (8 + k)) false (i + 1) (by omega)]
            have hsub : i + 1 - vPre.length = (i - (8 + k)) + 1 := by omega
            rw [hsub]
            change (vAll.drop (8 + k)).getD (i - (8 + k)) false = (vAll ++ [b]).getD i false
            rw [getD_snoc_lt _ _ _ _ (by omega)]
            conv_rhs => rw [hvAll_eq]
            rw [List.getD_append_right _ _ _ _ (by omega), hvPre_len]
          · by_cases h3 : i = 8 + k + d
            · simp only [perm, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
              rw [List.append_assoc, List.getD_append_right vPre ([b] ++ vAll.drop (8 + k)) false (8 + k) (by omega)]
              have hsub : 8 + k - vPre.length = 0 := by omega
              rw [hsub]
              change b = (vAll ++ [b]).getD i false
              rw [getD_snoc_eq _ _ _ _ (by omega)]
            · simp only [perm, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
              rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_append, List.length_singleton, List.length_drop, hvPre_len, hvAll_len]; omega),
                  List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hvAll_len]; omega)]
  have delete_dead_gate :
      ∀ (n : ℕ) (q : PEqualNP.CircuitLowerBounds.Circuit) (idx : ℕ),
        PEqualNP.MetaComplexity.FanInTwo q →
        idx < q.gates.length →
        q.output ≠ n + 1 + idx →
        (∀ (j : ℕ), idx < j → ∀ (hj : j < q.gates.length), (n + 1 + idx) ∉ (normGate q.gates[j]).inputs) →
        ∃ q' : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo q' ∧ q'.size + 1 = q.size ∧
          ∀ v : List Bool, v.length = n + 1 → q'.eval v = q.eval v := by
    clear c6_lb case_r1 case_r2 case_r3 P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0 hi_lb trim_prefix
    intro n q idx hqfan hidx hout hno
    let m := n + 1 + idx
    let B := n + 1 + q.gates.length
    let delW : ℕ → ℕ := fun a => if a < m then a else if a = m then B else a - 1
    let pre := q.gates.take idx
    let post := q.gates.drop (idx + 1)
    have hqsp : q.gates = pre ++ q.gates[idx] :: post := by
      have h1 := List.take_append_drop idx q.gates
      have h2 : q.gates.drop idx = q.gates[idx] :: post := List.drop_eq_getElem_cons hidx
      rw [h2] at h1; exact h1.symm
    let q' : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨pre.map (mapGate delW) ++ post.map (mapGate delW), delW q.output⟩
    have hq'fan : PEqualNP.MetaComplexity.FanInTwo q' := by
      intro g hg
      rcases List.mem_append.mp hg with hp | hp
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hp
        exact mapGate_ok delW g0 (hqfan g0 (List.mem_of_mem_take hg0))
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hp
        exact mapGate_ok delW g0 (hqfan g0 (List.mem_of_mem_drop hg0))
    have hq'sz : q'.size + 1 = q.size := by
      change (pre.map (mapGate delW) ++ post.map (mapGate delW)).length + 1 = q.gates.length
      rw [List.length_append, List.length_map, List.length_map, List.length_take_of_le (Nat.le_of_lt hidx), List.length_drop]
      omega
    refine ⟨q', hq'fan, hq'sz, ?_⟩
    intro v hvlen
    have hpre_eq : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        w.length + gs.length ≤ m →
        wiresFrom (gs.map (mapGate delW)) w = wiresFrom gs w := by
      intro gs
      induction gs with
      | nil => intro w _; rfl
      | cons g gs ih =>
        intro w hle
        have hval :
            (mapGate delW g).op.eval ((mapGate delW g).inputs.map fun i => w.getD i false) =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          change g.op.eval ((g.inputs.map delW).map _) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          change w.getD (delW i) false = w.getD i false
          by_cases hlt : i < w.length
          · have him : i < m := by rw [List.length_cons] at hle; omega
            simp only [delW, ite_eq_left him]
          · have hd : w.length ≤ delW i := by
              simp only [delW]; split_ifs <;> (rw [List.length_cons] at hle; omega)
            rw [List.getD_eq_default _ _ hd, List.getD_eq_default _ _ (by omega)]
        change wiresFrom (gs.map (mapGate delW)) (w ++ [_]) = wiresFrom gs (w ++ [_])
        rw [hval]
        apply ih _ (by rw [List.length_append, List.length_singleton]; rw [List.length_cons] at hle; omega)
    have hpost_run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (wNew wOld : List Bool),
        (∀ g ∈ gs, Ok g ∧ m ∉ (normGate g).inputs) →
        wOld.length = wNew.length + 1 → m < wOld.length → wOld.length + gs.length ≤ B →
        (∀ a, a ≠ m → wNew.getD (delW a) false = wOld.getD a false) →
        ∀ a, a ≠ m → (wiresFrom (gs.map (mapGate delW)) wNew).getD (delW a) false =
          (wiresFrom gs wOld).getD a false := by
      intro gs
      induction gs with
      | nil => intro wNew wOld _ _ _ _ hag a ha; exact hag a ha
      | cons g gs ih =>
        intro wNew wOld hok hlen hmlt hBle hag
        obtain ⟨hgok, hgno⟩ := hok g List.mem_cons_self
        have hval :
            (mapGate delW g).op.eval ((mapGate delW g).inputs.map fun i => wNew.getD i false) =
            g.op.eval (g.inputs.map fun i => wOld.getD i false) := by
          rw [← normGate_eval (mapGate delW g), ← normGate_eval g]
          have hnm : (normGate (mapGate delW g)).inputs = (normGate g).inputs.map delW := by
            obtain ⟨op, ins⟩ := g
            cases op
            · rfl
            · rfl
            · exact List.map_take.symm
            · rfl
            · rfl
          have hnop : (normGate (mapGate delW g)).op = (normGate g).op := by
            obtain ⟨op, ins⟩ := g
            cases op <;> rfl
          rw [hnop, hnm, List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hag i (fun heq => hgno (heq ▸ hi))
        change ∀ a, a ≠ m → (wiresFrom (gs.map (mapGate delW)) (wNew ++ [_])).getD (delW a) false =
          (wiresFrom gs (wOld ++ [_])).getD a false
        rw [hval]
        apply ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
          (by rw [List.length_append, List.length_append, List.length_singleton, hlen])
          (by rw [List.length_append, List.length_singleton]; omega)
          (by rw [List.length_append, List.length_singleton]; rw [List.length_cons] at hBle; omega)
        intro a ha
        by_cases hlt : a < m
        · simp only [delW, ite_eq_left hlt]
          rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ (by omega)]
          have h1 := hag a ha
          simp only [delW, ite_eq_left hlt] at h1
          exact h1
        · simp only [delW, ite_eq_right hlt, ite_eq_right ha]
          by_cases hlt2 : a < wOld.length
          · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ hlt2]
            have h1 := hag a ha
            simp only [delW, ite_eq_right hlt, ite_eq_right ha] at h1
            exact h1
          · by_cases heq2 : a = wOld.length
            · rw [getD_snoc_eq _ _ _ _ (by omega), getD_snoc_eq _ _ _ _ heq2]
            · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega),
                  List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)]
    change (wiresFrom (pre.map (mapGate delW) ++ post.map (mapGate delW)) v).getD (delW q.output) false =
      (wiresFrom q.gates v).getD q.output false
    conv_rhs => rw [hqsp]
    rw [wiresFrom_append, wiresFrom_append]
    have hpe : wiresFrom (pre.map (mapGate delW)) v = wiresFrom pre v := by
      apply hpre_eq
      rw [hvlen, List.length_take_of_le (Nat.le_of_lt hidx)]
    rw [hpe]
    let wPre := wiresFrom pre v
    have hwPre_len : wPre.length = m := by
      rw [wiresFrom_len, hvlen, List.length_take_of_le (Nat.le_of_lt hidx)]
    have hpost_ok : ∀ g ∈ post, Ok g ∧ m ∉ (normGate g).inputs := by
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
      rw [List.getElem_drop]
      have hklt : idx + 1 + k < q.gates.length := by rw [List.length_drop] at hk; omega
      exact ⟨hqfan _ (List.getElem_mem hklt), hno (idx + 1 + k) (by omega) hklt⟩
    change (wiresFrom (post.map (mapGate delW)) wPre).getD (delW q.output) false =
      (wiresFrom post (wPre ++ [_])).getD q.output false
    apply hpost_run post wPre (wPre ++ [_]) hpost_ok
      (by rw [List.length_append, List.length_singleton])
      (by rw [List.length_append, List.length_singleton, hwPre_len]; omega)
      (by rw [List.length_append, List.length_singleton, hwPre_len, List.length_drop]; omega)
    · intro a ha
      by_cases hlt : a < m
      · simp only [delW, ite_eq_left hlt]
        rw [getD_snoc_lt _ _ _ _ (by omega)]
      · simp only [delW, ite_eq_right hlt, ite_eq_right ha]
        rw [List.getD_eq_default _ _ (by omega),
            List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hwPre_len]; omega)]
    · exact hout
  have main_ind : ∀ (m : ℕ) (P Q : PEqualNP.CircuitLowerBounds.Circuit),
      Q.size = m →
      PEqualNP.MetaComplexity.FanInTwo P →
      PEqualNP.MetaComplexity.FanInTwo Q →
      1 ≤ P.size → P.size ≤ 4 → P.size + Q.size ≤ 13 →
      (∀ x : Fin 8 → Bool, edgeF x = false → (x 0 || x 3) = true →
        (P.wires (List.ofFn x)).getD (7 + P.size) false = false) →
      (∀ x : Fin 8 → Bool, Q.eval (P.wires (List.ofFn x) ++ [(P.wires (List.ofFn x)).getD (7 + P.size) false]) = edgeF x) →
      ∃ x : Fin 8 → Bool, Q.eval (P.wires (List.ofFn x) ++ [true]) ≠ hiF x := by
    clear P0 Q0 wire4 hP0 hQ0 hP0le hsum0 hw4lo hw4hi w0 u0 hu0 hlow0 trim_prefix
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro P Q hQm hPfan hQfan hP1 hP4 hsum hu hlow
      let n := 8 + P.size
      let r := Q.gates.countP (reads n)
      by_cases hr1 : r = 1
      · exact case_r1 P Q hPfan hQfan hP1 hP4 hsum hr1 hu hlow
      by_cases hr2 : r = 2
      · exact case_r2 P Q hPfan hQfan hP1 hP4 hsum hr2 hu hlow
      by_contra! hhigh
      let gs := Q.gates.map normGate
      have hnok : ∀ g ∈ gs, NOk g := by
        intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        exact normGate_nok g0 (hQfan g0 hg0)
      have hPwlen : ∀ x : Fin 8 → Bool, (P.wires (List.ofFn x)).length = n := by
        intro x
        change (wiresFrom P.gates (List.ofFn x)).length = n
        rw [wiresFrom_len, List.length_ofFn]; rfl
      have hQgs_eval : ∀ (x : Fin 8 → Bool) (b : Bool),
          (wiresFrom gs (P.wires (List.ofFn x) ++ [b])).getD Q.output false = Q.eval (P.wires (List.ofFn x) ++ [b]) := by
        intro x b
        change (wiresFrom (Q.gates.map normGate) _).getD Q.output false = _
        rw [wiresFrom_norm]; rfl
      by_cases hr0 : r = 0
      · have hnone : ∀ g ∈ gs, n ∉ g.inputs := by
          intro g hg
          obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
          have hrf : ¬reads n g0 = true := List.countP_eq_zero.mp hr0 g0 hg0
          intro hmem
          exact hrf ((reads_iff n g0 (hQfan g0 hg0)).mpr hmem)
        have hout_ne : Q.output ≠ n := by
          intro heq
          have h0 := hhigh (fun _ => false)
          rw [← hQgs_eval, heq, wiresFrom_getD_lt _ _ _ (by rw [List.length_append, List.length_singleton, hPwlen]; omega),
              getD_snoc_eq _ _ _ _ (hPwlen _).symm] at h0
          have hhi0 : hiF (fun _ => false) = false := rfl
          rw [hhi0] at h0; exact Bool.noConfusion h0
        let x0 : Fin 8 → Bool := fun i => decide (i = 0)
        have hsame := cut_agree n gs hnone (P.wires (List.ofFn x0) ++ [(P.wires (List.ofFn x0)).getD (7 + P.size) false])
          (P.wires (List.ofFn x0) ++ [true])
          (by rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]) (by
            intro i hi
            rw [getD_snoc_ne _ _ _ _ (by rw [hPwlen]; exact hi),
                getD_snoc_ne _ _ _ _ (by rw [hPwlen]; exact hi)]) Q.output hout_ne
        rw [hQgs_eval, hQgs_eval, hlow x0, hhigh x0] at hsame
        have h1 : edgeF x0 = false := rfl
        have h2 : hiF x0 = true := rfl
        rw [h1, h2] at hsame; exact Bool.noConfusion hsame
      let initP : List (Bool ⊕ ℕ) := (List.range n).map Sum.inr ++ [Sum.inl true]
      let acc := elim 8 gs (initP, P.gates)
      have hinit_len : initP.length = n + 1 := by
        rw [List.length_append, List.length_map, List.length_range, List.length_singleton]
      have hacc_inv : ∀ x : Fin 8 → Bool, Inv 8 (List.ofFn x) (wiresFrom gs (P.wires (List.ofFn x) ++ [true])) acc := by
        intro x
        apply elim_inv 8 (List.ofFn x) gs _ (initP, P.gates) (fun g hg => (hnok g hg).1)
        refine ⟨List.length_ofFn, by rw [hinit_len, List.length_append, List.length_singleton, hPwlen], ?_⟩
        intro i
        rcases Nat.lt_trichotomy i n with hlt | heq | hgt
        · rw [getD_snoc_lt _ _ _ _ (by rw [List.length_map, List.length_range]; exact hlt),
              getD_snoc_lt _ _ _ _ (by rw [hPwlen]; exact hlt)]
          rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hlt),
              List.getElem_map, List.getElem_range]
          exact ⟨hlt, rfl⟩
        · subst heq
          rw [getD_snoc_eq _ _ _ _ (by rw [List.length_map, List.length_range]),
              getD_snoc_eq _ _ _ _ (hPwlen x).symm]
          exact ⟨trivial, rfl⟩
        · rw [List.getD_eq_default _ _ (by rw [hinit_len]; omega),
              List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hPwlen]; omega)]
          exact ⟨trivial, rfl⟩
      have hacc_val : ∀ x : Fin 8 → Bool,
          statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD Q.output (Sum.inl false)) = hiF x := by
        intro x
        have h1 := ((hacc_inv x).2.2 Q.output).2
        rw [hQgs_eval, hhigh x] at h1
        exact h1
      have hacc_ge10 : 10 ≤ acc.2.length := by
        by_contra! hle9
        cases ho : acc.1.getD Q.output (Sum.inl false) with
        | inr k =>
          apply hi_lb
          refine ⟨⟨acc.2, k⟩, elim_ok 8 gs (initP, P.gates) hPfan, by change acc.2.length ≤ 9; omega, ?_⟩
          intro x
          have hx := hacc_val x
          rw [ho] at hx; exact hx
        | inl b =>
          have h0 := hacc_val (fun _ => false)
          have h1 := hacc_val (fun _ => true)
          rw [ho] at h0 h1
          have hf0 : hiF (fun _ => false) = false := rfl
          have hf1 : hiF (fun _ => true) = true := rfl
          rw [hf0] at h0; rw [hf1] at h1
          exact Bool.noConfusion (h0.symm.trans h1)
      have hstat_n : acc.1.getD n (Sum.inl false) = Sum.inl true := by
        rw [elim_getD 8 n _ gs (initP, P.gates) (by rw [hinit_len]; omega)]
        exact getD_snoc_eq _ _ _ _ (by rw [List.length_map, List.length_range])
      let isR : ℕ → Bool := fun idx =>
        Option.elim Q.gates[idx]? false (reads n)
      let SR : Finset ℕ := (Finset.range Q.gates.length).filter (fun idx => isR idx = true)
      have hSR_card : SR.card = r := by
        have h1 : Q.gates.countP (reads n) =
            (Finset.univ.filter (fun i : Fin Q.gates.length => reads n (Q.gates.get i))).card := by
          have h := List.countP_ofFn (fun i : Fin Q.gates.length => Q.gates.get i) (reads n)
          simpa only [List.ofFn_get] using h
        rw [show r = Q.gates.countP (reads n) from rfl, h1]
        symm
        apply Finset.card_bij (fun (i : Fin Q.gates.length) _ => i.val)
        · intro i hi
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨i.isLt, ?_⟩
          dsimp only [isR]
          rw [List.getElem?_eq_getElem i.isLt]
          exact (Finset.mem_filter.mp hi).2
        · intro i1 _ i2 _ heq; exact Fin.ext heq
        · intro idx hidx
          rw [Finset.mem_filter, Finset.mem_range] at hidx
          refine ⟨⟨idx, hidx.1⟩, ?_, rfl⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have h2 : isR idx = true := hidx.2
          dsimp only [isR] at h2
          rw [List.getElem?_eq_getElem hidx.1] at h2
          exact h2
      have hSR_ok : ∀ p ∈ SR, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < initP.length + p ∧
          ∃ c, acc.1.getD a (Sum.inl false) = Sum.inl c := by
        intro p hp
        rw [Finset.mem_filter, Finset.mem_range] at hp
        have h2 : isR p = true := hp.2
        dsimp only [isR] at h2
        rw [List.getElem?_eq_getElem hp.1] at h2
        refine ⟨normGate Q.gates[p], ?_, n, (reads_iff n Q.gates[p] (hQfan _ (List.getElem_mem hp.1))).mp h2,
          by omega, true, hstat_n⟩
        rw [List.getElem?_map, List.getElem?_eq_getElem hp.1]; rfl
      have hr_le3 : r ≤ 3 := by
        have hcnt := elim_count 8 (initP, P.gates) gs hnok SR hSR_ok
        have hgslen : gs.length = Q.size := List.length_map _
        change acc.2.length + SR.card ≤ P.size + gs.length at hcnt
        omega
      have hr3 : r = 3 := by omega
      have hsum13 : P.size + Q.size = 13 := by
        have hcnt := elim_count 8 (initP, P.gates) gs hnok SR hSR_ok
        have hgslen : gs.length = Q.size := List.length_map _
        change acc.2.length + SR.card ≤ P.size + gs.length at hcnt
        omega
      have hall_and : ∀ g ∈ Q.gates, reads n g = true → g.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
        by_contra! hbad
        obtain ⟨g0, hg0mem, hg0r, hg0ne⟩ := hbad
        obtain ⟨idx0, hidx0, rfl⟩ := List.mem_iff_getElem.mp hg0mem
        let isConst : ℕ → Bool := fun j =>
          Sum.elim (fun _ => true) (fun _ => false) (acc.1.getD (n + 1 + j) (Sum.inl false))
        let K : Finset ℕ := (Finset.range Q.gates.length).filter (fun j => isConst j = true)
        have hidx0_K : idx0 ∈ K := by
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨hidx0, ?_⟩
          have hidx0_gs : idx0 < gs.length := by rw [List.length_map]; exact hidx0
          have hsp : gs = gs.take idx0 ++ gs[idx0] :: gs.drop (idx0 + 1) := by
            have h1 := List.take_append_drop idx0 gs
            have h2 : gs.drop idx0 = gs[idx0] :: gs.drop (idx0 + 1) := List.drop_eq_getElem_cons hidx0_gs
            rw [h2] at h1; exact h1.symm
          have hstep : acc = elim 8 (gs.drop (idx0 + 1)) (elimStep 8 (elim 8 (gs.take idx0) (initP, P.gates)) gs[idx0]) := by
            change elim 8 gs (initP, P.gates) = _
            conv_lhs => rw [hsp]
            rw [elim_append]; rfl
          have hlen_pre : (elim 8 (gs.take idx0) (initP, P.gates)).1.length = n + 1 + idx0 := by
            rw [elim_fst_len, hinit_len, List.length_take_of_le (Nat.le_of_lt hidx0_gs)]
          have hget : acc.1.getD (n + 1 + idx0) (Sum.inl false) =
              (simplify gs[idx0].op (8 + (elim 8 (gs.take idx0) (initP, P.gates)).2.length)
                (gs[idx0].inputs.map fun i => (elim 8 (gs.take idx0) (initP, P.gates)).1.getD i (Sum.inl false))).2 := by
            rw [hstep, elim_getD 8 (n + 1 + idx0) _ _ _ (by change n + 1 + idx0 < ((elim 8 (gs.take idx0) (initP, P.gates)).1 ++ [_]).length; rw [List.length_append, List.length_singleton, hlen_pre]; omega)]
            exact getD_snoc_eq _ _ _ _ hlen_pre.symm
          have hn_in : n ∈ gs[idx0].inputs := by
            have h1 := (reads_iff n Q.gates[idx0] (hQfan _ (List.getElem_mem hidx0))).mp hg0r
            have h2 : gs[idx0] = normGate Q.gates[idx0] := List.getElem_map _
            rw [h2]; exact h1
          have hpre_n : (elim 8 (gs.take idx0) (initP, P.gates)).1.getD n (Sum.inl false) = Sum.inl true := by
            rw [elim_getD 8 n _ _ _ (by rw [hinit_len]; omega)]
            exact getD_snoc_eq _ _ _ _ (by rw [List.length_map, List.length_range])
          have hmem_true : Sum.inl true ∈
              gs[idx0].inputs.map (fun i => (elim 8 (gs.take idx0) (initP, P.gates)).1.getD i (Sum.inl false)) :=
            List.mem_map.mpr ⟨n, hn_in, hpre_n⟩
          have hop_g : gs[idx0].op = .or ∨ gs[idx0].op = .not := by
            have h1 := (hQfan _ (List.getElem_mem hidx0)).1
            have h2 : gs[idx0].op = Q.gates[idx0].op := by
              have h3 : gs[idx0] = normGate Q.gates[idx0] := List.getElem_map _
              rw [h3]
              cases hqop : Q.gates[idx0].op <;> simp only [normGate, hqop]
            rw [h2]
            rcases h1 with h | h | h
            · exact (hg0ne h).elim
            · exact Or.inl h
            · exact Or.inr h
          have hconst : ∃ c, acc.1.getD (n + 1 + idx0) (Sum.inl false) = Sum.inl c := by
            rw [hget]
            rcases hop_g with hor | hnot
            · rw [hor]
              exact simplify_or_true _ _ (by rw [List.length_map]; exact (hnok _ (List.getElem_mem hidx0_gs)).1.2) hmem_true
            · rw [hnot]
              exact simplify_not_const _ _ true (by rw [List.length_map]; exact (hnok _ (List.getElem_mem hidx0_gs)).2 hnot) hmem_true
          obtain ⟨c, hc⟩ := hconst
          change Sum.elim (fun _ => true) (fun _ => false) (acc.1.getD (n + 1 + idx0) (Sum.inl false)) = true
          rw [hc]; rfl
        have hK_nonempty : K.Nonempty := ⟨idx0, hidx0_K⟩
        let idxMax := K.max' hK_nonempty
        have hidxMax_mem : idxMax ∈ K := Finset.max'_mem K hK_nonempty
        have hidxMax_lt : idxMax < Q.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hidxMax_mem).1
        have hidxMax_const : ∃ c, acc.1.getD (n + 1 + idxMax) (Sum.inl false) = Sum.inl c := by
          have hc := (Finset.mem_filter.mp hidxMax_mem).2
          cases h : acc.1.getD (n + 1 + idxMax) (Sum.inl false) with
          | inl c => exact ⟨c, rfl⟩
          | inr j =>
            change Sum.elim (fun _ => true) (fun _ => false) (acc.1.getD (n + 1 + idxMax) (Sum.inl false)) = true at hc
            rw [h] at hc; exact Bool.noConfusion hc
        obtain ⟨cMax, hcMax⟩ := hidxMax_const
        have hout_ne_max : Q.output ≠ n + 1 + idxMax := by
          intro heq
          have h0 := hacc_val (fun _ => false)
          have h1 := hacc_val (fun _ => true)
          rw [heq, hcMax] at h0 h1
          have hf0 : hiF (fun _ => false) = false := rfl
          have hf1 : hiF (fun _ => true) = true := rfl
          rw [hf0] at h0; rw [hf1] at h1
          exact Bool.noConfusion (h0.symm.trans h1)
        have hno_later : ∀ (j : ℕ), idxMax < j → ∀ (hj : j < Q.gates.length), (n + 1 + idxMax) ∉ (normGate Q.gates[j]).inputs := by
          intro j hjgt hjlt hmem
          have hj_notK : j ∉ K := fun hjK => Nat.not_lt_of_ge (Finset.le_max' K j hjK) hjgt
          by_cases hjSR : j ∈ SR
          · exfalso
            apply hj_notK
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨hjlt, ?_⟩
            have hj_gs : j < gs.length := by rw [List.length_map]; exact hjlt
            have hgj_eq : gs[j] = normGate Q.gates[j] := List.getElem_map _
            have hjr : reads n Q.gates[j] = true := by
              have h1 : isR j = true := (Finset.mem_filter.mp hjSR).2
              dsimp only [isR] at h1
              rw [List.getElem?_eq_getElem hjlt] at h1; exact h1
            have hn_in : n ∈ gs[j].inputs := by
              rw [hgj_eq]
              exact (reads_iff n Q.gates[j] (hQfan _ (List.getElem_mem hjlt))).mp hjr
            have hm_in : (n + 1 + idxMax) ∈ gs[j].inputs := by rw [hgj_eq]; exact hmem
            have hgj_all : ∀ a ∈ gs[j].inputs, a = n ∨ a = n + 1 + idxMax := by
              have hlen2 : gs[j].inputs.length ≤ 2 := (hnok gs[j] (List.getElem_mem hj_gs)).1.2
              rcases h : gs[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
              · rw [h] at hn_in; cases hn_in
              · rw [h] at hn_in hm_in
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hn_in hm_in
                omega
              · rw [h] at hn_in hm_in
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hn_in hm_in
                intro x hx
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hn_in with rfl | rfl <;> rcases hm_in with hma | hmb <;> omega
              · rw [h] at hlen2; simp only [List.length_cons] at hlen2; omega
            have hsp : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
              have h1 := List.take_append_drop j gs
              have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj_gs
              rw [h2] at h1; exact h1.symm
            have hstep : acc = elim 8 (gs.drop (j + 1)) (elimStep 8 (elim 8 (gs.take j) (initP, P.gates)) gs[j]) := by
              change elim 8 gs (initP, P.gates) = _
              conv_lhs => rw [hsp]
              rw [elim_append]; rfl
            have hlen_pre : (elim 8 (gs.take j) (initP, P.gates)).1.length = n + 1 + j := by
              rw [elim_fst_len, hinit_len, List.length_take_of_le (Nat.le_of_lt hj_gs)]
            have hget : acc.1.getD (n + 1 + j) (Sum.inl false) =
                (simplify gs[j].op (8 + (elim 8 (gs.take j) (initP, P.gates)).2.length)
                  (gs[j].inputs.map fun i => (elim 8 (gs.take j) (initP, P.gates)).1.getD i (Sum.inl false))).2 := by
              rw [hstep, elim_getD 8 (n + 1 + j) _ _ _ (by change n + 1 + j < ((elim 8 (gs.take j) (initP, P.gates)).1 ++ [_]).length; rw [List.length_append, List.length_singleton, hlen_pre]; omega)]
              exact getD_snoc_eq _ _ _ _ hlen_pre.symm
            have hconst : ∃ c, acc.1.getD (n + 1 + j) (Sum.inl false) = Sum.inl c := by
              rw [hget]
              have hop : gs[j].op = .and ∨ gs[j].op = .or ∨ gs[j].op = .not := by
                rcases (hnok _ (List.getElem_mem hj_gs)).1.1 with h | h | h
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr h)
              apply simplify_all_const _ _ _ hop (by rw [List.length_map]; exact (hnok _ (List.getElem_mem hj_gs)).1.2)
              intro s hs
              obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
              rcases hgj_all a ha with rfl | rfl
              · rw [elim_getD 8 n _ _ _ (by rw [hinit_len]; omega)]
                exact ⟨true, getD_snoc_eq _ _ _ _ (by rw [List.length_map, List.length_range])⟩
              · have hpre_m : (elim 8 (gs.take j) (initP, P.gates)).1.getD (n + 1 + idxMax) (Sum.inl false) = Sum.inl cMax := by
                  have h1 : acc.1.getD (n + 1 + idxMax) (Sum.inl false) =
                      (elim 8 (gs.take j) (initP, P.gates)).1.getD (n + 1 + idxMax) (Sum.inl false) := by
                    rw [hstep, elim_getD 8 (n + 1 + idxMax) _ _ _ (by change n + 1 + idxMax < ((elim 8 (gs.take j) (initP, P.gates)).1 ++ [_]).length; rw [List.length_append, List.length_singleton, hlen_pre]; omega)]
                    exact getD_snoc_ne _ _ _ _ (by omega)
                  rw [← h1, hcMax]
                exact ⟨cMax, hpre_m⟩
            obtain ⟨cj, hcj⟩ := hconst
            change Sum.elim (fun _ => true) (fun _ => false) (acc.1.getD (n + 1 + j) (Sum.inl false)) = true
            rw [hcj]; rfl
          · exfalso
            let S4 := insert j SR
            have hS4_card : S4.card = 4 := by
              rw [Finset.card_insert_of_notMem hjSR, hSR_card, hr3]
            have hS4_ok : ∀ p ∈ S4, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < initP.length + p ∧
                ∃ c, acc.1.getD a (Sum.inl false) = Sum.inl c := by
              intro p hp
              rcases Finset.mem_insert.mp hp with rfl | hpSR
              · refine ⟨normGate Q.gates[p], ?_, n + 1 + idxMax, hmem, by omega, cMax, hcMax⟩
                rw [List.getElem?_map, List.getElem?_eq_getElem hjlt]; rfl
              · exact hSR_ok p hpSR
            have hcnt := elim_count 8 (initP, P.gates) gs hnok S4 hS4_ok
            have hgslen : gs.length = Q.size := List.length_map _
            change acc.2.length + S4.card ≤ P.size + gs.length at hcnt
            omega
        obtain ⟨Q', hQ'fan, hQ'sz, hQ'eval⟩ := delete_dead_gate n Q idxMax hQfan hidxMax_lt hout_ne_max hno_later
        have hQ'lt : Q'.size < m := by omega
        obtain ⟨x, hx⟩ := ih Q'.size hQ'lt P Q' rfl hPfan hQ'fan hP1 hP4 (by omega) hu (by
          intro x
          rw [hQ'eval _ (by rw [List.length_append, List.length_singleton, hPwlen])]
          exact hlow x)
        exact hx ((hQ'eval _ (by rw [List.length_append, List.length_singleton, hPwlen])).trans (hhigh x))
      have hreads_u : ∃ g ∈ Q.gates, 7 + P.size ∈ g.inputs := by
        by_contra! hno_u
        have hno_u_gs : ∀ g ∈ gs, (7 + P.size) ∉ g.inputs := by
          intro g hg
          obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
          have h1 := hno_u g0 hg0
          obtain ⟨op, ins⟩ := g0
          cases op
          · exact h1
          · exact h1
          · intro hm; exact h1 (List.mem_of_mem_take hm)
          · exact h1
          · exact h1
        have hout_ne_u : Q.output ≠ 7 + P.size := by
          intro heq
          let x0 : Fin 8 → Bool := fun i => decide (i = 0)
          have h1 := hhigh x0
          rw [← hQgs_eval, heq, wiresFrom_getD_lt _ _ _ (by rw [List.length_append, List.length_singleton, hPwlen]; omega),
              getD_snoc_lt _ _ _ _ (by rw [hPwlen]; omega)] at h1
          have hu0' := hu x0 rfl rfl
          have hhi0 : hiF x0 = true := rfl
          rw [hu0', hhi0] at h1
          exact Bool.noConfusion h1
        let Pdrop := P.gates.dropLast
        have hPdrop_len : Pdrop.length + 1 = P.size := by
          change P.gates.dropLast.length + 1 = P.gates.length
          rw [List.length_dropLast]
          change 1 ≤ P.gates.length at hP1
          omega
        let initD : List (Bool ⊕ ℕ) :=
          (List.range (7 + P.size)).map Sum.inr ++ [Sum.inl false, Sum.inl true]
        let accD := elim 8 gs (initD, Pdrop)
        have hinitD_len : initD.length = n + 1 := by
          rw [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_singleton]; omega
        have haccD_inv : ∀ x : Fin 8 → Bool,
            Inv 8 (List.ofFn x) (wiresFrom gs (wiresFrom Pdrop (List.ofFn x) ++ [false, true])) accD := by
          intro x
          apply elim_inv 8 (List.ofFn x) gs _ (initD, Pdrop) (fun g hg => (hnok g hg).1)
          have hlenD : (wiresFrom Pdrop (List.ofFn x)).length = 7 + P.size := by
            rw [wiresFrom_len, List.length_ofFn]; omega
          refine ⟨List.length_ofFn, by rw [hinitD_len, List.length_append, hlenD, List.length_cons, List.length_singleton]; omega, ?_⟩
          intro i
          by_cases h1 : i < 7 + P.size
          · have hlt1 : i < ((List.range (7 + P.size)).map (Sum.inr : ℕ → Bool ⊕ ℕ)).length := by
              rw [List.length_map, List.length_range]; exact h1
            rw [List.getD_append _ _ _ _ hlt1, List.getD_append _ _ _ _ (by omega)]
            rw [List.getD_eq_getElem _ _ hlt1, List.getElem_map, List.getElem_range]
            exact ⟨by change i < 8 + Pdrop.length; omega, rfl⟩
          · by_cases h2 : i = 7 + P.size
            · subst h2
              rw [List.getD_append_right _ _ _ _ (by rw [List.length_map, List.length_range]),
                  List.getD_append_right _ _ _ _ (by omega)]
              have hs1 : 7 + P.size - ((List.range (7 + P.size)).map (Sum.inr : ℕ → Bool ⊕ ℕ)).length = 0 := by
                rw [List.length_map, List.length_range]; omega
              have hs2 : 7 + P.size - (wiresFrom Pdrop (List.ofFn x)).length = 0 := by omega
              rw [hs1, hs2]; exact ⟨trivial, rfl⟩
            · by_cases h3 : i = 8 + P.size
              · subst h3
                rw [List.getD_append_right _ _ _ _ (by rw [List.length_map, List.length_range]; omega),
                    List.getD_append_right _ _ _ _ (by omega)]
                have hs1 : 8 + P.size - ((List.range (7 + P.size)).map (Sum.inr : ℕ → Bool ⊕ ℕ)).length = 1 := by
                  rw [List.length_map, List.length_range]; omega
                have hs2 : 8 + P.size - (wiresFrom Pdrop (List.ofFn x)).length = 1 := by omega
                rw [hs1, hs2]; exact ⟨trivial, rfl⟩
              · rw [List.getD_eq_default _ _ (by rw [hinitD_len]; omega),
                    List.getD_eq_default _ _ (by rw [List.length_append, hlenD, List.length_cons, List.length_singleton]; omega)]
                exact ⟨trivial, rfl⟩
        have haccD_val : ∀ x : Fin 8 → Bool,
            statVal (wiresFrom accD.2 (List.ofFn x)) (accD.1.getD Q.output (Sum.inl false)) = hiF x := by
          intro x
          have h1 := ((haccD_inv x).2.2 Q.output).2
          have hPne : P.gates ≠ [] := by intro h; change 1 ≤ P.gates.length at hP1; rw [h] at hP1; exact absurd hP1 (by decide)
          have hPsp : P.gates = Pdrop ++ [P.gates.getLast hPne] :=
            (List.dropLast_append_getLast hPne).symm
          have hPw_eq : P.wires (List.ofFn x) ++ [true] =
              wiresFrom Pdrop (List.ofFn x) ++
                [(P.gates.getLast hPne).op.eval ((P.gates.getLast hPne).inputs.map fun i => (wiresFrom Pdrop (List.ofFn x)).getD i false), true] := by
            change wiresFrom P.gates (List.ofFn x) ++ [true] = _
            conv_lhs => rw [hPsp, wiresFrom_append]
            change (wiresFrom Pdrop (List.ofFn x) ++ [_]) ++ [true] = _
            rw [List.append_assoc]; rfl
          have hlenD : (wiresFrom Pdrop (List.ofFn x)).length = 7 + P.size := by
            rw [wiresFrom_len, List.length_ofFn]; omega
          have hag := cut_agree (7 + P.size) gs hno_u_gs
            (wiresFrom Pdrop (List.ofFn x) ++ [false, true])
            (P.wires (List.ofFn x) ++ [true])
            (by rw [hPw_eq, List.length_append, List.length_append]; rfl)
            (by
              intro i hi
              rw [hPw_eq]
              by_cases hlt : i < 7 + P.size
              · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
                cases hk : i - (wiresFrom Pdrop (List.ofFn x)).length with
                | zero => omega
                | succ k => cases k <;> rfl)
            Q.output hout_ne_u
          rw [h1, hag, hQgs_eval, hhigh x]
        have hstatD_n : accD.1.getD n (Sum.inl false) = Sum.inl true := by
          rw [elim_getD 8 n _ gs (initD, Pdrop) (by change n < initD.length; omega)]
          rw [List.getD_append_right _ _ _ _ (by rw [List.length_map, List.length_range]; omega)]
          have hs : n - ((List.range (7 + P.size)).map (Sum.inr : ℕ → Bool ⊕ ℕ)).length = 1 := by
            rw [List.length_map, List.length_range]; omega
          rw [hs]; rfl
        have hSR_okD : ∀ p ∈ SR, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < initD.length + p ∧
            ∃ c, accD.1.getD a (Sum.inl false) = Sum.inl c := by
          intro p hp
          rw [Finset.mem_filter, Finset.mem_range] at hp
          have h2 : isR p = true := hp.2
          dsimp only [isR] at h2
          rw [List.getElem?_eq_getElem hp.1] at h2
          refine ⟨normGate Q.gates[p], ?_, n,
            (reads_iff n Q.gates[p] (hQfan _ (List.getElem_mem hp.1))).mp h2, by omega, true, hstatD_n⟩
          rw [List.getElem?_map, List.getElem?_eq_getElem hp.1]; rfl
        have hcntD := elim_count 8 (initD, Pdrop) gs hnok SR hSR_okD
        have hszD9 : accD.2.length ≤ 9 := by
          have hgslen : gs.length = Q.size := List.length_map _
          change accD.2.length + SR.card ≤ Pdrop.length + gs.length at hcntD
          omega
        cases ho : accD.1.getD Q.output (Sum.inl false) with
        | inr k =>
          apply hi_lb
          refine ⟨⟨accD.2, k⟩, elim_ok 8 gs (initD, Pdrop) (fun g hg => hPfan g (List.dropLast_subset _ hg)), hszD9, ?_⟩
          intro x
          have hx := haccD_val x
          rw [ho] at hx; exact hx
        | inl b =>
          have h0 := haccD_val (fun _ => false)
          have h1 := haccD_val (fun _ => true)
          rw [ho] at h0 h1
          have hf0 : hiF (fun _ => false) = false := rfl
          have hf1 : hiF (fun _ => true) = true := rfl
          rw [hf0] at h0; rw [hf1] at h1
          exact Bool.noConfusion (h0.symm.trans h1)
      obtain ⟨x, hx⟩ := case_r3 P Q hPfan hQfan hP1 hP4 hsum13 hr3 hall_and hreads_u hu hlow
      exact hx (hhigh x)
  obtain ⟨P, Q, hPfan, hQfan, hP1, hP4, hsum, hu_eq, hQ_eq⟩ := trim_prefix
  obtain ⟨x, hx⟩ := main_ind Q.size P Q rfl hPfan hQfan hP1 hP4 hsum
    (fun x hx1 hx03 => (hu_eq x).trans (hu0 x hx1 hx03))
    (fun x => by rw [hu_eq x, hQ_eq x (u0 x)]; exact hlow0 x)
  exact ⟨x, by rw [← hQ_eq x true]; exact hx⟩

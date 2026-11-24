import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3248_1
    (hthree : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
      ∃ x : Fin 8 → Bool, PEqualNP.MetaComplexity.circuitFun 8 D
        (fun j => if j = 0 then !(x j) else x j) ≠
        ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (2,6), (3,7), (5,6), (7,5)] : List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2))
    (htwo : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
      ∃ x : Fin 8 → Bool, PEqualNP.MetaComplexity.circuitFun 8 D
        (fun j => if j = 1 then !(x j) else x j) ≠
        ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (2,6), (3,7), (5,6), (7,5)] : List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2))
    :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval ((List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ))]).set ↑x2 !x8 x2) ≠ x1 x8 := by
  -- The constant-propagation argument from L-meta-2565 is generalized to arbitrary input restrictions.
  have hfix : ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : Fin n)
      (f : Fin n → Option (Fin m)), PEqualNP.MetaComplexity.FanInTwo C → f j = none →
      (∃ a b : Fin n → Bool, (∀ i, i ≠ j → a i = b i) ∧
        PEqualNP.MetaComplexity.circuitFun n C a ≠ PEqualNP.MetaComplexity.circuitFun n C b) →
      (∃ a b : Fin m → Bool,
        PEqualNP.MetaComplexity.circuitFun n C (fun i => (f i).elim false a) ≠
        PEqualNP.MetaComplexity.circuitFun n C (fun i => (f i).elim false b)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size < C.size ∧
        ∀ z : Fin m → Bool, PEqualNP.MetaComplexity.circuitFun m D z =
          PEqualNP.MetaComplexity.circuitFun n C (fun i => (f i).elim false z) := by
    let wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

    have wiresFrom_append (gs gs' : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
        wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
      simp [wiresFrom, List.foldl_append]

    have wiresFrom_prefix (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ w : List Bool,
        ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
      induction gs with
      | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
      | cons g gs ih =>
        intro w
        obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
        have : wiresFrom (g :: gs) w
            = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
        rw [this, ht]; simp

    have length_wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
        (wiresFrom gs w).length = w.length + gs.length := by
      obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
      rw [ht]; simp [hl]

    have getD_wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
        (wiresFrom gs w).getD i false = w.getD i false := by
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
      rw [ht, List.getD_append _ _ _ _ h]

    let Ok (g : PEqualNP.CircuitLowerBounds.Gate) : Prop :=
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2

    have getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
        (L ++ [S]).getD j d = L.getD j d := by
      by_cases hj : j < L.length
      · exact List.getD_append _ _ _ _ hj
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

    have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
      simp

    have evalAnd (w : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval w = w.all id := rfl
    have evalOr (w : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval w = w.any id := rfl
    have evalNot (w : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.not.eval w = !(w.headD false) := rfl
    let normGate (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
      PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => PEqualNP.CircuitLowerBounds.Gate) g g
        ⟨PEqualNP.CircuitLowerBounds.GateOp.not, g.inputs.take 1⟩ (fun _ => g) g g.op

    have normGate_eval (g : PEqualNP.CircuitLowerBounds.Gate) (F : ℕ → Bool) :
        (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
      obtain ⟨op, inputs⟩ := g
      cases op <;> simp only [normGate]
      cases inputs <;> simp [evalAnd, evalOr, evalNot]

    let NOk (g : PEqualNP.CircuitLowerBounds.Gate) : Prop := Ok g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length ≤ 1)

    have normGate_nok (g : PEqualNP.CircuitLowerBounds.Gate) (h : Ok g) : NOk (normGate g) := by
      obtain ⟨op, inputs⟩ := g
      obtain ⟨hop, hlen⟩ := h
      rcases hop with h | h | h
      · have : op = PEqualNP.CircuitLowerBounds.GateOp.and := h
        subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
      · have : op = PEqualNP.CircuitLowerBounds.GateOp.or := h
        subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
      · have : op = PEqualNP.CircuitLowerBounds.GateOp.not := h
        subst this
        refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

    have wiresFrom_norm (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ w : List Bool,
        wiresFrom (gs.map normGate) w = wiresFrom gs w := by
      induction gs with
      | nil => intro w; rfl
      | cons g gs ih =>
        intro w
        have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
            (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
        have s2 : wiresFrom (g :: gs) w
            = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
        rw [s1, s2, normGate_eval, ih]

    let sval (w : List Bool) : Bool ⊕ ℕ → Bool := Sum.elim id (fun j => w.getD j false)
    let svalid (m : ℕ) : Bool ⊕ ℕ → Prop := Sum.elim (fun _ => True) (fun j => j < m)

    let simpNot (m : ℕ) (xs : List (Bool ⊕ ℕ)) : Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ) :=
      List.casesOn xs (none, Sum.inl true) fun a _ =>
        Sum.elim (fun c => (none, Sum.inl (!c)))
          (fun j => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.not,[j]⟩, Sum.inr m)) a

    let simpAnd (m : ℕ) (xs : List (Bool ⊕ ℕ)) : Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ) :=
      List.casesOn xs (none, Sum.inl true) fun a tail =>
        List.casesOn tail (none, a) fun b rest =>
          List.casesOn rest
            (Sum.elim (fun c => Sum.elim (fun d => (none, Sum.inl (c && d)))
                (fun j => (none, bif c then Sum.inr j else Sum.inl false)) b)
              (fun j => Sum.elim (fun c => (none, bif c then Sum.inr j else Sum.inl false))
                (fun k => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [j,k]⟩, Sum.inr m)) b) a)
            (fun _ _ => (none, Sum.inl false))

    let simpOr (m : ℕ) (xs : List (Bool ⊕ ℕ)) : Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ) :=
      List.casesOn xs (none, Sum.inl false) fun a tail =>
        List.casesOn tail (none, a) fun b rest =>
          List.casesOn rest
            (Sum.elim (fun c => Sum.elim (fun d => (none, Sum.inl (c || d)))
                (fun j => (none, bif c then Sum.inl true else Sum.inr j)) b)
              (fun j => Sum.elim (fun c => (none, bif c then Sum.inl true else Sum.inr j))
                (fun k => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [j,k]⟩, Sum.inr m)) b) a)
            (fun _ _ => (none, Sum.inl false))

    let simplify (op : PEqualNP.CircuitLowerBounds.GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ) :=
      PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ))
        (simpAnd m ins) (simpOr m ins) (simpNot m ins)
        (fun _ => (none, Sum.inl false)) (none, Sum.inl false) op

    have simplify_ok (op : PEqualNP.CircuitLowerBounds.GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
        ∀ g ∈ (simplify op m ins).1, Ok g := by
      intro g hg
      cases op <;> simp only [simplify] at hg
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp [simpAnd] at hg <;> (subst hg; simp [Ok])
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp [simpOr] at hg <;> (subst hg; simp [Ok])
      · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
          simp [simpNot] at hg <;> (subst hg; simp [Ok])
      · simp at hg
      · simp at hg

    have simplify_count (op : PEqualNP.CircuitLowerBounds.GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
        (hop : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ op = PEqualNP.CircuitLowerBounds.GateOp.not) (hlen : ins.length ≤ 2)
        (hnot : op = PEqualNP.CircuitLowerBounds.GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
        (simplify op m ins).1 = none := by
      obtain ⟨c, hc⟩ := hc
      rcases hop with rfl | rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp_all [simplify, simpAnd]
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp_all [simplify, simpOr]
      · have := hnot rfl
        rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

    have simplify_sound (op : PEqualNP.CircuitLowerBounds.GateOp) (hop : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ op = PEqualNP.CircuitLowerBounds.GateOp.not)
        (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
        (hv : ∀ s ∈ ins, svalid w.length s) :
        svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
        sval (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
          = op.eval (ins.map (sval w)) := by
      rcases hop with rfl | rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · simp [simplify, simpAnd, svalid, sval, evalAnd, evalOr, evalNot]
        · cases a <;> simp_all [simplify, simpAnd, svalid, sval, evalAnd, evalOr, evalNot, wiresFrom]
        · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
            simp_all [simplify, simpAnd, svalid, sval, evalAnd, evalOr, evalNot, wiresFrom]
        · simp at hlen
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · simp [simplify, simpOr, svalid, sval, evalAnd, evalOr, evalNot]
        · cases a <;> simp_all [simplify, simpOr, svalid, sval, evalAnd, evalOr, evalNot, wiresFrom]
        · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
            simp_all [simplify, simpOr, svalid, sval, evalAnd, evalOr, evalNot, wiresFrom]
        · simp at hlen
      · rcases ins with _ | ⟨a, l⟩
        · simp [simplify, simpNot, svalid, sval, evalAnd, evalOr, evalNot]
        · cases a <;> simp_all [simplify, simpNot, svalid, sval, evalAnd, evalOr, evalNot, wiresFrom]

    let elimStep (n : ℕ) (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) :
        List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate :=
      (acc.1 ++ [(simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
        acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

    let elim (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate) :
        List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate :=
      gs.foldl (elimStep n) acc

    have toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
      cases o <;> simp

    have elim_ok (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate,
        (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
      induction gs with
      | nil => intro acc h; exact h
      | cons g gs ih =>
        intro acc h
        apply ih (elimStep n acc g)
        intro g' hg'
        rcases List.mem_append.1 hg' with h1 | h1
        · exact h g' h1
        · exact simplify_ok _ _ _ g' (by simpa using h1)

    let hits (j : Nat) (g : PEqualNP.CircuitLowerBounds.Gate) : Bool := g.inputs.contains j

    have elim_count (j n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate,
        (∀ g ∈ gs, NOk g) → j < acc.1.length →
        acc.1.getD j (Sum.inl false) = Sum.inl false →
        (elim n gs acc).2.length + gs.countP (hits j) ≤ acc.2.length + gs.length := by
      induction gs with
      | nil => intro acc _ _ _; simp [elim]
      | cons g gs ih =>
        intro acc hok hlen hj
        have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
        have hl : (elimStep n acc g).1.length = acc.1.length + 1 := by simp [elimStep]
        have hj' : (elimStep n acc g).1.getD j (Sum.inl false) = Sum.inl false := by
          simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hj
        have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
          (by omega) hj'
        rw [h3, List.length_cons, List.countP_cons]
        by_cases hg : hits j g = true
        · have hnok := hok g List.mem_cons_self
          have hk : j ∈ g.inputs := List.contains_iff_mem.mp hg
          have hnone : (simplify g.op (n + acc.2.length)
              (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
            apply simplify_count
            · exact hnok.1.1
            · simpa using hnok.1.2
            · intro h; simpa using hnok.2 h
            · exact ⟨false, List.mem_map.2 ⟨j, hk, hj⟩⟩
          have h2 : (elimStep n acc g).2.length = acc.2.length := by
            show (acc.2 ++ (simplify g.op (n + acc.2.length)
              (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
            rw [hnone]; simp
          simp only [hg, ite_true]
          omega
        · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
            simp only [elimStep, List.length_append]
            have := toList_length_le (simplify g.op (n + acc.2.length)
              (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
            omega
          simp only [hg]
          simp only [Bool.false_eq_true, ite_false]
          omega

    have svalid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Bool ⊕ ℕ, svalid m s → svalid m' s := by
      intro s hj
      cases s with
      | inl c => trivial
      | inr j => exact lt_of_lt_of_le hj h

    have sval_append (w t : List Bool) : ∀ s : Bool ⊕ ℕ, svalid w.length s →
        sval (w ++ t) s = sval w s := by
      intro s hj
      cases s with
      | inl c => rfl
      | inr j => exact List.getD_append _ _ _ _ hj

    let Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate) : Prop :=
      acc.1.length = w.length ∧ ∀ i : ℕ,
        svalid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
        sval (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

    have inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List PEqualNP.CircuitLowerBounds.Gate) :
        ∀ (w : List Bool) (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
          Inv n y (wiresFrom gs w) (elim n gs acc) := by
      induction gs with
      | nil => intro w acc _ h; exact h
      | cons g gs ih =>
        intro w acc hok h
        apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
          (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        obtain ⟨hl, hi⟩ := h
        set w' := wiresFrom acc.2 y with hw'
        have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
        set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
        have hgok := hok g List.mem_cons_self
        have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
          (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            rw [lw']; exact (hi a).1)
        rw [lw'] at hs
        set r := simplify g.op (n + acc.2.length) ins with hr
        have hvals : ins.map (sval w') = g.inputs.map fun i => w.getD i false := by
          rw [hins, List.map_map]
          apply List.map_congr_left
          intro a _
          exact (hi a).2
        have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
          rw [wiresFrom_append]
        obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
        refine ⟨by simp [elimStep, hl], ?_⟩
        intro i
        show svalid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
          sval (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
        rw [hnew, List.length_append, ← Nat.add_assoc]
        by_cases hil : i = acc.1.length
        · subst hil
          rw [getD_snoc_eq, hl, getD_snoc_eq]
          exact ⟨hs.1, by rw [hs.2, hvals]⟩
        · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
          refine ⟨svalid_mono (by omega) _ (hi i).1, ?_⟩
          rw [ht, sval_append _ _ _ (by rw [lw']; exact (hi i).1)]
          exact (hi i).2


    have agree_off (j : Nat) (gs : List PEqualNP.CircuitLowerBounds.Gate) (unread : ∀ g ∈ gs, j ∉ g.inputs)
        (w w' : List Bool) (hl : w.length = w'.length)
        (hw : ∀ i, i ≠ j → w.getD i false = w'.getD i false) :
        ∀ i, i ≠ j → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
      induction gs generalizing w w' with
      | nil => exact hw
      | cons g gs ih =>
        have he : g.op.eval (g.inputs.map fun i => w.getD i false) =
            g.op.eval (g.inputs.map fun i => w'.getD i false) := by
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hw i (fun e => unread g List.mem_cons_self (e ▸ hi))
        apply ih (fun g' hg' => unread g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hl])
        intro i hij
        by_cases h : i = w.length
        · subst i; rw [getD_snoc_eq, hl, getD_snoc_eq, he]
        · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (by omega)]
          exact hw i hij

    let vars {n m : ℕ} (f : Fin n → Option (Fin m)) : List (Bool ⊕ ℕ) :=
      List.ofFn fun i => (f i).elim (Sum.inl false) (fun v => Sum.inr v.val)

    have vars_inv {n m : ℕ} (f : Fin n → Option (Fin m)) (z : Fin m → Bool) :
        Inv m (List.ofFn z) (List.ofFn fun i => (f i).elim false z) (vars f, []) := by
      refine ⟨by simp [vars], ?_⟩
      intro i
      by_cases h : i < n
      · simp only [vars, List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, dite_true,
            Option.getD_some, List.length_nil, Nat.add_zero, wiresFrom, List.foldl_nil]
        cases e : f ⟨i,h⟩ with
        | none => exact ⟨trivial,rfl⟩
        | some v =>
          change v.val < m ∧ (List.ofFn z).getD v.val false = z v
          exact ⟨v.isLt, by simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt]⟩
      · rw [List.getD_eq_default _ _ (by simp [vars]; omega), List.getD_eq_default _ _ (by simp; omega)]
        exact ⟨trivial,rfl⟩

    have restrict_gate (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : Fin n) (f : Fin n → Option (Fin m))
        (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hf : f j = none)
        (hs : ∃ a b : Fin n → Bool, (∀ i, i ≠ j → a i = b i) ∧ PEqualNP.MetaComplexity.circuitFun n C a ≠ PEqualNP.MetaComplexity.circuitFun n C b)
        (hv : ∃ a b : Fin m → Bool, PEqualNP.MetaComplexity.circuitFun n C (fun i => (f i).elim false a) ≠
          PEqualNP.MetaComplexity.circuitFun n C (fun i => (f i).elim false b)) :
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size < C.size ∧ ∀ z : Fin m → Bool,
          PEqualNP.MetaComplexity.circuitFun m D z = PEqualNP.MetaComplexity.circuitFun n C (fun i => (f i).elim false z) := by
      let gs := C.gates.map normGate
      have good : ∀ g ∈ gs, NOk g := by
        intro g hg
        obtain ⟨g0,h0,rfl⟩ := List.mem_map.mp hg
        exact normGate_nok _ (hfan g0 h0)
      have ev (a : Fin n → Bool) : (wiresFrom gs (List.ofFn a)).getD C.output false = PEqualNP.MetaComplexity.circuitFun n C a := by
        dsimp [gs]; rw [wiresFrom_norm]; rfl
      obtain ⟨x,y,hxy,hne⟩ := hs
      obtain ⟨a,b,hab⟩ := hv
      have hout : C.output ≠ j.val := by
        intro he
        apply hab
        rw [← ev, ← ev, he, getD_wiresFrom _ _ _ (by simpa using j.isLt),
          getD_wiresFrom _ _ _ (by simpa using j.isLt)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, hf]
      have used : ∃ g ∈ gs, j.val ∈ g.inputs := by
        by_contra unused
        push Not at unused
        apply hne
        rw [← ev, ← ev]
        apply agree_off j.val gs unused _ _ (by simp) _ _ hout
        intro i hi
        by_cases h : i < n
        · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] using
            (hxy ⟨i,h⟩ (fun e => hi (congrArg Fin.val e)))
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have pos : 0 < gs.countP (hits j.val) := by
        obtain ⟨g,hg,hw⟩ := used
        exact List.countP_pos_iff.mpr ⟨g, hg, List.contains_iff_mem.mpr hw⟩
      let start : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate := (vars f, [])
      let acc := elim m gs start
      have budget := elim_count j.val m gs start good (by simpa [start, vars] using j.isLt)
        (by simp [start, vars, List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, hf])
      have length_eq : gs.length = C.size := by
        change gs.length = C.gates.length
        simp [gs]
      change acc.2.length + gs.countP (hits j.val) ≤ 0 + gs.length at budget
      have out (z : Fin m → Bool) : sval (wiresFrom acc.2 (List.ofFn z))
          (acc.1.getD C.output (Sum.inl false)) = PEqualNP.MetaComplexity.circuitFun n C (fun i => (f i).elim false z) := by
        have h := inv_elim m (List.ofFn z) (by simp) gs _ start (fun g hg => (good g hg).1) (vars_inv f z)
        exact ((h.2 C.output).2).trans (ev _)
      cases he : acc.1.getD C.output (Sum.inl false) with
      | inl c =>
        exfalso
        apply hab
        rw [← out, ← out, he] <;> rfl
      | inr k =>
        refine ⟨⟨acc.2,k⟩, ?_, ?_, ?_⟩
        · exact elim_ok m gs start (by simp [start])
        · change acc.2.length < C.size; omega
        · intro z
          have e := out z
          rw [he] at e
          exact e
    exact restrict_gate
  classical
  let nine (x : Fin 9 → Bool) := ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let eight (x : Fin 8 → Bool) := ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (2,6), (3,7), (5,6), (7,5)] : List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2)
  change ∀ (k : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit), k ≠ 0 → k ≠ 6 →
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
    ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [x 0 || x 6]).set k.val (!(x k))) ≠ nine x
  intro k C hk0 hk6 hfan hsize
  by_contra hno
  let pack (r : Fin 9) (x : Fin 9 → Bool) (j : Fin 10) : Bool :=
    if h : j.val < 9 then if j.val = r.val then !(x ⟨j.val,h⟩) else x ⟨j.val,h⟩
    else x 0 || x 6
  have packList (r : Fin 9) (x : Fin 9 → Bool) : List.ofFn (pack r x) =
      (List.ofFn x ++ [x 0 || x 6]).set r.val (!(x r)) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    have h10 : i < 10 := by simpa using hi
    rw [List.getElem_ofFn, List.getElem_set]
    by_cases h : i < 9
    · simp only [pack, h, dite_true]
      by_cases e : i = r.val
      · subst i; simp
      · simp only [e, Ne.symm e, ite_false]
        rw [List.getElem_append_left (by simpa using h), List.getElem_ofFn]
    · have e : i = 9 := by omega
      subst i
      have ne : r.val ≠ 9 := by omega
      simp [pack, ne]
  have correct (x : Fin 9 → Bool) : PEqualNP.MetaComplexity.circuitFun 10 C (pack k x) = nine x := by
    unfold PEqualNP.MetaComplexity.circuitFun
    rw [packList]
    exact Classical.byContradiction fun hn => hno ⟨x, hn⟩
  -- With vertices zero and eight present, vertex six alone can change the edge test.
  let row (b : Bool) : Fin 9 → Bool := ![true,false,false,false,false,false,b,false,true]
  have sense : ∃ a b : Fin 10 → Bool, (∀ i, i ≠ 6 → a i = b i) ∧
      PEqualNP.MetaComplexity.circuitFun 10 C a ≠ PEqualNP.MetaComplexity.circuitFun 10 C b := by
    refine ⟨pack k (row false), pack k (row true), ?_, ?_⟩
    · have rowEq : ∀ i : Fin 9, i ≠ 6 → row false i = row true i := by decide +kernel
      intro i hi
      by_cases h : i.val < 9
      · have hj : (⟨i.val,h⟩ : Fin 9) ≠ 6 := by
          intro he
          apply hi
          exact Fin.ext (congrArg (fun q : Fin 9 => q.val) he)
        simp only [pack, h, dite_true, rowEq _ hj]
      · simp only [pack, h, dite_false]
        decide
    · rw [correct (row false), correct (row true)]
      decide
  let base : Fin 10 → Option (Fin 8) :=
    ![some 0,some 1,some 2,some 3,some 4,some 5,none,some 6,some 7,some 0]
  let embed (x : Fin 8 → Bool) : Fin 9 → Bool :=
    ![x 0,x 1,x 2,x 3,x 4,x 5,false,x 6,x 7]
  let drop : Fin 9 → Fin 8 := ![0,1,2,3,4,5,0,6,7]
  let flip (r : Fin 8) (x : Fin 8 → Bool) (j : Fin 8) := if j = r then !(x j) else x j
  -- These graph automorphisms move the distinguished input to the representative of its degree class.
  let perm : Fin 9 → Fin 8 → Fin 8 :=
    ![![0,1,2,3,4,5,6,7],
      ![0,1,2,3,4,5,6,7],
      ![2,1,0,5,6,3,4,7],
      ![2,6,5,0,1,3,7,4],
      ![0,4,3,2,1,5,7,6],
      ![5,6,2,3,7,0,1,4],
      ![0,1,2,3,4,5,6,7],
      ![3,4,0,5,7,2,1,6],
      ![3,7,5,0,4,2,6,1]]
  let rep (r : Fin 9) := perm r (drop r)
  let f (r : Fin 9) (j : Fin 10) := (base j).map (perm r)
  have which : ∀ r, rep r = 0 ∨ rep r = 1 := by decide +kernel
  have perm0 (a b c d e f g h : Bool) :
      ((a && b) || ((b && c) || ((c && d) || ((d && e) || ((e && a) || ((a && f) || ((c && g) || ((d && h) || ((f && g) || ((h && f) || (false))))))))))) =
      ((a && b) || ((b && c) || ((c && d) || ((d && e) || ((e && a) || ((a && f) || ((c && g) || ((d && h) || ((f && g) || ((h && f) || (false))))))))))) := by ac_rfl
  have perm1 (a b c d e f g h : Bool) :
      ((c && b) || ((b && a) || ((a && f) || ((f && g) || ((g && c) || ((c && d) || ((a && e) || ((f && h) || ((d && e) || ((h && d) || (false))))))))))) =
      ((a && b) || ((b && c) || ((c && d) || ((d && e) || ((e && a) || ((a && f) || ((c && g) || ((d && h) || ((f && g) || ((h && f) || (false))))))))))) := by ac_rfl
  have perm2 (a b c d e f g h : Bool) :
      ((c && g) || ((g && f) || ((f && a) || ((a && b) || ((b && c) || ((c && d) || ((f && h) || ((a && e) || ((d && h) || ((e && d) || (false))))))))))) =
      ((a && b) || ((b && c) || ((c && d) || ((d && e) || ((e && a) || ((a && f) || ((c && g) || ((d && h) || ((f && g) || ((h && f) || (false))))))))))) := by ac_rfl
  have perm3 (a b c d e f g h : Bool) :
      ((a && e) || ((e && d) || ((d && c) || ((c && b) || ((b && a) || ((a && f) || ((d && h) || ((c && g) || ((f && h) || ((g && f) || (false))))))))))) =
      ((a && b) || ((b && c) || ((c && d) || ((d && e) || ((e && a) || ((a && f) || ((c && g) || ((d && h) || ((f && g) || ((h && f) || (false))))))))))) := by ac_rfl
  have perm4 (a b c d e f g h : Bool) :
      ((f && g) || ((g && c) || ((c && d) || ((d && h) || ((h && f) || ((f && a) || ((c && b) || ((d && e) || ((a && b) || ((e && a) || (false))))))))))) =
      ((a && b) || ((b && c) || ((c && d) || ((d && e) || ((e && a) || ((a && f) || ((c && g) || ((d && h) || ((f && g) || ((h && f) || (false))))))))))) := by ac_rfl
  have perm5 (a b c d e f g h : Bool) :
      ((d && e) || ((e && a) || ((a && f) || ((f && h) || ((h && d) || ((d && c) || ((a && b) || ((f && g) || ((c && b) || ((g && c) || (false))))))))))) =
      ((a && b) || ((b && c) || ((c && d) || ((d && e) || ((e && a) || ((a && f) || ((c && g) || ((d && h) || ((f && g) || ((h && f) || (false))))))))))) := by ac_rfl
  have perm6 (a b c d e f g h : Bool) :
      ((d && h) || ((h && f) || ((f && a) || ((a && e) || ((e && d) || ((d && c) || ((f && g) || ((a && b) || ((c && g) || ((b && c) || (false))))))))))) =
      ((a && b) || ((b && c) || ((c && d) || ((d && e) || ((e && a) || ((a && f) || ((c && g) || ((d && h) || ((f && g) || ((h && f) || (false))))))))))) := by ac_rfl
  have graphSym (r : Fin 9) (x : Fin 8 → Bool) : eight (fun i => x (perm r i)) = eight x := by
    fin_cases r
    · exact perm0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    · exact perm0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    · exact perm1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    · exact perm2 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    · exact perm3 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    · exact perm4 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    · exact perm0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    · exact perm5 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    · exact perm6 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  have pullAll (r : Fin 9) (h0 : r ≠ 0) (h6 : r ≠ 6) (x : Fin 8 → Bool) :
      (fun j => (f r j).elim false (flip (rep r) x)) =
      pack r (embed fun i => x (perm r i)) := by
    funext j
    fin_cases r <;> first | exact (h0 rfl).elim | exact (h6 rfl).elim |
      (fin_cases j <;> first | rfl | exact (Bool.or_false _).symm)
  have pull := pullAll k hk0 hk6
  have restricted (x : Fin 8 → Bool) : nine (embed x) = eight x := by
    simp [nine, eight, embed]
  have projected (x : Fin 8 → Bool) :
      PEqualNP.MetaComplexity.circuitFun 10 C (fun j => (f k j).elim false (flip (rep k) x)) = eight x :=
    (congrArg (PEqualNP.MetaComplexity.circuitFun 10 C) (pull x)).trans
      ((correct (embed fun i => x (perm k i))).trans
        ((restricted (fun i => x (perm k i))).trans (graphSym k x)))
  have varying : ∃ a b : Fin 8 → Bool,
      PEqualNP.MetaComplexity.circuitFun 10 C (fun j => (f k j).elim false a) ≠
      PEqualNP.MetaComplexity.circuitFun 10 C (fun j => (f k j).elim false b) := by
    refine ⟨flip (rep k) (fun _ => false), flip (rep k) (fun j => decide (j = 0 ∨ j = 1)), ?_⟩
    rw [projected (fun _ => false), projected (fun j => decide (j = 0 ∨ j = 1))]
    decide
  obtain ⟨D, hD, bound, same⟩ := hfix 10 8 C 6 (f k) hfan rfl sense varying
  have allx (x : Fin 8 → Bool) : PEqualNP.MetaComplexity.circuitFun 8 D (flip (rep k) x) = eight x :=
    (same (flip (rep k) x)).trans (projected x)
  rcases which k with h | h
  · obtain ⟨x, hx⟩ := hthree D hD (by omega)
    apply hx
    simpa only [h, flip] using allx x
  · obtain ⟨x, hx⟩ := htwo D hD (by omega)
    apply hx
    simpa only [h, flip] using allx x

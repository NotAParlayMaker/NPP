import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_1677_705
  (minorLower : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4)) 12)
  (rawCase :
    let F := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    let good := fun (D : Circuit) =>
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 6]) = F x
    let eff := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let hit := fun g : Gate => (eff g).any fun i => decide (i = 6)
    ∀ (D : Circuit) (left right : List Gate) (g : Gate) (k : ℕ),
      FanInTwo D → D.size = 14 → D.gates.countP hit = 1 →
      D.gates = left ++ g :: right → g.op = .or →
      (g.inputs = [6,k] ∨ g.inputs = [k,6]) →
      (k = 1 ∨ k = 3 ∨ k = 4 ∨ k = 5) →
      (∃ h ∈ right, 10 + left.length ∈ eff h) → ¬ good D)
  (internalCase :
    let F := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    let good := fun (D : Circuit) =>
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 6]) = F x
    let eff := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let hit := fun g : Gate => (eff g).any fun i => decide (i = 6)
    ∀ (D : Circuit) (left right : List Gate) (g : Gate) (k : ℕ),
      FanInTwo D → D.size = 14 → D.gates.countP hit = 1 →
      D.gates = left ++ g :: right → g.op = .or →
      (g.inputs = [6,k] ∨ g.inputs = [k,6]) →
      (10 ≤ k ∧ k < 10 + left.length) →
      (∃ h ∈ right, 10 + left.length ∈ eff h) → ¬ good D) : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  have elimination :
      let pre := fun x : Fin 8 → Bool =>
        [x 1, x 0, x 4, x 7, x 5, x 2, false, x 6, x 3, x 1]
      let eff := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
      let hit := fun g : Gate => (eff g).any (fun i => decide (i = 6))
      let bad := fun (before : List Gate) (pivot : Gate) =>
        pivot.op = .and ∨ pivot.op = .not ∨
          pivot.op = .or ∧ ∀ i ∈ eff pivot, i = 6 ∨ 10 + before.length ≤ i
      ∀ D : Circuit, FanInTwo D → (∃ x : Fin 8 → Bool, D.eval (pre x) = false) →
        (∃ E : Circuit, FanInTwo E ∧ E.size + D.gates.countP hit ≤ D.size ∧
          ∀ x : Fin 8 → Bool, E.eval (List.ofFn x) = D.eval (pre x)) ∧
        ∀ (before after : List Gate) (pivot : Gate),
          D.gates = before ++ pivot :: after → D.gates.countP hit = 1 →
          hit pivot = true → bad before pivot →
          (∃ g ∈ after, 10 + before.length ∈ eff g) →
          ∃ E : Circuit, FanInTwo E ∧ E.size + 2 ≤ D.size ∧
            ∀ x : Fin 8 → Bool, E.eval (List.ofFn x) = D.eval (pre x) := by
    clear minorLower rawCase internalCase
    intro pre eff hit bad
    let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

    have wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
        wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
      simp [wiresFrom, List.foldl_append]

    have wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

    have length_wiresFrom (gs : List Gate) (w : List Bool) :
        (wiresFrom gs w).length = w.length + gs.length := by
      obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
      rw [ht]; simp [hl]

    let Ok (g : Gate) : Prop :=
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

    have getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
        (L ++ [S]).getD j d = L.getD j d := by
      by_cases hj : j < L.length
      · exact List.getD_append _ _ _ _ hj
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

    have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
      simp

    let NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

    let Stat := Bool ⊕ ℕ
    let readStat (w : List Bool) : Stat → Bool := Sum.elim id (fun j => w.getD j false)
    let validStat (m : ℕ) : Stat → Prop := Sum.elim (fun _ => True) (fun j => j < m)
    have evalAnd0 (l : List Bool) : GateOp.eval .and l = l.all id := rfl
    have evalOr0 (l : List Bool) : GateOp.eval .or l = l.any id := rfl
    have evalNot0 (l : List Bool) : GateOp.eval .not l = !(l.headD false) := rfl

    let normGate (g : Gate) : Gate :=
      GateOp.rec (motive := fun _ => Gate) g g ⟨.not, g.inputs.take 1⟩
        (fun _ => g) g g.op

    have normGate_eval (g : Gate) (F : ℕ → Bool) :
        (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
      obtain ⟨op, inputs⟩ := g
      cases op <;> simp only [normGate]
      cases inputs <;> simp [evalNot0]

    have normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
      obtain ⟨op, inputs⟩ := g
      obtain ⟨hop, hlen⟩ := h
      rcases hop with h | h | h
      · have : op = GateOp.and := h
        subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
      · have : op = GateOp.or := h
        subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
      · have : op = GateOp.not := h
        subst this
        refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate]

    have wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
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

    let simpNot (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
      List.rec (motive := fun _ => Option Gate × Stat) (none, Sum.inl true)
        (fun a _ _ => Sum.elim
          (fun c => (none, Sum.inl (!c)))
          (fun j => (some ⟨GateOp.not, [j]⟩, Sum.inr m)) a) ins

    let simpAnd (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
      let both (a b : Stat) : Option Gate × Stat :=
        Sum.elim
          (fun c => Sum.elim
            (fun d => (none, Sum.inl (c && d)))
            (fun k => (none, bif c then Sum.inr k else Sum.inl false)) b)
          (fun j => Sum.elim
            (fun d => (none, bif d then Sum.inr j else Sum.inl false))
            (fun k => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)) b) a
      List.rec (motive := fun _ => Option Gate × Stat) (none, Sum.inl true)
        (fun a rest _ => List.rec (motive := fun _ => Option Gate × Stat) (none, a)
          (fun b tail _ => List.rec (motive := fun _ => Option Gate × Stat) (both a b)
            (fun _ _ _ => (none, Sum.inl false)) tail) rest) ins

    let simpOr (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
      let both (a b : Stat) : Option Gate × Stat :=
        Sum.elim
          (fun c => Sum.elim
            (fun d => (none, Sum.inl (c || d)))
            (fun k => (none, bif c then Sum.inl true else Sum.inr k)) b)
          (fun j => Sum.elim
            (fun d => (none, bif d then Sum.inl true else Sum.inr j))
            (fun k => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)) b) a
      List.rec (motive := fun _ => Option Gate × Stat) (none, Sum.inl false)
        (fun a rest _ => List.rec (motive := fun _ => Option Gate × Stat) (none, a)
          (fun b tail _ => List.rec (motive := fun _ => Option Gate × Stat) (both a b)
            (fun _ _ _ => (none, Sum.inl false)) tail) rest) ins

    let simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
      GateOp.rec (motive := fun _ => Option Gate × Stat)
        (simpAnd m ins) (simpOr m ins) (simpNot m ins)
        (fun _ => (none, Sum.inl false)) (none, Sum.inl false) op

    have simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
        ∀ g ∈ (simplify op m ins).1, Ok g := by
      intro g hg
      cases op <;> simp only [simplify] at hg
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp [simpAnd] at hg
        subst g
        simp [Ok]
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp [simpOr] at hg
        subst g
        simp [Ok]
      · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
          simp [simpNot] at hg
        subst g
        simp [Ok]
      · simp at hg
      · simp at hg

    have simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
        (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
        (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
        (simplify op m ins).1 = none := by
      obtain ⟨c, hc⟩ := hc
      rcases hop with rfl | rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp_all [simplify, simpAnd]
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp_all [simplify, simpOr]
      · have := hnot rfl
        rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

    have simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
        (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
        (hv : ∀ s ∈ ins, validStat w.length s) :
        validStat (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
        readStat (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
          = op.eval (ins.map (readStat w)) := by
      rcases hop with rfl | rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · simp [simplify, simpAnd, validStat, readStat, evalAnd0]
        · cases a <;> simp_all [simplify, simpAnd, validStat, readStat, wiresFrom]
        · cases a <;> cases b <;> rename_i c e <;> cases c <;> cases e <;>
            simp_all [simplify, simpAnd, validStat, readStat, wiresFrom]
        · simp at hlen
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · simp [simplify, simpOr, validStat, readStat, evalOr0]
        · cases a <;> simp_all [simplify, simpOr, validStat, readStat, wiresFrom]
        · cases a <;> cases b <;> rename_i c e <;> cases c <;> cases e <;>
            simp_all [simplify, simpOr, validStat, readStat, wiresFrom]
        · simp at hlen
      · rcases ins with _ | ⟨a, l⟩
        · simp [simplify, simpNot, validStat, readStat, evalNot0]
        · cases a <;> simp_all [simplify, simpNot, validStat, readStat, wiresFrom]

    let elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
      (acc.1 ++ [(simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
        acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

    let elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
      gs.foldl (elimStep n) acc

    have toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
      cases o <;> simp

    have elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

    have validMono {m m' : ℕ} (h : m ≤ m') :
        ∀ s : Stat, validStat m s → validStat m' s := by
      intro s hs
      cases s with
      | inl b => trivial
      | inr j => exact lt_of_lt_of_le hs h

    have valAppend (w t : List Bool) : ∀ s : Stat, validStat w.length s →
        readStat (w ++ t) s = readStat w s := by
      intro s hs
      cases s with
      | inl b => rfl
      | inr j => exact List.getD_append _ _ _ _ hs

    let Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
      acc.1.length = w.length ∧ ∀ i : ℕ,
        validStat (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
        readStat (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

    have inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
        ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
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
        have hvals : ins.map (readStat w') = g.inputs.map fun i => w.getD i false := by
          rw [hins, List.map_map]
          apply List.map_congr_left
          intro a _
          exact (hi a).2
        have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
          rw [wiresFrom_append]
        obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
        refine ⟨by simp [elimStep, hl], ?_⟩
        intro i
        show validStat (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
          readStat (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
        rw [hnew, List.length_append, ← Nat.add_assoc]
        by_cases hil : i = acc.1.length
        · subst hil
          rw [getD_snoc_eq, hl, getD_snoc_eq]
          exact ⟨hs.1, by rw [hs.2, hvals]⟩
        · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
          refine ⟨validMono (by omega) _ (hi i).1, ?_⟩
          rw [ht, valAppend _ _ _ (by rw [lw']; exact (hi i).1)]
          exact (hi i).2

    have elimCountFrozen (n : ℕ) (frozen : ℕ → Bool) (gs : List Gate) :
        ∀ acc : List Stat × List Gate,
          (∀ g ∈ gs, NOk g) →
          (∀ k, frozen k = true → k < acc.1.length ∧
            ∃ b : Bool, acc.1.getD k (Sum.inl false) = Sum.inl b) →
          (elim n gs acc).2.length + gs.countP (fun g => g.inputs.any frozen) ≤
            acc.2.length + gs.length := by
      induction gs with
      | nil => intro acc _ _; simp [elim]
      | cons g gs ih =>
        intro acc hok hfrozen
        let update := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
        let acc' := (acc.1 ++ [update.2], acc.2 ++ update.1.toList)
        have htail := ih acc' (fun g' hg' => hok g' (List.mem_cons_of_mem g hg')) (by
          intro k hk
          obtain ⟨hlen, b, hval⟩ := hfrozen k hk
          refine ⟨by simp [acc']; omega, b, ?_⟩
          change (acc.1 ++ [update.2]).getD k (Sum.inl false) = Sum.inl b
          rwa [getD_snoc_ne _ _ _ _ (by omega)])
        have hstep : acc'.2.length + (if g.inputs.any frozen then 1 else 0) ≤ acc.2.length + 1 := by
          change (acc.2 ++ update.1.toList).length + _ ≤ _
          by_cases hread : g.inputs.any frozen = true
          · obtain ⟨k, hkg, hk⟩ := List.any_eq_true.mp hread
            have hg := hok g List.mem_cons_self
            have hnone : update.1 = none := by
              apply simplify_count _ _ _ hg.1.1
              · simpa using hg.1.2
              · intro hnot
                simpa using hg.2 hnot
              · obtain ⟨b, hb⟩ := (hfrozen k hk).2
                exact ⟨b, List.mem_map.2 ⟨k, hkg, hb⟩⟩
            simp [hnone, hread]
          · have hl := toList_length_le update.1
            simp only [List.length_append, ite_eq_right hread, Nat.add_zero]
            omega
        change (elim n gs acc').2.length + (g :: gs).countP (fun g => g.inputs.any frozen) ≤ _
        rw [List.countP_cons, List.length_cons]
        omega

    let rows {n : ℕ} (entries : List (Bool ⊕ ℕ)) (z : Fin n → Bool) : List Bool :=
      entries.map (Sum.elim id (fun k => (List.ofFn z).getD k false))

    let initStat (n : ℕ) : Bool ⊕ ℕ → Stat :=
      Sum.elim Sum.inl (fun j => if j < n then Sum.inr j else Sum.inl false)

    let initial (n : ℕ) (entries : List (Bool ⊕ ℕ)) : List Stat :=
      entries.map (initStat n)

    have inv_initial (n : ℕ) (entries : List (Bool ⊕ ℕ)) (z : Fin n → Bool) :
        Inv n (List.ofFn z) (rows entries z) (initial n entries, []) := by
      have hentry (e : Bool ⊕ ℕ) : validStat n (initStat n e) ∧
          readStat (List.ofFn z) (initStat n e) =
            Sum.elim id (fun k => (List.ofFn z).getD k false) e := by
        cases e with
        | inl b => exact ⟨trivial, rfl⟩
        | inr j =>
          by_cases hj : j < n <;> simp [initStat, validStat, readStat, hj]
      have hmap : (initial n entries).map (readStat (List.ofFn z)) = rows entries z := by
        simp only [initial, rows, List.map_map]
        apply List.map_congr_left
        intro e _
        exact (hentry e).2
      refine ⟨by simp [initial, rows], fun i => ⟨?_, ?_⟩⟩
      · change validStat n ((initial n entries).getD i (Sum.inl false))
        have he : (initial n entries).getD i (Sum.inl false) =
            initStat n (entries.getD i (.inl false)) :=
          List.getD_map entries (.inl false) (initStat n)
        rw [he]
        exact (hentry _).1
      · change readStat (List.ofFn z) ((initial n entries).getD i (Sum.inl false)) =
          (rows entries z).getD i false
        rw [← hmap]
        exact (List.getD_map (initial n entries) (Sum.inl false) (readStat (List.ofFn z))).symm

    have normInputs (g : Gate) (hg : Ok g) : (normGate g).inputs = eff g := by
      have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := hg.1
      obtain ⟨op, inputs⟩ := g
      change op = .and ∨ op = .or ∨ op = .not at hop
      rcases hop with rfl | rfl | rfl <;> rfl

    have normalizedCount (C : Circuit) (fan : FanInTwo C) (frozen : ℕ → Bool) :
        (C.gates.map normGate).countP (fun g => g.inputs.any frozen) =
          C.gates.countP (fun g => (eff g).any frozen) := by
      rw [List.countP_map]
      apply List.countP_congr
      intro g hg
      change ((normGate g).inputs.any frozen) ↔ ((eff g).any frozen)
      rw [normInputs g (fan g hg)]

    have realizeElim (n : ℕ) (entries : List (Bool ⊕ ℕ)) (C : Circuit)
        (fan : FanInTwo C) (budget : ℕ)
        (hsize : (elim n (C.gates.map normGate) (initial n entries, [])).2.length + budget ≤ C.size)
        (hFalse : ∃ z : Fin n → Bool, C.eval (rows entries z) = false) :
        ∃ D : Circuit, FanInTwo D ∧ D.size + budget ≤ C.size ∧
          ∀ z : Fin n → Bool, D.eval (List.ofFn z) = C.eval (rows entries z) := by
      let gs := C.gates.map normGate
      let init := initial n entries
      let acc := elim n gs (init, [])
      have hlen : acc.2.length + budget ≤ C.size := hsize
      have hok (g : Gate) (hg : g ∈ gs) : NOk g := by
        obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
        exact normGate_nok g₀ (fan g₀ hg₀)
      have hval (z : Fin n → Bool) :
          readStat (wiresFrom acc.2 (List.ofFn z)) (acc.1.getD C.output (Sum.inl false)) =
            C.eval (rows entries z) := by
        have hi := inv_elim n (List.ofFn z) (by simp) gs _ (init, [])
          (fun g hg => (hok g hg).1) (inv_initial n entries z)
        change _ = (wiresFrom C.gates (rows entries z)).getD C.output false
        rw [← wiresFrom_norm C.gates]
        exact (hi.2 C.output).2
      cases hout : acc.1.getD C.output (Sum.inl false) with
      | inr i =>
        refine ⟨⟨acc.2, i⟩, elim_ok n gs (init, []) (by simp), hlen, fun z => ?_⟩
        have hz := hval z
        rw [hout] at hz
        exact hz
      | inl b =>
        cases b
        · refine ⟨⟨[], n⟩, ?_, ?_, fun z => ?_⟩
          · intro g hg
            cases hg
          · change 0 + budget ≤ C.size
            omega
          · change (List.ofFn z).getD n false = _
            rw [List.getD_eq_default _ _ (by simp), ← hval z, hout]
            rfl
        · obtain ⟨z, hz⟩ := hFalse
          have hz' := hval z
          rw [hout, hz] at hz'
          cases hz'

    have dropFrozenRows (n : ℕ) (entries : List (Bool ⊕ ℕ)) (frozen : ℕ → Bool)
        (C : Circuit) (fan : FanInTwo C)
        (hFrozen : ∀ i, frozen i = true → i < entries.length ∧
          ∃ b : Bool, entries.getD i (.inl false) = .inl b)
        (hFalse : ∃ z : Fin n → Bool, C.eval (rows entries z) = false) :
        ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP (fun g =>
          (if g.op.eval [false] then g.inputs.take 1 else g.inputs).any frozen) ≤ C.size ∧
          ∀ z : Fin n → Bool, D.eval (List.ofFn z) = C.eval (rows entries z) := by
      let counted := fun g : Gate =>
        (if g.op.eval [false] then g.inputs.take 1 else g.inputs).any frozen
      let gs := C.gates.map normGate
      let init := initial n entries
      let acc := elim n gs (init, [])
      have hok (g : Gate) (hg : g ∈ gs) : NOk g := by
        obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
        exact normGate_nok g₀ (fan g₀ hg₀)
      have hcount : gs.countP (fun g => g.inputs.any frozen) = C.gates.countP counted :=
        normalizedCount C fan frozen
      have hlen : acc.2.length + C.gates.countP counted ≤ C.size := by
        have hgs : gs.length = C.size := List.length_map normGate
        have hbound := elimCountFrozen n frozen gs (init, []) hok (by
          intro i hi
          obtain ⟨hi, b, hb⟩ := hFrozen i hi
          have hinit : init.length = entries.length := List.length_map (initStat n)
          refine ⟨by simpa only [hinit] using hi, b, ?_⟩
          exact (List.getD_map entries (.inl false) (initStat n)).trans
            (congrArg (initStat n) hb))
        change acc.2.length + gs.countP (fun g => g.inputs.any frozen) ≤ 0 + gs.length at hbound
        simpa only [hcount, Nat.zero_add, hgs] using hbound
      exact realizeElim n entries C fan (C.gates.countP counted) hlen hFalse

    let entries : List (Bool ⊕ ℕ) :=
      [.inr 1, .inr 0, .inr 4, .inr 7, .inr 5, .inr 2, .inl false, .inr 6, .inr 3, .inr 1]

    have rows_pre (x : Fin 8 → Bool) : rows entries x = pre x := by
      simp [rows, entries, pre, List.getD_eq_getElem?_getD]

    have dropFrozen (D : Circuit) (fan : FanInTwo D)
        (negative : ∃ x : Fin 8 → Bool, D.eval (pre x) = false) :
        ∃ E : Circuit, FanInTwo E ∧ E.size + D.gates.countP hit ≤ D.size ∧
          ∀ x : Fin 8 → Bool, E.eval (List.ofFn x) = D.eval (pre x) := by
      let frozen := fun i : ℕ => decide (i = 6)
      have hconst (i : ℕ) (hi : frozen i = true) :
          i < entries.length ∧ ∃ b : Bool, entries.getD i (.inl false) = .inl b := by
        have he : i = 6 := of_decide_eq_true hi
        subst i
        exact ⟨by decide, false, rfl⟩
      have hf : ∃ y : Fin 8 → Bool, D.eval (rows entries y) = false := by
        simpa only [rows_pre] using negative
      obtain ⟨E, hE, hs, he⟩ := dropFrozenRows 8 entries frozen D fan hconst hf
      exact ⟨E, hE, hs, fun x => (he x).trans (congrArg D.eval (rows_pre x))⟩

    have elimStates (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
        (elim n gs acc).1.length = acc.1.length + gs.length ∧
        ∀ i < acc.1.length, (elim n gs acc).1.getD i (Sum.inl false) =
          acc.1.getD i (Sum.inl false) := by
      induction gs generalizing acc with
      | nil => exact ⟨by simp [elim], fun _ _ => rfl⟩
      | cons g gs ih =>
        let acc' := elimStep n acc g
        have hlen : acc'.1.length = acc.1.length + 1 := by simp [acc', elimStep]
        have h := ih acc'
        change (elim n gs acc').1.length = _ ∧ ∀ i < acc.1.length, _
        refine ⟨by rw [h.1, hlen, List.length_cons]; omega, fun i hi => ?_⟩
        change (elim n gs acc').1.getD i (Sum.inl false) = _
        rw [h.2 i (by omega)]
        exact getD_snoc_ne _ _ _ _ (by omega)

    have simpAndZero (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2)
        (hz : Sum.inl false ∈ ins) : simpAnd m ins = (none, Sum.inl false) := by
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
      · simp at hz
      · have h := List.mem_singleton.mp hz
        subst a
        rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with h | h
        · subst a
          cases b <;> simp [simpAnd]
        · subst b
          cases a <;> simp [simpAnd]
      · simp at hlen

    have orStatesFalse (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2)
        (hf : ∀ s ∈ ins, s = Sum.inl false) : simpOr m ins = (none, Sum.inl false) := by
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · rfl
      · have ha := hf a (by simp)
        simp [simpOr, ha]
      · have ha := hf a (by simp)
        have hb := hf b (by simp)
        simp [simpOr, ha, hb]
      · simp at hlen

    have pivotConstant (m : ℕ) (s : List Stat) (k : ℕ) (g : Gate) (ok : NOk g)
        (hread : k ∈ g.inputs) (hz : s.getD k (Sum.inl false) = Sum.inl false)
        (hKind : g.op = .and ∨ g.op = .not ∨
          g.op = .or ∧ ∀ i ∈ g.inputs, i = k ∨ s.length ≤ i) :
        ∃ b : Bool, simplify g.op m (g.inputs.map (fun i => s.getD i (Sum.inl false))) =
          (none, Sum.inl b) := by
      rcases hKind with hAnd | hNot | ⟨hOr, hAll⟩
      · refine ⟨false, ?_⟩
        rw [hAnd]
        apply simpAndZero
        · simpa using ok.1.2
        · exact List.mem_map.mpr ⟨k, hread, hz⟩
      · have hl := ok.2 hNot
        obtain ⟨a, b, hab⟩ := List.append_of_mem hread
        rw [hab, List.length_append, List.length_cons] at hl
        have ha : a = [] := List.length_eq_zero_iff.mp (by omega)
        have hb : b = [] := List.length_eq_zero_iff.mp (by omega)
        have hsingle : g.inputs = [k] := by simpa only [ha, hb, List.nil_append] using hab
        exact ⟨true, by
          simp only [hNot, hsingle, List.map_cons, List.map_nil, hz, simplify, simpNot]
          rfl⟩
      · refine ⟨false, ?_⟩
        rw [hOr]
        apply orStatesFalse
        · simpa using ok.1.2
        · intro v hv
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
          rcases hAll i hi with rfl | hn
          · exact hz
          · exact List.getD_eq_default _ _ hn

    have countPGain {α : Type} (p q : α → Bool) (l : List α)
        (hsub : ∀ g ∈ l, p g = true → q g = true)
        (extra : ∃ g ∈ l, p g = false ∧ q g = true) :
        l.countP p + 1 ≤ l.countP q := by
      obtain ⟨g, hg, hp, hq⟩ := extra
      obtain ⟨left, right, rfl⟩ := List.append_of_mem hg
      have hl : left.countP p ≤ left.countP q :=
        List.countP_mono_left fun x hx => hsub x (List.mem_append.mpr (Or.inl hx))
      have hr : right.countP p ≤ right.countP q :=
        List.countP_mono_left fun x hx =>
          hsub x (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx)))
      have hn : ¬p g := by simp [hp]
      simp only [List.countP_append, List.countP_cons_of_neg hn, List.countP_cons_of_pos hq]
      omega

    have elimCountExtra (n : ℕ) (frozen : ℕ → Bool)
        (before after : List Gate) (pivot : Gate) (acc : List Stat × List Gate)
        (hok : ∀ g ∈ before ++ pivot :: after, NOk g)
        (hfreeze : ∀ i, frozen i = true → i < acc.1.length ∧
          ∃ b : Bool, acc.1.getD i (Sum.inl false) = Sum.inl b)
        (k : ℕ) (hz : k < acc.1.length ∧ acc.1.getD k (Sum.inl false) = Sum.inl false)
        (hPivotRead : k ∈ pivot.inputs)
        (hKind : pivot.op = .and ∨ pivot.op = .not ∨
          pivot.op = .or ∧ ∀ i ∈ pivot.inputs, i = k ∨ acc.1.length + before.length ≤ i)
        (hconsumer : ∃ g ∈ after, (acc.1.length + before.length) ∈ g.inputs ∧
          g.inputs.any frozen = false) :
        (elim n (before ++ pivot :: after) acc).2.length +
          (before ++ pivot :: after).countP (fun g => g.inputs.any frozen) + 1 ≤
            acc.2.length + (before ++ pivot :: after).length := by
      let start := elim n before acc
      let start' := elimStep n start pivot
      let added := fun i : ℕ => frozen i || decide (i = start.1.length)
      have hstates := elimStates n before acc
      have hstart : start.1.length = acc.1.length + before.length := hstates.1
      have hkeep (i : ℕ) (hi : i < acc.1.length) :
          start.1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false) := hstates.2 i hi
      have hprefix : start.2.length + before.countP (fun g => g.inputs.any frozen) ≤
          acc.2.length + before.length :=
        elimCountFrozen n frozen before acc
          (fun g hg => hok g (List.mem_append.mpr (Or.inl hg))) hfreeze
      have hPivotOk := hok pivot (List.mem_append.mpr (Or.inr List.mem_cons_self))
      obtain ⟨b, hconst⟩ := pivotConstant (n + start.2.length) start.1 k pivot hPivotOk
        hPivotRead ((hkeep k hz.1).trans hz.2) (by simpa only [hstart] using hKind)
      have hstep : start' = (start.1 ++ [Sum.inl b], start.2) := by
        simp only [start', elimStep, hconst, Option.toList_none, List.append_nil]
      have hnew (j : ℕ) (hj : added j = true) : j < start'.1.length ∧
          ∃ b : Bool, start'.1.getD j (Sum.inl false) = Sum.inl b := by
        have hj' : frozen j = true ∨ j = start.1.length := by
          simpa only [added, Bool.or_eq_true_iff, decide_eq_true_eq] using hj
        rw [hstep]
        rcases hj' with hj | rfl
        · obtain ⟨hlt, b, hb⟩ := hfreeze j hj
          have hprev : j < start.1.length := by rw [hstart]; omega
          refine ⟨by simp; omega, b, ?_⟩
          rw [getD_snoc_ne _ _ _ _ (by omega), hkeep j hlt]
          exact hb
        · exact ⟨by simp, b, getD_snoc_eq _ _ _⟩
      have htail := elimCountFrozen n added after start'
        (fun g hg => hok g (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hg)))) hnew
      have hsnd : start'.2.length = start.2.length := by rw [hstep]
      rw [hsnd] at htail
      have hgain : after.countP (fun g => g.inputs.any frozen) + 1 ≤
          after.countP (fun g => g.inputs.any added) := by
        apply countPGain
        · intro g _ hg
          obtain ⟨j, hj, hfr⟩ := List.any_eq_true.mp hg
          exact List.any_eq_true.2 ⟨j, hj, by simp [added, hfr]⟩
        · obtain ⟨g, hg, hj, hf⟩ := hconsumer
          have hindex : start.1.length ∈ g.inputs := by rw [hstart]; exact hj
          exact ⟨g, hg, hf,
            List.any_eq_true.2 ⟨start.1.length, hindex, by simp [added]⟩⟩
      have hfold : elim n (before ++ pivot :: after) acc = elim n after start' := by
        simp [elim, List.foldl_append, start, start', elimStep]
      have hpivot : (if pivot.inputs.any frozen then 1 else 0) ≤ 1 := by
        cases pivot.inputs.any frozen <;> decide
      rw [hfold]
      simp only [List.countP_append, List.countP_cons, List.length_append, List.length_cons]
      omega

    have dropFrozenExtra (D : Circuit) (fan : FanInTwo D)
        (before : List Gate) (pivot : Gate) (after : List Gate)
        (hsplit : D.gates = before ++ pivot :: after)
        (hsole : D.gates.countP hit = 1)
        (hPivot : hit pivot = true ∧ bad before pivot)
        (hreader : ∃ g ∈ after, 10 + before.length ∈ eff g)
        (negative : ∃ x : Fin 8 → Bool, D.eval (pre x) = false) :
        ∃ E : Circuit, FanInTwo E ∧ E.size + 2 ≤ D.size ∧
          ∀ x : Fin 8 → Bool, E.eval (List.ofFn x) = D.eval (pre x) := by
      let frozen := fun i : ℕ => decide (i = 6)
      let init : List Stat × List Gate := (initial 8 entries, [])
      let left := before.map normGate
      let right := after.map normGate
      let pivot' := normGate pivot
      have hsplit' : D.gates.map normGate = left ++ pivot' :: right := by
        rw [hsplit, List.map_append, List.map_cons]
      have hpivotD : pivot ∈ D.gates := by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      have hnorm : pivot'.op = pivot.op := by
        obtain ⟨op, inputs⟩ := pivot
        cases op <;> rfl
      have heff : pivot'.inputs = eff pivot := normInputs pivot (fan pivot hpivotD)
      have hok (g : Gate) (hg : g ∈ left ++ pivot' :: right) : NOk g := by
        rw [← hsplit'] at hg
        obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
        exact normGate_nok g₀ (fan g₀ hg₀)
      have hz : 6 < init.1.length ∧ init.1.getD 6 (Sum.inl false) = Sum.inl false := by
        exact ⟨by decide, rfl⟩
      have hlen : init.1.length = 10 := rfl
      have hpivotRead : 6 ∈ pivot'.inputs := by
        rw [heff]
        have hhit : (eff pivot).any frozen = true := hPivot.1
        obtain ⟨i, hi, hfr⟩ := List.any_eq_true.mp hhit
        have e : i = 6 := of_decide_eq_true hfr
        exact e ▸ hi
      have hKind : pivot'.op = .and ∨ pivot'.op = .not ∨
          pivot'.op = .or ∧ ∀ i ∈ pivot'.inputs, i = 6 ∨ init.1.length + left.length ≤ i := by
        simpa only [bad, hnorm, heff, hlen, left, List.length_map] using hPivot.2
      have hafter : after.countP hit = 0 := by
        have h := hsole
        rw [hsplit, List.countP_append, List.countP_cons_of_pos hPivot.1] at h
        omega
      have hconsumer : ∃ g ∈ right, (init.1.length + left.length) ∈ g.inputs ∧
          g.inputs.any frozen = false := by
        obtain ⟨g, hg, hindex⟩ := hreader
        have hgD : g ∈ D.gates := by
          rw [hsplit]
          exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hg))
        have he := normInputs g (fan g hgD)
        refine ⟨normGate g, List.mem_map_of_mem hg, ?_, ?_⟩
        · simpa only [hlen, left, List.length_map, he] using hindex
        · rw [he]
          change hit g = false
          cases ht : hit g with
          | false => rfl
          | true =>
            have hpos : 0 < after.countP hit := List.countP_pos_iff.mpr ⟨g, hg, ht⟩
            omega
      have hbound := elimCountExtra 8 frozen left right pivot' init hok (by
        intro i hi
        have he : i = 6 := of_decide_eq_true hi
        subst i
        exact ⟨hz.1, false, hz.2⟩) 6 hz hpivotRead hKind hconsumer
      rw [← hsplit', normalizedCount D fan frozen] at hbound
      have hbudget : (elim 8 (D.gates.map normGate) init).2.length + 2 ≤ D.size := by
        have hsize : (D.gates.map normGate).length = D.size := List.length_map normGate
        change (elim 8 (D.gates.map normGate) init).2.length +
          D.gates.countP hit + 1 ≤ 0 + (D.gates.map normGate).length at hbound
        simpa only [Nat.add_assoc, Nat.zero_add, hsize, hsole] using hbound
      have hf : ∃ x : Fin 8 → Bool, D.eval (rows entries x) = false := by
        simpa only [rows_pre] using negative
      obtain ⟨E, hE, hsize, hEq⟩ := realizeElim 8 entries D fan 2 hbudget hf
      exact ⟨E, hE, hsize, fun x => (hEq x).trans (congrArg D.eval (rows_pre x))⟩

    intro D fan negative
    refine ⟨dropFrozen D fan negative, ?_⟩
    intro before after pivot split sole isHit isBad reader
    exact dropFrozenExtra D fan before pivot after split sole ⟨isHit, isBad⟩ reader negative
  have readers :
      let F := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      let good := fun (D : Circuit) =>
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 6]) = F x
      let eff := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
      let hit := fun g : Gate => (eff g).any fun i => decide (i = 6)
      ∀ D : Circuit, FanInTwo D → good D → 1 ≤ D.gates.countP hit ∧
        ∀ (left right : List Gate) (g : Gate), D.gates = left ++ g :: right →
          D.gates.countP hit = 1 → hit g = true →
          (∃ h ∈ right, 10 + left.length ∈ eff h) ∧
          ∀ k : ℕ, g.op = .or → (g.inputs = [6,k] ∨ g.inputs = [k,6]) →
            k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 7 ∧ k ≠ 8 ∧ k ≠ 9 := by
    clear minorLower rawCase internalCase elimination
    let F (x : Fin 9 → Bool) : Bool :=
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
      x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
      x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

    let inputs (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 6]

    let reads (g : Gate) : List ℕ :=
      if g.op.eval [false] then g.inputs.take 1 else g.inputs

    let hits6 (g : Gate) : Bool := (reads g).any (fun i => decide (i = 6))

    have input_length (x : Fin 9 → Bool) : (inputs x).length = 10 := by
      simp [inputs]

    let gateValue (w : List Bool) (g : Gate) : Bool :=
      g.op.eval (g.inputs.map fun i => w.getD i false)

    let step (w : List Bool) (g : Gate) : List Bool := w ++ [gateValue w g]

    have gate_kind {C : Circuit} (fan : FanInTwo C) {g : Gate} (hg : g ∈ C.gates) :
        g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (fan g hg).1

    have gateValue_congr {C : Circuit} (fan : FanInTwo C) {g : Gate}
        (hg : g ∈ C.gates) (w v : List Bool)
        (h : ∀ i ∈ reads g, w.getD i false = v.getD i false) :
        gateValue w g = gateValue v g := by
      have value (u : List Bool) :
          gateValue u g = g.op.eval ((reads g).map fun i => u.getD i false) := by
        rcases gate_kind fan hg with hop | hop | hop
        · simp only [gateValue, reads, hop, show GateOp.eval .and [false] = false from rfl,
            Bool.false_eq_true, ite_false]
        · simp only [gateValue, reads, hop, show GateOp.eval .or [false] = false from rfl,
            Bool.false_eq_true, ite_false]
        · simp only [gateValue, reads, hop, show GateOp.eval .not [false] = true from rfl,
            ite_true]
          cases g.inputs <;> rfl
      rw [value w, value v, List.map_congr_left h]

    have append_agree {w v : List Bool} (hlen : w.length = v.length) (s : List Bool)
        (i : ℕ) (hi : w.getD i false = v.getD i false) :
        (w ++ s).getD i false = (v ++ s).getD i false := by
      by_cases hw : i < w.length
      · rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ (by omega), hi]
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]

    have fold_agree {C : Circuit} (fan : FanInTwo C) (gs : List Gate)
        (hgs : ∀ g ∈ gs, g ∈ C.gates) (w v : List Bool) (hlen : w.length = v.length)
        (same : ℕ → Prop) (h : ∀ i, same i → w.getD i false = v.getD i false)
        (hr : ∀ g ∈ gs, ∀ i ∈ reads g, same i) :
        ∃ t, gs.foldl step w = w ++ t ∧ gs.foldl step v = v ++ t := by
      induction gs generalizing w v with
      | nil => exact ⟨[], by simp, by simp⟩
      | cons g tail ih =>
        have eq : gateValue w g = gateValue v g :=
          gateValue_congr fan (hgs g List.mem_cons_self) w v
            (fun i hi => h i (hr g List.mem_cons_self i hi))
        have len : (step w g).length = (step v g).length := by
          change (w ++ [gateValue w g]).length = (v ++ [gateValue v g]).length
          simp only [List.length_append, List.length_singleton, hlen]
        have agree (i : ℕ) (hi : same i) :
            (step w g).getD i false = (step v g).getD i false := by
          change (w ++ [gateValue w g]).getD i false = (v ++ [gateValue v g]).getD i false
          rw [eq]
          exact append_agree hlen _ i (h i hi)
        obtain ⟨s,hs,ht⟩ := ih (fun d hd => hgs d (List.mem_cons_of_mem _ hd)) _ _ len agree
          (fun d hd => hr d (List.mem_cons_of_mem _ hd))
        refine ⟨gateValue w g :: s, ?_, ?_⟩
        · rw [List.foldl_cons, hs]
          change (w ++ [gateValue w g]) ++ s = _
          rw [List.append_assoc]
          rfl
        · rw [List.foldl_cons, ht]
          change (v ++ [gateValue v g]) ++ s = _
          rw [List.append_assoc, ← eq]
          rfl

    have fold_prefix (gs : List Gate) (w : List Bool) :
        ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
      induction gs generalizing w with
      | nil => exact ⟨[], by simp, rfl⟩
      | cons g gs ih =>
        obtain ⟨t,ht,hl⟩ := ih (step w g)
        refine ⟨gateValue w g :: t, ?_, by simp [hl]⟩
        rw [List.foldl_cons, ht]
        change (w ++ [gateValue w g]) ++ t = _
        rw [List.append_assoc]
        rfl

    have eval_raw (C : Circuit) (w : List Bool) (i : ℕ)
        (hi : i < w.length) : (C.wires w).getD i false = w.getD i false := by
      change (C.gates.foldl step w).getD i false = _
      obtain ⟨t, ht, _⟩ := fold_prefix C.gates w
      rw [ht, List.getD_append _ _ _ _ hi]

    have has_reader {C : Circuit} (fan : FanInTwo C) (w v : List Bool)
        (hlen : w.length = v.length) (same : ℕ → Prop) (hout : same C.output)
        (hraw : ∀ i, same i → w.getD i false = v.getD i false)
        (hne : C.eval w ≠ C.eval v) :
        ∃ g ∈ C.gates, ∃ i ∈ reads g, ¬ same i := by
      by_contra! hnone
      obtain ⟨t,hw,hv⟩ := fold_agree fan C.gates (fun _ h => h) w v hlen same hraw hnone
      apply hne
      change (C.gates.foldl step w).getD C.output false = (C.gates.foldl step v).getD C.output false
      rw [hw,hv]
      exact append_agree hlen t _ (hraw _ hout)

    let probe (p : Fin 3) (i : Fin 9) : Bool :=
      decide (i = 0 ∨ i = 8 ∨ (p = 1 ∧ i = 2) ∨ (p = 2 ∧ i = 7))

    let plusSix (p : Fin 3) (i : Fin 9) : Bool := decide (i = 6) || probe p i

    have agree_rows (p : Fin 3) (i : ℕ) (hne : i ≠ 6) :
        (inputs (probe p)).getD i false = (inputs (plusSix p)).getD i false := by
      have short : ∀ (p : Fin 3) (i : Fin 10), i.val ≠ 6 →
          (inputs (probe p)).getD i.val false = (inputs (plusSix p)).getD i.val false := by decide +kernel
      by_cases hi : i < 10
      · exact short p ⟨i,hi⟩ hne
      · rw [List.getD_eq_default _ _ (by rw [input_length]; omega),
          List.getD_eq_default _ _ (by rw [input_length]; omega)]

    have different_rows (C : Circuit)
        (ev : ∀ x : Fin 9 → Bool, C.eval (inputs x) = F x) (p : Fin 3) :
        C.eval (inputs (probe p)) ≠ C.eval (inputs (plusSix p)) := by
      have diff : ∀ p : Fin 3, F (probe p) ≠ F (plusSix p) := by decide +kernel
      rw [ev,ev]
      exact diff p

    have read6_iff (g : Gate) : hits6 g = true ↔ 6 ∈ reads g := by
      change (reads g).any _ = true ↔ _
      rw [List.any_eq_true]
      constructor
      · rintro ⟨i,hi,h⟩
        exact (of_decide_eq_true h) ▸ hi
      · intro h
        exact ⟨6,h,rfl⟩

    have output_not_six (C : Circuit)
        (ev : ∀ x : Fin 9 → Bool, C.eval (inputs x) = F x) : C.output ≠ 6 := by
      intro hout
      let x : Fin 9 → Bool := fun i => decide (i = 6)
      have h := ev x
      change (C.wires (inputs x)).getD C.output false = F x at h
      rw [hout, eval_raw C _ 6 (by rw [input_length]; decide)] at h
      contradiction

    have six_required (C : Circuit) (fan : FanInTwo C)
        (ev : ∀ x : Fin 9 → Bool, C.eval (inputs x) = F x) :
        1 ≤ C.gates.countP hits6 := by
      obtain ⟨g,hg,i,hi,h⟩ := has_reader fan (inputs (probe 0)) (inputs (plusSix 0))
        (by rw [input_length,input_length]) (fun i => i ≠ 6) (output_not_six C ev)
        (agree_rows 0) (different_rows C ev 0)
      have yes : hits6 g = true := (read6_iff g).2 ((not_not.mp h) ▸ hi)
      have mem : g ∈ C.gates.filter hits6 := List.mem_filter.mpr ⟨hg,yes⟩
      rw [List.countP_eq_length_filter]
      have p := List.length_pos_of_mem mem
      omega

    have splitClean (C : Circuit) (before after : List Gate) (g : Gate)
        (split : C.gates = before ++ g :: after) (hg : hits6 g = true)
        (count : C.gates.countP hits6 = 1) :
        (∀ h ∈ before, 6 ∉ reads h) ∧ (∀ h ∈ after, 6 ∉ reads h) := by
      rw [split, List.countP_append,List.countP_cons,hg] at count
      simp only [ite_true] at count
      have left : before.countP hits6 = 0 := by omega
      have right : after.countP hits6 = 0 := by omega
      rw [List.countP_eq_length_filter] at left right
      constructor
      · intro h hm hr
        have hm' := List.mem_filter.mpr ⟨hm,(read6_iff h).2 hr⟩
        have := List.length_pos_of_mem hm'
        omega
      · intro h hm hr
        have hm' := List.mem_filter.mpr ⟨hm,(read6_iff h).2 hr⟩
        have := List.length_pos_of_mem hm'
        omega

    have pivotEval (C : Circuit) (before after : List Gate) (g : Gate)
        (split : C.gates = before ++ g :: after) (w : List Bool) :
        (C.wires w).getD (w.length + before.length) false = gateValue (before.foldl step w) g := by
      obtain ⟨t,ht,hl⟩ := fold_prefix before w
      obtain ⟨s,hs,_⟩ := fold_prefix after (step (before.foldl step w) g)
      change (C.gates.foldl step w).getD _ false = _
      rw [split,List.foldl_append,List.foldl_cons,hs]
      have yi : (before.foldl step w).length = w.length + before.length := by
        rw [ht,List.length_append,hl]
      rw [← yi]
      rw [List.getD_append _ _ _ _ (by simp [step])]
      change ((before.foldl step w) ++ [gateValue (before.foldl step w) g]).getD _ false = _
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
      rfl

    have prefixRaw (before : List Gate) (x : Fin 9 → Bool) (i : ℕ) (hi : i < 10) :
        (before.foldl step (inputs x)).getD i false = (inputs x).getD i false := by
      obtain ⟨t,ht,_⟩ := fold_prefix before (inputs x)
      rw [ht,List.getD_append _ _ _ _ (by rw [input_length]; exact hi)]

    have output_not_pivot (C : Circuit) (fan : FanInTwo C)
        (ev : ∀ x : Fin 9 → Bool, C.eval (inputs x) = F x)
        (before after : List Gate) (g : Gate) (split : C.gates = before ++ g :: after)
        (hg : hits6 g = true) :
        C.output ≠ 10 + before.length := by
      intro hOut
      have mem : g ∈ C.gates := by rw [split]; simp
      have read := (read6_iff g).1 hg
      have outputEq (x : Fin 9 → Bool) : gateValue (before.foldl step (inputs x)) g = F x := by
        have h := ev x
        change (C.wires (inputs x)).getD C.output false = F x at h
        rw [hOut, ← input_length x, pivotEval C before after g split] at h
        exact h
      rcases gate_kind fan mem with hAnd | hOr | hNot
      · let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
        have h := outputEq x
        have hz : (before.foldl step (inputs x)).getD 6 false = false :=
          (prefixRaw _ _ 6 (by decide)).trans rfl
        have hi : 6 ∈ g.inputs := by
          simpa only [reads, hAnd, show GateOp.eval .and [false] = false from rfl,
            Bool.false_eq_true, ite_false] using read
        change GateOp.eval g.op _ = F x at h
        rw [hAnd] at h
        change (_ : List Bool).all id = true at h
        have bad := List.all_eq_true.mp h false (List.mem_map.mpr ⟨6,hi,hz⟩)
        contradiction
      · let x : Fin 9 → Bool := fun i => decide (i = 6)
        have h := outputEq x
        have hz : (before.foldl step (inputs x)).getD 6 false = true :=
          (prefixRaw _ _ 6 (by decide)).trans rfl
        have hi : 6 ∈ g.inputs := by
          simpa only [reads, hOr, show GateOp.eval .or [false] = false from rfl,
            Bool.false_eq_true, ite_false] using read
        change GateOp.eval g.op _ = F x at h
        rw [hOr] at h
        change (_ : List Bool).any id = false at h
        have bad : (g.inputs.map fun i => (before.foldl step (inputs x)).getD i false).any id = true :=
          List.any_eq_true.mpr ⟨true,List.mem_map.mpr ⟨6,hi,hz⟩,rfl⟩
        rw [h] at bad
        contradiction
      · let x : Fin 9 → Bool := fun _ => false
        have h := outputEq x
        have hz : (before.foldl step (inputs x)).getD 6 false = false :=
          (prefixRaw _ _ 6 (by decide)).trans rfl
        have hi : 6 ∈ g.inputs.take 1 := by
          simpa only [reads, hNot, show GateOp.eval .not [false] = true from rfl, ite_true] using read
        change GateOp.eval g.op _ = F x at h
        rw [hNot] at h
        cases hs : g.inputs with
        | nil => rw [hs] at hi; cases hi
        | cons i is =>
          rw [hs] at hi h
          have eq : 6 = i := by simpa using hi
          subst i
          change Bool.not ((before.foldl step (inputs x)).getD 6 false) = F x at h
          rw [hz] at h
          contradiction

    have step_agree_off_last {w v : List Bool} (len : w.length = v.length)
        (a b : Bool) (i : ℕ) (hoff : i ≠ w.length)
        (hi : w.getD i false = v.getD i false) :
        (w ++ [a]).getD i false = (v ++ [b]).getD i false := by
      by_cases hlt : i < w.length
      · rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ (by omega)]
        exact hi
      · have hleft : (w ++ [a]).length ≤ i := by
          simp only [List.length_append, List.length_singleton]; omega
        have hright : (v ++ [b]).length ≤ i := by
          simp only [List.length_append, List.length_singleton]; omega
        rw [List.getD_eq_default _ _ hleft, List.getD_eq_default _ _ hright]

    have same_prefix (C : Circuit) (fan : FanInTwo C)
        (before after : List Gate) (g : Gate) (split : C.gates = before ++ g :: after)
        (hg : hits6 g = true) (count : C.gates.countP hits6 = 1) (p : Fin 3) :
        ∃ t,
          before.foldl step (inputs (probe p)) = inputs (probe p) ++ t ∧
          before.foldl step (inputs (plusSix p)) = inputs (plusSix p) ++ t := by
      have clean := (splitClean C before after g split hg count).1
      apply fold_agree fan before
      · intro h hh
        rw [split]
        exact List.mem_append.mpr (Or.inl hh)
      · rw [input_length,input_length]
      · exact agree_rows p
      · intro d hd i hi he
        subst i
        exact clean d hd hi

    have fold_length (gs : List Gate) (w : List Bool) :
        (gs.foldl step w).length = w.length + gs.length := by
      obtain ⟨t,ht,hl⟩ := fold_prefix gs w
      rw [ht,List.length_append,hl]

    have eval_after (C : Circuit)
        (before after : List Gate) (g : Gate) (split : C.gates = before ++ g :: after)
        (w : List Bool) :
        (⟨after,C.output⟩ : Circuit).eval (step (before.foldl step w) g) = C.eval w := by
      change (after.foldl step (step (before.foldl step w) g)).getD C.output false =
        (C.gates.foldl step w).getD C.output false
      rw [split,List.foldl_append,List.foldl_cons]

    have fan_after (C : Circuit) (fan : FanInTwo C)
        (before after : List Gate) (g : Gate) (split : C.gates = before ++ g :: after) :
        FanInTwo (⟨after,C.output⟩ : Circuit) := by
      intro h hh
      apply fan h
      rw [split]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hh))

    have unique_has_follower (C : Circuit) (fan : FanInTwo C)
        (ev : ∀ x : Fin 9 → Bool, C.eval (inputs x) = F x)
        (before after : List Gate) (g : Gate) (split : C.gates = before ++ g :: after)
        (hg : hits6 g = true) (count : C.gates.countP hits6 = 1) :
        ∃ h ∈ after, 10 + before.length ∈ reads h := by
      let R : Circuit := ⟨after,C.output⟩
      let w := before.foldl step (inputs (probe 0))
      let v := before.foldl step (inputs (plusSix 0))
      let same := fun i : ℕ => i ≠ 6 ∧ i ≠ 10 + before.length
      have wl : w.length = 10 + before.length := by
        change (before.foldl step _).length = _
        rw [fold_length,input_length]
      have vl : v.length = 10 + before.length := by
        change (before.foldl step _).length = _
        rw [fold_length,input_length]
      have sl : (step w g).length = (step v g).length := by
        change (w ++ [_]).length = (v ++ [_]).length
        simp only [List.length_append,List.length_singleton,wl,vl]
      have raw (i : ℕ) (hi : same i) : (step w g).getD i false = (step v g).getD i false := by
        change (w ++ [_]).getD i false = (v ++ [_]).getD i false
        apply step_agree_off_last (wl.trans vl.symm) _ _ i
        · rw [wl]
          exact hi.2
        · obtain ⟨t,ht,hs⟩ := same_prefix C fan before after g split hg count 0
          change (before.foldl step _).getD i false = (before.foldl step _).getD i false
          rw [ht,hs]
          exact append_agree (by rw [input_length,input_length]) t i (agree_rows 0 i hi.1)
      have diff : R.eval (step w g) ≠ R.eval (step v g) := by
        change (⟨after,C.output⟩ : Circuit).eval (step _ g) ≠
          (⟨after,C.output⟩ : Circuit).eval (step _ g)
        rw [eval_after C before after g split, eval_after C before after g split]
        exact different_rows C ev 0
      obtain ⟨h,hm,i,hi,hDifferent⟩ := has_reader (fan_after C fan before after g split)
        (step w g) (step v g) sl same
        ⟨output_not_six C ev,output_not_pivot C fan ev before after g split hg⟩ raw diff
      have n6 : i ≠ 6 := by
        intro e
        subst i
        exact (splitClean C before after g split hg count).2 h hm hi
      have eq : i = 10 + before.length := by
        by_contra hn
        exact hDifferent ⟨n6,hn⟩
      exact ⟨h,hm,eq ▸ hi⟩

    have assert_partner_true (k : ℕ)
        (bad : k = 0 ∨ k = 2 ∨ k = 7 ∨ k = 8 ∨ k = 9) :
        ∃ p : Fin 3,
          (inputs (probe p)).getD k false = true ∧ (inputs (plusSix p)).getD k false = true := by
      have table : ∀ i : Fin 10, (i.val = 0 ∨ i.val = 2 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9) →
        ∃ p : Fin 3, (inputs (probe p)).getD i.val false = true ∧
          (inputs (plusSix p)).getD i.val false = true := by decide +kernel
      have lt : k < 10 := by omega
      exact table ⟨k,lt⟩ bad

    have or_partner (C : Circuit) (fan : FanInTwo C)
        (ev : ∀ x : Fin 9 → Bool, C.eval (inputs x) = F x)
        (before after : List Gate) (g : Gate) (split : C.gates = before ++ g :: after)
        (hg : hits6 g = true) (count : C.gates.countP hits6 = 1)
        (hOr : g.op = .or) (k : ℕ) (hOperands : g.inputs = [6,k] ∨ g.inputs = [k,6]) :
        ¬(k = 0 ∨ k = 2 ∨ k = 7 ∨ k = 8 ∨ k = 9) := by
      intro bad
      obtain ⟨p,hp,hq⟩ := assert_partner_true k bad
      have lt : k < 10 := by omega
      have evalOr (a b : Bool) : GateOp.eval .or [a,b] = (a || b) := by
        cases a <;> cases b <;> rfl
      have pivotTrue (x : Fin 9 → Bool) (hx : (inputs x).getD k false = true) :
          gateValue (before.foldl step (inputs x)) g = true := by
        have hk := (prefixRaw before x k lt).trans hx
        change g.op.eval (g.inputs.map fun i => (before.foldl step (inputs x)).getD i false) = true
        rcases hOperands with h | h <;>
          simp only [hOr,h,List.map_cons,List.map_nil,evalOr,hk,Bool.or_true,Bool.true_or]
      let R : Circuit := ⟨after,C.output⟩
      let w := before.foldl step (inputs (probe p))
      let v := before.foldl step (inputs (plusSix p))
      let w' := step w g
      let v' := step v g
      have pstep : w' = w ++ [true] := by
        change w ++ [gateValue w g] = _
        rw [pivotTrue (probe p) hp]
      have qstep : v' = v ++ [true] := by
        change v ++ [gateValue v g] = _
        rw [pivotTrue (plusSix p) hq]
      obtain ⟨t,hpt,hqt⟩ := same_prefix C fan before after g split hg count p
      have w'repr : w' = inputs (probe p) ++ (t ++ [true]) := by
        rw [pstep]
        change before.foldl step (inputs (probe p)) ++ [true] = _
        rw [hpt,List.append_assoc]
      have v'repr : v' = inputs (plusSix p) ++ (t ++ [true]) := by
        rw [qstep]
        change before.foldl step (inputs (plusSix p)) ++ [true] = _
        rw [hqt,List.append_assoc]
      have hrs (i : ℕ) (hi : i ≠ 6) : w'.getD i false = v'.getD i false := by
        rw [w'repr,v'repr]
        exact append_agree (by rw [input_length,input_length]) _ _ (agree_rows p i hi)
      have sameLen : w'.length = v'.length := by
        simp only [w'repr,v'repr,List.length_append,input_length]
      have diff : R.eval w' ≠ R.eval v' := by
        change (⟨after,C.output⟩ : Circuit).eval (step _ g) ≠
          (⟨after,C.output⟩ : Circuit).eval (step _ g)
        rw [eval_after C before after g split, eval_after C before after g split]
        exact different_rows C ev p
      obtain ⟨h,hm,i,hi,hns⟩ := has_reader (fan_after C fan before after g split)
        w' v' sameLen (fun i => i ≠ 6) (output_not_six C ev) hrs diff
      have eq : i = 6 := not_not.mp hns
      exact (splitClean C before after g split hg count).2 h hm (eq ▸ hi)

    dsimp only
    intro D fan good
    refine ⟨six_required D fan good, ?_⟩
    intro left right g split count hg
    refine ⟨unique_has_follower D fan good left right g split hg count, ?_⟩
    intro k hOr hOperands
    have excluded := or_partner D fan good left right g split hg count hOr k hOperands
    push Not at excluded
    exact excluded
  let F := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let H := fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4)
  let pre := fun x : Fin 8 → Bool => [x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3,x 1]
  let eff := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
  let hit := fun g : Gate => (eff g).any fun i => decide (i = 6)
  let degenerate := fun (earlier : List Gate) (g : Gate) =>
      g.op = .and ∨ g.op = .not ∨
        g.op = .or ∧ ∀ i ∈ eff g, i = 6 ∨ 10 + earlier.length ≤ i
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      ((⟨gs,0⟩ : Circuit).wires w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map fun j => w.getD j false)
      change ((⟨gs,0⟩ : Circuit).wires (w ++ [b])).getD i false = _
      rw [ih (w ++ [b]) (by simp; omega), List.getD_append _ _ _ _ hi]
  intro C ok fst computed
  obtain ⟨gates,o⟩ := C
  cases gates with
  | nil =>
    have bad := fst (fun _ => true)
    contradiction
  | cons g gs =>
    by_contra short
    let T : Circuit := ⟨gs,o⟩
    have dsize : T.size ≤ 14 := by
      change ¬ 16 ≤ gs.length + 1 at short
      change gs.length ≤ 14
      omega
    have okT : FanInTwo T := fun v hv => ok v (List.mem_cons_of_mem _ hv)
    have extn (x : Fin 9 → Bool) : T.eval (List.ofFn x ++ [x 0 || x 6]) = F x := by
      let w := List.ofFn x
      let b := g.op.eval (g.inputs.map fun j => w.getD j false)
      have hn : w.length = 9 := List.length_ofFn
      have h := fst x
      change ((⟨gs,0⟩ : Circuit).wires (w ++ [b])).getD 9 false = (x 0 || x 6) at h
      rw [keep gs _ _ (by simp [hn]), List.getD_append_right _ _ _ _ (by omega), hn] at h
      change b = (x 0 || x 6) at h
      rw [← h]
      exact congrFun computed x
    have cut : ∀ x : Fin 8 → Bool,
        let y : Fin 9 → Bool := ![x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3]
        (List.ofFn y ++ [y 0 || y 6] = pre x) ∧ F y = H x := by decide +kernel
    have zero (x : Fin 8 → Bool) : T.eval (pre x) = H x := by
      let y : Fin 9 → Bool := ![x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3]
      have e := cut x
      change (List.ofFn y ++ [y 0 || y 6] = pre x) ∧ F y = H x at e
      rw [← e.1, extn, e.2]
    have negative : ∃ x : Fin 8 → Bool, T.eval (pre x) = false :=
      ⟨fun _ => false, (zero (fun _ => false)).trans rfl⟩
    have bound (E : Circuit) (fE : FanInTwo E)
        (he : ∀ x : Fin 8 → Bool, E.eval (List.ofFn x) = T.eval (pre x)) : 13 ≤ E.size := by
      by_contra h
      exact minorLower ⟨E,fE,by omega,fun x => (he x).trans (zero x)⟩
    have er := elimination T okT negative
    obtain ⟨E, fE, szE, eE⟩ := er.1
    have low := bound E fE eE
    have rew := readers T okT extn
    have one : 1 ≤ T.gates.countP hit := rew.1
    change E.size + T.gates.countP hit ≤ T.size at szE
    have only : T.gates.countP hit = 1 := by omega
    have exactSize : T.size = 14 := by omega
    obtain ⟨pivot, hpivot, mark⟩ := List.countP_pos_iff.mp (show 0 < T.gates.countP hit by omega)
    obtain ⟨left,right,hsplit⟩ := List.append_of_mem hpivot
    obtain ⟨use,forbidden⟩ := rew.2 left right pivot hsplit only mark
    have hKind := (okT pivot hpivot).1
    change pivot.op = .and ∨ pivot.op = .or ∨ pivot.op = .not at hKind
    have notBad : ¬ degenerate left pivot := by
      intro bad
      obtain ⟨R,fR,sR,eR⟩ := er.2 left right pivot hsplit only mark bad use
      have lower := bound R fR eR
      change R.size + 2 ≤ T.size at sR
      omega
    have allowed : pivot.op = .or := by
      rcases hKind with h | h | h
      · exact (notBad (Or.inl h)).elim
      · exact h
      · exact (notBad (Or.inr (Or.inl h))).elim
    have effEq : eff pivot = pivot.inputs := by
      change (if pivot.op.eval [false] then pivot.inputs.take 1 else pivot.inputs) = _
      rw [allowed]
      rfl
    have goodPartner : ∃ j ∈ pivot.inputs, j ≠ 6 ∧ j < 10 + left.length := by
      by_contra! noPartner
      apply notBad
      refine Or.inr (Or.inr ⟨allowed, fun i hi => ?_⟩)
      rw [effEq] at hi
      by_cases hi6 : i = 6
      · exact Or.inl hi6
      · exact Or.inr (noPartner i hi hi6)
    obtain ⟨k,hmem,hneq,hk⟩ := goodPartner
    have six : 6 ∈ pivot.inputs := by
      obtain ⟨i,hi,heq⟩ := List.any_eq_true.mp mark
      have e : i = 6 := of_decide_eq_true heq
      rwa [effEq, e] at hi
    have pair (l : List ℕ) (a b : ℕ) (hl : l.length ≤ 2) (ha : a ∈ l) (hb : b ∈ l)
        (hab : b ≠ a) : l = [a,b] ∨ l = [b,a] := by
      rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩
      · simp at ha
      · simp only [List.mem_singleton] at ha hb
        exact (hab (hb.trans ha.symm)).elim
      · rcases List.mem_pair.mp ha with ha | ha <;>
          rcases List.mem_pair.mp hb with hb | hb
        · exact (hab (hb.trans ha.symm)).elim
        · exact Or.inl (by rw [← ha,← hb])
        · exact Or.inr (by rw [← ha,← hb])
        · exact (hab (hb.trans ha.symm)).elim
      · simp only [List.length_cons] at hl
        omega
    have hpair := pair pivot.inputs 6 k (okT pivot hpivot).2 six hmem hneq
    obtain ⟨h0,h2,h7,h8,h9⟩ := forbidden k allowed hpair
    by_cases high : 10 ≤ k
    · exact internalCase T left right pivot k okT exactSize only hsplit allowed hpair ⟨high,hk⟩ use extn
    · have original : k = 1 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
      exact rawCase T left right pivot k okT exactSize only hsplit allowed hpair original use extn

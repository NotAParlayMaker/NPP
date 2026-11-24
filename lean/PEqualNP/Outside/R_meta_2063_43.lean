import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_2063_43
  (oneMissing :
    let S := singerLines3
    let flag := fun e : Fin 13 × Fin 13 => incidenceInput {e.1} {e.2}
    ∀ (D : Circuit) (e : Fin 13 × Fin 13), e ∈ incidences S →
      Monotone2 D → ReadsBack 26 D → D.eval (flag e) = false →
      (∀ f ∈ incidences S, f ≠ e → D.eval (flag f) = true) →
      (∀ Q, IsQuadrangle S Q → D.eval (incidenceInput Q (missLines S Q)) = false) →
      62 ≤ D.size)
  (manyCritical :
    let S := singerLines3
    let row := fun Q => incidenceInput Q (missLines S Q)
    let valid := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
      ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
    let inner := fun (C : Circuit) i => (gateAt C i).op = .and ∧
      ∃ j, (gateAt C j).op = .and ∧ InCone 26 C i j
    let hard := fun C : Circuit => (∃ i, inner C i) ∧ ∀ i, inner C i →
      (∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26+i) false = true) ∧
      2 ≤ ((incidences S).filter fun e =>
        ({C with gates := C.gates.set i ⟨.or,[]⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false).card
    ∀ C, valid C → hard C → 64 ≤ C.size) : have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → x4 x5 → x5.size < (64 : ℕ) → (∀ (x10 x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x10 x11 → ∃ (x15 : Finset (Fin (13 : ℕ))), x2 x15 ∧ (x5.wires (x3 x15)).getD ((26 : ℕ) + x10) Bool.false = Bool.true) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x4 x12 ∧ x12.size < x5.size := by
  have zeroAndPrune (n : ℕ) (C : Circuit) (i j : ℕ) (mono : Monotone2 C)
      (back : ReadsBack n C) (cone : InCone n C i j)
      (negative : ∃ w : List Bool, w.length = n ∧ (⟨C.gates.set i ⟨.or, []⟩, C.output⟩ : Circuit).eval w = false) :
      ∃ E : Circuit, Monotone2 E ∧ ReadsBack n E ∧ E.size + 2 ≤ C.size ∧
        ∀ w : List Bool, w.length = n → E.eval w = (⟨C.gates.set i ⟨.or, []⟩, C.output⟩ : Circuit).eval w := by
    clear oneMissing manyCritical
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

    let zeroGate : Gate := ⟨.or, []⟩

    let forceZero (C : Circuit) (i : ℕ) : Circuit :=
      ⟨C.gates.set i zeroGate, C.output⟩

    have absentConeFold (n i : ℕ) (gs : List Gate)
        (hread : ∀ g ∈ gs, n + i ∉ g.inputs) :
        ∀ cs : List (List ℕ), (∀ j, i ∉ cs.getD j []) →
          ∀ j, i ∉ (gs.foldl (coneStep n) cs).getD j [] := by
      induction gs with
      | nil => intro cs h; exact h
      | cons g gs ih =>
        intro cs h
        apply ih (fun g' hg' => hread g' (List.mem_cons_of_mem _ hg')) (coneStep n cs g)
        intro j hj
        let extra := (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => (w - n) :: cs.getD (w - n) [])
        change i ∈ (cs ++ [extra]).getD j [] at hj
        by_cases he : j = cs.length
        · subst j
          rw [getD_snoc_eq] at hj
          obtain ⟨w, hw, hwv⟩ := List.mem_flatMap.mp hj
          obtain ⟨hwg, hb⟩ := List.mem_filter.mp hw
          have hn : n ≤ w := (of_decide_eq_true hb).1
          rcases List.mem_cons.mp hwv with he' | hv
          · have e : w = n + i := by omega
            exact hread g List.mem_cons_self (e ▸ hwg)
          · exact h _ hv
        · rw [getD_snoc_ne _ _ _ _ he] at hj
          exact h _ hj

    have coneHasReader (n : ℕ) (C : Circuit) (i j : ℕ) (h : InCone n C i j) :
        ∃ g ∈ C.gates, n + i ∈ g.inputs := by
      by_contra hnone
      have hread : ∀ g ∈ C.gates, n + i ∉ g.inputs :=
        fun g hg hi => hnone ⟨g, hg, hi⟩
      exact absentConeFold n i C.gates hread [] (by simp) j h

    have gateAt_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
        gateAt C k = C.gates[k] := by
      exact List.getD_eq_getElem _ _ hk

    have coneHasLaterReader (n : ℕ) (C : Circuit) (i j : ℕ)
        (back : ReadsBack n C) (h : InCone n C i j) :
        ∃ k, i < k ∧ k < C.gates.length ∧ n + i ∈ (gateAt C k).inputs := by
      obtain ⟨g, hg, hin⟩ := coneHasReader n C i j h
      obtain ⟨k, hk, hg'⟩ := List.getElem_of_mem hg
      have hAt : gateAt C k = g := (gateAt_getElem C k hk).trans hg'
      have hin' : n + i ∈ (gateAt C k).inputs := hAt.symm ▸ hin
      have hlt := back k hk (n + i) hin'
      exact ⟨k, by omega, hk, hin'⟩

    have elimStateLength (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
        (elim n gs acc).1.length = acc.1.length + gs.length := by
      induction gs generalizing acc with
      | nil => simp [elim]
      | cons g gs ih =>
        change (elim n gs (elimStep n acc g)).1.length = _
        rw [ih]
        simp [elimStep]
        omega

    let rawStates (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i.val)

    have rawStateInv (n : ℕ) (w : List Bool) (hw : w.length = n) :
        Inv n w w (rawStates n, []) := by
      refine ⟨by simp [rawStates, hw], fun i => ?_⟩
      by_cases hi : i < n
      · have hget : (rawStates n).getD i (Sum.inl false) = Sum.inr i := by
          simp [rawStates, List.getD_eq_getElem?_getD, hi]
        change validStat n ((rawStates n).getD i (Sum.inl false)) ∧
          readStat w ((rawStates n).getD i (Sum.inl false)) = w.getD i false
        rw [hget]
        exact ⟨hi, rfl⟩
      · have hget : (rawStates n).getD i (Sum.inl false) = Sum.inl false := by
          exact List.getD_eq_default _ _ (by simpa only [rawStates, List.length_ofFn] using Nat.le_of_not_gt hi)
        change validStat n ((rawStates n).getD i (Sum.inl false)) ∧
          readStat w ((rawStates n).getD i (Sum.inl false)) = w.getD i false
        rw [hget, List.getD_eq_default _ _ (by omega)]
        exact ⟨trivial, rfl⟩

    have zeroBetweenBudget (n : ℕ) (before after : List Gate)
        (hbefore : ∀ g ∈ before, NOk g) (hafter : ∀ g ∈ after, NOk g)
        (hread : ∃ g ∈ after, n + before.length ∈ g.inputs) :
        (elim n (before ++ zeroGate :: after) (rawStates n, [])).2.length + 2 ≤
          (before ++ zeroGate :: after).length := by
      let first := elim n before (rawStates n, [])
      let next := (first.1 ++ [Sum.inl false], first.2)
      let mask := fun k : ℕ => decide (k = n + before.length)
      have hlen : first.1.length = n + before.length := by
        simp [first, elimStateLength, rawStates]
      have hprefix : first.2.length ≤ before.length := by
        have h := elimCountFrozen n (fun _ => false) before (rawStates n, []) hbefore (by simp)
        change first.2.length + _ ≤ 0 + before.length at h
        omega
      have htail := elimCountFrozen n mask after next hafter (by
        intro k hk
        have e : k = first.1.length := (of_decide_eq_true hk).trans hlen.symm
        subst k
        exact ⟨by simp [next], false, getD_snoc_eq _ _ _⟩)
      have hone : 0 < after.countP (fun g => g.inputs.any mask) := by
        obtain ⟨g, hg, hi⟩ := hread
        exact List.countP_pos_iff.mpr ⟨g, hg, List.any_eq_true.mpr ⟨_, hi, by simp [mask]⟩⟩
      have hfold : elim n (before ++ zeroGate :: after) (rawStates n, []) = elim n after next := by
        change (before ++ zeroGate :: after).foldl (elimStep n) (rawStates n, []) =
          after.foldl (elimStep n) next
        rw [List.foldl_append, List.foldl_cons]
        change after.foldl (elimStep n) (elimStep n first zeroGate) = _
        have e : elimStep n first zeroGate = next := by
          simp [elimStep, zeroGate, simplify, simpOr, next]
        rw [e]
      rw [hfold]
      change (elim n after next).2.length + after.countP (fun g => g.inputs.any mask) ≤
        first.2.length + after.length at htail
      simp only [List.length_append, List.length_cons]
      omega

    let MonoGate (g : Gate) : Prop :=
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

    have mono_nok {g : Gate} (h : MonoGate g) : NOk g := by
      obtain ⟨hs, hl⟩ := h
      rcases hs with ha | ho
      · exact ⟨⟨Or.inl ha, hl⟩, fun hn => by rw [ha] at hn; cases hn⟩
      · exact ⟨⟨Or.inr (Or.inl ho), hl⟩, fun hn => by rw [ho] at hn; cases hn⟩

    have simplifyTopo (op : GateOp) (m : ℕ) (ins : List Stat)
        (hop : op = .and ∨ op = .or) (hv : ∀ s ∈ ins, validStat m s) :
        ∀ g ∈ (simplify op m ins).1, MonoGate g ∧ ∀ i ∈ g.inputs, i < m := by
      intro g hg
      rcases hop with rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp [simplify, simpAnd] at hg
        subst g
        refine ⟨⟨Or.inl rfl, le_rfl⟩, fun i hi => ?_⟩
        exact hv (Sum.inr i) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
          rcases hi with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl)
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp [simplify, simpOr] at hg
        subst g
        refine ⟨⟨Or.inr rfl, le_rfl⟩, fun i hi => ?_⟩
        exact hv (Sum.inr i) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
          rcases hi with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl)

    have appendTopo (n : ℕ) (gs : List Gate) (extra : Option Gate)
        (h : Monotone2 ⟨gs, 0⟩ ∧ ReadsBack n ⟨gs, 0⟩)
        (hNew : ∀ g ∈ extra, MonoGate g ∧ ∀ i ∈ g.inputs, i < n + gs.length) :
        Monotone2 ⟨gs ++ extra.toList, 0⟩ ∧ ReadsBack n ⟨gs ++ extra.toList, 0⟩ := by
      cases extra with
      | none => simpa using h
      | some g =>
        obtain ⟨hg, hr⟩ := hNew g (by simp)
        change Monotone2 ⟨gs ++ [g], 0⟩ ∧ ReadsBack n ⟨gs ++ [g], 0⟩
        constructor
        · intro g' hm
          rcases List.mem_append.mp hm with hm | hm
          · exact h.1 g' hm
          · have e := List.mem_singleton.mp hm
            subst g'
            exact hg
        · intro j hj i hi
          change j < (gs ++ [g]).length at hj
          change i ∈ ((gs ++ [g]).getD j ⟨.or, []⟩).inputs at hi
          by_cases hj' : j < gs.length
          · rw [List.getD_append _ _ _ _ hj'] at hi
            exact h.2 j hj' i hi
          · have e : j = gs.length := by
              simp only [List.length_append, List.length_cons, List.length_nil] at hj
              omega
            subst j
            rw [getD_snoc_eq] at hi
            exact hr i hi

    have elimTopo (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
        ∀ w acc, (∀ g ∈ gs, MonoGate g) → Inv n y w acc →
          (Monotone2 ⟨acc.2, 0⟩ ∧ ReadsBack n ⟨acc.2, 0⟩) →
          Monotone2 ⟨(elim n gs acc).2, 0⟩ ∧ ReadsBack n ⟨(elim n gs acc).2, 0⟩ := by
      induction gs with
      | nil => intro w acc hl hv ht; exact ht
      | cons g gs ih =>
        intro w acc hl hv ht
        let ins := g.inputs.map (fun i => acc.1.getD i (Sum.inl false))
        have hg := hl g List.mem_cons_self
        have hnew := simplifyTopo g.op (n + acc.2.length) ins hg.1 (by
          intro s hs
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
          exact (hv.2 i).1)
        have hinv := inv_elim n y hy [g] w acc (by
          intro g' hg'
          have e := List.mem_singleton.mp hg'
          subst g'
          exact (mono_nok hg).1) hv
        exact ih _ _ (fun g' hg' => hl g' (List.mem_cons_of_mem g hg')) hinv
          (appendTopo n acc.2 (simplify g.op (n + acc.2.length) ins).1 ht hnew)

    obtain ⟨k, hik, hk, hkread⟩ := coneHasLaterReader n C i j back cone
    have hi : i < C.gates.length := by omega
    let before := C.gates.take i
    let after := C.gates.drop (i + 1)
    have hbefore : before.length = i := by
      change (C.gates.take i).length = i
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    have hlen : (forceZero C i).gates.length = C.gates.length := by
      change (C.gates.set i zeroGate).length = _
      simp
    have hshape : (forceZero C i).gates = before ++ zeroGate :: after := by
      change C.gates.set i zeroGate = _
      rw [List.set_eq_take_append_cons_drop, ite_eq_left hi]
    have hp (g) (hg : g ∈ before) : MonoGate g := mono g (List.mem_of_mem_take hg)
    have hq (g) (hg : g ∈ after) : MonoGate g := mono g (List.mem_of_mem_drop hg)
    have hread : ∃ g ∈ after, n + before.length ∈ g.inputs := by
      have hidx : k - (i + 1) < after.length := by simp [after]; omega
      refine ⟨after[k - (i + 1)], List.getElem_mem hidx, ?_⟩
      have e : i + 1 + (k - (i + 1)) = k := by omega
      simpa only [after, List.getElem_drop, e, hbefore, gateAt_getElem C k hk] using hkread
    let gs := before ++ zeroGate :: after
    let acc := elim n gs (rawStates n, [])
    have hlegal (g) (hg : g ∈ gs) : MonoGate g := by
      rcases List.mem_append.mp hg with hg | hg
      · exact hp g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inr rfl, by decide⟩
      · exact hq g hg
    have hbudget : acc.2.length + 2 ≤ C.size := by
      have h := zeroBetweenBudget n before after
        (fun g hg => mono_nok (hp g hg)) (fun g hg => mono_nok (hq g hg)) hread
      have hs : gs.length = C.size := by
        change (before ++ zeroGate :: after).length = C.gates.length
        rw [← hshape, hlen]
      change acc.2.length + 2 ≤ gs.length at h
      rw [← hs]
      exact h
    have hval (w : List Bool) (hw : w.length = n) :
        readStat (wiresFrom acc.2 w) (acc.1.getD C.output (Sum.inl false)) =
          (forceZero C i).eval w := by
      have he := inv_elim n w hw gs w (rawStates n, [])
        (fun g hg => (mono_nok (hlegal g hg)).1) (rawStateInv n w hw)
      change _ = (wiresFrom (forceZero C i).gates w).getD C.output false
      rw [hshape]
      exact (he.2 C.output).2
    obtain ⟨w, hw, hneg⟩ := negative
    have hTopo := elimTopo n w hw gs w (rawStates n, []) hlegal (rawStateInv n w hw) (by
      constructor
      · intro g hg
        cases hg
      · intro k hk
        simp at hk)
    cases hout : acc.1.getD C.output (Sum.inl false) with
    | inr l =>
      refine ⟨⟨acc.2, l⟩, hTopo.1, hTopo.2, hbudget, fun x hx => ?_⟩
      have h := hval x hx
      rw [hout] at h
      exact h
    | inl b =>
      cases b
      · refine ⟨⟨[], n⟩, ?_, ?_, ?_, fun x hx => ?_⟩
        · intro g hg
          cases hg
        · intro k hk
          simp at hk
        · change 0 + 2 ≤ C.size
          omega
        · change x.getD n false = _
          rw [List.getD_eq_default _ _ (by omega), ← hval x hx, hout]
          rfl
      · have h := hval w hw
        rw [hout, hneg] at h
        cases h
  have forceZeroReject (C : Circuit) (hMono : Monotone2 C) (i : ℕ) (x : List Bool) :
      C.eval x = false → ({C with gates := C.gates.set i ⟨.or,[]⟩} : Circuit).eval x = false := by
    clear oneMissing manyCritical zeroAndPrune
    let leW := fun (a b : List Bool) =>
      a.length = b.length ∧ ∀ k, a.getD k false = true → b.getD k false = true
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
    have refl (a : List Bool) : leW a a := ⟨rfl, fun _ h => h⟩
    have extend (a b : List Bool) (u v : Bool) (hab : leW a b) (huv : u = true → v = true) :
        leW (a ++ [u]) (b ++ [v]) := by
      refine ⟨?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, hab.1]
      intro k h
      by_cases hk : k < a.length
      · rw [List.getD_append a [u] false k hk] at h
        rw [List.getD_append b [v] false k (hab.1 ▸ hk)]
        exact hab.2 k h
      · rw [List.getD_append_right a [u] false k (Nat.le_of_not_lt hk)] at h
        rw [List.getD_append_right b [v] false k (hab.1 ▸ Nat.le_of_not_lt hk), ← hab.1]
        cases hsub : k - a.length with
        | zero =>
          rw [hsub] at h
          exact huv h
        | succ t =>
          have hf : ([u] : List Bool).getD (t + 1) false = false := rfl
          rw [hsub, hf] at h
          contradiction
    have stepMono (a b : List Bool) (g : Gate) (hOp : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
        (hab : leW a b) : leW (step a g) (step b g) := by
      apply extend a b _ _ hab
      change g.op = .and ∨ g.op = .or at hOp
      rcases hOp with hAnd | hOr
      · rw [hAnd]
        change ((g.inputs.map fun k => a.getD k false).all id = true →
          (g.inputs.map fun k => b.getD k false).all id = true)
        intro h
        apply List.all_eq_true.mpr
        intro value mem
        obtain ⟨k,hk,rfl⟩ := List.mem_map.mp mem
        exact hab.2 k (List.all_eq_true.mp h _ (List.mem_map.mpr ⟨k,hk,rfl⟩))
      · rw [hOr]
        change ((g.inputs.map fun k => a.getD k false).any id = true →
          (g.inputs.map fun k => b.getD k false).any id = true)
        simp only [List.any_eq_true, List.mem_map, id_eq]
        rintro ⟨_, ⟨k,hk,rfl⟩,hkV⟩
        exact ⟨_, ⟨k,hk,rfl⟩,hab.2 k hkV⟩
    have foldMono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
        (a b : List Bool) (hab : leW a b) : leW (gs.foldl step a) (gs.foldl step b) := by
      induction gs generalizing a b with
      | nil => exact hab
      | cons g gs ih =>
        exact ih (fun d hd => hg d (List.mem_cons_of_mem _ hd)) _ _
          (stepMono a b g (hg g List.mem_cons_self) hab)
    have lower (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
        (k : ℕ) (w : List Bool) :
        leW ((gs.set k ⟨.or,[]⟩).foldl step w) (gs.foldl step w) := by
      induction gs generalizing k w with
      | nil => exact refl w
      | cons g gs ih =>
        have tailOps : ∀ d ∈ gs, d.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
          fun d hd => hg d (List.mem_cons_of_mem _ hd)
        cases k with
        | zero =>
          apply foldMono gs tailOps
          exact extend w w false _ (refl w) (by intro h; contradiction)
        | succ k =>
          exact ih tailOps k (step w g)
    intro h
    have leC := (lower C.gates (fun g hg => (hMono g hg).1) i x).2 C.output
    cases hV : ({C with gates := C.gates.set i ⟨.or,[]⟩} : Circuit).eval x with
    | false => rfl
    | true =>
      have ht : C.eval x = true := leC hV
      rw [h] at ht
      contradiction
  intro x1 x2 x3 x4 C mono back ok small hDirty hNested
  have geom : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ x1 (p-l) = true := by decide +kernel
  have isQ (Q : Finset (Fin 13)) : IsQuadrangle singerLines3 Q ↔ x2 Q := by
    have eq (l : Fin 13) : Q ∩ singerLines3 l = {p ∈ Q | x1 (p-l) = true} := by
      ext p
      simp only [Finset.mem_inter,Finset.mem_filter]
      exact and_congr_right fun _ => geom p l
    change (_ ∧ ∀ l, (Q ∩ singerLines3 l).card ≤ 2) ↔
      (_ ∧ ∀ l, (Q.filter fun p => x1 (p-l) = true).card ≤ 2)
    simp only [eq]
  have rows (Q : Finset (Fin 13)) : incidenceInput Q (missLines singerLines3 Q) = x3 Q := by
    change List.ofFn _ ++ List.ofFn _ = List.ofFn _ ++ List.ofFn _
    apply congrArg (List.append (List.ofFn fun p : Fin 13 => decide (p ∈ Q)))
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    change (l ∈ (Finset.univ.filter fun w : Fin 13 => Disjoint (singerLines3 w) Q)) ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_right]
    exact forall₂_congr fun p _ => by rw [geom]; simp
  have flagRow (p l : Fin 13) :
      incidenceInput {p} {l} =
        (List.ofFn fun a : Fin 13 => decide (a = p)) ++
          List.ofFn (fun b : Fin 13 => decide (b = l)) := by
    change (List.ofFn fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))) = _
    simp only [Finset.mem_singleton]
  have positive : RightOnIncidentPairs singerLines3 C := by
    intro l p hp
    rw [flagRow]
    exact ok.1 p l ((geom p l).mp hp)
  have negative : ∀ Q, IsQuadrangle singerLines3 Q →
      C.eval (incidenceInput Q (missLines singerLines3 Q)) = false := by
    intro Q hQ
    rw [rows]
    exact ok.2 Q ((isQ Q).mp hQ)
  let S := singerLines3
  let flag := fun e : Fin 13 × Fin 13 => incidenceInput {e.1} {e.2}
  let row := fun Q => incidenceInput Q (missLines S Q)
  have len (A B : Finset (Fin 13)) : (incidenceInput A B).length = 26 := by
    change ((List.ofFn fun a : Fin 13 => decide (a ∈ A)) ++
      List.ofFn (fun b : Fin 13 => decide (b ∈ B))).length = 26
    simp only [List.length_append, List.length_ofFn]
  let inner := fun (i : ℕ) => (gateAt C i).op = .and ∧
    ∃ j, (gateAt C j).op = .and ∧ InCone 26 C i j
  let forced := fun (i : ℕ) => ({C with gates := C.gates.set i ⟨.or,[]⟩} : Circuit)
  let lost := fun i => (incidences S).filter fun e => (forced i).eval (flag e) = false
  have nested : ∃ i, inner i := by
    obtain ⟨i,j,hi,hj,hij⟩ := hNested
    exact ⟨i,hi,j,hj,hij⟩
  by_cases hAll : ∀ i, inner i → 2 ≤ (lost i).card
  · have sufficient := manyCritical C ⟨mono,back,positive,negative⟩
      ⟨nested, fun i hi => ⟨by
        obtain ⟨j,hj,hij⟩ := hi.2
        obtain ⟨Q,hQ,hV⟩ := hDirty i j hi.1 hj hij
        exact ⟨Q,(isQ Q).mpr hQ,by simpa only [row, S, rows] using hV⟩, hAll i hi⟩⟩
    exact False.elim (Nat.not_le_of_lt small sufficient)
  push Not at hAll
  obtain ⟨i,hi,hFew⟩ := hAll
  obtain ⟨j,_,hij⟩ := hi.2
  have hasNegative : ∃ w : List Bool, w.length = 26 ∧ (forced i).eval w = false := by
    let Q : Finset (Fin 13) := {0,1,2,5}
    have hQ : IsQuadrangle singerLines3 Q := by decide +kernel
    exact ⟨row Q,len _ _,forceZeroReject C mono i _ (negative Q hQ)⟩
  obtain ⟨D,hMono,hBack,hSize,hSem⟩ := zeroAndPrune 26 C i j mono back hij hasNegative
  have reject : ∀ Q, IsQuadrangle S Q → D.eval (row Q) = false :=
    fun Q hQ => (hSem (row Q) (len _ _)).trans (forceZeroReject C mono i _ (negative Q hQ))
  have isLost (e : Fin 13 × Fin 13) :
      e ∈ lost i ↔ e ∈ incidences S ∧ D.eval (flag e) = false := by
    change e ∈ ((incidences S).filter fun f => (forced i).eval (flag f) = false) ↔ _
    rw [Finset.mem_filter, hSem (flag e) (len _ _)]
  have keep (e : Fin 13 × Fin 13) (he : e ∈ incidences S) (hk : e ∉ lost i) :
      D.eval (flag e) = true := by
    cases hV : D.eval (flag e) with
    | true => rfl
    | false => exact (hk ((isLost e).mpr ⟨he,hV⟩)).elim
  by_cases hasLost : (lost i).Nonempty
  · obtain ⟨e,he⟩ := hasLost
    have atMostOne : (lost i).card ≤ 1 := by omega
    have others (f : Fin 13 × Fin 13) (hf : f ∈ incidences S) (different : f ≠ e) :
        D.eval (flag f) = true := by
      apply keep f hf
      intro h
      exact different ((Finset.card_le_one.mp atMostOne) f h e he)
    obtain ⟨incident,rejected⟩ := (isLost e).mp he
    have bound := oneMissing D e incident hMono hBack rejected others reject
    omega
  refine ⟨D,hMono,hBack,⟨?_,?_⟩,by omega⟩
  · intro p l hp
    have he : (p,l) ∈ incidences S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (geom p l).mpr hp⟩
    rw [← flagRow]
    exact keep (p,l) he (fun h => hasLost ⟨(p,l),h⟩)
  · intro Q hQ
    rw [← rows]
    exact reject Q ((isQ Q).mpr hQ)

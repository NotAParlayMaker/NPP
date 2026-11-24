import PEqualNP.Defs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_5006_1
    (rawKnown : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (deletionKnown : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x2 : Fin (8 : ℕ) → Bool) => x1 (Fin.cons Bool.false x2)) (11 : ℕ))
    (binaryKnown : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x4 : Fin (9 : ℕ)) (x5 : Fin (9 : ℕ)), ([(34 : ℕ), (68 : ℕ), (136 : ℕ), (272 : ℕ), (1 : ℕ), (128 : ℕ), (256 : ℕ), (0 : ℕ), (32 : ℕ)].getD ↑x4 (0 : ℕ)).testBit ↑x5 = Bool.true ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true)) → (14 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.op.eval [Bool.true]) x1.gates) :
  ∀ (x1 : Fin (9 : ℕ)), x1 = (1 : Fin (9 : ℕ)) ∨ x1 = (2 : Fin (9 : ℕ)) ∨ x1 = (3 : Fin (9 : ℕ)) ∨ x1 = (4 : Fin (9 : ℕ)) ∨ x1 = (6 : Fin (9 : ℕ)) → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  have evalAnd (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := rfl
  have evalNot (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.not.eval l = !(l.headD false) := rfl
  let F (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5

  let pins (u : Fin 9) (x : Fin 9 → Bool) : List Bool :=
    List.ofFn x ++ [!x 0, x 0 || x u]

  let Allowed (u : Fin 9) : Prop := u=1 ∨ u=2 ∨ u=3 ∨ u=4 ∨ u=6

  let run (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have run_prefix (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ w : List Bool,
      ∃ t : List Bool, run gs w = w ++ t := by
    clear rawKnown deletionKnown binaryKnown
    clear Allowed pins F evalNot evalOr evalAnd
    induction gs with
    | nil => intro w; exact ⟨[], by simp [run]⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_⟩
      change run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
      rw [ht]; simp

  have run_old (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    clear rawKnown deletionKnown binaryKnown
    clear Allowed pins F evalNot evalOr evalAnd
    obtain ⟨t, ht⟩ := run_prefix gs w
    rw [ht, List.getD_append _ _ _ _ hi]

  have pos_getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
      (w ++ [b]).getD i false = w.getD i false := by
    clear rawKnown deletionKnown binaryKnown
    clear run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    by_cases h : i < w.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have pair_form (l : List ℕ) (hlen : l.length ≤ 2) (h0 : 0 ∈ l) (h9 : 9 ∈ l) :
      l = [0,9] ∨ l = [9,0] := by
    clear rawKnown deletionKnown binaryKnown
    clear pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    cases l with
    | nil => simp at h0
    | cons a l =>
      cases l with
      | nil => simp at h0 h9; omega
      | cons b l =>
        have hl : l=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
        subst l
        simp only [List.mem_cons] at h0 h9
        rcases h0 with h | h <;> rcases h9 with h' | h' <;> simp_all <;> omega

  have op_mono (op : PEqualNP.CircuitLowerBounds.GateOp) (hop : op=.and ∨ op=.or) (l : List ℕ)
      (f f' : ℕ → Bool) (hr : ∀ i ∈ l, f i=true → f' i=true) :
      op.eval (l.map f)=true → op.eval (l.map f')=true := by
    clear rawKnown deletionKnown binaryKnown
    clear pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    rcases hop with rfl | rfl
    · change (l.map f).all id=true → (l.map f').all id=true
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, id]
      intro h i hi
      exact hr i hi (h i hi)
    · change (l.map f).any id=true → (l.map f').any id=true
      simp only [List.any_map, List.any_eq_true, Function.comp_apply, id]
      rintro ⟨i,hi,hv⟩
      exact ⟨i,hi,hr i hi hv⟩

  have gate_order (g : PEqualNP.CircuitLowerBounds.Gate) (hop : g.op=.and ∨ g.op=.or) (hlen : g.inputs.length ≤ 2)
      (both : 0 ∈ g.inputs → 9 ∈ g.inputs) (a b : List Bool)
      (a0 : a.getD 0 false=true) (a9 : a.getD 9 false=false)
      (b0 : b.getD 0 false=false) (b9 : b.getD 9 false=true)
      (hr : ∀ i, i≠0 → a.getD i false=true → b.getD i false=true) :
      g.op.eval (g.inputs.map fun i => a.getD i false)=true →
        g.op.eval (g.inputs.map fun i => b.getD i false)=true := by
    clear rawKnown deletionKnown binaryKnown
    clear pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    by_cases h0 : 0 ∈ g.inputs
    · have form := pair_form g.inputs hlen h0 (both h0)
      rcases hop with hop | hop
      · rw [hop]
        change (g.inputs.map fun i => a.getD i false).all id=true →
          (g.inputs.map fun i => b.getD i false).all id=true
        rcases form with form | form <;>
          simp only [form,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,a0,a9,b0,b9] <;> decide
      · rw [hop]
        change (g.inputs.map fun i => a.getD i false).any id=true →
          (g.inputs.map fun i => b.getD i false).any id=true
        rcases form with form | form <;>
          simp only [form,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,a0,a9,b0,b9] <;> decide
    · apply op_mono g.op hop
      intro i hi
      exact hr i (fun e => h0 (e ▸ hi))

  have run_order (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (mono : ∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2)
      (both : ∀ g ∈ gs, 0 ∈ g.inputs → 9 ∈ g.inputs) :
      ∀ a b : List Bool, a.length=b.length → 11 ≤ a.length →
        a.getD 0 false=true → a.getD 9 false=false →
        b.getD 0 false=false → b.getD 9 false=true →
        (∀ i, i≠0 → a.getD i false=true → b.getD i false=true) →
        ∀ i, i≠0 → (run gs a).getD i false=true → (run gs b).getD i false=true := by
    clear rawKnown deletionKnown binaryKnown
    clear run_old run_prefix Allowed pins F evalNot evalOr evalAnd
    induction gs with
    | nil => intro a b _ _ _ _ _ _ hr; exact hr
    | cons g gs ih =>
      intro a b hl hmin a0 a9 b0 b9 hr
      let za := g.op.eval (g.inputs.map fun i => a.getD i false)
      let zb := g.op.eval (g.inputs.map fun i => b.getD i false)
      apply ih (fun h hh => mono h (List.mem_cons_of_mem _ hh))
        (fun h hh => both h (List.mem_cons_of_mem _ hh)) (a++[za]) (b++[zb])
      · simp [hl]
      · simp; omega
      · rw [List.getD_append _ _ _ _ (by omega)]; exact a0
      · rw [List.getD_append _ _ _ _ (by omega)]; exact a9
      · rw [List.getD_append _ _ _ _ (by omega)]; exact b0
      · rw [List.getD_append _ _ _ _ (by omega)]; exact b9
      · intro i hi ha
        by_cases he : i=a.length
        · subst i
          have hea : (a++[za]).getD a.length false=za := by simp
          have heb : (b++[zb]).getD a.length false=zb := by rw [hl]; simp
          rw [hea] at ha
          rw [heb]
          exact gate_order g (mono g List.mem_cons_self).1 (mono g List.mem_cons_self).2
            (both g List.mem_cons_self) a b a0 a9 b0 b9 hr ha
        · rw [pos_getD_snoc_ne _ _ _ he] at ha
          rw [pos_getD_snoc_ne _ _ _ (by omega)]
          exact hr i hi ha

  let bits (r : ℕ) : Fin 9 → Bool := fun i => r.testBit i.val

  let pinWitness (i : Fin 11) : ℕ := if i.val=9 then 0 else if i.val<9 then 2^i.val else 1

  have pin_mismatch : ∀ (u : Fin 9) (i : Fin 11),
      (pins u (bits (pinWitness i))).getD i.val false ≠ F (bits (pinWitness i)) := by
    clear rawKnown deletionKnown binaryKnown
    clear run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed evalNot evalOr evalAnd
    decide +kernel

  have output_beyond (u : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (correct : ∀ x, C.eval (pins u x)=F x) : 11 ≤ C.output := by
    clear rawKnown deletionKnown binaryKnown
    clear run_order gate_order op_mono pair_form pos_getD_snoc_ne Allowed evalNot evalOr evalAnd
    by_contra! small
    have h := pin_mismatch u ⟨C.output,small⟩
    have e := correct (bits (pinWitness ⟨C.output,small⟩))
    change (run C.gates (pins u (bits (pinWitness ⟨C.output,small⟩)))).getD C.output false = _ at e
    rw [run_old _ _ _ (by simpa only [pins,List.length_append,List.length_ofFn,List.length_cons,
      List.length_nil] using small)] at e
    exact h e

  let witness (u : Fin 9) : ℕ :=
    if u=1 then 2 else if u=2 then 20 else if u=3 then 10 else if u=4 then 16 else 80

  let row (u : Fin 9) (b : Bool) : Fin 9 → Bool := Function.update (bits (witness u)) 0 b

  have row_facts : ∀ u : Fin 9, Allowed u →
      F (row u false)=false ∧ F (row u true)=true ∧
        ∀ i : Fin 11, i.val≠0 →
          (pins u (row u true)).getD i.val false=true →
          (pins u (row u false)).getD i.val false=true := by
    clear rawKnown deletionKnown binaryKnown
    clear output_beyond pin_mismatch pinWitness run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run evalNot evalOr evalAnd
    unfold Allowed
    decide +kernel

  have raw_slots (u : Fin 9) (b : Bool) :
      (pins u (row u b)).getD 0 false=b ∧ (pins u (row u b)).getD 9 false=(!b) := by
    clear rawKnown deletionKnown binaryKnown
    clear row_facts output_beyond pin_mismatch pinWitness run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed F evalNot evalOr evalAnd
    constructor <;> rfl

  have positive_reader (u : Fin 9) (hu : Allowed u) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (mono : PEqualNP.MetaComplexity.Monotone2 C) (correct : ∀ x, C.eval (pins u x)=F x) :
      ∃ g ∈ C.gates, 0 ∈ g.inputs ∧ 9 ∉ g.inputs := by
    clear rawKnown deletionKnown binaryKnown
    clear evalNot evalOr evalAnd
    by_contra! absent
    have both : ∀ g ∈ C.gates, 0 ∈ g.inputs → 9 ∈ g.inputs := absent
    have lower := output_beyond u C correct
    have facts := row_facts u hu
    have hr : ∀ i, i≠0 → (pins u (row u true)).getD i false=true →
        (pins u (row u false)).getD i false=true := by
      intro i hi
      by_cases hlt : i<11
      · exact facts.2.2 ⟨i,hlt⟩ hi
      · rw [List.getD_eq_default _ _ (by simp [pins]; omega)]
        simp
    have h := run_order C.gates (fun g hg => mono g hg) both
      (pins u (row u true)) (pins u (row u false)) (by simp [pins]) (by simp [pins])
      (raw_slots u true).1 (raw_slots u true).2 (raw_slots u false).1 (raw_slots u false).2 hr
      C.output (by omega)
    have ht : (run C.gates (pins u (row u true))).getD C.output false=true :=
      (correct _).trans facts.2.1
    have hf := h ht
    change C.eval (pins u (row u false))=true at hf
    rw [correct, facts.1] at hf
    cases hf

  let wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wires_eq (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

  have wiresFrom_append (gs gs' : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
    clear rawKnown deletionKnown binaryKnown
    clear wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    simp [wiresFrom, List.foldl_append]

  have wiresFrom_start (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ w : List Bool,
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    clear rawKnown deletionKnown binaryKnown
    clear wiresFrom_append wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
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
    clear rawKnown deletionKnown binaryKnown
    clear wiresFrom_append wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
    rw [ht]; simp [hl]

  have getD_wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (wiresFrom gs w).getD i false = w.getD i false := by
    clear rawKnown deletionKnown binaryKnown
    clear length_wiresFrom wiresFrom_append wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
    rw [ht, List.getD_append _ _ _ _ h]

  let Ok (g : PEqualNP.CircuitLowerBounds.Gate) : Prop :=
    g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2


  have getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
      (L ++ [S]).getD j d = L.getD j d := by
    clear rawKnown deletionKnown binaryKnown
    clear Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    by_cases hj : j < L.length
    · exact List.getD_append _ _ _ _ hj
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
    clear rawKnown deletionKnown binaryKnown
    clear getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    simp

  let NOk (g : PEqualNP.CircuitLowerBounds.Gate) : Prop := Ok g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length ≤ 1)

  let Stat := Bool ⊕ Nat

  let statVal (w : List Bool) : Stat → Bool :=
    Sum.rec id (fun j => w.getD j false)

  let statValid (m : ℕ) : Stat → Prop :=
    Sum.rec (fun _ => True) (fun j => j < m)

  let simpNot (m : ℕ) (ins : List Stat) : Option PEqualNP.CircuitLowerBounds.Gate × Stat :=
    List.rec (none, Sum.inl true)
      (fun a _ _ => Sum.rec (fun c => (none, Sum.inl (!c)))
        (fun j => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.not,[j]⟩,Sum.inr m)) a) ins

  let simpAnd (m : ℕ) (ins : List Stat) : Option PEqualNP.CircuitLowerBounds.Gate × Stat :=
    let binary (a b : Stat) : Option PEqualNP.CircuitLowerBounds.Gate × Stat :=
      Sum.rec
        (fun c => Sum.rec (fun d => (none, Sum.inl (c && d)))
          (fun j => (none, bif c then Sum.inr j else Sum.inl false)) b)
        (fun j => Sum.rec (fun c => (none, bif c then Sum.inr j else Sum.inl false))
          (fun k => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.and,[j,k]⟩,Sum.inr m)) b) a
    List.rec (none, Sum.inl true)
      (fun a tail _ => List.rec (none,a)
        (fun b rest _ => List.rec (binary a b) (fun _ _ _ => (none,Sum.inl false)) rest) tail) ins

  let simpOr (m : ℕ) (ins : List Stat) : Option PEqualNP.CircuitLowerBounds.Gate × Stat :=
    let binary (a b : Stat) : Option PEqualNP.CircuitLowerBounds.Gate × Stat :=
      Sum.rec
        (fun c => Sum.rec (fun d => (none, Sum.inl (c || d)))
          (fun j => (none, bif c then Sum.inl true else Sum.inr j)) b)
        (fun j => Sum.rec (fun c => (none, bif c then Sum.inl true else Sum.inr j))
          (fun k => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.or,[j,k]⟩,Sum.inr m)) b) a
    List.rec (none, Sum.inl false)
      (fun a tail _ => List.rec (none,a)
        (fun b rest _ => List.rec (binary a b) (fun _ _ _ => (none,Sum.inl false)) rest) tail) ins

  let simplify (op : PEqualNP.CircuitLowerBounds.GateOp) (m : ℕ) (ins : List Stat) : Option PEqualNP.CircuitLowerBounds.Gate × Stat :=
    PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Option PEqualNP.CircuitLowerBounds.Gate × Stat)
      (simpAnd m ins) (simpOr m ins) (simpNot m ins)
      (fun _ => (none,Sum.inl false)) (none,Sum.inl false) op

  have simplify_ok (op : PEqualNP.CircuitLowerBounds.GateOp) (m : ℕ) (ins : List Stat) :
      ∀ g ∈ (simplify op m ins).1, Ok g := by
    clear rawKnown deletionKnown binaryKnown
    clear statValid statVal NOk getD_snoc_eq getD_snoc_ne getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
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

  have simplify_count (op : PEqualNP.CircuitLowerBounds.GateOp) (m : ℕ) (ins : List Stat)
      (hop : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ op = PEqualNP.CircuitLowerBounds.GateOp.not) (hlen : ins.length ≤ 2)
      (hnot : op = PEqualNP.CircuitLowerBounds.GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
      (simplify op m ins).1 = none := by
    clear rawKnown deletionKnown binaryKnown
    clear simplify_ok statValid statVal NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    obtain ⟨c, hc⟩ := hc
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplify, simpAnd]
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplify, simpOr]
    · have := hnot rfl
      rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

  have simplify_sound (op : PEqualNP.CircuitLowerBounds.GateOp) (hop : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ op = PEqualNP.CircuitLowerBounds.GateOp.not)
      (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
      (hv : ∀ s ∈ ins, ((fun s m => statValid m s) s) w.length) :
      ((fun s m => statValid m s) ((simplify op w.length ins).2)) (w.length + (simplify op w.length ins).1.toList.length) ∧
      ((fun s m => statVal m s) ((simplify op w.length ins).2)) (wiresFrom (simplify op w.length ins).1.toList w)
        = op.eval (ins.map (statVal w)) := by
    clear rawKnown deletionKnown binaryKnown
    clear simplify_count simplify_ok NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplify, simpAnd, statValid, statVal, evalAnd,evalOr,evalNot]
      · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, evalAnd,evalOr,evalNot, wiresFrom]
      · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
          simp_all [simplify, simpAnd, statValid, statVal, evalAnd,evalOr,evalNot, wiresFrom]
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplify, simpOr, statValid, statVal, evalAnd,evalOr,evalNot]
      · cases a <;> simp_all [simplify, simpOr, statValid, statVal, evalAnd,evalOr,evalNot, wiresFrom]
      · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
          simp_all [simplify, simpOr, statValid, statVal, evalAnd,evalOr,evalNot, wiresFrom]
      · simp at hlen
    · rcases ins with _ | ⟨a, l⟩
      · simp [simplify, simpNot, statValid, statVal, evalAnd,evalOr,evalNot]
      · cases a <;> simp_all [simplify, simpNot, statValid, statVal, evalAnd,evalOr,evalNot, wiresFrom]

  let elimStep (n : ℕ) (acc : List Stat × List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) : List Stat × List PEqualNP.CircuitLowerBounds.Gate :=
    (acc.1 ++ [(simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
      acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

  let elim (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Stat × List PEqualNP.CircuitLowerBounds.Gate) : List Stat × List PEqualNP.CircuitLowerBounds.Gate :=
    gs.foldl (elimStep n) acc

  have toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
    clear rawKnown deletionKnown binaryKnown
    clear elim elimStep simplify_sound simplify_count simplify_ok simplify simpOr simpAnd simpNot statValid statVal Stat NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    cases o <;> simp

  have elim_ok (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ acc : List Stat × List PEqualNP.CircuitLowerBounds.Gate,
      (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
    clear rawKnown deletionKnown binaryKnown
    clear toList_length_le simplify_sound simplify_count statValid statVal NOk getD_snoc_eq getD_snoc_ne getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    induction gs with
    | nil => intro acc h; exact h
    | cons g gs ih =>
      intro acc h
      apply ih (elimStep n acc g)
      intro g' hg'
      rcases List.mem_append.1 hg' with h1 | h1
      · exact h g' h1
      · exact simplify_ok _ _ _ g' (by simpa using h1)

  have elim_len (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ acc : List Stat × List PEqualNP.CircuitLowerBounds.Gate,
      (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
    clear rawKnown deletionKnown binaryKnown
    clear elim_ok simplify_sound simplify_count simplify_ok statValid statVal NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    induction gs with
    | nil => intro acc; simp [elim]
    | cons g gs ih =>
      intro acc
      have h1 := ih (elimStep n acc g)
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
      rw [h3, List.length_cons]; omega

  have stat_valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, ((fun s m => statValid m s) s) m → ((fun s m => statValid m s) s) m' := by
    clear rawKnown deletionKnown binaryKnown
    clear elim_len elim_ok toList_length_le elim elimStep simplify_sound simplify_count simplify_ok simplify simpOr simpAnd simpNot statVal NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    intro s hs
    cases s with
    | inl c => trivial
    | inr j => exact lt_of_lt_of_le hs h

  have stat_val_append (w t : List Bool) : ∀ s : Stat, ((fun s m => statValid m s) s) w.length →
      ((fun s m => statVal m s) s) (w ++ t) = ((fun s m => statVal m s) s) w := by
    clear rawKnown deletionKnown binaryKnown
    clear stat_valid_mono elim_len elim_ok toList_length_le elim elimStep simplify_sound simplify_count simplify_ok simplify simpOr simpAnd simpNot NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    intro s hs
    cases s with
    | inl c => rfl
    | inr j => exact List.getD_append _ _ _ _ hs

  let Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List PEqualNP.CircuitLowerBounds.Gate) : Prop :=
    acc.1.length = w.length ∧ ∀ i : ℕ,
      ((fun s m => statValid m s) (acc.1.getD i (Sum.inl false))) (n + acc.2.length) ∧
      ((fun s m => statVal m s) (acc.1.getD i (Sum.inl false))) (wiresFrom acc.2 y) = w.getD i false

  have inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List PEqualNP.CircuitLowerBounds.Gate) :
      ∀ (w : List Bool) (acc : List Stat × List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
        Inv n y (wiresFrom gs w) (elim n gs acc) := by
    clear rawKnown deletionKnown binaryKnown
    clear elim_len elim_ok toList_length_le simplify_count simplify_ok NOk getD_wiresFrom wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F
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
      have hs := simplify_sound g.op hgok.1 w' ins (by simpa only [hins, List.length_map] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          rw [lw']; exact (hi a).1)
      rw [lw'] at hs
      set r := simplify g.op (n + acc.2.length) ins with hr
      have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
        rw [hins, List.map_map]
        apply List.map_congr_left
        intro a _
        exact (hi a).2
      have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
        rw [wiresFrom_append]
      obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
      refine ⟨?_, ?_⟩
      · change (acc.1 ++ [r.2]).length = (w ++ [_]).length
        simp only [List.length_append, List.length_singleton, hl]
      intro i
      show ((fun s m => statValid m s) ((acc.1 ++ [r.2]).getD i (Sum.inl false))) (n + (acc.2 ++ r.1.toList).length) ∧
        ((fun s m => statVal m s) ((acc.1 ++ [r.2]).getD i (Sum.inl false))) (wiresFrom (acc.2 ++ r.1.toList) y) = _
      rw [hnew, List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq]
        exact ⟨hs.1, by rw [hs.2, hvals]⟩
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
        refine ⟨stat_valid_mono (by omega) _ (hi i).1, ?_⟩
        rw [ht, stat_val_append _ _ _ (by rw [lw']; exact (hi i).1)]
        exact (hi i).2

  have elimStep_none (n : ℕ) (acc : List Stat × List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (hg : NOk g) (k : ℕ)
      (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
      (elimStep n acc g).2.length = acc.2.length := by
    clear rawKnown deletionKnown binaryKnown
    clear inv_elim Inv stat_val_append stat_valid_mono elim_len elim_ok toList_length_le elim simplify_sound simplify_ok statValid statVal getD_snoc_eq getD_snoc_ne getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    have hnone : (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
      apply simplify_count
      · exact hg.1.1
      · simpa using hg.1.2
      · intro h; simpa using hg.2 h
      · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
    show (acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
    rw [hnone]; simp



  let marked (g : PEqualNP.CircuitLowerBounds.Gate) : Bool := g.inputs.any (fun i => decide (i=0 ∨ i=9))
  let sliceStats (u : Fin 9) : List Stat :=
    [.inl false,.inr 0,.inr 1,.inr 2,.inr 3,.inr 4,.inr 5,.inr 6,.inr 7,.inl true,.inr (u.val-1)]
  let readStats (s : List Stat) (w : List Bool) := s.map (statVal w)

  have baseInv {n : ℕ} (s : List Stat) (pre : List PEqualNP.CircuitLowerBounds.Gate) (y : List Bool)
      (valid : ∀ a ∈ s, ((fun s m => statValid m s) a) (n+pre.length)) :
      Inv n y (readStats s (wiresFrom pre y)) (s,pre) := by
    clear rawKnown deletionKnown binaryKnown
    clear sliceStats marked elimStep_none inv_elim stat_val_append stat_valid_mono elim_len elim_ok toList_length_le elim elimStep simplify_sound simplify_count simplify_ok simplify simpOr simpAnd simpNot NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    constructor
    · simp [readStats]
    intro i
    change ((fun s m => statValid m s) (s.getD i (.inl false))) (n+pre.length) ∧ ((fun s m => statVal m s) (s.getD i (.inl false))) (wiresFrom pre y) = (readStats s (wiresFrom pre y)).getD i false
    by_cases hi : i<s.length
    · rw [List.getD_eq_getElem _ _ hi]
      refine ⟨valid _ (List.getElem_mem _),?_⟩
      rw [List.getD_eq_getElem _ _ (by simpa [readStats] using hi)]
      exact (List.getElem_map ..).symm
    · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp [readStats];omega)]
      exact ⟨trivial,rfl⟩

  have extract {n budget : ℕ} (f : (Fin n → Bool) → Bool) (s : List Stat) (pre gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ)
      (ok : ∀ g ∈ gs, Ok g) (first : ∀ g ∈ pre, Ok g) (valid : ∀ a ∈ s, ((fun s m => statValid m s) a) (n+pre.length))
      (nonconst : ∃ x y, f x ≠ f y)
      (size : (elim n gs (s,pre)).2.length ≤ budget)
      (value : ∀ x : Fin n → Bool,
        (wiresFrom gs (readStats s (wiresFrom pre (List.ofFn x)))).getD o false = f x) :
      PEqualNP.MetaComplexity.HasCircuitSize n f budget := by
    clear rawKnown deletionKnown binaryKnown
    clear sliceStats marked elimStep_none elim_len toList_length_le simplify_count NOk getD_wiresFrom wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F
    let done := elim n gs (s,pre)
    have value' (x : Fin n → Bool) :
        ((fun s m => statVal m s) (done.1.getD o (.inl false))) (wiresFrom done.2 (List.ofFn x)) = f x :=
      ((inv_elim n _ (by simp) gs _ _ ok (baseInv s pre (List.ofFn x) valid)).2 o).2.trans (value x)
    cases e : done.1.getD o (.inl false) with
    | inl b =>
      obtain ⟨x,y,ne⟩ := nonconst
      apply False.elim; apply ne
      rw [← value' x,← value' y,e] <;> rfl
    | inr i =>
      refine ⟨⟨done.2,i⟩,elim_ok n gs _ first,size,?_⟩
      intro y
      have h := value' y
      rw [e] at h
      exact h

  have markedCost (gs : List PEqualNP.CircuitLowerBounds.Gate) (ok : ∀ g ∈ gs, NOk g)
      (acc : List Stat × List PEqualNP.CircuitLowerBounds.Gate)
      (base : ∀ i : ℕ, i=0 ∨ i=9 → i<acc.1.length ∧ ∃ b, acc.1.getD i (.inl false) = .inl b) :
      (elim 8 gs acc).2.length + (gs.filter marked).length ≤ acc.2.length + gs.length := by
    clear rawKnown deletionKnown binaryKnown
    clear extract baseInv readStats sliceStats inv_elim Inv stat_val_append stat_valid_mono elim_len elim_ok simplify_sound simplify_ok statValid statVal getD_snoc_eq getD_snoc_ne getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    induction gs generalizing acc with
    | nil => simp [elim]
    | cons g gs ih =>
      let next := elimStep 8 acc g
      have keep : ∀ i : ℕ, i=0 ∨ i=9 → i<next.1.length ∧ ∃ b, next.1.getD i (.inl false) = .inl b := by
        intro i h
        obtain ⟨small,b,e⟩ := base i h
        refine ⟨by simp [next,elimStep];omega,b,?_⟩
        change (acc.1++[_]).getD i (.inl false) = _
        rw [List.getD_append _ _ _ _ small,e]
      have tail := ih (fun k hk => ok k (List.mem_cons_of_mem _ hk)) next keep
      change (elim 8 gs next).2.length + ((g::gs).filter marked).length ≤ _
      by_cases h : marked g = true
      · obtain ⟨i,hi,hm⟩ := List.any_eq_true.mp h
        have prop : i=0 ∨ i=9 := of_decide_eq_true hm
        obtain ⟨_,b,e⟩ := base i prop
        have same := elimStep_none 8 acc g (ok _ List.mem_cons_self) i hi b e
        change next.2.length = acc.2.length at same
        simp [List.filter_cons,h];omega
      · have inc : next.2.length ≤ acc.2.length+1 := by
          simp only [next,elimStep,List.length_append]
          have := toList_length_le ((simplify g.op (8 + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (.inl false))).1)
          omega
        simp [List.filter_cons,h];omega

  have sliceRow (u : Fin 9) (hu : Allowed u) (y : Fin 8 → Bool) :
      readStats (sliceStats u) (wiresFrom [] (List.ofFn y)) = pins u (Fin.cons false y) := by
    clear rawKnown deletionKnown binaryKnown
    clear markedCost extract baseInv marked elimStep_none inv_elim Inv stat_val_append stat_valid_mono elim_len elim_ok toList_length_le elim elimStep simplify_sound simplify_count simplify_ok simplify simpOr simpAnd simpNot statValid NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run F evalNot evalOr evalAnd
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> rfl

  have fewReaders (cofactor : ¬PEqualNP.MetaComplexity.HasCircuitSize 8 (fun y => F (Fin.cons false y)) 11)
      (u : Fin 9) (hu : Allowed u) (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ)
      (ok : ∀ g ∈ gs, NOk g) (len : gs.length≤13)
      (hit : ∀ x, (wiresFrom gs (pins u x)).getD o false = F x) :
      (gs.filter marked).length ≤ 1 := by
    clear rawKnown deletionKnown binaryKnown
    clear elim_len getD_wiresFrom wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run
    by_contra! many
    apply cofactor
    apply extract (fun y => F (Fin.cons false y)) (sliceStats u) [] gs o
      (fun g hg => (ok g hg).1) (by simp)
    · intro a ha
      simp only [sliceStats,List.mem_cons,List.not_mem_nil,or_false] at ha
      have bound := u.isLt
      rcases ha with h|h|h|h|h|h|h|h|h|h|h <;> subst a <;>
        simp only [statValid,List.length_nil,Nat.add_zero] <;> omega
    · exact ⟨fun _ => false,fun _ => true,by decide⟩
    · have counted := markedCost gs ok (sliceStats u,[]) (by
        intro i hi; rcases hi with rfl | rfl <;> exact ⟨by simp [sliceStats],_,rfl⟩)
      simp only [List.length_nil,Nat.zero_add] at counted
      omega
    · intro y; rw [sliceRow u hu,hit]

  have outside (a b t : List Bool) (i : ℕ) (hlen : a.length=b.length)
      (atBase : a.getD i false = b.getD i false) :
      (a++t).getD i false = (b++t).getD i false := by
    clear rawKnown deletionKnown binaryKnown
    clear fewReaders sliceRow markedCost extract baseInv readStats sliceStats marked elimStep_none inv_elim Inv stat_val_append stat_valid_mono elim_len elim_ok toList_length_le elim elimStep simplify_sound simplify_count simplify_ok simplify simpOr simpAnd simpNot statValid statVal Stat NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    by_cases h : i<a.length
    · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (by omega)]; exact atBase
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),hlen]

  have sameSuffix (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : List Bool)
      (step : ∀ g ∈ gs, ∀ t : List Bool,
        g.op.eval (g.inputs.map fun i => (a++t).getD i false) =
        g.op.eval (g.inputs.map fun i => (b++t).getD i false)) (pre : List Bool) :
      ∃ t, wiresFrom gs (a++pre) = a++t ∧ wiresFrom gs (b++pre) = b++t := by
    clear rawKnown deletionKnown binaryKnown
    clear outside fewReaders sliceRow markedCost extract baseInv readStats sliceStats marked elimStep_none inv_elim Inv stat_val_append stat_valid_mono elim_len elim_ok toList_length_le elim elimStep simplify_sound simplify_count simplify_ok simplify simpOr simpAnd simpNot statValid statVal Stat NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    induction gs generalizing pre with
    | nil => exact ⟨pre,rfl,rfl⟩
    | cons g gs ih =>
      let z := g.op.eval (g.inputs.map fun i => (a++pre).getD i false)
      have e := step g List.mem_cons_self pre
      obtain ⟨t,ha,hb⟩ := ih (fun k hk => step k (List.mem_cons_of_mem _ hk)) (pre++[z])
      refine ⟨t,?_,?_⟩
      · simpa only [wiresFrom,List.foldl_cons,List.append_assoc,z] using ha
      · change wiresFrom gs ((b++pre)++[_]) = b++t
        rw [← e,List.append_assoc]; exact hb

  have sameOutput (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : List Bool) (o : ℕ) (len : a.length=b.length) (hi : a.length≤o)
      (step : ∀ g ∈ gs, ∀ t : List Bool, g.op.eval (g.inputs.map fun i => (a++t).getD i false) =
        g.op.eval (g.inputs.map fun i => (b++t).getD i false)) :
      (wiresFrom gs a).getD o false = (wiresFrom gs b).getD o false := by
    clear rawKnown deletionKnown binaryKnown
    clear outside fewReaders sliceRow markedCost extract baseInv readStats sliceStats marked elimStep_none inv_elim Inv stat_val_append stat_valid_mono elim_len elim_ok toList_length_le elim elimStep simplify_sound simplify_count simplify_ok simplify simpOr simpAnd simpNot statValid statVal Stat NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    obtain ⟨t,ha,hb⟩ := sameSuffix gs a b step []
    simp only [List.append_nil] at ha hb
    rw [ha,hb,List.getD_append_right _ _ _ _ hi,List.getD_append_right _ _ _ _ (by omega),len]

  have uniqueMarked {gs : List PEqualNP.CircuitLowerBounds.Gate} {a g : PEqualNP.CircuitLowerBounds.Gate} (cap : (gs.filter marked).length ≤ 1)
      (ha : a ∈ gs) (ma : marked a = true) (hg : g ∈ gs) (mg : marked g = true) : g=a := by
    clear rawKnown deletionKnown binaryKnown
    clear sameOutput sameSuffix outside fewReaders sliceRow markedCost extract baseInv readStats sliceStats elimStep_none inv_elim Inv stat_val_append stat_valid_mono elim_len elim_ok toList_length_le elim elimStep simplify_sound simplify_count simplify_ok simplify simpOr simpAnd simpNot statValid statVal Stat NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F evalNot evalOr evalAnd
    have p := List.mem_filter.mpr (And.intro ha ma)
    have q := List.mem_filter.mpr (And.intro hg mg)
    generalize e : gs.filter marked = l at p q cap
    cases l with
    | nil => simp at p
    | cons k l =>
      have en : l=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at cap;omega)
      subst l; simp only [List.mem_singleton] at p q; exact q.trans p.symm

  let aliasStats : List Stat :=
    [.inr 0,.inr 1,.inr 2,.inr 3,.inr 4,.inr 5,.inr 6,.inr 7,.inr 8,.inl false,.inr 9]
  let orGate (u : Fin 9) : PEqualNP.CircuitLowerBounds.Gate := ⟨.or,[0,u.val]⟩
  let altPins (u : Fin 9) (x : Fin 9 → Bool) := List.ofFn x ++ [false,x 0 || x u]

  have aliasRow (u : Fin 9) (x : Fin 9 → Bool) :
      readStats aliasStats (wiresFrom [orGate u] (List.ofFn x)) = altPins u x := by
    clear rawKnown deletionKnown binaryKnown
    clear uniqueMarked sameOutput sameSuffix outside fewReaders sliceRow markedCost extract baseInv sliceStats marked elimStep_none inv_elim Inv stat_val_append stat_valid_mono elim_len elim_ok toList_length_le elim elimStep simplify_sound simplify_count simplify_ok simplify simpOr simpAnd simpNot statValid NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed pins F
    fin_cases u <;> simp [readStats,aliasStats,wiresFrom,orGate,statVal,altPins,evalAnd,evalOr,evalNot]

  have altAgree (u : Fin 9) (x : Fin 9 → Bool) (i : ℕ) (hi : i≠9) :
      (altPins u x).getD i false = (pins u x).getD i false := by
    clear rawKnown deletionKnown binaryKnown
    clear aliasRow orGate aliasStats uniqueMarked sameOutput sameSuffix outside fewReaders sliceRow markedCost extract baseInv readStats sliceStats marked elimStep_none inv_elim Inv stat_val_append stat_valid_mono elim_len elim_ok toList_length_le elim elimStep simplify_sound simplify_count simplify_ok simplify simpOr simpAnd simpNot statValid statVal Stat NOk getD_snoc_eq getD_snoc_ne Ok getD_wiresFrom length_wiresFrom wiresFrom_start wiresFrom_append wires_eq wiresFrom positive_reader raw_slots row_facts row witness output_beyond pin_mismatch pinWitness bits run_order gate_order op_mono pair_form pos_getD_snoc_ne run_old run_prefix run Allowed F evalNot evalOr evalAnd
    by_cases small : i<11
    · interval_cases i <;> (try contradiction) <;> rfl
    · rw [List.getD_eq_default _ _ (by simp [altPins];omega),
          List.getD_eq_default _ _ (by simp [pins];omega)]

  have needNine (raw : ¬PEqualNP.MetaComplexity.HasCircuitSize 9 F 14) (u : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (fan : PEqualNP.MetaComplexity.FanInTwo C) (size : C.size≤13)
      (correct : ∀ x, C.eval (pins u x)=F x) : ∃ g ∈ C.gates, 9∈g.inputs := by
    clear rawKnown deletionKnown binaryKnown
    clear uniqueMarked fewReaders sliceRow markedCost sliceStats marked elimStep_none simplify_count NOk getD_wiresFrom wires_eq positive_reader raw_slots row_facts row witness run_order gate_order op_mono pair_form pos_getD_snoc_ne Allowed
    by_contra! absent
    have output := output_beyond u C correct
    apply raw
    apply extract F aliasStats [orGate u] C.gates C.output fan
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst g
      simp [Ok,orGate]
    · intro a ha
      simp only [aliasStats,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with h|h|h|h|h|h|h|h|h|h|h <;> subst a <;> simp [statValid]
    · exact ⟨fun _ => false,fun _ => true,by decide⟩
    · have b := elim_len 9 C.gates (aliasStats,[orGate u])
      simp only [List.length_singleton] at b
      change C.gates.length≤13 at size
      omega
    · intro x
      rw [aliasRow]
      have same := sameOutput C.gates (altPins u x) (pins u x) C.output
        (by simp [altPins,pins]) (by simpa [altPins] using output) (by
          intro g hg t
          congr 1
          apply List.map_congr_left
          intro i hi
          exact outside _ _ _ _ (by simp [altPins,pins]) (altAgree u x i (by
            intro e; subst i; exact absent g hg hi)))
      exact same.trans (correct x)

  have monotone_contradiction
      (raw : ¬PEqualNP.MetaComplexity.HasCircuitSize 9 F 14)
      (cofactor : ¬PEqualNP.MetaComplexity.HasCircuitSize 8 (fun y => F (Fin.cons false y)) 11)
      (u : Fin 9) (hu : Allowed u) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (mono : PEqualNP.MetaComplexity.Monotone2 C) (size : C.size≤13)
      (correct : ∀ x, C.eval (pins u x)=F x) : False := by
    clear rawKnown deletionKnown binaryKnown
    clear getD_wiresFrom wires_eq
    have fan : PEqualNP.MetaComplexity.FanInTwo C := by
      intro g hg
      rcases mono g hg with ⟨op,arity⟩
      refine ⟨?_,arity⟩
      rcases op with op | op
      · exact Or.inl op
      · exact Or.inr (Or.inl op)
    have normal : ∀ g ∈ C.gates, NOk g := by
      intro g hg
      refine ⟨fan g hg,?_⟩
      intro hn
      have op := (mono g hg).1
      rcases op with ha | ho
      · cases (hn.symm.trans ha)
      · cases (hn.symm.trans ho)
    have cap := fewReaders cofactor u hu C.gates C.output normal size correct
    obtain ⟨p,hp,h0,h9⟩ := positive_reader u hu C mono correct
    obtain ⟨q,hq,hq9⟩ := needNine raw u C fan size correct
    have mp : marked p=true := List.any_eq_true.mpr ⟨0,h0,by decide⟩
    have mq : marked q=true := List.any_eq_true.mpr ⟨9,hq9,by decide⟩
    have eq := uniqueMarked cap hp mp hq mq
    exact h9 (eq ▸ hq9)

  let preGates (u : Fin 9) : List PEqualNP.CircuitLowerBounds.Gate := [⟨.not,[0]⟩, ⟨.or,[0,u.val]⟩]

  let full (u : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit) : PEqualNP.CircuitLowerBounds.Circuit := ⟨preGates u ++ C.gates,C.output⟩

  have getD_ofFn {α : Type} (n : ℕ) (x : Fin n → α) (d : α) (i : Fin n) :
      (List.ofFn x).getD i.val d = x i := by simp

  have prefix_values (u : Fin 9) (x : Fin 9 → Bool) :
      run (preGates u) (List.ofFn x) = pins u x := by
    clear rawKnown deletionKnown binaryKnown
    have h0 : (List.ofFn x).getD 0 false = x 0 := getD_ofFn 9 x false 0
    have hu : (List.ofFn x).getD u.val false = x u := getD_ofFn 9 x false u
    change ((List.ofFn x ++ [!((List.ofFn x).getD 0 false)]) ++
      [((List.ofFn x ++ [!((List.ofFn x).getD 0 false)]).getD 0 false ||
        ((List.ofFn x ++ [!((List.ofFn x).getD 0 false)]).getD u.val false || false))]) = _
    rw [h0]
    rw [List.getD_append _ _ _ _ (by simp),
      List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using u.isLt), h0, hu]
    simp [pins]

  have prefix_eval (u : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 9 → Bool) :
      (full u C).eval (List.ofFn x) = C.eval (pins u x) := by
    clear rawKnown deletionKnown binaryKnown
    change (run (preGates u ++ C.gates) (List.ofFn x)).getD C.output false = _
    have h : run (preGates u ++ C.gates) (List.ofFn x) = run C.gates (run (preGates u) (List.ofFn x)) := by
      simp only [run,List.foldl_append]
    rw [h,prefix_values]
    rfl

  have prefix_fan (u : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) : PEqualNP.MetaComplexity.FanInTwo (full u C) := by
    clear rawKnown deletionKnown binaryKnown
    intro g hg
    change g ∈ preGates u ++ C.gates at hg
    rcases List.mem_append.1 hg with h | h
    · simp only [preGates,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl <;> simp
    · exact fan g h

  have binary_count (u : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit) :
      (full u C).gates.countP (fun g => g.op.eval [true]) =
        C.gates.countP (fun g => g.op.eval [true]) + 1 := by
    clear rawKnown deletionKnown binaryKnown
    change (([⟨.not,[0]⟩,⟨.or,[0,u.val]⟩] : List PEqualNP.CircuitLowerBounds.Gate) ++ C.gates).countP (fun g => g.op.eval [true]) = _
    rw [List.countP_append]
    have hnot : (⟨PEqualNP.CircuitLowerBounds.GateOp.not,[0]⟩ : PEqualNP.CircuitLowerBounds.Gate).op.eval [true] = false := rfl
    have hor : (⟨PEqualNP.CircuitLowerBounds.GateOp.or,[0,u.val]⟩ : PEqualNP.CircuitLowerBounds.Gate).op.eval [true] = true := rfl
    simp only [List.countP_cons,List.countP_nil,hnot,hor,Bool.false_eq_true,↓reduceIte]
    omega

  have suffix_monotone (u : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (lower : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → (∀ x : Fin 9 → Bool, D.eval (List.ofFn x)=F x) →
        14 ≤ D.gates.countP (fun g => g.op.eval [true]))
      (fan : PEqualNP.MetaComplexity.FanInTwo C) (size : C.size ≤ 13)
      (correct : ∀ x : Fin 9 → Bool, C.eval (pins u x)=F x) : PEqualNP.MetaComplexity.Monotone2 C := by
    clear rawKnown deletionKnown binaryKnown
    have bound := lower (full u C) (prefix_fan u C fan) (fun x => (prefix_eval u C x).trans (correct x))
    rw [binary_count] at bound
    have cap := List.countP_le_length (p := fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [true]) (l := C.gates)
    have exactCount : C.gates.countP (fun g => g.op.eval [true]) = C.gates.length := by
      change C.gates.length ≤ 13 at size
      omega
    have every := List.countP_eq_length.mp exactCount
    intro g hg
    obtain ⟨hop,hlen⟩ := fan g hg
    refine ⟨?_,hlen⟩
    rcases hop with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · have hh := every g hg
      rw [hn] at hh
      change false=true at hh
      cases hh

  let packed (x : Fin 9 → Bool) : Bool := decide
    (∃ u v : Fin 9, (([34,68,136,272,1,128,256,0,32] : List Nat).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true)
  have target_bridge : ∀ x : Fin 9 → Bool, packed x = F x := by
    decide +kernel
  have raw : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 F 14 := by
    rintro ⟨C,fan,size,correct⟩
    have bound := rawKnown C fan (funext correct)
    omega
  have cofactor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun y => F (Fin.cons false y)) 11 := deletionKnown
  have lower (C : PEqualNP.CircuitLowerBounds.Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
      (correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x)=F x) :
      14 ≤ C.gates.countP (fun g => g.op.eval [true]) := by
    exact binaryKnown C fan (funext fun x => (correct x).trans (target_bridge x).symm)
  intro u hu C fan size
  by_contra! correct
  have mono := suffix_monotone u C lower fan size correct
  exact monotone_contradiction raw cofactor u hu C mono size correct

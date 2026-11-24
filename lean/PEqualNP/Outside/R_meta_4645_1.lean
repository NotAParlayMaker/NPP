import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 14000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4645_1
  (minors : (¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 5 && x 7) 11) ∧ (¬ HasCircuitSize 7 (fun x : Fin 7 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 5 || x 4 && x 6 || x 6 && x 3) 10))
  (erase :
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let rows := fun (n : ℕ) (entries : List (Bool ⊕ ℕ)) (x : Fin n → Bool) => entries.map (Sum.elim id (fun i => (List.ofFn x).getD i false))
    ∀ (n : ℕ) (entries : List (Bool ⊕ ℕ)) (fixed : ℕ → Bool) (C : Circuit), FanInTwo C →
      (∀ i, fixed i = true → i < entries.length ∧ ∃ b : Bool, entries.getD i (.inl false) = .inl b) →
      (∃ x : Fin n → Bool, C.eval (rows n entries x) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP (fun g => (reads g).any fixed) ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (rows n entries x))
  (one :
    let F := fun x : Fin 9 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let hit0 := fun g : Gate => (reads g).any (fun i => decide (i = 0 ∨ i = 9))
    let hit04 := fun g : Gate => (reads g).any (fun i => decide (i = 0 ∨ i = 4 ∨ i = 9))
    ∀ D : Circuit, FanInTwo D → 13 ≤ D.size → D.size ≤ 14 → D.gates.countP hit0 = 1 →
      2 ≤ D.gates.countP hit04 → 11 + D.gates.countP hit04 ≤ D.size →
      (∀ g ∈ D.gates, hit0 g = true → ∀ i ∈ reads g, i < 10 → i = 0 ∨ i = 9) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0]) ≠ F x)
  (two :
    let F := fun x : Fin 9 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let hit0 := fun g : Gate => (reads g).any (fun i => decide (i = 0 ∨ i = 9))
    let hit04 := fun g : Gate => (reads g).any (fun i => decide (i = 0 ∨ i = 4 ∨ i = 9))
    ∀ D : Circuit, FanInTwo D → D.size = 14 → D.gates.countP hit0 = 2 →
      2 ≤ D.gates.countP hit04 → D.gates.countP hit04 ≤ 3 →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0]) ≠ F x) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = !x3 (0 : Fin (9 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan first target
  let F := fun x : Fin 9 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let H := fun x : Fin 8 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 5 && x 7
  let T := fun x : Fin 7 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 5 || x 4 && x 6 || x 6 && x 3
  let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
  let rows := fun (n : ℕ) (entries : List (Bool ⊕ ℕ)) (x : Fin n → Bool) => entries.map (Sum.elim id (fun i => (List.ofFn x).getD i false))
  let inputs (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  have boolAnd (l : List Bool) : GateOp.eval .and l = l.all id := rfl
  have boolOr (l : List Bool) : GateOp.eval .or l = l.any id := rfl
  have boolNot (l : List Bool) : GateOp.eval .not l = !(l.headD false) := rfl
  have stripHead (C : Circuit) (fan : FanInTwo C)
      (first : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !(x 0)) :
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!(x 0)]) = circuitFun 9 C x := by
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
    cases hg : C.gates with
    | nil =>
      have h := first (fun _ => false)
      change (C.gates.foldl step (List.ofFn (fun _ : Fin 9 => false))).getD 9 false = true at h
      rw [hg, List.foldl_nil, List.getD_eq_default _ _ (by simp)] at h
      cases h
    | cons g gs =>
      have hseed (x : Fin 9 → Bool) : step (List.ofFn x) g = List.ofFn x ++ [!(x 0)] := by
        let b := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
        have hl : (List.ofFn x ++ [b]).getD 9 false = b := by
          have hs : (List.ofFn x ++ [b]).getD (List.ofFn x).length false = b := by simp
          simpa only [List.length_ofFn] using hs
        have h := first x
        change (C.gates.foldl step (List.ofFn x)).getD 9 false = _ at h
        rw [hg, List.foldl_cons, keep gs _ 9 (by simp [step])] at h
        change (List.ofFn x ++ [b]).getD 9 false = _ at h
        rw [hl] at h
        exact congrArg (fun v => List.ofFn x ++ [v]) h
      refine ⟨⟨gs, C.output⟩, ?_, ?_, fun x => ?_⟩
      · intro g' hm
        change g' ∈ gs at hm
        exact fan g' (by
          rw [hg]
          exact List.mem_cons_of_mem g hm)
      · change gs.length + 1 = C.gates.length
        rw [hg, List.length_cons]
      · change (gs.foldl step (List.ofFn x ++ [!(x 0)])).getD C.output false =
          (C.gates.foldl step (List.ofFn x)).getD C.output false
        rw [hg, List.foldl_cons, hseed]
  have inputs_length (x : Fin 9 → Bool) : (inputs x).length = 10 := by simp [inputs]

  let signed (i : ℕ) : Bool := decide (i = 0 ∨ i = 9)

  let dropped (i : ℕ) : Bool := decide (i = 0 ∨ i = 4 ∨ i = 9)

  let hit0 (g : Gate) : Bool := (reads g).any signed

  let hit04 (g : Gate) : Bool := (reads g).any dropped

  let gateValue (w : List Bool) (g : Gate) : Bool :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  have gate_kind {C : Circuit} (hC : FanInTwo C) {g : Gate} (hg : g ∈ C.gates) :
      g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1

  have gateValue_congr {C : Circuit} (hC : FanInTwo C) {g : Gate}
      (hg : g ∈ C.gates) (w v : List Bool)
      (h : ∀ i ∈ reads g, w.getD i false = v.getD i false) :
      gateValue w g = gateValue v g := by
    have value (u : List Bool) :
        gateValue u g = g.op.eval ((reads g).map fun i => u.getD i false) := by
      rcases gate_kind hC hg with hop | hop | hop
      · simp [gateValue, reads, hop, boolAnd]
      · simp [gateValue, reads, hop, boolOr]
      · dsimp only [gateValue, reads]
        rw [hop]
        cases g.inputs <;> rfl
    rw [value w, value v, List.map_congr_left h]

  -- Equal appended values produce a common suffix of computed wires.
  have common_suffix (gs : List Gate) (w v : List Bool)
      (h : ∀ g ∈ gs, ∀ s, gateValue (w ++ s) g = gateValue (v ++ s) g) (s : List Bool) :
      ∃ t, gs.foldl (fun u g => u ++ [gateValue u g]) (w ++ s) = w ++ t ∧
        gs.foldl (fun u g => u ++ [gateValue u g]) (v ++ s) = v ++ t := by
    induction gs generalizing s with
    | nil => exact ⟨s, rfl, rfl⟩
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons, h g (by simp) s, List.append_assoc, List.append_assoc]
      exact ih (fun a ha => h a (by simp [ha])) _

  have append_agree {w v : List Bool} (hlen : w.length = v.length) (s : List Bool)
      (i : ℕ) (hi : w.getD i false = v.getD i false) :
      (w ++ s).getD i false = (v ++ s).getD i false := by
    by_cases hw : i < w.length
    · rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ (by omega), hi]
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]

  have eval_eq_of_steps (C : Circuit) (w v : List Bool)
      (hlen : w.length = v.length) (hout : w.getD C.output false = v.getD C.output false)
      (h : ∀ g ∈ C.gates, ∀ s, gateValue (w ++ s) g = gateValue (v ++ s) g) :
      C.eval w = C.eval v := by
    obtain ⟨t, hw, hv⟩ := common_suffix C.gates w v h []
    simp only [List.append_nil] at hw hv
    change C.wires w = w ++ t at hw
    change C.wires v = v ++ t at hv
    change (C.wires w).getD C.output false = (C.wires v).getD C.output false
    rw [hw, hv]
    exact append_agree hlen t _ hout

  have eval_raw (C : Circuit) (w : List Bool) (hout : C.output < w.length) :
      C.eval w = w.getD C.output false := by
    obtain ⟨t, hw, _⟩ := common_suffix C.gates w w (fun _ _ _ => rfl) []
    simp only [List.append_nil] at hw
    change C.wires w = w ++ t at hw
    change (C.wires w).getD C.output false = w.getD C.output false
    rw [hw, List.getD_append _ _ _ _ hout]

  have has_reader {C : Circuit} (hC : FanInTwo C) (w v : List Bool)
      (hlen : w.length = v.length) (bad : ℕ → Prop) (hout : ¬bad C.output)
      (hraw : ∀ i, ¬bad i → w.getD i false = v.getD i false)
      (hne : C.eval w ≠ C.eval v) : ∃ g ∈ C.gates, ∃ i ∈ reads g, bad i := by
    by_contra! hnone
    refine hne (eval_eq_of_steps C w v hlen (hraw _ hout) ?_)
    intro g hg s
    apply gateValue_congr hC hg
    intro i hi
    exact append_agree hlen s i (hraw i (hnone g hg i hi))

  have equal_hit {gs : List Gate} {p : Gate → Bool} (h : gs.countP p ≤ 1)
      {g k : Gate} (hg : g ∈ gs) (hk : k ∈ gs) (hpg : p g = true) (hpk : p k = true) :
      g = k := by
    have mg : g ∈ gs.filter p := List.mem_filter.mpr ⟨hg, hpg⟩
    have mk : k ∈ gs.filter p := List.mem_filter.mpr ⟨hk, hpk⟩
    rw [List.countP_eq_length_filter] at h
    cases he : gs.filter p with
    | nil => simp [he] at mg
    | cons a t =>
      simp only [he, List.length_cons] at h
      have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
      simp only [he, ht, List.mem_singleton] at mg mk
      exact mg.trans mk.symm

  have binary_at {C : Circuit} (hC : FanInTwo C) {g : Gate} (hg : g ∈ C.gates)
      {q other : ℕ} (hq : q ∈ reads g) (h4 : other ∈ reads g) (hne : q ≠ other) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ i, g.inputs = [i, other] ∨ g.inputs = [other, i] := by
    have hlarge : 2 ≤ (reads g).length := by
      cases he : reads g with
      | nil => simp [he] at hq
      | cons a t =>
        cases t with
        | nil =>
          simp only [he, List.mem_singleton] at hq h4
          exact False.elim (hne (hq.trans h4.symm))
        | cons b t => simp
    have hkind : g.op = .and ∨ g.op = .or := by
      rcases gate_kind hC hg with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · have hs : (reads g).length ≤ 1 := by
          simp [reads, hop, boolNot]
        omega
    have he : reads g = g.inputs := by
      rcases hkind with hop | hop <;> simp [reads, hop, boolAnd, boolOr]
    rw [he] at h4 hlarge
    have hsmall := (hC g hg).2
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (by omega : g.inputs.length = 2)
    rw [hab] at h4
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
    rcases h4 with ha | hb
    · exact ⟨hkind, b, Or.inr (by simpa only [ha] using hab)⟩
    · exact ⟨hkind, a, Or.inl (by simpa only [hb] using hab)⟩

  have past (x : Fin 9 → Bool) (i : ℕ) (hi : 10 ≤ i) :
      (inputs x).getD i false = false := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none_iff.mpr]
    · rfl
    · simpa only [inputs_length] using hi

  have no_raw_output (C : Circuit) (ev : ∀ x, C.eval (inputs x) = F x) : 10 ≤ C.output := by
    have check : ∀ i : Fin 10,
        let x : Fin 9 → Bool := fun j => decide (i.val = j.val)
        (inputs x).getD i.val false ≠ F x := by decide +kernel
    by_contra! small
    let i : Fin 10 := ⟨C.output,small⟩
    let x : Fin 9 → Bool := fun j => decide (i.val = j.val)
    have neq := check i
    change (inputs x).getD C.output false ≠ F x at neq
    exact neq ((eval_raw C (inputs x) (by simpa only [inputs_length] using small)).symm.trans (ev x))

  have read_on_difference (C : Circuit) (fan : FanInTwo C) (ev : ∀ x, C.eval (inputs x) = F x)
      (a b : Fin 9 → Bool) (different : F a ≠ F b) (bad : ℕ → Bool)
      (bounded : ∀ i, bad i = true → i < 10)
      (agree : ∀ i : Fin 10, bad i.val = false → (inputs a).getD i.val false = (inputs b).getD i.val false) :
      ∃ g ∈ C.gates, ∃ i ∈ reads g, bad i = true := by
    have ho := no_raw_output C ev
    have raw (i : ℕ) (hn : ¬ bad i = true) :
        (inputs a).getD i false = (inputs b).getD i false := by
      by_cases hi : i < 10
      · have off : bad i = false := by cases hh : bad i <;> simp_all
        exact agree ⟨i,hi⟩ off
      · rw [past _ _ (by omega),past _ _ (by omega)]
    have outputs : C.eval (inputs a) ≠ C.eval (inputs b) := by rw [ev,ev]; exact different
    exact has_reader fan (inputs a) (inputs b) (by simp only [inputs_length]) (fun i => bad i = true)
      (fun h => by have := bounded _ h; omega) raw outputs

  have sign_read (C : Circuit) (fan : FanInTwo C) (ev : ∀ x, C.eval (inputs x) = F x) :
      ∃ g ∈ C.gates, ∃ i ∈ reads g, signed i = true := by
    let a : Fin 9 → Bool := fun j => decide (j = 1)
    let b : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = 1)
    refine read_on_difference C fan ev a b (by decide) signed ?_ ?_
    · intro i h
      change decide (i = 0 ∨ i = 9) = true at h
      have hh := of_decide_eq_true h
      omega
    · decide +kernel

  have four_read (C : Circuit) (fan : FanInTwo C) (ev : ∀ x, C.eval (inputs x) = F x) :
      ∃ g ∈ C.gates, 4 ∈ reads g := by
    let a : Fin 9 → Bool := fun j => decide (j = 3)
    let b : Fin 9 → Bool := fun j => decide (j = 3 ∨ j = 4)
    obtain ⟨g,hg,i,hi,eq⟩ := read_on_difference C fan ev a b (by decide) (fun i => decide (i=4))
      (by intro i h; have he : i=4 := of_decide_eq_true h; omega) (by decide +kernel)
    have value : i = 4 := of_decide_eq_true eq
    exact ⟨g,hg,value ▸ hi⟩
  have hit_of_mark {g : Gate} {p : ℕ → Bool} {i : ℕ}
      (has : i ∈ reads g) (mark : p i = true) : (reads g).any p = true :=
    List.any_eq_true.mpr ⟨i,has,mark⟩

  have count_sign (C : Circuit) (fan : FanInTwo C) (ev : ∀ x, C.eval (inputs x) = F x) :
      1 ≤ C.gates.countP hit0 := by
    obtain ⟨g,hg,i,hi,hm⟩ := sign_read C fan ev
    have mem : g ∈ C.gates.filter hit0 := List.mem_filter.mpr ⟨hg,hit_of_mark hi hm⟩
    rw [List.countP_eq_length_filter]
    have nonempty := List.length_pos_of_mem mem
    omega

  have conflict (C : Circuit) (fan : FanInTwo C) (ev : ∀ x, C.eval (inputs x) = F x)
      (g : Gate) (hg : g ∈ C.gates) (h0 : hit0 g = true) (v : Fin 9)
      (vne : v ≠ 0) (h4 : v.val ∈ reads g)
      (unique : ∀ k ∈ C.gates, hit0 k = true → k = g) : False := by
    obtain ⟨q,hq,hqa⟩ := List.any_eq_true.mp h0
    have qi : q = 0 ∨ q = 9 := of_decide_eq_true hqa
    have vl := v.isLt
    have vn : v.val ≠ 0 := fun eq => vne (Fin.ext eq)
    obtain ⟨shape,i,wi⟩ := binary_at fan hg hq h4 (by omega)
    let absorb := g.op.eval [true,false]
    let anchor (v : Fin 9) (b : Bool) : Fin 9 :=
      if b then (if v = 2 ∨ v = 6 then 4 else 1) else (if v = 1 then 4 else 1)
    let ax (v : Fin 9) (b : Bool) (j : Fin 9) := decide (j = anchor v b) || (b && decide (j = v))
    let bx (v : Fin 9) (b : Bool) (j : Fin 9) := decide (j = 0) || ax v b j
    have diff : ∀ (v : Fin 9), v ≠ 0 → ∀ b : Bool, F (ax v b) ≠ F (bx v b) := by decide +kernel
    have check : ∀ (v : Fin 9) (b : Bool) (i : Fin 10), signed i.val = false →
        (inputs (ax v b)).getD i.val false = (inputs (bx v b)).getD i.val false := by decide +kernel
    have fourA : ∀ (v : Fin 9), v ≠ 0 → ∀ b : Bool,
        (inputs (ax v b)).getD v.val false = b := by decide +kernel
    have fourB : ∀ (v : Fin 9), v ≠ 0 → ∀ b : Bool,
        (inputs (bx v b)).getD v.val false = b := by decide +kernel
    let x := ax v absorb
    let y := bx v absorb
    have neq : C.eval (inputs x) ≠ C.eval (inputs y) := by rw [ev,ev]; exact diff v vne absorb
    have agrees (i : ℕ) (h : signed i = false) :
        (inputs x).getD i false = (inputs y).getD i false := by
      by_cases bound : i < 10
      · exact check v absorb ⟨i,bound⟩ h
      · rw [past _ _ (by omega),past _ _ (by omega)]
    have ho := no_raw_output C ev
    have hoSig : signed C.output = false := by
      change decide (C.output = 0 ∨ C.output = 9) = false
      exact decide_eq_false (by omega)
    apply neq
    refine eval_eq_of_steps C (inputs x) (inputs y) (by simp only [inputs_length]) (agrees _ hoSig) ?_
    intro k hk t
    by_cases markedGate : hit0 k = true
    · have he := unique k hk markedGate
      subst k
      have xa : (inputs x ++ t).getD v.val false = absorb := by
        rw [List.getD_append _ _ _ _ (by rw [inputs_length]; omega)]
        exact fourA v vne absorb
      have ya : (inputs y ++ t).getD v.val false = absorb := by
        rw [List.getD_append _ _ _ _ (by rw [inputs_length]; omega)]
        exact fourB v vne absorb
      simp only [List.getD_eq_getElem?_getD] at xa ya
      rcases shape with op | op <;> rcases wi with eqn | eqn <;>
        simp [gateValue,op,eqn,boolAnd,boolOr,xa,ya,absorb]
    · apply gateValue_congr fan hk
      intro j hj
      have off : signed j = false := by
        cases hb : signed j
        · rfl
        · exact False.elim (markedGate (hit_of_mark hj hb))
      exact append_agree (by simp only [inputs_length]) t j (agrees j off)

  have one_no_other_raw (C : Circuit) (fan : FanInTwo C) (ev : ∀ x, C.eval (inputs x) = F x)
      (h : C.gates.countP hit0 ≤ 1) :
      ∀ g ∈ C.gates, hit0 g = true → ∀ i ∈ reads g, i < 10 → i = 0 ∨ i = 9 := by
    intro g hg hs i hi lt
    by_contra bad
    have small : i < 9 := by omega
    let v : Fin 9 := ⟨i,small⟩
    have vne : v ≠ 0 := fun same => bad (Or.inl (congrArg Fin.val same))
    exact conflict C fan ev g hg hs v vne hi (fun k hk hit => equal_hit h hk hg hit hs)

  have count_both (C : Circuit) (fan : FanInTwo C) (ev : ∀ x, C.eval (inputs x) = F x) :
      2 ≤ C.gates.countP hit04 := by
    have larger {g : Gate} (h : hit0 g = true) : hit04 g = true := by
      obtain ⟨i,hi,mark⟩ := List.any_eq_true.mp h
      have hit : i = 0 ∨ i = 9 := of_decide_eq_true mark
      exact hit_of_mark hi (decide_eq_true (by omega : i = 0 ∨ i = 4 ∨ i = 9))
    obtain ⟨g,hg,hg4⟩ := four_read C fan ev
    have gp : hit04 g = true := hit_of_mark hg4 (by decide : dropped 4 = true)
    obtain ⟨k,hk,i,hi,marked⟩ := sign_read C fan ev
    have kp : hit0 k = true := hit_of_mark hi marked
    by_contra! tooSmall
    have bound : C.gates.countP hit04 ≤ 1 := by omega
    have he := equal_hit bound hk hg (larger kp) gp
    subst k
    exact conflict C fan ev g hg kp 4 (by decide) hg4 (fun j hj hp => equal_hit bound hj hg (larger hp) gp)
  by_contra! tooSmall
  obtain ⟨D,df,cost,tail⟩ := stripHead C fan first
  have budget : D.size ≤ 14 := by omega
  have computes (x : Fin 9 → Bool) : D.eval (inputs x) = F x :=
    (tail x).trans (congrFun target x)
  let cut0 (x : Fin 8 → Bool) : Fin 9 → Bool :=
    ![false,x 0,x 1,x 2,x 6,x 7,x 4,x 5,x 3]
  let cut04 (x : Fin 7 → Bool) : Fin 9 → Bool :=
    ![false,x 0,x 1,x 2,false,x 3,x 4,x 5,x 6]
  let rows0 : List (Bool ⊕ ℕ) :=
    [.inl false,.inr 0,.inr 1,.inr 2,.inr 6,.inr 7,.inr 4,.inr 5,.inr 3,.inl true]
  let rows04 : List (Bool ⊕ ℕ) :=
    [.inl false,.inr 0,.inr 1,.inr 2,.inl false,.inr 3,.inr 4,.inr 5,.inr 6,.inl true]
  have map0 : ∀ x, F (cut0 x) = H x := by
    dsimp only [F,H,cut0]
    decide +kernel
  have map04 : ∀ x, F (cut04 x) = T x := by
    dsimp only [F,T,cut04]
    decide +kernel
  have fixed0 (i : ℕ) (h : signed i = true) :
      i < rows0.length ∧ ∃ b : Bool, rows0.getD i (.inl false) = .inl b := by
    change decide (i = 0 ∨ i = 9) = true at h
    rcases of_decide_eq_true h with rfl | rfl
    · exact ⟨by decide,false,rfl⟩
    · exact ⟨by decide,true,rfl⟩
  have fixed04 (i : ℕ) (h : dropped i = true) :
      i < rows04.length ∧ ∃ b : Bool, rows04.getD i (.inl false) = .inl b := by
    change decide (i = 0 ∨ i = 4 ∨ i = 9) = true at h
    rcases of_decide_eq_true h with rfl | rfl | rfl
    · exact ⟨by decide,false,rfl⟩
    · exact ⟨by decide,false,rfl⟩
    · exact ⟨by decide,true,rfl⟩
  have args0 (x : Fin 8 → Bool) : inputs (cut0 x) = rows 8 rows0 x := rfl
  have args04 (x : Fin 7 → Bool) : inputs (cut04 x) = rows 7 rows04 x := rfl
  have sat0 (x : Fin 8 → Bool) : D.eval (rows 8 rows0 x) = H x := by
    rw [← args0,computes,map0]
  have sat04 (x : Fin 7 → Bool) : D.eval (rows 7 rows04 x) = T x := by
    rw [← args04,computes,map04]
  have lower (n cap : ℕ) (entries : List (Bool ⊕ ℕ)) (fixed : ℕ → Bool)
      (G : (Fin n → Bool) → Bool) (smallImpossible : ¬ HasCircuitSize n G cap)
      (hc : ∀ i, fixed i = true → i < entries.length ∧
        ∃ b : Bool, entries.getD i (.inl false) = .inl b)
      (conforms : ∀ x, D.eval (rows n entries x) = G x)
      (hzero : G (fun _ => false) = false) :
      (cap+1) + D.gates.countP (fun g => (reads g).any fixed) ≤ D.size := by
    obtain ⟨E,ef,delta,same⟩ := erase n entries fixed D df hc
      ⟨fun _ => false, (conforms (fun _ => false)).trans hzero⟩
    change E.size + D.gates.countP (fun g => (reads g).any fixed) ≤ D.size at delta
    have enough : cap+1 ≤ E.size := by
      by_contra hs
      exact smallImpossible ⟨E,ef,by omega,fun x => (same x).trans (conforms x)⟩
    omega
  have from0 : 12 + D.gates.countP hit0 ≤ D.size :=
    lower 8 11 rows0 signed H minors.1 fixed0 sat0 rfl
  have from04 : 11 + D.gates.countP hit04 ≤ D.size :=
    lower 7 10 rows04 dropped T minors.2 fixed04 sat04 rfl
  have need0 := count_sign D df computes
  have need04 := count_both D df computes
  by_cases lone : D.gates.countP hit0 = 1
  · have noRaw := one_no_other_raw D df computes (by omega)
    obtain ⟨x,fails⟩ := one D df (by omega) budget lone need04 from04 noRaw
    exact fails (computes x)
  · have exactSize : D.size = 14 := by omega
    have exactSigned : D.gates.countP hit0 = 2 := by omega
    have maxFrozen : D.gates.countP hit04 ≤ 3 := by omega
    obtain ⟨x,fails⟩ := two D df exactSize exactSigned need04 maxFrozen
    exact fails (computes x)

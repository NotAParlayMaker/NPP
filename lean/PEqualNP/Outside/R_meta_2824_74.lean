import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- An OR feeder cannot inherit a true raw input through a chain of OR gates.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_2824_74
  (distinct : let pick : Fin 3 → Fin 9 := ![4,6,7]
    let reads := fun (p : Fin 9) (g : Gate) =>
      (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains p.val
    let arc := fun (C : Circuit) (a b : Nat) => a < b ∧ ∃ j : Fin C.size,
      b = 9+j.val ∧ (C.gates.get j).op = .or ∧ a ∈ (C.gates.get j).inputs
    ∀ (C : Circuit) (reader : Fin 3 → Fin C.size) (feed : Fin 3 → Nat), FanInTwo C → C.size ≤ 14 →
    Function.Injective feed →
    (∀ t, 9 ≤ feed t ∧ feed t < 9+(reader t).val ∧
      (C.gates.get (reader t)).op = .or ∧
      ((C.gates.get (reader t)).inputs = [(pick t).val,feed t] ∨
        (C.gates.get (reader t)).inputs = [feed t,(pick t).val]) ∧
      ∀ j : Fin C.size, reads (pick t) (C.gates.get j) = true → j = reader t) →
    (∀ t (u : Fin 9), ¬ Relation.TransGen (arc C) u.val (feed t)) →
    ∃ x : Fin 9 → Bool, circuitFun 9 C x ≠
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
  (shared : let pick : Fin 3 → Fin 9 := ![4,6,7]
    let reads := fun (p : Fin 9) (g : Gate) =>
      (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains p.val
    let arc := fun (C : Circuit) (a b : Nat) => a < b ∧ ∃ j : Fin C.size,
      b = 9+j.val ∧ (C.gates.get j).op = .or ∧ a ∈ (C.gates.get j).inputs
    ∀ (C : Circuit) (reader : Fin 3 → Fin C.size) (feed : Fin 3 → Nat), FanInTwo C → C.size ≤ 14 →
    ¬ Function.Injective feed →
    (∀ t, 9 ≤ feed t ∧ feed t < 9+(reader t).val ∧
      (C.gates.get (reader t)).op = .or ∧
      ((C.gates.get (reader t)).inputs = [(pick t).val,feed t] ∨
        (C.gates.get (reader t)).inputs = [feed t,(pick t).val]) ∧
      ∀ j : Fin C.size, reads (pick t) (C.gates.get j) = true → j = reader t) →
    (∀ t (u : Fin 9), ¬ Relation.TransGen (arc C) u.val (feed t)) →
    ∃ x : Fin 9 → Bool, circuitFun 9 C x ≠
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Gate) => (if x3.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs).contains ↑x2; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → (∀ (x6 : Fin (9 : ℕ)), x6 = (4 : Fin (9 : ℕ)) ∨ x6 = (6 : Fin (9 : ℕ)) ∨ x6 = (7 : Fin (9 : ℕ)) → ∃ (x8 : Fin x3.size) (x9 : ℕ), (9 : ℕ) ≤ x9 ∧ x9 < (9 : ℕ) + ↑x8 ∧ (x3.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ((x3.gates.get x8).inputs = [↑x6, x9] ∨ (x3.gates.get x8).inputs = [x9, ↑x6]) ∧ ∀ (x10 : Fin x3.size), x2 x6 (x3.gates.get x10) = Bool.true → x10 = x8) → ∃ (x7 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 x7 ≠ x1 x7 := by
  dsimp only
  intro C fan size given
  classical
  let target := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let pick : Fin 3 → Fin 9 := ![4,6,7]
  let effective := fun (g : Gate) => if g.op.eval [false,false] then g.inputs.take 1 else g.inputs
  let reads := fun (p : Fin 9) (g : Gate) => (effective g).contains p.val
  let arc := fun (a b : Nat) => a < b ∧ ∃ j : Fin C.size,
    b = 9+j.val ∧ (C.gates.get j).op = .or ∧ a ∈ (C.gates.get j).inputs
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let W := fun (x : Fin 9 → Bool) (i : Nat) => (C.wires (List.ofFn x)).getD i false
  change ∃ x : Fin 9 → Bool, W x C.output ≠ target x
  by_contra impossible
  have correct (x : Fin 9 → Bool) : W x C.output = target x := by
    by_contra differ
    exact impossible ⟨x,differ⟩
  have picked : ∀ t : Fin 3, pick t = 4 ∨ pick t = 6 ∨ pick t = 7 := by decide +kernel
  choose reader feed spec using (fun t : Fin 3 => given (pick t) (picked t))
  have basis (j : Fin C.size) : (C.gates.get j).op = .and ∨
      (C.gates.get j).op = .or ∨ (C.gates.get j).op = .not :=
    (fan _ (List.get_mem C.gates j)).1
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have eval_eq (g : Gate) (ops : g.op = .and ∨ g.op = .or ∨ g.op = .not) (a b : Nat → Bool)
      (h : ∀ i ∈ effective g, a i = b i) : g.op.eval (g.inputs.map a) = g.op.eval (g.inputs.map b) := by
    obtain ⟨op,l⟩ := g
    rcases ops with rfl | rfl | rfl
    · change ∀ i ∈ l, a i = b i at h
      rw [List.map_congr_left (fun i hi => h i hi)]
    · change ∀ i ∈ l, a i = b i at h
      rw [List.map_congr_left (fun i hi => h i hi)]
    · cases l with
      | nil => rfl
      | cons i is =>
        have hi : i ∈ effective ⟨.not,i::is⟩ := by change i ∈ [i]; simp
        change (!a i) = (!b i)
        rw [h i hi]
  have lengthRun (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
  have keep (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have raw (x : Fin 9 → Bool) (i : Fin 9) : W x i.val = x i := by
    change (C.gates.foldl step (List.ofFn x)).getD i.val false = x i
    rw [keep _ _ _ (by simp)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  have beyond (x : Fin 9 → Bool) (i : Nat) (hi : 9+C.size ≤ i) : W x i = false := by
    change (C.gates.foldl step (List.ofFn x)).getD i false = false
    apply List.getD_eq_default
    change 9+C.gates.length ≤ i at hi
    simpa only [lengthRun, List.length_ofFn] using hi
  let readAt := fun (x : Fin 9 → Bool) (j : Fin C.size) (i : Nat) =>
    if i < 9+j.val then W x i else false
  have gateW (x : Fin 9 → Bool) (j : Fin C.size) : W x (9+j.val) =
      (C.gates.get j).op.eval ((C.gates.get j).inputs.map (readAt x j)) := by
    let g := C.gates.get j
    let w := (C.gates.take j.val).foldl step (List.ofFn x)
    have lt : j.val < C.gates.length := j.isLt
    have len : w.length = 9+j.val := by simp [w,lengthRun,Nat.min_eq_left lt.le]
    have split : C.gates = C.gates.take j.val ++ g :: C.gates.drop (j.val + 1) := by
      change C.gates = C.gates.take j.val ++ C.gates[j.val] :: C.gates.drop (j.val + 1)
      simp
    have eqRun : C.wires (List.ofFn x) = (C.gates.drop (j.val + 1)).foldl step (step w g) := by
      change C.gates.foldl step (List.ofFn x) = _
      conv_lhs => rw [split]
      rw [List.foldl_append, List.foldl_cons]
    have before (i : Nat) (iLt : i < 9+j.val) : W x i = w.getD i false := by
      change (C.wires (List.ofFn x)).getD i false = _
      rw [eqRun, keep _ _ _ (by simp [step,len]; omega)]
      exact List.getD_append _ _ _ _ (len ▸ iLt)
    change (C.wires (List.ofFn x)).getD (9+j.val) false = g.op.eval (g.inputs.map (readAt x j))
    rw [eqRun, keep _ _ _ (by simp [step,len])]
    have atEnd : (step w g).getD (9+j.val) false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD (9+j.val) false = _
      rw [List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self]
      rfl
    rw [atEnd]
    apply congrArg g.op.eval
    apply List.map_congr_left
    intro i _
    dsimp only [readAt]
    split_ifs with h
    · exact (before i h).symm
    · exact List.getD_eq_default _ _ (by omega)
  have propagates (x : Fin 9 → Bool) (a b : Nat) (h : arc a b) (on : W x a = true) : W x b = true := by
    obtain ⟨lt,j,eq,hop,pin⟩ := h
    rw [eq, gateW, hop, evalOr]
    apply List.any_eq_true.mpr
    refine ⟨true,List.mem_map.mpr ⟨a,pin,?_⟩,rfl⟩
    have hlt : a < 9+j.val := by omega
    simpa [readAt,hlt] using on
  have routeTrue (x : Fin 9 → Bool) (a b : Nat) (h : Relation.TransGen arc a b)
      (on : W x a = true) : W x b = true := by
    induction h with
    | single edge => exact propagates x _ _ edge on
    | tail route edge ih => exact propagates x _ _ edge ih
  have starts {a b : Nat} (h : Relation.TransGen arc a b) : ∃ c, arc a c ∧ c ≤ b := by
    induction h with
    | single edge => exact ⟨_,edge,le_rfl⟩
    | tail route edge ih => obtain ⟨c,hc,hb⟩ := ih; exact ⟨c,hc,hb.trans edge.1.le⟩
  have orReads (g : Gate) (hop : g.op = .or) (p : Fin 9) (h : p.val ∈ g.inputs) : reads p g = true := by
    have eq : effective g = g.inputs := by
      change (if g.op.eval [false,false] then _ else _) = _
      rw [hop]
      rfl
    change (effective g).contains p.val = true
    simpa only [eq,List.contains_iff_mem] using h
  let witnessMask (t : Fin 3) (u : Fin 9) : Nat :=
    (![![1,10,5,8,0,40,65,129,257], ![257,2,260,10,18,34,0,130,256],
      ![5,34,4,40,20,32,68,0,260]] : Fin 3 → Fin 9 → Nat) t u
  let off (t : Fin 3) (u i : Fin 9) := (witnessMask t u).testBit i.val
  let on (t : Fin 3) (u i : Fin 9) := decide (i = pick t) || off t u i
  have witnesses : ∀ t u, u ≠ pick t → target (off t u) = false ∧ target (on t u) = true ∧
      off t u u = true ∧ on t u u = true ∧
      ∀ i : Fin 9, i.val ≠ (pick t).val → off t u i = on t u i := by decide +kernel
  let single (i j : Fin 9) : Bool := decide (i = j)
  have singleOff : ∀ i, target (single i) = false ∧ single i i = true := by decide +kernel
  have outNotRaw (p : Fin 9) : C.output ≠ p.val := by
    intro eq
    have h := correct (single p)
    rw [eq, raw, (singleOff p).1, (singleOff p).2] at h
    contradiction
  have excluded : ∀ t (u : Fin 9), ¬ Relation.TransGen arc u.val (feed t) := by
    intro t u path
    obtain ⟨inFeed,earlier,op,pins,onlyReader⟩ := spec t
    by_cases same : u = pick t
    · subst u
      obtain ⟨c,hc,hcFeed⟩ := starts path
      obtain ⟨_,j,eq,hop,mem⟩ := hc
      have idx := onlyReader j (orReads _ hop _ mem)
      rw [idx] at eq
      omega
    obtain ⟨targetOff,targetOn,rawOff,rawOn,agreement⟩ := witnesses t u same
    have sourceArc : arc (feed t) (9+(reader t).val) := by
      refine ⟨earlier,reader t,rfl,op,?_⟩
      rcases pins with e | e <;> simp [e]
    have sourceOff : W (off t u) (9+(reader t).val) = true :=
      propagates _ _ _ sourceArc (routeTrue _ _ _ path ((raw _ u).trans rawOff))
    have sourceOn : W (on t u) (9+(reader t).val) = true :=
      propagates _ _ _ sourceArc (routeTrue _ _ _ path ((raw _ u).trans rawOn))
    have propagate (p : Nat) : p ≠ (pick t).val → W (off t u) p = W (on t u) p := by
      induction p using Nat.strong_induction_on with
      | ind p ih =>
        intro ne
        by_cases base : p < 9
        · exact (raw _ ⟨p,base⟩).trans ((agreement ⟨p,base⟩ ne).trans (raw _ ⟨p,base⟩).symm)
        · by_cases within : p < 9+C.size
          · let j : Fin C.size := ⟨p-9,by omega⟩
            have eq : p = 9+j.val := by dsimp [j]; omega
            rw [eq]
            by_cases isReader : j = reader t
            · rw [isReader, sourceOff, sourceOn]
            · rw [gateW, gateW]
              apply eval_eq _ (basis j)
              intro i hi
              have different : i ≠ (pick t).val := by
                intro e
                subst i
                apply isReader
                apply onlyReader j
                change (effective (C.gates.get j)).contains (pick t).val = true
                exact List.contains_iff_mem.mpr hi
              dsimp only [readAt]
              split_ifs with before
              · apply ih i (by omega) different
              · rfl
          · rw [beyond _ _ (by omega),beyond _ _ (by omega)]
    have eq := propagate C.output (outNotRaw (pick t))
    have h0 := correct (off t u)
    have h1 := correct (on t u)
    rw [eq,targetOff] at h0
    rw [h0,targetOn] at h1
    contradiction
  have finish : ∃ x : Fin 9 → Bool, W x C.output ≠ target x := by
    by_cases inj : Function.Injective feed
    · exact distinct C reader feed fan size inj spec excluded
    · exact shared C reader feed fan size inj spec excluded
  exact impossible finish

import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotPremium

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_2909_1
  (h1 : ∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
    circuitFun 9 C ≠ fun x =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  (h2 : ∀ C : Circuit, FanInTwo C →
    C.gates.countP (fun g => GateOp.rec true true false (fun _ => false) false g.op) ≤ 12 →
    ¬ (∀ x : Fin 9 → Bool, (x 0 = false ∨ x 2 = false) →
      circuitFun 9 C x =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → PEqualNP.NotPremium.AtMostOneNot x1.gates → ∀ (x6 : Fin x1.gates.length), (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∃ x8 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) { gates := PEqualNP.NotPremium.replaceByConst x1.gates (↑x6) Bool.false, output := x1.output : PEqualNP.CircuitLowerBounds.Circuit } fun (x9 : Fin (9 : ℕ)) => x8.testBit ↑x9) = Bool.false) → (∃ x9 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) { gates := PEqualNP.NotPremium.replaceByConst x1.gates (↑x6) Bool.true, output := x1.output : PEqualNP.CircuitLowerBounds.Circuit } fun (x10 : Fin (9 : ℕ)) => x9.testBit ↑x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x10 : Fin (9 : ℕ) → Bool) => x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) := by
  intro C fan first size oneNot q qnot hmiss _hspur correct
  let edgeF : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let pBin (g : Gate) : Bool :=
    GateOp.rec true true false (fun _ => false) false g.op
  have evalAnd : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have evalOr : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have evalNot : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  let remap (pos repl k : ℕ) : ℕ :=
    if k < pos then k else if k = pos then repl else k - 1
  let remapGate (pos repl : ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (remap pos repl)⟩
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (k : ℕ),
      k < w.length → (gs.foldl step w).getD k false = w.getD k false := by
    intro gs
    induction gs with
    | nil => intro w k _; rfl
    | cons g gs ih =>
      intro w k hk
      rw [List.foldl_cons, ih (step w g) k (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hk
  have getD_ge_len : ∀ (w : List Bool) (k : ℕ), w.length ≤ k → w.getD k false = false := by
    intro w k hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
  have getD_append_last : ∀ (w : List Bool) (b : Bool),
      (w ++ [b]).getD w.length false = b := by
    intro w b
    simp [List.getD_eq_getElem?_getD]
  have delete_post_inv : ∀ (pos repl : ℕ) (gs : List Gate) (a b : List Bool),
      a.length = b.length + 1 →
      pos ≤ b.length →
      (repl < pos ∨ b.length + gs.length ≤ repl) →
      (∀ k, k < pos → a.getD k false = b.getD k false) →
      a.getD pos false = b.getD repl false →
      (∀ k, pos < k → a.getD k false = b.getD (k - 1) false) →
      ∀ k, (gs.foldl step a).getD k false =
        ((gs.map (remapGate pos repl)).foldl step b).getD (remap pos repl k) false := by
    intro pos repl gs
    induction gs with
    | nil =>
      intro a b _ _ _ hlt heq hgt k
      simp only [List.map_nil, List.foldl_nil, remap]
      split_ifs with h1 h2
      · exact hlt k h1
      · subst h2; exact heq
      · exact hgt k (by omega)
    | cons g gs ih =>
      intro a b hlen hpos hrepl hlt heq hgt k
      have hmap : ∀ j, a.getD j false = b.getD (remap pos repl j) false := by
        intro j
        simp only [remap]
        split_ifs with h1 h2
        · exact hlt j h1
        · subst h2; exact heq
        · exact hgt j (by omega)
      have hval : (remapGate pos repl g).op.eval
          ((remapGate pos repl g).inputs.map fun i => b.getD i false) =
          g.op.eval (g.inputs.map fun i => a.getD i false) := by
        simp only [remapGate, List.map_map, Function.comp_def]
        congr 1
        apply List.map_congr_left
        intro j _
        exact (hmap j).symm
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      apply ih (step a g) (step b (remapGate pos repl g))
      · simp [step, hlen]
      · simp [step]; omega
      · rcases hrepl with hr | hr
        · exact Or.inl hr
        · right; simp [step] at *; omega
      · intro j hj
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hlt j hj
      · rw [List.getD_append _ _ _ _ (by omega)]
        rw [heq]
        rcases hrepl with hr | hr
        · rw [List.getD_append _ _ _ _ (by omega)]
        · rw [getD_ge_len b repl (by simp at hr; omega)]
          rw [getD_ge_len (step b (remapGate pos repl g)) repl (by simp [step] at hr ⊢; omega)]
      · intro j hj
        by_cases hja : j < a.length
        · rw [List.getD_append _ _ _ _ hja, List.getD_append _ _ _ _ (by omega)]
          exact hgt j hj
        · by_cases hje : j = a.length
          · subst hje
            have hjb : a.length - 1 = b.length := by omega
            rw [getD_append_last, hjb, getD_append_last, hval]
          · rw [getD_ge_len (step a g) j (by simp [step]; omega)]
            rw [getD_ge_len (step b (remapGate pos repl g)) (j - 1) (by simp [step]; omega)]
  have delete_gate_eval : ∀ (gs : List Gate) (p repl : ℕ) (w0 : List Bool)
      (hp : p < gs.length),
      let pre := gs.take p
      let post := gs.drop (p + 1)
      let w := pre.foldl step w0
      (repl < w0.length + p ∨ w0.length + gs.length ≤ repl) →
      gs[p].op.eval (gs[p].inputs.map fun i => w.getD i false) = w.getD repl false →
      ∀ o, (gs.foldl step w0).getD o false =
        ((pre ++ post.map (remapGate (w0.length + p) repl)).foldl step w0).getD
          (remap (w0.length + p) repl o) false := by
    intro gs p repl w0 hp pre post w hrepl hval o
    have hsplit : gs = pre ++ gs[p] :: post := by
      calc
        gs = gs.take (p + 1) ++ gs.drop (p + 1) := (List.take_append_drop (p + 1) gs).symm
        _ = (gs.take p ++ [gs[p]]) ++ gs.drop (p + 1) := by rw [List.take_append_getElem hp]
        _ = pre ++ gs[p] :: post := by simp [pre, post]
    have hwlen : w.length = w0.length + p := by
      dsimp [w, pre]
      rw [foldl_len, List.length_take_of_le (by omega)]
    rw [List.foldl_append]
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    apply delete_post_inv (w0.length + p) repl post (step w gs[p]) w
    · simp [step]
    · omega
    · rcases hrepl with hr | hr
      · exact Or.inl hr
      · right; simp [post, hwlen]; omega
    · intro k hk
      exact List.getD_append _ _ _ _ (by omega)
    · rw [← hwlen, getD_append_last]
      exact hval
    · intro k hk
      rw [getD_ge_len (step w gs[p]) k (by simp [step, hwlen]; omega)]
      rw [getD_ge_len w (k - 1) (by omega)]
  have fan_delete : ∀ (gs : List Gate) (p repl : ℕ),
      (∀ g ∈ gs, (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) ∧ g.inputs.length ≤ 2) →
      ∀ g ∈ gs.take p ++ (gs.drop (p + 1)).map (remapGate (9 + p) repl),
        (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) ∧ g.inputs.length ≤ 2 := by
    intro gs p repl hfan g hg
    rcases List.mem_append.mp hg with hpre | hpost
    · exact hfan g (List.mem_of_mem_take hpre)
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hpost
      simpa [remapGate] using hfan h (List.mem_of_mem_drop hh)
  have countP_delete : ∀ (gs : List Gate) (p repl : ℕ) (hp : p < gs.length),
      pBin gs[p] = true →
      (gs.take p ++ (gs.drop (p + 1)).map (remapGate (9 + p) repl)).countP pBin + 1 =
        gs.countP pBin := by
    intro gs p repl hp hpb
    have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
      calc
        gs = gs.take (p + 1) ++ gs.drop (p + 1) := (List.take_append_drop (p + 1) gs).symm
        _ = (gs.take p ++ [gs[p]]) ++ gs.drop (p + 1) := by rw [List.take_append_getElem hp]
        _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by simp
    have hmap : ((gs.drop (p + 1)).map (remapGate (9 + p) repl)).countP pBin =
        (gs.drop (p + 1)).countP pBin := by
      rw [List.countP_map]
      congr 1
    conv_rhs => rw [hsplit]
    rw [List.countP_append, List.countP_append, List.countP_cons, hmap, hpb]
    simp only [↓reduceIte]
    omega
  obtain ⟨gates, o⟩ := C
  change gates.length = 15 at size
  cases gates with
  | nil => simp at size
  | cons g0 tail =>
    have htail_len : tail.length = 14 := by simp at size; omega
    have hg0_eval : ∀ x : Fin 9 → Bool,
        g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 && x 2) := by
      intro x
      have hx := first x
      change (tail.foldl step (step (List.ofFn x) g0)).getD 9 false = (x 0 && x 2) at hx
      rw [foldl_getD_lt tail (step (List.ofFn x) g0) 9 (by simp [step])] at hx
      have hlast := getD_append_last (List.ofFn x) (g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false))
      simp only [List.length_ofFn] at hlast
      exact hlast.symm.trans hx
    have hg0_ne_not : g0.op ≠ GateOp.not := by
      intro hnot
      have h := hg0_eval (fun _ => false)
      rw [hnot] at h
      have hz : ∀ j : ℕ, (List.ofFn (fun _ : Fin 9 => false)).getD j false = false := by
        intro j
        by_cases hj : j < 9
        · interval_cases j <;> rfl
        · exact getD_ge_len _ j (by simp; omega)
      cases hins : g0.inputs with
      | nil => rw [hins, evalNot] at h; cases h
      | cons a rest =>
        rw [hins, evalNot] at h; simp only [List.map_cons, List.headD_cons, hz] at h
        cases h
    have hq_ne_zero : q.val ≠ 0 := by
      intro h0
      have hget : (g0 :: tail).get q = g0 := by
        simp [List.get_eq_getElem, h0]
      rw [hget] at qnot
      exact hg0_ne_not qnot
    let q' : ℕ := q.val - 1
    have hq'_lt : q' < tail.length := by
      have := q.isLt
      simp at this
      omega
    have hq_eq : q.val = q' + 1 := by omega
    have hq'_not : tail[q'].op = GateOp.not := by
      have : (g0 :: tail).get q = tail[q'] := by
        simp [List.get_eq_getElem, hq_eq]
      rw [← this]
      exact qnot
    have hunique : ∀ (j : ℕ) (hj : j < tail.length), j ≠ q' → tail[j].op ≠ GateOp.not := by
      intro j hj hne hjn
      obtain ⟨ι, hι⟩ := oneNot
      obtain ⟨a, ha⟩ := hι q qnot
      obtain ⟨b, hb⟩ := hι ⟨j + 1, by simp; omega⟩ (by simpa [List.get_eq_getElem] using hjn)
      have hab : a = b := Subsingleton.elim a b
      subst hab
      have hqeq : q = ⟨j + 1, by simp; omega⟩ := ha.symm.trans hb
      have hval : q.val = j + 1 := congrArg Fin.val hqeq
      omega
    have htail_bin : ∀ (j : ℕ) (hj : j < tail.length), j ≠ q' →
        tail[j].op = GateOp.and ∨ tail[j].op = GateOp.or := by
      intro j hj hne
      have hmem : tail[j] ∈ g0 :: tail := List.mem_cons_of_mem g0 (List.getElem_mem hj)
      have hop := (fan tail[j] hmem).1
      have hnn := hunique j hj hne
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hnn h)
    have htail_pBin : tail.countP pBin = 13 := by
      have hsplit : tail = tail.take q' ++ tail[q'] :: tail.drop (q' + 1) := by
        calc
          tail = tail.take (q' + 1) ++ tail.drop (q' + 1) := (List.take_append_drop (q' + 1) tail).symm
          _ = (tail.take q' ++ [tail[q']]) ++ tail.drop (q' + 1) := by rw [List.take_append_getElem hq'_lt]
          _ = tail.take q' ++ tail[q'] :: tail.drop (q' + 1) := by simp
      have htake_all : ∀ g ∈ tail.take q', pBin g = true := by
        intro g hg
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
        rw [List.length_take_of_le (by omega)] at hj
        rw [List.getElem_take]
        rcases htail_bin j (by omega) (by omega) with ho | ho <;> simp [pBin, ho]
      have hdrop_all : ∀ g ∈ tail.drop (q' + 1), pBin g = true := by
        intro g hg
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
        rw [List.length_drop] at hj
        rw [List.getElem_drop]
        rcases htail_bin (q' + 1 + j) (by omega) (by omega) with ho | ho <;> simp [pBin, ho]
      have hqpb : pBin tail[q'] = false := by simp [pBin, hq'_not]
      conv_lhs => rw [hsplit]
      rw [List.countP_append, List.countP_cons, hqpb]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [List.countP_eq_length.mpr htake_all, List.countP_eq_length.mpr hdrop_all]
      rw [List.length_take_of_le (by omega), List.length_drop]
      omega
    have ho_ne_9 : o ≠ 9 := by
      intro ho9
      subst ho9
      let x01 : Fin 9 → Bool := fun i => decide (i.val = 0 ∨ i.val = 1)
      have hc := congrFun correct x01
      have hf := first x01
      change (Circuit.wires ⟨g0 :: tail, 9⟩ (List.ofFn x01)).getD 9 false = edgeF x01 at hc
      rw [hf] at hc
      have : (x01 0 && x01 2) = false := by decide
      have : edgeF x01 = true := by decide
      simp_all
    let tail1 : List Gate := tail.map (remapGate 9 100)
    let o1 : ℕ := remap 9 100 o
    let D1 : Circuit := ⟨tail1, o1⟩
    have hD1_len : tail1.length = 14 := by simp [tail1, htail_len]
    have hD1_fan : FanInTwo D1 := by
      intro g hg
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
      simpa [remapGate] using fan h (List.mem_cons_of_mem g0 hh)
    have hD1_pBin : tail1.countP pBin = 13 := by
      dsimp [tail1]
      rw [List.countP_map]
      exact htail_pBin
    have hD1_adm : ∀ x : Fin 9 → Bool, (x 0 = false ∨ x 2 = false) →
        circuitFun 9 D1 x = edgeF x := by
      intro x hadm
      have h02 : (x 0 && x 2) = false := by rcases hadm with h | h <;> simp [h]
      have hdg := delete_gate_eval (g0 :: tail) 0 100 (List.ofFn x) (by simp)
        (by right; simp [htail_len])
        (by
          simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero]
          rw [hg0_eval x, h02, getD_ge_len (List.ofFn x) 100 (by simp)])
        o
      have hc := congrFun correct x
      change ((g0 :: tail).foldl step (List.ofFn x)).getD o false = edgeF x at hc
      rw [← hc]
      change (tail1.foldl step (List.ofFn x)).getD o1 false = ((g0 :: tail).foldl step (List.ofFn x)).getD o false
      simpa [tail1, o1] using hdg.symm
    by_cases hbin9 : ∃ (p : Fin tail.length), p.val ≠ q' ∧ 9 ∈ (tail.get p).inputs
    · obtain ⟨p, hpne, hp9⟩ := hbin9
      have hp_lt : p.val < tail1.length := by simpa [tail1] using p.isLt
      have hp_op : tail1[p.val].op = GateOp.and ∨ tail1[p.val].op = GateOp.or := by
        simpa [tail1, remapGate] using htail_bin p.val p.isLt hpne
      have hp_pBin : pBin tail1[p.val] = true := by
        rcases hp_op with h | h <;> simp [pBin, h]
      have hp_len : tail1[p.val].inputs.length ≤ 2 := by
        have hmem : tail1[p.val] ∈ tail1 := List.getElem_mem hp_lt
        exact (hD1_fan _ hmem).2
      have hp_100 : 100 ∈ tail1[p.val].inputs := by
        have h9' : 9 ∈ tail[p.val].inputs := by simpa [List.get_eq_getElem] using hp9
        have hmem := List.mem_map_of_mem (f := remap 9 100) h9'
        simpa [tail1, remapGate, remap] using hmem
      have hrepl_ex : ∃ repl : ℕ, (repl < 9 + p.val ∨ repl = 100) ∧
          ∀ w : List Bool, w.length = 9 + p.val →
            tail1[p.val].op.eval (tail1[p.val].inputs.map fun i => w.getD i false) =
              w.getD repl false := by
        rcases hp_op with hand | hor
        · refine ⟨100, Or.inr rfl, fun w hw => ?_⟩
          rw [hand, getD_ge_len w 100 (by omega)]
          change (tail1[p.val].inputs.map fun i => w.getD i false).all id = false
          rw [List.all_eq_false]
          exact ⟨false, List.mem_map.mpr ⟨100, hp_100, getD_ge_len w 100 (by omega)⟩, by decide⟩
        · rcases hins : tail1[p.val].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · rw [hins] at hp_100; simp at hp_100
          · rw [hins] at hp_100
            have ha : a = 100 := (List.mem_singleton.mp hp_100).symm
            subst ha
            refine ⟨100, Or.inr rfl, fun w hw => ?_⟩
            rw [hor]
            rw [evalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          · rw [hins] at hp_100
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp_100
            rcases hp_100 with rfl | rfl
            · by_cases hblt : b < 9 + p.val
              · refine ⟨b, Or.inl hblt, fun w hw => ?_⟩
                rw [hor]
                rw [evalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, getD_ge_len w 100 (by omega), Bool.false_or, Bool.or_false]
              · refine ⟨100, Or.inr rfl, fun w hw => ?_⟩
                rw [hor]
                rw [evalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, getD_ge_len w 100 (by omega), getD_ge_len w b (by omega), Bool.or_false]
            · by_cases halt : a < 9 + p.val
              · refine ⟨a, Or.inl halt, fun w hw => ?_⟩
                rw [hor]
                rw [evalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, getD_ge_len w 100 (by omega), Bool.or_false]
              · refine ⟨100, Or.inr rfl, fun w hw => ?_⟩
                rw [hor]
                rw [evalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, getD_ge_len w 100 (by omega), getD_ge_len w a (by omega), Bool.or_false]
          · rw [hins] at hp_len; simp at hp_len
      obtain ⟨repl, hrepl_ok, hrepl_eval⟩ := hrepl_ex
      let D2 : Circuit :=
        ⟨tail1.take p.val ++ (tail1.drop (p.val + 1)).map (remapGate (9 + p.val) repl),
         remap (9 + p.val) repl o1⟩
      have hD2_fan : FanInTwo D2 := fan_delete tail1 p.val repl hD1_fan
      have hD2_cnt : D2.gates.countP pBin ≤ 12 := by
        have h := countP_delete tail1 p.val repl hp_lt hp_pBin
        dsimp [D2]
        omega
      apply h2 D2 hD2_fan hD2_cnt
      intro x hadm
      have hdg := delete_gate_eval tail1 p.val repl (List.ofFn x) hp_lt
        (by
          rcases hrepl_ok with hr | hr
          · exact Or.inl (by simpa using hr)
          · right; subst hr; simp [hD1_len])
        (by
          apply hrepl_eval
          rw [foldl_len, List.length_take_of_le (by omega)]
          simp)
        o1
      change circuitFun 9 D2 x = edgeF x
      rw [← hD1_adm x hadm]
      change (D2.gates.foldl step (List.ofFn x)).getD D2.output false = (tail1.foldl step (List.ofFn x)).getD o1 false
      simpa [D2] using hdg.symm
    · push_neg at hbin9
      by_cases hq9 : tail[q'].inputs.head? = some 9
      · have hq1_head : tail1[q'].inputs.head? = some 100 := by
          simp [tail1, remapGate]
          cases hqi : tail[q'].inputs with
          | nil => rw [hqi] at hq9; simp at hq9
          | cons a rest =>
            rw [hqi] at hq9
            simp at hq9
            subst hq9
            simp [remap]
        have hq1_true : ∀ x : Fin 9 → Bool,
            ((tail1.take (q' + 1)).foldl step (List.ofFn x)).getD (9 + q') false = true := by
          intro x
          rw [← List.take_append_getElem (by omega : q' < tail1.length), List.foldl_append,
              List.foldl_cons, List.foldl_nil]
          have hlenw : ((tail1.take q').foldl step (List.ofFn x)).length = 9 + q' := by
            rw [foldl_len, List.length_take_of_le (by omega)]
            simp
          rw [← hlenw, getD_append_last]
          have hq1_op : tail1[q'].op = GateOp.not := by
            simpa [tail1, remapGate] using hq'_not
          rw [hq1_op]
          cases hqi : tail1[q'].inputs with
          | nil => rw [hqi] at hq1_head; simp at hq1_head
          | cons a rest =>
            rw [hqi] at hq1_head
            simp at hq1_head
            subst hq1_head
            rw [evalNot]; simp only [List.map_cons, List.headD_cons, getD_ge_len ((tail1.take q').foldl step (List.ofFn x)) 100 (by omega), Bool.not_false]
        have ho_ne_q : o ≠ 10 + q' := by
          intro hoq
          let x0 : Fin 9 → Bool := fun _ => false
          have ha := hD1_adm x0 (Or.inl rfl)
          have hsplit : tail1 = tail1.take (q' + 1) ++ tail1.drop (q' + 1) :=
            (List.take_append_drop (q' + 1) tail1).symm
          have ho1_eq : o1 = 9 + q' := by
            dsimp [o1, remap]
            rw [hoq]
            split_ifs <;> omega
          have hev : circuitFun 9 D1 x0 = true := by
            change (tail1.foldl step (List.ofFn x0)).getD o1 false = true
            rw [ho1_eq]
            conv_lhs => rw [hsplit, List.foldl_append]
            rw [foldl_getD_lt (tail1.drop (q' + 1)) _ (9 + q')
              (by rw [foldl_len, List.length_take_of_le (by omega)]; simp)]
            exact hq1_true x0
          rw [hev] at ha
          have h0f : edgeF x0 = false := by decide
          rw [h0f] at ha
          exact Bool.noConfusion ha
        by_cases hread : ∃ (r : Fin tail.length), q' < r.val ∧ (10 + q') ∈ (tail.get r).inputs
        · obtain ⟨r, hqr, hr_in⟩ := hread
          have hr_lt : r.val < tail1.length := by simpa [tail1] using r.isLt
          have hr_op : tail1[r.val].op = GateOp.and ∨ tail1[r.val].op = GateOp.or := by
            simpa [tail1, remapGate] using htail_bin r.val r.isLt (by omega)
          have hr_pBin : pBin tail1[r.val] = true := by
            rcases hr_op with h | h <;> simp [pBin, h]
          have hr_len : tail1[r.val].inputs.length ≤ 2 :=
            (hD1_fan _ (List.getElem_mem hr_lt)).2
          have hr_in1 : (9 + q') ∈ tail1[r.val].inputs := by
            have hin' : 10 + q' ∈ tail[r.val].inputs := by simpa [List.get_eq_getElem] using hr_in
            have hmem := List.mem_map_of_mem (f := remap 9 100) hin'
            have hrm : remap 9 100 (10 + q') = 9 + q' := by
              dsimp [remap]; split_ifs <;> omega
            rw [hrm] at hmem
            simpa [tail1, remapGate] using hmem
          have hrepl_ex : ∃ repl : ℕ, (repl < 9 + r.val ∨ repl = 100) ∧
              ∀ w : List Bool, w.length = 9 + r.val → w.getD (9 + q') false = true →
                tail1[r.val].op.eval (tail1[r.val].inputs.map fun i => w.getD i false) =
                  w.getD repl false := by
            rcases hr_op with hand | hor
            · rcases hins : tail1[r.val].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
              · rw [hins] at hr_in1; simp at hr_in1
              · rw [hins] at hr_in1
                have ha : a = 9 + q' := (List.mem_singleton.mp hr_in1).symm
                subst ha
                refine ⟨9 + q', Or.inl (by omega), fun w _ hqtr => ?_⟩
                rw [hand]
                rw [evalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              · rw [hins] at hr_in1
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_in1
                rcases hr_in1 with rfl | rfl
                · by_cases hblt : b < 9 + r.val
                  · refine ⟨b, Or.inl hblt, fun w _ hqtr => ?_⟩
                    rw [hand]
                    rw [evalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hqtr, Bool.true_and, Bool.and_true]
                  · refine ⟨100, Or.inr rfl, fun w hw hqtr => ?_⟩
                    rw [hand]
                    rw [evalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hqtr, getD_ge_len w 100 (by omega), getD_ge_len w b (by omega), Bool.true_and, Bool.and_true]
                · by_cases halt : a < 9 + r.val
                  · refine ⟨a, Or.inl halt, fun w _ hqtr => ?_⟩
                    rw [hand]
                    rw [evalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hqtr, Bool.and_true]
                  · refine ⟨100, Or.inr rfl, fun w hw hqtr => ?_⟩
                    rw [hand]
                    rw [evalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hqtr, getD_ge_len w 100 (by omega), getD_ge_len w a (by omega), Bool.and_true]
              · rw [hins] at hr_len; simp at hr_len
            · refine ⟨9 + q', Or.inl (by omega), fun w _ hqtr => ?_⟩
              rw [hor, hqtr]
              change (tail1[r.val].inputs.map fun i => w.getD i false).any id = true
              rw [List.any_eq_true]
              exact ⟨true, List.mem_map.mpr ⟨9 + q', hr_in1, hqtr⟩, rfl⟩
          obtain ⟨repl, hrepl_ok, hrepl_eval⟩ := hrepl_ex
          let D2 : Circuit :=
            ⟨tail1.take r.val ++ (tail1.drop (r.val + 1)).map (remapGate (9 + r.val) repl),
             remap (9 + r.val) repl o1⟩
          have hD2_fan : FanInTwo D2 := fan_delete tail1 r.val repl hD1_fan
          have hD2_cnt : D2.gates.countP pBin ≤ 12 := by
            have h := countP_delete tail1 r.val repl hr_lt hr_pBin
            dsimp [D2]
            omega
          apply h2 D2 hD2_fan hD2_cnt
          intro x hadm
          have hdg := delete_gate_eval tail1 r.val repl (List.ofFn x) hr_lt
            (by
              rcases hrepl_ok with hr' | hr'
              · exact Or.inl (by simpa using hr')
              · right; subst hr'; simp [hD1_len])
            (by
              apply hrepl_eval
              · rw [foldl_len, List.length_take_of_le (by omega)]; simp
              · have htsplit : tail1.take r.val =
                    tail1.take (q' + 1) ++ (tail1.take r.val).drop (q' + 1) := by
                  conv_lhs => rw [← List.take_append_drop (q' + 1) (tail1.take r.val)]
                  rw [List.take_take, Nat.min_eq_left (by omega)]
                rw [htsplit, List.foldl_append]
                rw [foldl_getD_lt _ _ (9 + q')
                  (by rw [foldl_len, List.length_take_of_le (by omega)]; simp)]
                exact hq1_true x)
            o1
          change circuitFun 9 D2 x = edgeF x
          rw [← hD1_adm x hadm]
          change (D2.gates.foldl step (List.ofFn x)).getD D2.output false = (tail1.foldl step (List.ofFn x)).getD o1 false
          simpa [D2] using hdg.symm
        · push_neg at hread
          have hpost_eq : ∀ (gs : List Gate) (a b : List Bool),
              a.length = b.length →
              (∀ g ∈ gs, (10 + q') ∉ g.inputs) →
              (∀ k, k ≠ 10 + q' → a.getD k false = b.getD k false) →
              ∀ k, k ≠ 10 + q' → (gs.foldl step a).getD k false = (gs.foldl step b).getD k false := by
            intro gs
            induction gs with
            | nil => intro a b _ _ heq k hk; exact heq k hk
            | cons g gs ih =>
              intro a b hlen hno heq k hk
              have hval : g.op.eval (g.inputs.map fun i => a.getD i false) =
                  g.op.eval (g.inputs.map fun i => b.getD i false) := by
                congr 1
                apply List.map_congr_left
                intro j hj
                exact heq j (fun hje => hno g List.mem_cons_self (hje ▸ hj))
              rw [List.foldl_cons, List.foldl_cons]
              apply ih (step a g) (step b g) (by simp [step, hlen])
                (fun g' hg' => hno g' (List.mem_cons_of_mem g hg')) _ k hk
              intro j hj
              by_cases hjl : j < a.length
              · rw [List.getD_append _ _ _ _ hjl, List.getD_append _ _ _ _ (by omega)]
                exact heq j hj
              · by_cases hje : j = a.length
                · subst hje
                  rw [getD_append_last, hlen, getD_append_last, hval]
                · rw [getD_ge_len (step a g) j (by simp [step]; omega)]
                  rw [getD_ge_len (step b g) j (by simp [step]; omega)]
          have hC0_eq : ∀ x : Fin 9 → Bool,
              circuitFun 9 ⟨replaceByConst (g0 :: tail) q.val false, o⟩ x = edgeF x := by
            intro x
            have hc : circuitFun 9 ⟨g0 :: tail, o⟩ x = edgeF x := congrFun correct x
            rw [← hc]
            change ((replaceByConst (g0 :: tail) q.val false).foldl step (List.ofFn x)).getD o false =
              ((g0 :: tail).foldl step (List.ofFn x)).getD o false
            have hqlt_all : q.val < (g0 :: tail).length := q.isLt
            have hset : replaceByConst (g0 :: tail) q.val false =
                (g0 :: tail).take q.val ++ constGate false :: (g0 :: tail).drop (q.val + 1) := by
              change (g0 :: tail).set q.val (constGate false) = _
              rw [List.set_eq_take_append_cons_drop, ite_eq_left hqlt_all]
            have horig : (g0 :: tail) =
                (g0 :: tail).take q.val ++ (g0 :: tail)[q.val] :: (g0 :: tail).drop (q.val + 1) := by
              calc
                g0 :: tail = (g0 :: tail).take (q.val + 1) ++ (g0 :: tail).drop (q.val + 1) :=
                  (List.take_append_drop (q.val + 1) _).symm
                _ = ((g0 :: tail).take q.val ++ [(g0 :: tail)[q.val]]) ++ (g0 :: tail).drop (q.val + 1) := by
                  rw [List.take_append_getElem hqlt_all]
                _ = _ := by rw [List.append_assoc]; rfl
            rw [hset]
            conv_rhs => rw [horig]
            rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
            let w := ((g0 :: tail).take q.val).foldl step (List.ofFn x)
            have hwlen : w.length = 10 + q' := by
              dsimp [w]
              rw [foldl_len, List.length_take_of_le (by omega)]
              simp; omega
            have hno_post : ∀ g ∈ (g0 :: tail).drop (q.val + 1), (10 + q') ∉ g.inputs := by
              intro g hg
              have hdrop : (g0 :: tail).drop (q.val + 1) = tail.drop (q' + 1) := by
                rw [hq_eq]; rfl
              rw [hdrop] at hg
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
              rw [List.length_drop] at hj
              rw [List.getElem_drop]
              exact hread ⟨q' + 1 + j, by omega⟩ (by dsimp; omega)
            apply hpost_eq _ (step w (constGate false)) (step w (g0 :: tail)[q.val])
              (by simp [step]) hno_post _ o ho_ne_q
            intro k hk
            by_cases hkl : k < w.length
            · rw [List.getD_append _ _ _ _ hkl, List.getD_append _ _ _ _ hkl]
            · rw [getD_ge_len (step w (constGate false)) k (by simp [step]; omega)]
              rw [getD_ge_len (step w (g0 :: tail)[q.val]) k (by simp [step]; omega)]
          obtain ⟨m, hm, hmf⟩ := hmiss
          have htrue : ∀ n ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288] : List ℕ),
              edgeF (fun j : Fin 9 => n.testBit j.val) = true := by decide
          rw [hC0_eq, htrue m hm] at hmf
          exact Bool.noConfusion hmf
      · have hdead_post : ∀ (gs : List Gate) (a b : List Bool),
            a.length = b.length + 1 →
            9 ≤ b.length →
            (∀ g ∈ gs, (g.op = GateOp.not → g.inputs.head? ≠ some 9) ∧
              (g.op ≠ GateOp.not → 9 ∉ g.inputs)) →
            (∀ k, k < 9 → a.getD k false = b.getD k false) →
            (∀ k, 9 < k → a.getD k false = b.getD (k - 1) false) →
            ∀ k, k ≠ 9 → (gs.foldl step a).getD k false =
              ((gs.map (remapGate 9 100)).foldl step b).getD (remap 9 100 k) false := by
          intro gs
          induction gs with
          | nil =>
            intro a b _ _ _ hlt hgt k hk
            simp only [List.map_nil, List.foldl_nil, remap]
            split_ifs with h1
            · exact hlt k h1
            · exact hgt k (by omega)
          | cons g gs ih =>
            intro a b hlen hb9 hok hlt hgt k hk
            have hne_map : ∀ j, j ≠ 9 → a.getD j false = b.getD (remap 9 100 j) false := by
              intro j hj
              simp only [remap]
              split_ifs with h1
              · exact hlt j h1
              · exact hgt j (by omega)
            have hval : (remapGate 9 100 g).op.eval
                ((remapGate 9 100 g).inputs.map fun i => b.getD i false) =
                g.op.eval (g.inputs.map fun i => a.getD i false) := by
              have hgk := hok g List.mem_cons_self
              by_cases hgn : g.op = GateOp.not
              · have hh := hgk.1 hgn
                rw [hgn]
                cases hgi : g.inputs with
                | nil => dsimp only [remapGate]; rw [hgi, evalNot, evalNot]; rfl
                | cons u rest =>
                  rw [hgi] at hh
                  have hu9 : u ≠ 9 := by simpa using hh
                  dsimp only [remapGate]; rw [hgi, evalNot, evalNot]; simp only [List.map_cons, List.headD_cons]
                  congr 1
                  exact (hne_map u hu9).symm
              · have hnin := hgk.2 hgn
                simp only [remapGate, List.map_map, Function.comp_def]
                congr 1
                apply List.map_congr_left
                intro j hj
                exact (hne_map j (fun hje => hnin (hje ▸ hj))).symm
            rw [List.map_cons, List.foldl_cons, List.foldl_cons]
            apply ih (step a g) (step b (remapGate 9 100 g)) (by simp [step, hlen])
              (by simp [step]; omega) (fun g' hg' => hok g' (List.mem_cons_of_mem g hg'))
            · intro j hj
              rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              exact hlt j hj
            · intro j hj
              by_cases hja : j < a.length
              · rw [List.getD_append _ _ _ _ hja, List.getD_append _ _ _ _ (by omega)]
                exact hgt j hj
              · by_cases hje : j = a.length
                · subst hje
                  have hjb : a.length - 1 = b.length := by omega
                  rw [getD_append_last, hjb, getD_append_last, hval]
                · rw [getD_ge_len (step a g) j (by simp [step]; omega)]
                  rw [getD_ge_len (step b (remapGate 9 100 g)) (j - 1) (by simp [step]; omega)]
            · exact hk
        have hok_tail : ∀ g ∈ tail, (g.op = GateOp.not → g.inputs.head? ≠ some 9) ∧
            (g.op ≠ GateOp.not → 9 ∉ g.inputs) := by
          intro g hg
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
          constructor
          · intro hgn
            by_cases hjq : j = q'
            · subst hjq; exact hq9
            · exact False.elim (hunique j hj hjq hgn)
          · intro hgn
            by_cases hjq : j = q'
            · subst hjq; exact False.elim (hgn hq'_not)
            · exact hbin9 ⟨j, hj⟩ hjq
        have hD1_all : circuitFun 9 D1 = edgeF := by
          funext x
          have hc : circuitFun 9 ⟨g0 :: tail, o⟩ x = edgeF x := congrFun correct x
          rw [← hc]
          have hdp := hdead_post tail (step (List.ofFn x) g0) (List.ofFn x)
            (by simp [step]) (by simp) hok_tail
            (fun k hk => List.getD_append _ _ _ _ (by simp; omega))
            (fun k hk => by
              rw [getD_ge_len (step (List.ofFn x) g0) k (by simp [step]; omega)]
              rw [getD_ge_len (List.ofFn x) (k - 1) (by simp; omega)])
            o ho_ne_9
          change (tail1.foldl step (List.ofFn x)).getD o1 false = ((g0 :: tail).foldl step (List.ofFn x)).getD o false
          exact hdp.symm
        exact h1 D1 hD1_fan (by change tail1.length ≤ 14; omega) hD1_all

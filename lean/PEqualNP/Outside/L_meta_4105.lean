import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4105_aux

-- copied from the merged file L_meta_534.lean (no constant gate, no duplicate wire in a minimal circuit)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · rw [if_pos hgt]; exact hm.2.2.2.2.2 u hgt
  · rw [if_neg hgt]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'

def effInputs (g : Gate) : List ℕ :=
  GateOp.casesOn (motive := fun _ => List ℕ) g.op
    g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs

lemma eval_eq_effInputs (g : Gate) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((effInputs g).map f) := by
  cases hop : g.op <;> simp only [effInputs, hop, GateOp.eval]
  cases g.inputs <;> simp

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

-- Part 1: Output is the last gate when C.gates is nonempty

lemma output_last {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y)
    (hne : C.gates ≠ []) :
    C.output + 1 = n + C.gates.length := by
  by_contra hne_out
  by_cases hge : n + C.gates.length ≤ C.output
  · obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    simp only [circuitFun, Circuit.eval]
    rw [getD_ge_length _ _ (by rw [wires_length]; exact hge),
        getD_ge_length _ _ (by rw [wires_length]; exact hge)]
  · have hpos : 0 < C.gates.length := List.length_pos_of_ne_nil hne
    have hlt : C.output < n + (C.gates.length - 1) := by omega
    have hsplit : C.gates = C.gates.dropLast ++ [C.gates.getLast hne] :=
      (List.dropLast_append_getLast hne).symm
    let D : Circuit := ⟨C.gates.dropLast, C.output⟩
    have hfitD : FanInTwo D := fun g hg => hmin.1 g (List.dropLast_subset _ hg)
    have hfunD : circuitFun n D = circuitFun n C := by
      funext x
      simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
      conv_rhs => rw [hsplit, List.foldl_append]
      have hlt' : C.output < (C.gates.dropLast.foldl stepWire (List.ofFn x)).length := by
        rw [foldl_stepWire_length, List.length_ofFn, List.length_dropLast]
        exact hlt
      exact (foldl_stepWire_getD_lt [C.gates.getLast hne] _ C.output hlt').symm
    have hle := hmin.2 D hfitD hfunD
    simp only [Circuit.size, D, List.length_dropLast] at hle
    omega

-- Part 2: Every gate except the last is read by some later gate

lemma every_gate_read {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y)
    (j : ℕ) (hj : j + 1 < C.gates.length) :
    ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (effInputs p.1).contains (n + j) = true := by
  by_contra hno
  have hne : C.gates ≠ [] := by intro h; simp [h] at hj
  have hout : C.output + 1 = n + C.gates.length := output_last hmin hnc hne
  have hj_lt : j < C.gates.length := by omega
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj_lt
  have hnot_read : ∀ (t : ℕ) (ht : t < post.length),
      ∀ u ∈ effInputs (post[t]'ht), u ≠ n + j := by
    intro t ht u hu heq
    subst heq
    apply hno
    have hidx : j + 1 + t < C.gates.length := by
      have := congrArg List.length hgs; simp [hpre_len] at this; omega
    have hget : C.gates[j + 1 + t]'hidx = post[t]'ht := by
      have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; exact hidx) = post[t]'ht := by
        rw [List.getElem_append_right (by omega)]
        have hsub : j + 1 + t - pre.length = t + 1 := by omega
        simp [hsub]
      simpa [hgs] using h1
    refine ⟨(post[t]'ht, j + 1 + t), ?_, by omega, List.contains_iff_mem.mpr hu⟩
    have hmem : (C.gates.zipIdx)[j + 1 + t]'(by simp [hidx]) ∈ C.gates.zipIdx := List.getElem_mem _
    simpa [List.getElem_zipIdx, hget] using hmem
  let shiftGate (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftDown (n + j))⟩
  let D : Circuit := ⟨pre ++ post.map shiftGate, C.output - 1⟩
  have hfitD : FanInTwo D := by
    intro g hg
    rcases List.mem_append.mp hg with hpre | hpost
    · exact hmin.1 g (by rw [hgs]; exact List.mem_append_left _ hpre)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hpost
      have hg0C := hmin.1 g0 (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨hg0C.1, by simp [shiftGate, hg0C.2]⟩
  have hfunD : circuitFun n D = circuitFun n C := by
    funext x
    simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
    conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
    rw [List.foldl_append]
    let w0 := pre.foldl stepWire (List.ofFn x)
    have hw0_len : w0.length = n + j := by
      simp [w0, foldl_stepWire_length, hpre_len]
    let bOld := gj.op.eval (gj.inputs.map fun i => w0.getD i false)
    have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
    have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
        ((post.map shiftGate).foldl stepWire w0) := by
      refine foldl_wiresMatch w0 bOld post (post.map shiftGate) (stepWire w0 gj) w0 hm0
        (by simp) ?_
      intro t htC htD vC vD hmv _
      simp only [List.getElem_map, shiftGate]
      rw [eval_eq_effInputs ⟨(post[t]'htC).op, (post[t]'htC).inputs.map (shiftDown (n + j))⟩,
          eval_eq_effInputs (post[t]'htC)]
      have heff_map : effInputs ⟨(post[t]'htC).op, (post[t]'htC).inputs.map (shiftDown (n + j))⟩ =
          (effInputs (post[t]'htC)).map (shiftDown (n + j)) := by
        cases h : (post[t]'htC).op <;> simp [effInputs, h, List.map_take]
      rw [heff_map, List.map_map]
      congr 1
      refine List.map_congr_left fun u hu => ?_
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by rw [hw0_len]; exact hnot_read t htC u hu)
    exact hmEnd.2.2.2.2.2 C.output (by omega)
  have hle := hmin.2 D hfitD hfunD
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  simp only [Circuit.size, D, List.length_append, List.length_map] at hle
  omega

-- Part 3: No gate computes the same function as an earlier wire

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

lemma no_duplicate_wire {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C)
    (i j : ℕ) (hij : i < n + j) (hj : j < C.gates.length) :
    ∃ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false := by
  by_contra hsame
  push Not at hsame
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  let aliasGate (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire (n + j) i)⟩
  let D : Circuit := ⟨pre ++ post.map aliasGate, aliasWire (n + j) i C.output⟩
  have hfitD : FanInTwo D := by
    intro g hg
    rcases List.mem_append.mp hg with hpre | hpost
    · exact hmin.1 g (by rw [hgs]; exact List.mem_append_left _ hpre)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hpost
      have hg0C := hmin.1 g0 (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨hg0C.1, by simp [aliasGate, hg0C.2]⟩
  have hfunD : circuitFun n D = circuitFun n C := by
    funext x
    have hxy := hsame x
    simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
    conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
    rw [List.foldl_append]
    let w0 := pre.foldl stepWire (List.ofFn x)
    have hw0_len : w0.length = n + j := by
      simp [w0, foldl_stepWire_length, hpre_len]
    let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
    have hval_eq : w0.getD i false = bOld := by
      have hCi : (C.wires (List.ofFn x)).getD i false = w0.getD i false := by
        rw [wires_eq_foldl, hgs, List.foldl_append]
        exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
      have hCj : (C.wires (List.ofFn x)).getD (n + j) false = bOld := by
        rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
        rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
      rw [← hCi, ← hCj, hxy]
    have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
    have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
        ∀ u, vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
      intro vC vD hmv u
      unfold aliasWire
      by_cases hu : u = n + j
      · subst hu
        rw [if_pos rfl, hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
      · rw [if_neg hu, ← hw0_len]
        exact wiresMatch_getD_shiftDown hmv (by omega)
    have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
        ((post.map aliasGate).foldl stepWire w0) := by
      refine foldl_wiresMatch w0 bOld post (post.map aliasGate) (stepWire w0 gj) w0 hm0
        (by simp) ?_
      intro t htC htD vC vD hmv _
      simp only [List.getElem_map, aliasGate, List.map_map]
      congr 1
      refine List.map_congr_left fun u _ => ?_
      exact halias_get vC vD hmv u
    exact halias_get _ _ hmEnd C.output
  have hle := hmin.2 D hfitD hfunD
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  simp only [Circuit.size, D, List.length_append, List.length_map] at hle
  omega

-- Part 4: No gate computes a constant function

def rewriteTrueGate (wOld : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => ⟨.and, (g.inputs.filter (fun u => u != wOld)).map (shiftDown wOld)⟩
  | .or =>
    if g.inputs.contains wOld then ⟨.and, []⟩
    else ⟨.or, g.inputs.map (shiftDown wOld)⟩
  | .not =>
    match g.inputs with
    | [] => ⟨.not, []⟩
    | u :: _ => if u = wOld then ⟨.or, []⟩ else ⟨.not, [shiftDown wOld u]⟩
  | op => ⟨op, g.inputs.map (shiftDown wOld)⟩

lemma rewriteTrueGate_fit (wOld : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (rewriteTrueGate wOld g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (rewriteTrueGate wOld g).inputs.length ≤ 2 := by
  obtain ⟨hop, hlen⟩ := hg
  change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
  rcases hop with h | h | h
  · simp only [rewriteTrueGate, h, List.length_map]
    refine ⟨Or.inl rfl, (List.length_filter_le _ _).trans hlen⟩
  · simp only [rewriteTrueGate, h]
    split
    · exact ⟨Or.inl rfl, by simp⟩
    · exact ⟨Or.inr (Or.inl rfl), by simp [hlen]⟩
  · simp only [rewriteTrueGate, h]
    cases g.inputs with
    | nil => simp
    | cons u rest =>
      by_cases hu : u = wOld <;> simp [hu]

lemma rewriteTrueGate_eval (w0 : List Bool) (vC vD : List Bool)
    (hm : wiresMatch w0 true vC vD) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (rewriteTrueGate w0.length g).op.eval
      ((rewriteTrueGate w0.length g).inputs.map fun i => vD.getD i false) =
    g.op.eval (g.inputs.map fun i => vC.getD i false) := by
  change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
  rcases hop with h | h | h
  · simp only [rewriteTrueGate, h, GateOp.eval, List.map_map, List.all_map]
    induction g.inputs with
    | nil => rfl
    | cons u us ih =>
      by_cases hu : u = w0.length
      · subst hu
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          List.all_cons, Function.comp_apply, id_eq, hm.2.2.1, Bool.true_and]
        exact ih
      · have hne : (u != w0.length) = true := bne_iff_ne.mpr hu
        simp only [List.filter_cons, hne, ↓reduceIte, List.all_cons, Function.comp_apply, id_eq]
        rw [wiresMatch_getD_shiftDown hm hu, ih]
  · simp only [rewriteTrueGate, h]
    by_cases hmem : g.inputs.contains w0.length = true
    · rw [if_pos hmem]
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      refine ⟨true, List.mem_map.mpr ⟨w0.length, List.contains_iff_mem.mp hmem, hm.2.2.1⟩, rfl⟩
    · rw [if_neg hmem]
      simp only [GateOp.eval, List.map_map]
      congr 1
      refine List.map_congr_left fun u hu => ?_
      have hne : u ≠ w0.length := fun heq => hmem (List.contains_iff_mem.mpr (heq ▸ hu))
      exact wiresMatch_getD_shiftDown hm hne
  · obtain ⟨op, inputs⟩ := g
    dsimp only at h ⊢
    subst h
    cases inputs with
    | nil => simp [rewriteTrueGate, GateOp.eval]
    | cons u rest =>
      by_cases hu : u = w0.length
      · subst hu
        simp only [rewriteTrueGate, GateOp.eval, ↓reduceIte, List.map_nil, List.any_nil,
          List.map_cons, List.headD_cons, hm.2.2.1, Bool.not_true]
      · simp only [rewriteTrueGate, GateOp.eval, hu, ↓reduceIte, List.map_cons, List.map_nil,
          List.headD_cons, wiresMatch_getD_shiftDown hm hu]

lemma no_const_gate {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ x y : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false := by
  by_contra hconst
  push Not at hconst
  let x0 : Fin n → Bool := fun _ => false
  let b : Bool := (C.wires (List.ofFn x0)).getD (n + j) false
  have hall : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = b :=
    fun x => hconst x x0
  have hout_ne : C.output ≠ n + j := by
    intro heq
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    simp only [circuitFun, Circuit.eval, heq, hall x, hall y]
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  cases hb : b with
  | false =>
    let big : ℕ := n + C.gates.length
    let aliasGate (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire (n + j) big)⟩
    let D : Circuit := ⟨pre ++ post.map aliasGate, shiftDown (n + j) C.output⟩
    have hfitD : FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with hpre | hpost
      · exact hmin.1 g (by rw [hgs]; exact List.mem_append_left _ hpre)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hpost
        have hg0C := hmin.1 g0 (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
        exact ⟨hg0C.1, by simp [aliasGate, hg0C.2]⟩
    have hfunD : circuitFun n D = circuitFun n C := by
      funext x
      simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
      conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
      rw [List.foldl_append]
      let w0 := pre.foldl stepWire (List.ofFn x)
      have hw0_len : w0.length = n + j := by
        simp [w0, foldl_stepWire_length, hpre_len]
      have hbf : gj.op.eval (gj.inputs.map fun k => w0.getD k false) = false := by
        have hCj : (C.wires (List.ofFn x)).getD (n + j) false =
            gj.op.eval (gj.inputs.map fun k => w0.getD k false) := by
          rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
          rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
        rw [← hCj, hall x, hb]
      have hm0 : wiresMatch w0 false (stepWire w0 gj) w0 := by
        unfold stepWire; rw [hbf]; exact wiresMatch_init w0 false
      have hlenC : C.gates.length = pre.length + 1 + post.length := by
        have := congrArg List.length hgs; simp at this; omega
      have hmEnd : wiresMatch w0 false (post.foldl stepWire (stepWire w0 gj))
          ((post.map aliasGate).foldl stepWire w0) := by
        refine foldl_wiresMatch w0 false post (post.map aliasGate) (stepWire w0 gj) w0 hm0
          (by simp) ?_
        intro t htC htD vC vD hmv hvlen
        simp only [List.getElem_map, aliasGate, List.map_map]
        congr 1
        refine List.map_congr_left fun u _ => ?_
        simp only [Function.comp_apply, aliasWire]
        by_cases hu : u = n + j
        · subst hu
          simp only [↓reduceIte]
          rw [getD_ge_length vD big (by omega), ← hw0_len, hmv.2.2.1]
        · simp only [hu, ↓reduceIte]
          rw [← hw0_len]
          exact wiresMatch_getD_shiftDown hmv (by omega)
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmEnd (by rw [hw0_len]; exact hout_ne)
    have hle := hmin.2 D hfitD hfunD
    have hlenC : C.gates.length = pre.length + 1 + post.length := by
      have := congrArg List.length hgs; simp at this; omega
    simp only [Circuit.size, D, List.length_append, List.length_map] at hle
    omega
  | true =>
    let D : Circuit := ⟨pre ++ post.map (rewriteTrueGate (n + j)), shiftDown (n + j) C.output⟩
    have hfitD : FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with hpre | hpost
      · exact hmin.1 g (by rw [hgs]; exact List.mem_append_left _ hpre)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hpost
        have hg0C := hmin.1 g0 (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
        exact rewriteTrueGate_fit (n + j) g0 hg0C
    have hfunD : circuitFun n D = circuitFun n C := by
      funext x
      simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
      conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
      rw [List.foldl_append]
      let w0 := pre.foldl stepWire (List.ofFn x)
      have hw0_len : w0.length = n + j := by
        simp [w0, foldl_stepWire_length, hpre_len]
      have hbt : gj.op.eval (gj.inputs.map fun k => w0.getD k false) = true := by
        have hCj : (C.wires (List.ofFn x)).getD (n + j) false =
            gj.op.eval (gj.inputs.map fun k => w0.getD k false) := by
          rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
          rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
        rw [← hCj, hall x, hb]
      have hm0 : wiresMatch w0 true (stepWire w0 gj) w0 := by
        unfold stepWire; rw [hbt]; exact wiresMatch_init w0 true
      have hmEnd : wiresMatch w0 true (post.foldl stepWire (stepWire w0 gj))
          ((post.map (rewriteTrueGate (n + j))).foldl stepWire w0) := by
        refine foldl_wiresMatch w0 true post (post.map (rewriteTrueGate (n + j)))
          (stepWire w0 gj) w0 hm0 (by simp) ?_
        intro t htC htD vC vD hmv _
        simp only [List.getElem_map]
        have hgC := hmin.1 (post[t]'htC)
          (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.getElem_mem htC)))
        simpa only [hw0_len] using rewriteTrueGate_eval w0 vC vD hmv (post[t]'htC) hgC.1
      simpa only [hw0_len] using wiresMatch_getD_shiftDown hmEnd (by rw [hw0_len]; exact hout_ne)
    have hle := hmin.2 D hfitD hfunD
    have hlenC : C.gates.length = pre.length + 1 + post.length := by
      have := congrArg List.length hgs; simp at this; omega
    simp only [Circuit.size, D, List.length_append, List.length_map] at hle
    omega

theorem main (n : ℕ) (C : Circuit)
    (hmin : IsMinimalCircuit n C)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) :
    (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧
    (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧
    (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧
    (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧
      (GateOp.casesOn (motive := fun _ => List ℕ) p.1.op
        p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true) :=
  ⟨fun j hj => no_const_gate hmin hnc j hj,
   fun i j hij hj => no_duplicate_wire hmin i j hij hj,
   fun hne => output_last hmin hnc hne,
   fun j hj => every_gate_read hmin hnc j hj⟩


-- evaluation toolkit
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

lemma shape {n : ℕ} (gs : List Gate)
    (hF : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hA : ∀ j, j < gs.length → ∃ x y : Fin n → Bool, val gs x (n + j) ≠ val gs y (n + j))
    (hB : ∀ i j, i < n + j → j < gs.length → ∃ x : Fin n → Bool,
      val gs x i ≠ val gs x (n + j))
    (j : ℕ) (hj : j < gs.length) :
    (gs[j].op = GateOp.not ∧ ∃ a, a < n + j ∧ gs[j].inputs.take 1 = [a]) ∨
    ((gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) ∧
      ∃ a, a < n + j ∧ ∃ b, b < n + j ∧ a ≠ b ∧ gs[j].inputs = [a, b]) := by
  have hv := fun x : Fin n → Bool => val_gate gs x j hj
  have constC : ∀ c : Bool, (∀ x : Fin n → Bool, val gs x (n + j) = c) → False := by
    intro c hc
    obtain ⟨x, y, hne⟩ := hA j hj
    exact hne (by rw [hc x, hc y])
  have copyC : ∀ a, a < n + j → (∀ x : Fin n → Bool, val gs x (n + j) = val gs x a) → False := by
    intro a ha hc
    obtain ⟨x, hne⟩ := hB a j ha hj
    exact hne (hc x).symm
  obtain ⟨hop, hlen⟩ := hF _ (List.getElem_mem hj)
  generalize gs[j] = g at hv hop hlen ⊢
  obtain ⟨op, ins⟩ := g
  simp only at hv hop hlen ⊢
  rcases hop with rfl | rfl | rfl
  · right
    refine ⟨Or.inl rfl, ?_⟩
    match ins, hlen with
    | [], _ => exact (constC true (fun x => by rw [hv x]; simp [GateOp.eval])).elim
    | [a], _ =>
      by_cases ha : a < n + j
      · exact (copyC a ha (fun x => by rw [hv x]; simp [GateOp.eval, ha])).elim
      · exact (constC false (fun x => by rw [hv x]; simp [GateOp.eval, ha])).elim
    | [a, b], _ =>
      by_cases ha : a < n + j
      · by_cases hb : b < n + j
        · by_cases hab : a = b
          · subst hab
            exact (copyC a ha (fun x => by rw [hv x]; simp [GateOp.eval, ha])).elim
          · exact ⟨a, ha, b, hb, hab, rfl⟩
        · exact (constC false (fun x => by rw [hv x]; simp [GateOp.eval, hb])).elim
      · exact (constC false (fun x => by rw [hv x]; simp [GateOp.eval, ha])).elim
    | _ :: _ :: _ :: _, h => simp at h
  · right
    refine ⟨Or.inr rfl, ?_⟩
    match ins, hlen with
    | [], _ => exact (constC false (fun x => by rw [hv x]; simp [GateOp.eval])).elim
    | [a], _ =>
      by_cases ha : a < n + j
      · exact (copyC a ha (fun x => by rw [hv x]; simp [GateOp.eval, ha])).elim
      · exact (constC false (fun x => by rw [hv x]; simp [GateOp.eval, ha])).elim
    | [a, b], _ =>
      by_cases ha : a < n + j
      · by_cases hb : b < n + j
        · by_cases hab : a = b
          · subst hab
            exact (copyC a ha (fun x => by rw [hv x]; simp [GateOp.eval, ha])).elim
          · exact ⟨a, ha, b, hb, hab, rfl⟩
        · exact (copyC a ha (fun x => by rw [hv x]; simp [GateOp.eval, ha, hb])).elim
      · by_cases hb : b < n + j
        · exact (copyC b hb (fun x => by rw [hv x]; simp [GateOp.eval, ha, hb])).elim
        · exact (constC false (fun x => by rw [hv x]; simp [GateOp.eval, ha, hb])).elim
    | _ :: _ :: _ :: _, h => simp at h
  · left
    refine ⟨rfl, ?_⟩
    match ins with
    | [] => exact (constC true (fun x => by rw [hv x]; simp [GateOp.eval])).elim
    | a :: t =>
      by_cases ha : a < n + j
      · exact ⟨a, ha, by simp⟩
      · exact (constC true (fun x => by rw [hv x]; simp [GateOp.eval, ha])).elim

def trim (g : Gate) : Gate :=
  { op := g.op, inputs := List.take (bif g.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) g.inputs }

lemma step_trim (w : List Bool) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    step w (trim g) = step w g := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := h
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl
  · simp [step, trim, GateOp.eval, List.take_of_length_le hlen]
  · simp [step, trim, GateOp.eval, List.take_of_length_le hlen]
  · cases ins with
    | nil => simp [step, trim, GateOp.eval]
    | cons a t => simp [step, trim, GateOp.eval]

lemma fold_trim (gs : List Gate)
    (hF : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (w : List Bool) :
    (gs.map trim).foldl step w = gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [step_trim w g (hF g List.mem_cons_self), ih (fun g' hg' => hF g' (List.mem_cons_of_mem _ hg'))]

lemma final : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x5.gates = List.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => { op := x6.op, inputs := List.take (bif x6.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x6.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates ∧ x5.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ ∀ (x6 : List PEqualNP.CircuitLowerBounds.Gate) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 : List PEqualNP.CircuitLowerBounds.Gate), x5.gates = x6 ++ x7 :: x8 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∃ x10 < x1 + x6.length, x7.inputs = [x10]) ∨ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ x10 < x1 + x6.length, ∃ x11 < x1 + x6.length, x10 ≠ x11 ∧ x7.inputs = [x10, x11] := by
  intro n C hmin hnc
  obtain ⟨hA, hB, _, _⟩ := main n C hmin hnc
  have hF : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmin.1 g hg
    exact ⟨by simpa using h1, h2⟩
  refine ⟨⟨C.gates.map trim, C.output⟩, rfl, ?_, ?_, ?_⟩
  · simp [Circuit.size]
  · funext x
    show ((C.gates.map trim).foldl step (List.ofFn x)).getD C.output false =
      (C.gates.foldl step (List.ofFn x)).getD C.output false
    rw [fold_trim C.gates hF]
  · intro l g r h
    have h' : C.gates.map trim = l ++ g :: r := h
    have hj : l.length < C.gates.length := by
      have := congrArg List.length h'
      simp at this
      omega
    have h2 : (C.gates.map trim)[l.length]? = some g := by
      rw [h']
      simp
    rw [List.getElem?_map, List.getElem?_eq_getElem hj] at h2
    simp only [Option.map_some, Option.some.injEq] at h2
    subst h2
    rcases shape C.gates hF hA hB l.length hj with ⟨hop, a, ha, hin⟩ | ⟨hop, a, ha, b, hb, hab, hin⟩
    · left
      refine ⟨hop, a, ha, ?_⟩
      simp [trim, hop, GateOp.eval, hin]
    · right
      refine ⟨hop, a, ha, b, hb, hab, ?_⟩
      rcases hop with hop | hop <;> simp [trim, hop, GateOp.eval, hin]

end PEqualNP.Outside.L_meta_4105_aux

theorem PEqualNP.Outside.L_meta_4105 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x5.gates = List.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => { op := x6.op, inputs := List.take (bif x6.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x6.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates ∧ x5.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ ∀ (x6 : List PEqualNP.CircuitLowerBounds.Gate) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 : List PEqualNP.CircuitLowerBounds.Gate), x5.gates = x6 ++ x7 :: x8 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∃ x10 < x1 + x6.length, x7.inputs = [x10]) ∨ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ x10 < x1 + x6.length, ∃ x11 < x1 + x6.length, x10 ≠ x11 ∧ x7.inputs = [x10, x11] := by
  exact PEqualNP.Outside.L_meta_4105_aux.final

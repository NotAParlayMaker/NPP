import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CircuitMoves

namespace PEqualNP.Outside.L_meta_4295

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl evalStep w

lemma evalStep_length (w : List Bool) (g : Gate) :
    (evalStep w g).length = w.length + 1 := by
  simp [evalStep]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    simp only [run, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih, evalStep_length]
    omega

lemma run_append (gs1 gs2 : List Gate) (w : List Bool) :
    run (gs1 ++ gs2) w = run gs2 (run gs1 w) := by
  simp [run, List.foldl_append]

lemma getD_append_lt (w ext : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ ext).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_len (w ext : List Bool) (b : Bool) :
    (w ++ b :: ext).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_eq_false_of_le (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma evalStep_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (evalStep w g).getD i false = w.getD i false :=
  getD_append_lt w [g.op.eval (g.inputs.map fun j => w.getD j false)] i hi

lemma evalStep_getD_len (w : List Bool) (g : Gate) :
    (evalStep w g).getD w.length false = g.op.eval (g.inputs.map fun j => w.getD j false) :=
  getD_append_len w [] _

lemma run_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hlt : i < (evalStep w g).length := by rw [evalStep_length]; omega
    exact (ih (evalStep w g) hlt).trans (evalStep_getD_lt w g i hi)

lemma run_take_length (gs : List Gate) (m : ℕ) (hm : m < gs.length) (x : List Bool) :
    (run (gs.take m) x).length = x.length + m := by
  rw [run_length, List.length_take]
  omega

lemma eraseGate_length (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length = C.gates.length - 1 := by
  simp only [eraseGate, hm, ↓reduceIte, List.length_append, List.length_take, List.length_map,
    List.length_drop]
  omega

lemma eraseRedirect_lt (n m p k i : ℕ) (hp : p < n + m) (hm : m ≤ k) (hi : i < n + (k + 1)) :
    eraseRedirect n m p i < n + k := by
  unfold eraseRedirect
  split_ifs with h1 h2 <;> omega

lemma liftAt_isAO2 (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hOut : C.output < n + C.gates.length) :
    IsAO2 n (liftAt n C m p h) ∧ (liftAt n C m p h).output < n + (liftAt n C m p h).gates.length := by
  rcases hAO with ⟨hAndOr, hReads, hLen⟩
  let E := eraseGate n C m p
  let C' := liftAt n C m p h
  have hElen : E.gates.length = C.gates.length - 1 := eraseGate_length n C m p hm
  have hC'gates : C'.gates = E.gates ++ [⟨GateOp.or, [E.output, h]⟩] := rfl
  have hC'len : C'.gates.length = E.gates.length + 1 := by
    rw [hC'gates, List.length_append]
    simp
  have hEsplit : E.gates = C.gates.take m ++
      (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) := by
    simp [E, eraseGate, hm]
  have hEmem : ∀ g ∈ E.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    rw [hEsplit, List.mem_append] at hg
    rcases hg with hlt | hrt
    · have hmemC : g ∈ C.gates := List.mem_of_mem_take hlt
      exact ⟨hAndOr g hmemC, hLen g hmemC⟩
    · rw [List.mem_map] at hrt
      rcases hrt with ⟨g0, hg0, rfl⟩
      have hmemC : g0 ∈ C.gates := List.mem_of_mem_drop hg0
      exact ⟨hAndOr g0 hmemC, by simpa using hLen g0 hmemC⟩
  have hC'AndOr : AndOrOnly C' := by
    intro g hg
    rw [hC'gates, List.mem_append, List.mem_singleton] at hg
    rcases hg with h1 | rfl
    · exact (hEmem g h1).1
    · exact Or.inr rfl
  have hC'Len : ∀ g ∈ C'.gates, g.inputs.length = 2 := by
    intro g hg
    rw [hC'gates, List.mem_append, List.mem_singleton] at hg
    rcases hg with h1 | rfl
    · exact (hEmem g h1).2
    · rfl
  have hEout : E.output < n + E.gates.length := by
    have hEq : E.output = eraseRedirect n m p C.output := by simp [E, eraseGate, hm]
    rw [hEq]
    apply eraseRedirect_lt n m p E.gates.length C.output hp (by omega)
    omega
  have hC'Reads : ReadsBack n C' := by
    intro j hj i hi
    have hga : gateAt C' j = C'.gates.getD j ⟨GateOp.or, []⟩ := rfl
    rw [hga] at hi
    by_cases hjLast : j = E.gates.length
    · subst hjLast
      have hgateLast : C'.gates.getD E.gates.length ⟨GateOp.or, []⟩ = ⟨GateOp.or, [E.output, h]⟩ := by
        rw [hC'gates]
        simp [List.getD_eq_getElem?_getD]
      rw [hgateLast] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hEout
      · omega
    · have hjE : j < E.gates.length := by omega
      have hgetC' : C'.gates.getD j ⟨GateOp.or, []⟩ = E.gates.getD j ⟨GateOp.or, []⟩ := by
        rw [hC'gates, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hjE]
      rw [hgetC'] at hi
      by_cases hjm : j < m
      · have hgateE : E.gates.getD j ⟨GateOp.or, []⟩ = gateAt C j := by
          rw [hEsplit, gateAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by rw [List.length_take]; omega), List.getElem?_take_of_lt hjm]
        rw [hgateE] at hi
        exact hReads j (by omega) i hi
      · have htakeLen : (C.gates.take m).length = m := by rw [List.length_take]; omega
        have hjdrop : j - m < ((C.gates.drop (m + 1)).map
            (fun g : Gate => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).length := by
          simp only [List.length_map, List.length_drop]
          omega
        have hj1lt : j + 1 < C.gates.length := by omega
        have hgateE : E.gates.getD j ⟨GateOp.or, []⟩ =
            ⟨(gateAt C (j + 1)).op, (gateAt C (j + 1)).inputs.map (eraseRedirect n m p)⟩ := by
          rw [hEsplit, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), htakeLen]
          rw [List.getElem?_map, List.getElem?_drop]
          have hj1id : m + 1 + (j - m) = j + 1 := by omega
          rw [hj1id, gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1lt]
          rfl
        rw [hgateE] at hi
        simp only [List.mem_map] at hi
        rcases hi with ⟨i0, hi0, rfl⟩
        have hi0lt : i0 < n + (j + 1) := hReads (j + 1) hj1lt i0 hi0
        exact eraseRedirect_lt n m p j i0 hp (by omega) hi0lt
  refine ⟨⟨hC'AndOr, hC'Reads, hC'Len⟩, ?_⟩
  have hC'out : C'.output = n + E.gates.length := rfl
  rw [hC'out, hC'len]
  omega

def liftIdx (n m i : ℕ) : ℕ :=
  if i < n + m then i else i + 1

def LeRel (n m p : ℕ) (u v : List Bool) : Prop :=
  u.length + 1 = v.length ∧ n + m ≤ u.length ∧
    (∀ i < u.length, u.getD i false = true → v.getD (liftIdx n m i) false = true) ∧
    (v.getD p false = true → v.getD (n + m) false = true)

def EqRel (n m p : ℕ) (u v : List Bool) : Prop :=
  u.length + 1 = v.length ∧ n + m ≤ u.length ∧
    (∀ i < u.length, u.getD i false = v.getD (liftIdx n m i) false) ∧
    v.getD (n + m) false = v.getD p false

lemma leRel_wire (n m p : ℕ) (hp_lt : p < n + m) (u v : List Bool) (hrel : LeRel n m p u v) (j : ℕ) :
    u.getD (eraseRedirect n m p j) false = true → v.getD j false = true := by
  rcases hrel with ⟨hlen, hnm, hmap, hp⟩
  intro hu
  unfold eraseRedirect at hu
  split_ifs at hu with hj1 hj2
  · subst hj1
    have hvp : v.getD (liftIdx n m p) false = true := hmap p (by omega) hu
    have hl : liftIdx n m p = p := by unfold liftIdx; rw [if_pos hp_lt]
    rw [hl] at hvp
    exact hp hvp
  · by_cases hju : j - 1 < u.length
    · have h1 := hmap (j - 1) hju hu
      have hl : liftIdx n m (j - 1) = j := by unfold liftIdx; split_ifs <;> omega
      rwa [hl] at h1
    · have hu_f : u.getD (j - 1) false = false := getD_eq_false_of_le u (j - 1) (by omega)
      rw [hu_f] at hu
      cases hu
  · have hju : j < u.length := by omega
    have h1 := hmap j hju hu
    have hl : liftIdx n m j = j := by unfold liftIdx; split_ifs <;> omega
    rwa [hl] at h1

lemma eqRel_wire (n m p : ℕ) (hp_lt : p < n + m) (u v : List Bool) (hrel : EqRel n m p u v) (j : ℕ) :
    u.getD (eraseRedirect n m p j) false = v.getD j false := by
  rcases hrel with ⟨hlen, hnm, hmap, hp⟩
  unfold eraseRedirect
  split_ifs with hj1 hj2
  · subst hj1
    have hl : liftIdx n m p = p := by unfold liftIdx; rw [if_pos hp_lt]
    have hvp : u.getD p false = v.getD p false := by simpa [hl] using hmap p (by omega)
    exact hvp.trans hp.symm
  · by_cases hju : j - 1 < u.length
    · have hl : liftIdx n m (j - 1) = j := by unfold liftIdx; split_ifs <;> omega
      simpa [hl] using hmap (j - 1) hju
    · rw [getD_eq_false_of_le u (j - 1) (by omega), getD_eq_false_of_le v j (by omega)]
  · have hju : j < u.length := by omega
    have hl : liftIdx n m j = j := by unfold liftIdx; split_ifs <;> omega
    simpa [hl] using hmap j hju

lemma evalStep_leRel (n m p : ℕ) (hp_lt : p < n + m) (u v : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hrel : LeRel n m p u v) :
    LeRel n m p
      (evalStep u ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)
      (evalStep v g) := by
  rcases hrel with ⟨hlen, hnm, hmap, hp⟩
  have hrel0 : LeRel n m p u v := ⟨hlen, hnm, hmap, hp⟩
  have hwire := leRel_wire n m p hp_lt u v hrel0
  have hpv : (evalStep v g).getD p false = v.getD p false := evalStep_getD_lt v g p (by omega)
  have hnmv : (evalStep v g).getD (n + m) false = v.getD (n + m) false :=
    evalStep_getD_lt v g (n + m) (by omega)
  refine ⟨by rw [evalStep_length, evalStep_length, hlen], by rw [evalStep_length]; omega, ?_, ?_⟩
  · intro i hi hui
    rw [evalStep_length] at hi
    by_cases hiu : i < u.length
    · have hli : liftIdx n m i < v.length := by unfold liftIdx; split_ifs <;> omega
      rw [evalStep_getD_lt _ _ i hiu] at hui
      rw [evalStep_getD_lt _ _ (liftIdx n m i) hli]
      exact hmap i hiu hui
    · have hieq : i = u.length := by omega
      subst hieq
      have hli : liftIdx n m u.length = v.length := by
        unfold liftIdx
        split_ifs with hs <;> omega
      rw [hli, evalStep_getD_len]
      rw [evalStep_getD_len] at hui
      rcases hop with hand | hor
      · rw [hand] at hui ⊢
        dsimp [GateOp.eval] at hui ⊢
        rw [List.all_eq_true] at hui ⊢
        intro b hb
        rw [List.mem_map] at hb
        rcases hb with ⟨j, hj, rfl⟩
        have hb1 := hui (u.getD (eraseRedirect n m p j) false)
          (List.mem_map.mpr ⟨eraseRedirect n m p j, List.mem_map.mpr ⟨j, hj, rfl⟩, rfl⟩)
        exact hwire j hb1
      · rw [hor] at hui ⊢
        dsimp [GateOp.eval] at hui ⊢
        rw [List.any_eq_true] at hui ⊢
        rcases hui with ⟨b, hb, hbt⟩
        rw [List.mem_map] at hb
        rcases hb with ⟨j0, hj0, rfl⟩
        rw [List.mem_map] at hj0
        rcases hj0 with ⟨j, hj, rfl⟩
        exact ⟨v.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, hwire j hbt⟩
  · intro hvp
    rw [hpv] at hvp
    rw [hnmv]
    exact hp hvp

lemma evalStep_eqRel (n m p : ℕ) (hp_lt : p < n + m) (u v : List Bool) (g : Gate)
    (hrel : EqRel n m p u v) :
    EqRel n m p
      (evalStep u ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)
      (evalStep v g) := by
  rcases hrel with ⟨hlen, hnm, hmap, hp⟩
  have hrel0 : EqRel n m p u v := ⟨hlen, hnm, hmap, hp⟩
  have hwire := eqRel_wire n m p hp_lt u v hrel0
  have hpv : (evalStep v g).getD p false = v.getD p false := evalStep_getD_lt v g p (by omega)
  have hnmv : (evalStep v g).getD (n + m) false = v.getD (n + m) false :=
    evalStep_getD_lt v g (n + m) (by omega)
  refine ⟨by rw [evalStep_length, evalStep_length, hlen], by rw [evalStep_length]; omega, ?_, ?_⟩
  · intro i hi
    rw [evalStep_length] at hi
    by_cases hiu : i < u.length
    · have hli : liftIdx n m i < v.length := by unfold liftIdx; split_ifs <;> omega
      rw [evalStep_getD_lt _ _ i hiu, evalStep_getD_lt _ _ (liftIdx n m i) hli]
      exact hmap i hiu
    · have hieq : i = u.length := by omega
      subst hieq
      have hli : liftIdx n m u.length = v.length := by
        unfold liftIdx
        split_ifs with hs <;> omega
      rw [hli, evalStep_getD_len, evalStep_getD_len]
      have hcongr : (List.map (eraseRedirect n m p) g.inputs).map (fun j => u.getD j false) =
          g.inputs.map (fun j => v.getD j false) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro j _
        exact hwire j
      rw [hcongr]
  · rw [hpv, hnmv]
    exact hp

lemma run_leRel (n m p : ℕ) (hp_lt : p < n + m) (gs : List Gate) (u v : List Bool)
    (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (hrel : LeRel n m p u v) :
    LeRel n m p
      (run (gs.map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)) u)
      (run gs v) := by
  induction gs generalizing u v with
  | nil => exact hrel
  | cons g gs ih =>
    simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
    exact ih _ _ (fun g' hg' => hAO g' (List.mem_cons_of_mem _ hg'))
      (evalStep_leRel n m p hp_lt u v g (hAO g List.mem_cons_self) hrel)

lemma run_eqRel (n m p : ℕ) (hp_lt : p < n + m) (gs : List Gate) (u v : List Bool) (hrel : EqRel n m p u v) :
    EqRel n m p
      (run (gs.map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)) u)
      (run gs v) := by
  induction gs generalizing u v with
  | nil => exact hrel
  | cons g gs ih =>
    simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
    exact ih _ _ (evalStep_eqRel n m p hp_lt u v g hrel)

lemma split_gates (gs : List Gate) (m : ℕ) (gm : Gate) (hm : m < gs.length)
    (hget : gs[m]? = some gm) :
    gs = gs.take m ++ gm :: gs.drop (m + 1) := by
  have hdrop : gs.drop m = gm :: gs.drop (m + 1) := by
    rw [List.drop_eq_getElem_cons hm]
    have hgm : gs[m] = gm := by simpa [hm] using hget
    rw [hgm]
  rw [← hdrop, List.take_append_drop]

lemma or_eval_pair (w : List Bool) (p h : ℕ) :
    GateOp.or.eval ([p, h].map fun i => w.getD i false) = (w.getD p false || w.getD h false) := by
  simp [GateOp.eval]

lemma gate_or_eval_pair (w : List Bool) (g : Gate) (p h : ℕ)
    (hg : g = ⟨GateOp.or, [p, h]⟩ ∨ g = ⟨GateOp.or, [h, p]⟩) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = (w.getD p false || w.getD h false) := by
  rcases hg with rfl | rfl
  · exact or_eval_pair w p h
  · rw [or_eval_pair w h p, Bool.or_comm]

lemma eraseGate_le (n : ℕ) (C : Circuit) (m p h : ℕ) (gm : Gate)
    (hAO : AndOrOnly C) (hm : m < C.gates.length) (hget : C.gates[m]? = some gm)
    (hgm : gm = ⟨GateOp.or, [p, h]⟩ ∨ gm = ⟨GateOp.or, [h, p]⟩) (hp : p < n + m)
    (x : Fin n → Bool) :
    LeRel n m p ((eraseGate n C m p).wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
  let xL := List.ofFn x
  have hxL : xL.length = n := List.length_ofFn
  let w0 := run (C.gates.take m) xL
  have hw0 : w0.length = n + m := by rw [← hxL]; exact run_take_length C.gates m hm xL
  have hsplit := split_gates C.gates m gm hm hget
  have hCw : C.wires xL = run (C.gates.drop (m + 1)) (evalStep w0 gm) := by
    change run C.gates xL = _
    conv_lhs => rw [hsplit]
    rw [run_append]
    rfl
  have hEw : (eraseGate n C m p).wires xL =
      run ((C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)) w0 := by
    change run (eraseGate n C m p).gates xL = _
    have hEg : (eraseGate n C m p).gates = C.gates.take m ++
        (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) := by
      simp [eraseGate, hm]
    rw [hEg, run_append]
  rw [hEw, hCw]
  apply run_leRel n m p hp (C.gates.drop (m + 1)) w0 (evalStep w0 gm)
    (fun g hg => hAO g (List.mem_of_mem_drop hg))
  refine ⟨by rw [evalStep_length], by omega, ?_, ?_⟩
  · intro i hi hui
    have hl : liftIdx n m i = i := by unfold liftIdx; split_ifs <;> omega
    rw [hl, evalStep_getD_lt w0 gm i hi]
    exact hui
  · intro hvp
    rw [evalStep_getD_lt w0 gm p (by omega)] at hvp
    rw [← hw0, evalStep_getD_len, gate_or_eval_pair w0 gm p h hgm, hvp]
    rfl

lemma eraseGate_eq_of_h_false (n : ℕ) (C : Circuit) (m p h : ℕ) (gm : Gate)
    (hm : m < C.gates.length) (hget : C.gates[m]? = some gm)
    (hgm : gm = ⟨GateOp.or, [p, h]⟩ ∨ gm = ⟨GateOp.or, [h, p]⟩) (hp : p < n + m) (hh : h < n + m)
    (x : Fin n → Bool) (hfalse : (C.wires (List.ofFn x)).getD h false = false) :
    EqRel n m p ((eraseGate n C m p).wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
  let xL := List.ofFn x
  have hxL : xL.length = n := List.length_ofFn
  let w0 := run (C.gates.take m) xL
  have hw0 : w0.length = n + m := by rw [← hxL]; exact run_take_length C.gates m hm xL
  have hsplit := split_gates C.gates m gm hm hget
  have hCw : C.wires xL = run (C.gates.drop (m + 1)) (evalStep w0 gm) := by
    change run C.gates xL = _
    conv_lhs => rw [hsplit]
    rw [run_append]
    rfl
  have hEw : (eraseGate n C m p).wires xL =
      run ((C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)) w0 := by
    change run (eraseGate n C m p).gates xL = _
    have hEg : (eraseGate n C m p).gates = C.gates.take m ++
        (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) := by
      simp [eraseGate, hm]
    rw [hEg, run_append]
  have hw0h : w0.getD h false = false := by
    have h1 : (evalStep w0 gm).getD h false = w0.getD h false := evalStep_getD_lt w0 gm h (by omega)
    have h2 : (C.wires xL).getD h false = (evalStep w0 gm).getD h false := by
      rw [hCw]
      exact run_getD_lt (C.gates.drop (m + 1)) (evalStep w0 gm) h (by rw [evalStep_length]; omega)
    rw [← h1, ← h2]
    exact hfalse
  rw [hEw, hCw]
  apply run_eqRel n m p hp (C.gates.drop (m + 1)) w0 (evalStep w0 gm)
  refine ⟨by rw [evalStep_length], by omega, ?_, ?_⟩
  · intro i hi
    have hl : liftIdx n m i = i := by unfold liftIdx; split_ifs <;> omega
    rw [hl, evalStep_getD_lt w0 gm i hi]
  · rw [evalStep_getD_lt w0 gm p (by omega), ← hw0, evalStep_getD_len,
      gate_or_eval_pair w0 gm p h hgm, hw0h, Bool.or_false]

lemma liftAt_eval (n : ℕ) (C : Circuit) (m p h : ℕ) (gm : Gate)
    (hm : m < C.gates.length) (hget : C.gates[m]? = some gm)
    (hgm : gm = ⟨GateOp.or, [p, h]⟩ ∨ gm = ⟨GateOp.or, [h, p]⟩)
    (hp : p < n + m) (hh : h < n + m) (hbelow : WireBelowOutput n C h)
    (x : Fin n → Bool) :
    (liftAt n C m p h).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let xL := List.ofFn x
  have hxL : xL.length = n := List.length_ofFn
  let E := eraseGate n C m p
  let C' := liftAt n C m p h
  have hEwLen : (E.wires xL).length = n + E.gates.length := by
    change (run E.gates xL).length = _
    rw [run_length, hxL]
  have hC'wires : C'.wires xL = evalStep (E.wires xL) ⟨GateOp.or, [E.output, h]⟩ := by
    change run (E.gates ++ [⟨GateOp.or, [E.output, h]⟩]) xL = _
    rw [run_append]
    rfl
  have hC'eval : C'.eval xL = ((E.wires xL).getD E.output false || (E.wires xL).getD h false) := by
    change (C'.wires xL).getD C'.output false = _
    have hCout : C'.output = (E.wires xL).length := by rw [hEwLen]; rfl
    rw [hC'wires, hCout, evalStep_getD_len, or_eval_pair]
  have hhlt : h < (E.wires xL).length := by
    rw [hEwLen, eraseGate_length n C m p hm]
    omega
  have hhagree : (E.wires xL).getD h false = (C.wires xL).getD h false := by
    let w0 := run (C.gates.take m) xL
    have hw0 : w0.length = n + m := by rw [← hxL]; exact run_take_length C.gates m hm xL
    have hsplit := split_gates C.gates m gm hm hget
    have hCw : C.wires xL = run (C.gates.drop (m + 1)) (evalStep w0 gm) := by
      change run C.gates xL = _
      conv_lhs => rw [hsplit]
      rw [run_append]
      rfl
    have hEw : E.wires xL =
        run ((C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)) w0 := by
      change run E.gates xL = _
      have hEg : E.gates = C.gates.take m ++
          (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) := by
        simp [E, eraseGate, hm]
      rw [hEg, run_append]
    rw [hEw, hCw]
    have h1 := run_getD_lt ((C.gates.drop (m + 1)).map
      (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)) w0 h (by omega)
    have h2 := run_getD_lt (C.gates.drop (m + 1)) (evalStep w0 gm) h (by rw [evalStep_length]; omega)
    rw [h1, h2, evalStep_getD_lt w0 gm h (by omega)]
  rw [hC'eval, hhagree]
  cases hhv : (C.wires xL).getD h false with
  | true =>
    rw [Bool.or_true]
    exact (hbelow x hhv).symm
  | false =>
    rw [Bool.or_false]
    have hrel := eraseGate_eq_of_h_false n C m p h gm hm hget hgm hp hh x hhv
    have hEeq : E.output = eraseRedirect n m p C.output := by simp [E, eraseGate, hm]
    change (E.wires xL).getD E.output false = (C.wires xL).getD C.output false
    rw [hEeq]
    exact eqRel_wire n m p hp (E.wires xL) (C.wires xL) hrel C.output

def belowSet (n : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k => WireBelowOutput n C (n + k))

lemma liftAt_belowSet_card (n : ℕ) (C : Circuit) (m p h : ℕ) (gm : Gate)
    (hAO : AndOrOnly C) (hm : m < C.gates.length) (hget : C.gates[m]? = some gm)
    (hgm : gm = ⟨GateOp.or, [p, h]⟩ ∨ gm = ⟨GateOp.or, [h, p]⟩) (hp : p < n + m)
    (hnbelow : ¬ WireBelowOutput n C p)
    (heval : ∀ x : Fin n → Bool, (liftAt n C m p h).eval (List.ofFn x) = C.eval (List.ofFn x)) :
    (belowSet n C).card + 1 ≤ (belowSet n (liftAt n C m p h)).card := by
  classical
  let E := eraseGate n C m p
  let C' := liftAt n C m p h
  let L := C.gates.length - 1
  have hEL : E.gates.length = L := eraseGate_length n C m p hm
  have hC'gates : C'.gates = E.gates ++ [⟨GateOp.or, [E.output, h]⟩] := rfl
  have hC'L : C'.gates.length = L + 1 := by rw [hC'gates, List.length_append, hEL]; simp
  have hmNotMem : m ∉ belowSet n C := by
    intro hmMem
    have hmb : WireBelowOutput n C (n + m) := (Finset.mem_filter.mp hmMem).2
    have hx : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false = true ∧
        C.eval (List.ofFn x) = false := by
      apply Classical.byContradiction
      intro hno
      apply hnbelow
      intro x hx
      cases hc : C.eval (List.ofFn x) with
      | true => rfl
      | false => exact False.elim (hno ⟨x, hx, hc⟩)
    rcases hx with ⟨x, hxp, hxc⟩
    let xL := List.ofFn x
    have hxL : xL.length = n := List.length_ofFn
    let w0 := run (C.gates.take m) xL
    have hw0 : w0.length = n + m := by rw [← hxL]; exact run_take_length C.gates m hm xL
    have hsplit := split_gates C.gates m gm hm hget
    have hCw : C.wires xL = run (C.gates.drop (m + 1)) (evalStep w0 gm) := by
      change run C.gates xL = _
      conv_lhs => rw [hsplit]
      rw [run_append]
      rfl
    have hw0p : w0.getD p false = true := by
      have h1 : (C.wires xL).getD p false = (evalStep w0 gm).getD p false := by
        rw [hCw]
        exact run_getD_lt (C.gates.drop (m + 1)) (evalStep w0 gm) p (by rw [evalStep_length]; omega)
      rw [evalStep_getD_lt w0 gm p (by omega)] at h1
      rw [← h1]
      exact hxp
    have hnmTrue : (C.wires xL).getD (n + m) false = true := by
      rw [hCw, run_getD_lt (C.gates.drop (m + 1)) (evalStep w0 gm) (n + m) (by rw [evalStep_length]; omega),
        ← hw0, evalStep_getD_len, gate_or_eval_pair w0 gm p h hgm, hw0p]
      rfl
    have hct := hmb x hnmTrue
    rw [hct] at hxc
    cases hxc
  let shiftDown : ℕ → ℕ := fun k => if k < m then k else k - 1
  have hInj : Set.InjOn shiftDown (belowSet n C : Set ℕ) := by
    intro k1 hk1 k2 hk2 heq
    have h1ne : k1 ≠ m := fun he => hmNotMem (he ▸ hk1)
    have h2ne : k2 ≠ m := fun he => hmNotMem (he ▸ hk2)
    dsimp [shiftDown] at heq
    split_ifs at heq <;> omega
  have hImgLt : ∀ k ∈ (belowSet n C).image shiftDown, k < L := by
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨k, hk, rfl⟩
    have hkne : k ≠ m := fun he => hmNotMem (he ▸ hk)
    have hklt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    dsimp [shiftDown]
    split_ifs <;> omega
  have hLNotMem : L ∉ (belowSet n C).image shiftDown := fun hL => (hImgLt L hL).ne rfl
  have hImgSub : (belowSet n C).image shiftDown ⊆ belowSet n C' := by
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨k, hk, rfl⟩
    have hkne : k ≠ m := fun he => hmNotMem (he ▸ hk)
    have hklt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hkBelow : WireBelowOutput n C (n + k) := (Finset.mem_filter.mp hk).2
    have hylt : shiftDown k < L := by dsimp [shiftDown]; split_ifs <;> omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    intro x hxy
    let xL := List.ofFn x
    have hxL : xL.length = n := List.length_ofFn
    have hEwLen : (E.wires xL).length = n + L := by
      change (run E.gates xL).length = _
      rw [run_length, hxL, hEL]
    have hC'wires : C'.wires xL = evalStep (E.wires xL) ⟨GateOp.or, [E.output, h]⟩ := by
      change run (E.gates ++ [⟨GateOp.or, [E.output, h]⟩]) xL = _
      rw [run_append]
      rfl
    have hEy : (E.wires xL).getD (n + shiftDown k) false = true := by
      have hagree : (C'.wires xL).getD (n + shiftDown k) false = (E.wires xL).getD (n + shiftDown k) false := by
        rw [hC'wires]
        exact evalStep_getD_lt (E.wires xL) _ (n + shiftDown k) (by omega)
      rw [← hagree]
      exact hxy
    have hle := eraseGate_le n C m p h gm hAO hm hget hgm hp x
    have hlift : liftIdx n m (n + shiftDown k) = n + k := by
      unfold liftIdx
      dsimp [shiftDown]
      split_ifs <;> omega
    have hCy : (C.wires xL).getD (n + k) false = true := by
      have hmap := hle.2.2.1 (n + shiftDown k) (by rw [hEwLen]; omega) hEy
      rwa [hlift] at hmap
    rw [heval x]
    exact hkBelow x hCy
  have hLMem : L ∈ belowSet n C' := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    intro x hx
    have hC'out : C'.output = n + L := by change n + E.gates.length = n + L; rw [hEL]
    change (C'.wires (List.ofFn x)).getD C'.output false = true
    rw [hC'out]
    exact hx
  have hsub : insert L ((belowSet n C).image shiftDown) ⊆ belowSet n C' := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy0
    · exact hLMem
    · exact hImgSub hy0
  calc
    (belowSet n C).card + 1 = ((belowSet n C).image shiftDown).card + 1 := by
      rw [Finset.card_image_of_injOn hInj]
    _ = (insert L ((belowSet n C).image shiftDown)).card := by
      rw [Finset.card_insert_of_notMem hLNotMem]
    _ ≤ (belowSet n C').card := Finset.card_le_card hsub

lemma liftAt_length (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (liftAt n C m p h).gates.length = C.gates.length := by
  have hEL := eraseGate_length n C m p hm
  dsimp [liftAt]
  rw [List.length_append, List.length_singleton, hEL]
  omega

lemma wireBelowOutput_of_or_gate (n : ℕ) (C : Circuit) (j u v : ℕ)
    (hAO : IsAO2 n C) (hj : j < C.gates.length) (hget : C.gates[j]? = some ⟨GateOp.or, [u, v]⟩)
    (hbelow : WireBelowOutput n C (n + j)) :
    WireBelowOutput n C u ∧ WireBelowOutput n C v := by
  have hga : gateAt C j = ⟨GateOp.or, [u, v]⟩ := by
    simp [gateAt, List.getD_eq_getElem?_getD, hget]
  have hu_lt : u < n + j := hAO.2.1 j hj u (by rw [hga]; simp)
  have hv_lt : v < n + j := hAO.2.1 j hj v (by rw [hga]; simp)
  have hstep : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false =
        ((C.wires (List.ofFn x)).getD u false || (C.wires (List.ofFn x)).getD v false) := by
    intro x
    let xL := List.ofFn x
    have hxL : xL.length = n := List.length_ofFn
    let w0 := run (C.gates.take j) xL
    have hw0 : w0.length = n + j := by rw [← hxL]; exact run_take_length C.gates j hj xL
    have hsplit := split_gates C.gates j ⟨GateOp.or, [u, v]⟩ hj hget
    have hCw : C.wires xL = run (C.gates.drop (j + 1)) (evalStep w0 ⟨GateOp.or, [u, v]⟩) := by
      change run C.gates xL = _
      conv_lhs => rw [hsplit]
      rw [run_append]
      rfl
    have hgm : (C.wires xL).getD (n + j) false =
        (w0.getD u false || w0.getD v false) := by
      rw [hCw, run_getD_lt (C.gates.drop (j + 1)) (evalStep w0 _) (n + j)
        (by rw [evalStep_length]; omega)]
      rw [← hw0, evalStep_getD_len, or_eval_pair]
    have hu : (C.wires xL).getD u false = w0.getD u false := by
      rw [hCw, run_getD_lt (C.gates.drop (j + 1)) (evalStep w0 _) u (by rw [evalStep_length]; omega),
        evalStep_getD_lt w0 _ u (by omega)]
    have hv : (C.wires xL).getD v false = w0.getD v false := by
      rw [hCw, run_getD_lt (C.gates.drop (j + 1)) (evalStep w0 _) v (by rw [evalStep_length]; omega),
        evalStep_getD_lt w0 _ v (by omega)]
    change (C.wires xL).getD (n + j) false =
      ((C.wires xL).getD u false || (C.wires xL).getD v false)
    rw [hgm, hu, hv]
  refine ⟨?_, ?_⟩
  · intro x hx
    apply hbelow x
    rw [hstep x, hx]
    rfl
  · intro x hx
    apply hbelow x
    rw [hstep x, hx, Bool.or_true]

lemma lift_step (n : ℕ) (C : Circuit) (m p h : ℕ) (gm : Gate)
    (hAO : IsAO2 n C) (hOut : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hget : C.gates[m]? = some gm)
    (hgm : gm = ⟨GateOp.or, [p, h]⟩ ∨ gm = ⟨GateOp.or, [h, p]⟩)
    (hnh : n ≤ h) (hbelow : WireBelowOutput n C h) (hnbelow : ¬ WireBelowOutput n C p) :
    ∃ C' : Circuit, Lift n C C' ∧ IsAO2 n C' ∧ C'.output < n + C'.gates.length ∧
      C'.gates.length - (belowSet n C').card < C.gates.length - (belowSet n C).card := by
  have hga : gateAt C m = gm := by simp [gateAt, List.getD_eq_getElem?_getD, hget]
  have hp : p < n + m := by
    apply hAO.2.1 m hm p
    rw [hga]
    rcases hgm with rfl | rfl <;> simp
  have hh : h < n + m := by
    apply hAO.2.1 m hm h
    rw [hga]
    rcases hgm with rfl | rfl <;> simp
  have hgate_or : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩ := by
    rcases hgm with rfl | rfl
    · exact Or.inl hget
    · exact Or.inr hget
  let C' := liftAt n C m p h
  have hLift : Lift n C C' := ⟨m, hm, p, hp, h, hh, hnh, hgate_or, hbelow, rfl⟩
  obtain ⟨hAO', hOut'⟩ := liftAt_isAO2 n C m p h hAO hm hp hh hOut
  have heval := liftAt_eval n C m p h gm hm hget hgm hp hh hbelow
  have hcard1 : (belowSet n C).card + 1 ≤ (belowSet n C').card :=
    liftAt_belowSet_card n C m p h gm hAO.1 hm hget hgm hp hnbelow heval
  have hlen' : C'.gates.length = C.gates.length := liftAt_length n C m p h hm
  have hle' : (belowSet n C').card ≤ C'.gates.length := by
    calc
      (belowSet n C').card ≤ (Finset.range C'.gates.length).card := Finset.card_filter_le _ _
      _ = C'.gates.length := Finset.card_range _
  exact ⟨C', hLift, hAO', hOut', by omega⟩

lemma normalize (k n : ℕ) (C : Circuit)
    (hAO : IsAO2 n C) (hOut : C.output < n + C.gates.length)
    (hk : C.gates.length - (belowSet n C).card ≤ k) :
    ∃ C' : Circuit, Relation.ReflTransGen (Lift n) C C' ∧
      ∀ j < C'.gates.length, ∀ u v : ℕ,
        C'.gates[j]? = some ⟨GateOp.or, [u, v]⟩ →
        (n ≤ v → WireBelowOutput n C' v → WireBelowOutput n C' u) ∧
        (n ≤ u → WireBelowOutput n C' u → WireBelowOutput n C' v) := by
  classical
  induction k generalizing C with
  | zero =>
    have hcard : (belowSet n C).card = C.gates.length := by
      have hle : (belowSet n C).card ≤ C.gates.length := by
        calc
          (belowSet n C).card ≤ (Finset.range C.gates.length).card := Finset.card_filter_le _ _
          _ = C.gates.length := Finset.card_range _
      omega
    have hall : ∀ j < C.gates.length, WireBelowOutput n C (n + j) := by
      intro j hj
      have heq : belowSet n C = Finset.range C.gates.length :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hcard, Finset.card_range])
      have hjmem : j ∈ belowSet n C := by rw [heq]; exact Finset.mem_range.mpr hj
      exact (Finset.mem_filter.mp hjmem).2
    refine ⟨C, Relation.ReflTransGen.refl, ?_⟩
    intro j hj u v hget
    obtain ⟨hu, hv⟩ := wireBelowOutput_of_or_gate n C j u v hAO hj hget (hall j hj)
    exact ⟨fun _ _ => hu, fun _ _ => hv⟩
  | succ k ih =>
    by_cases hdone : ∀ j < C.gates.length, ∀ u v : ℕ,
        C.gates[j]? = some ⟨GateOp.or, [u, v]⟩ →
        (n ≤ v → WireBelowOutput n C v → WireBelowOutput n C u) ∧
        (n ≤ u → WireBelowOutput n C u → WireBelowOutput n C v)
    · exact ⟨C, Relation.ReflTransGen.refl, hdone⟩
    · have hex : ∃ m < C.gates.length, ∃ p h : ℕ, ∃ gm : Gate,
          C.gates[m]? = some gm ∧ (gm = ⟨GateOp.or, [p, h]⟩ ∨ gm = ⟨GateOp.or, [h, p]⟩) ∧
          n ≤ h ∧ WireBelowOutput n C h ∧ ¬ WireBelowOutput n C p := by
        apply Classical.byContradiction
        intro hno
        apply hdone
        intro j hj u v hget
        constructor
        · intro hnv hbv
          apply Classical.byContradiction
          intro hnbu
          exact hno ⟨j, hj, u, v, ⟨GateOp.or, [u, v]⟩, hget, Or.inl rfl, hnv, hbv, hnbu⟩
        · intro hnu hbu
          apply Classical.byContradiction
          intro hnbv
          exact hno ⟨j, hj, v, u, ⟨GateOp.or, [u, v]⟩, hget, Or.inr rfl, hnu, hbu, hnbv⟩
      rcases hex with ⟨m, hm, p, h, gm, hget, hgm, hnh, hbelow, hnbelow⟩
      obtain ⟨C', hLift, hAO', hOut', hdrop⟩ :=
        lift_step n C m p h gm hAO hOut hm hget hgm hnh hbelow hnbelow
      obtain ⟨C'', hSteps, hRes⟩ := ih C' hAO' hOut' (by omega)
      exact ⟨C'', Relation.ReflTransGen.head hLift hSteps, hRes⟩

end PEqualNP.Outside.L_meta_4295

theorem PEqualNP.Outside.L_meta_4295 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift x1) x2 x5 ∧ ∀ x6 < x5.gates.length, ∀ (x8 x9 : ℕ), x5.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9) := by
  intro n C hAO hOut
  exact PEqualNP.Outside.L_meta_4295.normalize (C.gates.length - (PEqualNP.Outside.L_meta_4295.belowSet n C).card) n C hAO hOut (le_refl _)

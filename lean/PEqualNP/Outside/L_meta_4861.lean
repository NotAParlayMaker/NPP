import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4861

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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
  · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
  · simp only [hgt, ↓reduceIte]
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

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

def eraseC (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma erase_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (h : W n C x i = W n C x (n + j) ∨
      ∀ k, j < k → k < C.gates.length → n + j ∉ (gateAt C k).inputs) :
    ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
      W n (eraseC n C j i) x (aliasWire (n + j) i u) = W n C x u := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  have htake : C.gates.take j = pre := by rw [hgs, ← hpre_len]; simp
  have hdrop : C.gates.drop (j + 1) = post := by rw [hgs, ← hpre_len]; simp
  intro u hu
  simp only [W, eraseC, wires_eq_foldl, htake, hdrop]
  conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hCi : W n C x i = w0.getD i false := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
  have hCj : W n C x (n + j) = bOld := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
  have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
      ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
        vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
    intro vC vD hmv u hu'
    unfold aliasWire
    by_cases hu : u = n + j
    · have hval_eq : w0.getD i false = bOld := by rw [← hCi, ← hCj]; exact hu' hu
      subst hu
      simp only [↓reduceIte]
      rw [hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
    · simp only [hu, ↓reduceIte]
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate (n + j) i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 bOld post (post.map (aliasGate (n + j) i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    refine halias_get vC vD hmv u ?_
    intro hun
    rcases h with h | h
    · exact h
    · exfalso
      have hget : gateAt C (j + 1 + t) = post[t] := by
        rw [gateAt_eq C (j + 1 + t) (by omega)]
        have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; omega) = post[t]'htC := by
          rw [List.getElem_append_right (by omega)]
          have hsub : j + 1 + t - pre.length = t + 1 := by omega
          simp [hsub]
        simpa [hgs] using h1
      exact h (j + 1 + t) (by omega) (by omega) (by rw [hget, ← hun]; exact hu)
  exact halias_get _ _ hmEnd u hu

lemma erase_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (eraseC n C j i).gates.length + 1 = C.gates.length := by
  simp [eraseC]; omega


def effective (g : Gate) : List Nat :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

def trimGate (g : Gate) : Gate := ⟨g.op, effective g⟩

def trimCircuit (C : Circuit) : Circuit := ⟨C.gates.map trimGate, C.output⟩

lemma effective_eval (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (w : List Bool) :
    g.op.eval ((effective g).map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · simp [effective, GateOp.eval, List.take_of_length_le hl]
  · simp [effective, GateOp.eval, List.take_of_length_le hl]
  · cases ins <;> rfl

lemma trim_fan (C : Circuit) (hc : FanInTwo C) : FanInTwo (trimCircuit C) := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  refine ⟨(hc q hq).1, ?_⟩
  simp only [trimGate, effective, List.length_take]
  exact (Nat.min_le_right _ _).trans (hc q hq).2

lemma trim_fold (gs : List Gate)
    (hc : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) (w : List Bool) :
    (gs.map trimGate).foldl stepWire w = gs.foldl stepWire w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have he : stepWire w (trimGate g) = stepWire w g := by
      simp only [stepWire, trimGate]
      rw [effective_eval g (hc g List.mem_cons_self).1
        (hc g List.mem_cons_self).2 w]
    rw [he]
    exact ih (fun q hq => hc q (List.mem_cons_of_mem _ hq)) _

lemma trim_fun (n : Nat) (C : Circuit) (hc : FanInTwo C) :
    circuitFun n (trimCircuit C) = circuitFun n C := by
  funext x
  change ((C.gates.map trimGate).foldl stepWire (List.ofFn x)).getD C.output false = _
  rw [trim_fold C.gates hc]
  rfl

lemma trim_size (C : Circuit) : (trimCircuit C).size = C.size := by
  simp [trimCircuit, Circuit.size]

lemma minimal_trim (n : Nat) (C : Circuit) (hc : IsMinimalCircuit n C) :
    IsMinimalCircuit n (trimCircuit C) := by
  refine ⟨trim_fan C hc.1, ?_⟩
  intro D hd he
  rw [trim_size]
  exact hc.2 D hd (he.trans (trim_fun n C hc.1))

lemma erase_fan (n : Nat) (C : Circuit) (j i : Nat) (hc : FanInTwo C) :
    FanInTwo (eraseC n C j i) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hc g (List.mem_of_mem_take hg)
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    have hh := hc q (List.mem_of_mem_drop hq)
    exact ⟨hh.1, by simpa [aliasGate] using hh.2⟩

def takeCircuit (C : Circuit) (m : Nat) : Circuit := ⟨C.gates.take m, C.output⟩

lemma take_fan (C : Circuit) (hc : FanInTwo C) (m : Nat) :
    FanInTwo (takeCircuit C m) :=
  fun g hg => hc g (List.mem_of_mem_take hg)

lemma take_eval (n : Nat) (C : Circuit) (m : Nat) (hm : m ≤ C.gates.length)
    (ho : C.output < n + m) (x : Fin n → Bool) :
    (takeCircuit C m).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  change ((C.gates.take m).foldl stepWire (List.ofFn x)).getD C.output false = _
  have hw : C.wires (List.ofFn x) =
      (C.gates.drop m).foldl stepWire ((C.gates.take m).foldl stepWire (List.ofFn x)) := by
    conv_lhs =>
      rw [wires_eq_foldl, ← List.take_append_drop m C.gates, List.foldl_append]
  change _ = (C.wires (List.ofFn x)).getD C.output false
  rw [hw]
  symm
  apply foldl_stepWire_getD_lt
  rw [foldl_stepWire_length]
  simpa [List.length_take, Nat.min_eq_left hm] using ho

lemma minimal_output (n : Nat) (C : Circuit) (hc : IsMinimalCircuit n C)
    (hpos : 0 < C.size) : n ≤ C.output ∧ C.output + 1 = n + C.size := by
  have hlow : n ≤ C.output := by
    by_contra hn
    have ho : C.output < n := by omega
    let D : Circuit := ⟨[], C.output⟩
    have hd : FanInTwo D := by simp [FanInTwo, D]
    have he : circuitFun n D = circuitFun n C := by
      funext x
      exact (foldl_stepWire_getD_lt C.gates (List.ofFn x) C.output
        (by simpa using ho)).symm
    have hb := hc.2 D hd he
    change C.size ≤ 0 at hb
    omega
  have hhigh : C.output < n + C.size := by
    by_contra hn
    let D : Circuit := ⟨[], n⟩
    have hd : FanInTwo D := by simp [FanInTwo, D]
    have he : circuitFun n D = circuitFun n C := by
      funext x
      have hw : (C.wires (List.ofFn x)).length = n + C.size := wires_length n C x
      change (List.ofFn x).getD n false = (C.wires (List.ofFn x)).getD C.output false
      rw [getD_ge_length _ _ (by simp), getD_ge_length _ _ (by rw [hw]; omega)]
    have hb := hc.2 D hd he
    change C.size ≤ 0 at hb
    omega
  refine ⟨hlow, ?_⟩
  by_contra hn
  let m := C.output - n + 1
  have hm : m < C.gates.length := by change m < C.size; dsimp [m]; omega
  have he : circuitFun n (takeCircuit C m) = circuitFun n C := by
    funext x
    exact take_eval n C m (by omega) (by dsimp [m]; omega) x
  have hb := hc.2 (takeCircuit C m) (take_fan C hc.1 m) he
  simp only [takeCircuit, Circuit.size, List.length_take, Nat.min_eq_left (Nat.le_of_lt hm)] at hb
  change C.size ≤ m at hb
  omega

lemma minimal_read (n : Nat) (C : Circuit) (hc : IsMinimalCircuit n C) (hn : 0 < n)
    (hout : C.output + 1 = n + C.size) (j : Nat) (hj : j + 1 < C.size) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra hno
  push Not at hno
  have he : circuitFun n (eraseC n C j 0) = circuitFun n C := by
    funext x
    exact erase_wires n C j 0 (by change j < C.size; omega) (by omega) x
      (Or.inr hno) C.output (by intro h; omega)
  have hb := hc.2 (eraseC n C j 0) (erase_fan n C j 0 hc.1) he
  have hl := erase_length n C j 0 (by change j < C.size; omega)
  change C.size ≤ (eraseC n C j 0).gates.length at hb
  change (eraseC n C j 0).gates.length + 1 = C.size at hl
  omega

def AgreeExcept (v : Nat) (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, i ≠ v → w.getD i false = z.getD i false

lemma append_agree (v : Nat) (w z : List Bool) (b : Bool)
    (h : AgreeExcept v w z) : AgreeExcept v (w ++ [b]) (z ++ [b]) := by
  obtain ⟨hl, ha⟩ := h
  refine ⟨by simp [hl], ?_⟩
  intro i hi
  by_cases hb : i < w.length
  · rw [List.getD_append _ _ _ _ hb, List.getD_append _ _ _ _ (by omega)]
    exact ha i hi
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hl]

lemma no_read_fold (v : Nat) (gs : List Gate) (w z : List Bool)
    (hn : ∀ g ∈ gs, v ∉ g.inputs) (ha : AgreeExcept v w z) :
    AgreeExcept v (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact ha
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih _ _ (fun q hq => hn q (List.mem_cons_of_mem _ hq))
    have he : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => z.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ha.2 i (fun h => hn g List.mem_cons_self (h ▸ hi))
    unfold stepWire
    rw [he]
    exact append_agree v w z _ ha

lemma update_agree {n : Nat} (x : Fin n → Bool) (v : Fin n) (b : Bool) :
    AgreeExcept v.val (List.ofFn (Function.update x v b)) (List.ofFn x) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hn : i < n
  · have hne : (⟨i, hn⟩ : Fin n) ≠ v := fun h => hi (congrArg Fin.val h)
    simp [hn, Function.update_of_ne hne]
  · rw [getD_ge_length _ _ (by simp; omega), getD_ge_length _ _ (by simp; omega)]

lemma graph_zero {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) : graphFun G A (fun _ => false) = false := by
  simp [graphFun]

lemma graph_singleton {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (v : Fin n) (hv : v ∈ A) :
    graphFun G A (Function.update (fun _ => false) v true) = true := by
  have he : ∃ a ∈ A, (Function.update (fun _ => false) v true) a = true :=
    ⟨v, hv, by simp⟩
  simp [graphFun, he]

lemma marked_reader_of_output_ne {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (he : circuitFun n C = graphFun G A)
    (v : Fin n) (hv : v ∈ A) (ho : C.output ≠ v.val) :
    ∃ g ∈ C.gates, v.val ∈ g.inputs := by
  by_contra hn
  have hn' : ∀ g ∈ C.gates, v.val ∉ g.inputs := by
    intro g hg hi
    exact hn ⟨g, hg, hi⟩
  let x : Fin n → Bool := fun _ => false
  let y := Function.update x v true
  have ha := no_read_fold v.val C.gates (List.ofFn y) (List.ofFn x) hn'
    (update_agree x v true)
  have hout : circuitFun n C y = circuitFun n C x := ha.2 C.output ho
  rw [he, graph_zero] at hout
  have hy : graphFun G A y = true := graph_singleton G A v hv
  rw [hy] at hout
  exact Bool.noConfusion hout

lemma marked_reader {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (hc : IsMinimalCircuit n C)
    (he : circuitFun n C = graphFun G A) (hpos : 0 < C.size)
    (v : Fin n) (hv : v ∈ A) : ∃ g ∈ C.gates, v.val ∈ g.inputs := by
  apply marked_reader_of_output_ne G A C he v hv
  have hl := (minimal_output n C hc hpos).1
  have := v.isLt
  omega

def rawSet (n : Nat) (g : Gate) : Finset Nat :=
  g.inputs.toFinset.filter fun i => i < n

def innerSet (n : Nat) (g : Gate) : Finset Nat :=
  g.inputs.toFinset \ rawSet n g

lemma partition_cards (n : Nat) (g : Gate) :
    (rawSet n g).card + (innerSet n g).card = g.inputs.toFinset.card := by
  have hs : rawSet n g ⊆ g.inputs.toFinset := Finset.filter_subset _ _
  have hl := Finset.card_le_card hs
  rw [innerSet, Finset.card_sdiff, Finset.inter_eq_left.mpr hs]
  omega

lemma raw_card (n : Nat) (g : Gate) :
    (rawSet n g).card = ∑ v : Fin n, if v.val ∈ g.inputs then 1 else 0 := by
  classical
  let V : Finset (Fin n) := Finset.univ.filter fun v => v.val ∈ g.inputs
  have he : rawSet n g = V.image Fin.val := by
    ext i
    simp only [rawSet, Finset.mem_filter, List.mem_toFinset, Finset.mem_image]
    constructor
    · rintro ⟨hg, hi⟩
      exact ⟨⟨i, hi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(Finset.mem_filter.mp hv).2, v.isLt⟩
  rw [he, Finset.card_image_of_injective _ Fin.val_injective]
  simp only [V, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma raw_readers (n : Nat) (gs : List Gate) :
    ∑ v : Fin n, (gs.filter fun g => g.inputs.contains v.val).length =
      (gs.map fun g => (rawSet n g).card).sum := by
  classical
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hl (v : Fin n) :
        ((g :: gs).filter fun q => q.inputs.contains v.val).length =
          (if v.val ∈ g.inputs then 1 else 0) +
            (gs.filter fun q => q.inputs.contains v.val).length := by
      by_cases hv : v.val ∈ g.inputs <;> simp [hv, Nat.add_comm]
    simp only [hl, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [ih, ← raw_card]

def innerUsed (n : Nat) (gs : List Gate) : Finset Nat :=
  gs.foldr (fun g s => innerSet n g ∪ s) ∅

lemma innerUsed_mem (n : Nat) (gs : List Gate) (i : Nat) :
    i ∈ innerUsed n gs ↔ ∃ g ∈ gs, i ∈ innerSet n g := by
  induction gs with
  | nil => simp [innerUsed]
  | cons g gs ih =>
    change i ∈ innerSet n g ∪ innerUsed n gs ↔ ∃ q ∈ g :: gs, i ∈ innerSet n q
    simp [ih]

lemma innerUsed_card (n : Nat) (gs : List Gate) :
    (innerUsed n gs).card ≤ (gs.map fun g => (innerSet n g).card).sum := by
  induction gs with
  | nil => simp [innerUsed]
  | cons g gs ih =>
    have hu := Finset.card_union_le (innerSet n g) (innerUsed n gs)
    change (innerSet n g ∪ innerUsed n gs).card ≤ _
    simp only [List.map_cons, List.sum_cons]
    omega

lemma marked_count_le {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (hc : IsMinimalCircuit n C)
    (he : circuitFun n C = graphFun G A) (hpos : 0 < C.size) :
    A.card + (∑ v ∈ Aᶜ, (C.gates.filter fun g => g.inputs.contains v.val).length) ≤
      ∑ v : Fin n, (C.gates.filter fun g => g.inputs.contains v.val).length := by
  classical
  have h : (∑ v ∈ A, 1) ≤
      ∑ v ∈ A, (C.gates.filter fun g => g.inputs.contains v.val).length := by
    apply Finset.sum_le_sum
    intro v hv
    obtain ⟨g, hg, hi⟩ := marked_reader G A C hc he hpos v hv
    have hm : g ∈ C.gates.filter (fun g => g.inputs.contains v.val) :=
      List.mem_filter.mpr ⟨hg, by simpa using hi⟩
    exact List.length_pos_of_mem hm
  have ha : A.card ≤ ∑ v ∈ A,
      (C.gates.filter fun g => g.inputs.contains v.val).length := by simpa using h
  have hs := Finset.sum_add_sum_compl A
    (fun v : Fin n => (C.gates.filter fun g => g.inputs.contains v.val).length)
  omega

lemma internal_coverage (n : Nat) (C : Circuit) (hc : IsMinimalCircuit n C)
    (hn : 0 < n) (hpos : 0 < C.size) :
    C.size - 1 ≤ (innerUsed n C.gates).card := by
  have hout := (minimal_output n C hc hpos).2
  have hs : (Finset.range (C.size - 1)).image (fun j => n + j) ⊆ innerUsed n C.gates := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hj' : j + 1 < C.size := by
      have := Finset.mem_range.mp hj
      omega
    obtain ⟨k, hjk, hk, hread⟩ := minimal_read n C hc hn hout j hj'
    have hg : gateAt C k ∈ C.gates := by
      rw [gateAt_eq C k hk]
      exact List.getElem_mem hk
    apply (innerUsed_mem n C.gates (n + j)).mpr
    refine ⟨gateAt C k, hg, ?_⟩
    simp [innerSet, rawSet, hread]
  have hb := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h),
    Finset.card_range] at hb
  exact hb

lemma trim_capacity (g : Gate) :
    (trimGate g).inputs.length + (if (trimGate g).op.eval [false] then 1 else 0) ≤ 2 := by
  simp only [trimGate, effective, List.length_take]
  by_cases h : g.op.eval [false] = true
  · simp [h]
  · have hf : g.op.eval [false] = false := by simpa using h
    simp [hf]

lemma list_capacity (n : Nat) (gs : List Gate)
    (hc : ∀ g ∈ gs, g.inputs.length + (if g.op.eval [false] then 1 else 0) ≤ 2) :
    (gs.map fun g => (rawSet n g).card).sum +
      (gs.map fun g => (innerSet n g).card).sum +
      (gs.filter fun g => g.op.eval [false]).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have ht := ih (fun q hq => hc q (List.mem_cons_of_mem _ hq))
    have hh := hc g List.mem_cons_self
    have hp := partition_cards n g
    have hl := List.toFinset_card_le g.inputs
    cases h : g.op.eval [false] <;>
      simp [h] at hh ⊢ <;> omega

lemma graph_no_inputs (G : SimpleGraph (Fin 0)) [DecidableRel G.Adj]
    (A : Finset (Fin 0)) : graphFun G A = (fun _ => false) := by
  funext x
  simp [graphFun]

lemma positive_inputs {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (hc : IsMinimalCircuit n C)
    (he : circuitFun n C = graphFun G A) (hpos : 0 < C.size) : 0 < n := by
  by_contra hn
  have hz : n = 0 := by omega
  subst n
  let D : Circuit := ⟨[], 0⟩
  have hd : FanInTwo D := by simp [D, FanInTwo]
  have hf : circuitFun 0 D = circuitFun 0 C := by
    rw [he, graph_no_inputs]
    funext x
    simp [circuitFun, Circuit.eval, Circuit.wires, D]
  have hb := hc.2 D hd hf
  change C.size ≤ 0 at hb
  omega

lemma zero_marked {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (he : circuitFun n C = graphFun G A)
    (hz : C.size = 0) : A.card ≤ 1 := by
  have hg : C.gates = [] := List.eq_nil_of_length_eq_zero hz
  have ho : ∀ v ∈ A, C.output = v.val := by
    intro v hv
    by_contra hn
    obtain ⟨g, hmem, _⟩ := marked_reader_of_output_ne G A C he v hv hn
    simp [hg] at hmem
  apply Finset.card_le_one.mpr
  intro u hu v hv
  exact Fin.ext ((ho u hu).symm.trans (ho v hv))

lemma trimmed_bound {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (hc : IsMinimalCircuit n C)
    (he : circuitFun n C = graphFun G A)
    (hcap : ∀ g ∈ C.gates, g.inputs.length + (if g.op.eval [false] then 1 else 0) ≤ 2) :
    A.card + (∑ v ∈ Aᶜ, (C.gates.filter fun g => g.inputs.contains v.val).length) +
      (C.gates.filter fun g => g.op.eval [false]).length ≤ C.size + 1 := by
  by_cases hz : C.size = 0
  · have ha := zero_marked G A C he hz
    have hg : C.gates = [] := List.eq_nil_of_length_eq_zero hz
    simpa [hg, hz] using ha
  · have hpos : 0 < C.size := by omega
    have hn := positive_inputs G A C hc he hpos
    have hmarked := marked_count_le G A C hc he hpos
    rw [raw_readers] at hmarked
    have hi := internal_coverage n C hc hn hpos
    have hic := innerUsed_card n C.gates
    have htotal := list_capacity n C.gates hcap
    change _ ≤ 2 * C.size at htotal
    omega

lemma original_bound {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (hc : IsMinimalCircuit n C)
    (he : circuitFun n C = graphFun G A) :
    A.card + (∑ v ∈ Aᶜ, (C.gates.filter fun g => (effective g).contains v.val).length) +
      (C.gates.filter fun g => g.op.eval [false]).length ≤ C.size + 1 := by
  have hm := minimal_trim n C hc
  have hf : circuitFun n (trimCircuit C) = graphFun G A :=
    (trim_fun n C hc.1).trans he
  have hcap : ∀ g ∈ (trimCircuit C).gates,
      g.inputs.length + (if g.op.eval [false] then 1 else 0) ≤ 2 := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    exact trim_capacity q
  have hb := trimmed_bound G A (trimCircuit C) hm hf hcap
  simpa only [trimCircuit, List.filter_map, List.length_map, Function.comp_def,
    trimGate, Circuit.size] using hb


end PEqualNP.Outside.L_meta_4861

theorem PEqualNP.Outside.L_meta_4861 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x8 → x5.size ≤ x8) → x4.card + ∑ x9 ∈ x4ᶜ, (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x10.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x10.inputs).contains ↑x9) x5.gates).length + (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => x9.op.eval [Bool.false]) x5.gates).length ≤ x5.size + (1 : ℕ) := by
  intro n G inst A C hfan heq hsize
  have hmin : PEqualNP.MetaComplexity.IsMinimalCircuit n C := by
    refine ⟨hfan, ?_⟩
    intro D hD hfun
    apply hsize D.size
    refine ⟨D, hD, le_rfl, ?_⟩
    intro x
    exact congrFun (hfun.trans heq) x
  exact PEqualNP.Outside.L_meta_4861.original_bound G A C hmin heq

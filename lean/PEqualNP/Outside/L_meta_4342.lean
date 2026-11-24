import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4342

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def rs (s : List (Option Bool)) (i : ℕ) : Option Bool := s.getD i (some false)

def absb (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

def reals (s : List (Option Bool)) (g : Gate) : List ℕ :=
  g.inputs.filter (fun i => rs s i = none)

def newStat (s : List (Option Bool)) (g : Gate) : Option Bool :=
  if g.inputs.any (fun i => rs s i = some (absb g)) then some (absb g)
  else if reals s g = [] then some (!absb g) else none

def newGate (s : List (Option Bool)) (g : Gate) : Gate :=
  if newStat s g = none then ⟨g.op, [(reals s g).headD 0, (reals s g).reverse.headD 0]⟩
  else ⟨GateOp.and, [0, 0]⟩

lemma gate_ok (s : List (Option Bool)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hl : g.inputs.length ≤ 2) (V W : ℕ → Bool)
    (h : ∀ i ∈ g.inputs, (rs s i = none → W i = V i) ∧ (∀ b, rs s i = some b → V i = b)) :
    (∀ b, newStat s g = some b → g.op.eval (g.inputs.map V) = b) ∧
    (newStat s g = none →
      (newGate s g).op.eval ((newGate s g).inputs.map W) = g.op.eval (g.inputs.map V)) := by
  obtain ⟨op, l⟩ := g
  simp only at hop hl h ⊢
  rcases l with _ | ⟨p, _ | ⟨q, _ | ⟨r, t⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [newStat, newGate, reals, absb, GateOp.eval]
  · have hp := h p (by simp)
    rcases hop with rfl | rfl <;>
    · cases hs : rs s p with
      | none =>
        have e := hp.1 hs
        simp [newStat, newGate, reals, absb, GateOp.eval, hs, e]
      | some b =>
        have e := hp.2 b hs
        cases b <;> simp [newStat, newGate, reals, absb, GateOp.eval, hs, e]
  · have hp := h p (by simp)
    have hq := h q (by simp)
    rcases hop with rfl | rfl <;>
    · cases hs : rs s p with
      | none =>
        have e := hp.1 hs
        cases ht : rs s q with
        | none =>
          have e2 := hq.1 ht
          simp [newStat, newGate, reals, absb, GateOp.eval, hs, e, ht, e2]
        | some c =>
          have e2 := hq.2 c ht
          cases c <;> simp [newStat, newGate, reals, absb, GateOp.eval, hs, e, ht, e2]
      | some b =>
        have e := hp.2 b hs
        cases ht : rs s q with
        | none =>
          have e2 := hq.1 ht
          cases b <;> simp [newStat, newGate, reals, absb, GateOp.eval, hs, e, ht, e2]
        | some c =>
          have e2 := hq.2 c ht
          cases b <;> cases c <;> simp [newStat, newGate, reals, absb, GateOp.eval, hs, e, ht, e2]
  · simp at hl


def stepS (s : List (Option Bool)) (g : Gate) : List (Option Bool) := s ++ [newStat s g]

def S (n : ℕ) (gs : List Gate) : List (Option Bool) := gs.foldl stepS (List.replicate n none)

lemma foldS_length (gs : List Gate) (w : List (Option Bool)) :
    (gs.foldl stepS w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepS]
    omega

lemma S_length (n : ℕ) (gs : List Gate) : (S n gs).length = n + gs.length := by
  simp [S, foldS_length]

lemma foldS_getD_lt (gs : List Gate) (w : List (Option Bool)) (i : ℕ) (hi : i < w.length) :
    rs (gs.foldl stepS w) i = rs w i := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepS w g).length := by simp [stepS]; omega
    rw [ih (stepS w g) hlt]
    simp [rs, stepS, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma rs_ge (s : List (Option Bool)) (i : ℕ) (hi : s.length ≤ i) : rs s i = some false := by
  simp [rs, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma rs_lt (s : List (Option Bool)) (i : ℕ) (hi : rs s i ≠ some false) : i < s.length := by
  by_contra h
  exact hi (rs_ge s i (by omega))

lemma S_prefix (n : ℕ) (gs : List Gate) (j i : ℕ) (hj : j ≤ gs.length) (hi : i < n + j) :
    rs (S n gs) i = rs (S n (gs.take j)) i := by
  unfold S
  conv_lhs => rw [← List.take_append_drop j gs]
  rw [List.foldl_append]
  apply foldS_getD_lt
  rw [foldS_length]; simp; omega

lemma S_gate (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    rs (S n gs) (n + j) = newStat (S n (gs.take j)) gs[j] := by
  rw [S_prefix n gs (j + 1) (n + j) hj (by omega)]
  have e : gs.take (j + 1) = gs.take j ++ [gs[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  have hl : (S n (gs.take j)).length = n + j := by
    rw [S_length]; simp; omega
  unfold S at hl ⊢
  rw [e, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, stepS]
  rw [← hl]
  simp [rs, List.getD_eq_getElem?_getD]

lemma S_input (n : ℕ) (gs : List Gate) (i : ℕ) (hi : i < n) : rs (S n gs) i = none := by
  unfold S
  rw [foldS_getD_lt _ _ _ (by simp; omega)]
  simp [rs, List.getD_eq_getElem?_getD, hi]

def Dg (n : ℕ) (C : Circuit) : List Gate :=
  List.ofFn (fun j : Fin C.gates.length => newGate (S n (C.gates.take j)) C.gates[j])

def D (n : ℕ) (C : Circuit) : Circuit :=
  ⟨Dg n C, if rs (S n C.gates) C.output = none then C.output else n + C.gates.length⟩

lemma D_len (n : ℕ) (C : Circuit) : (D n C).gates.length = C.gates.length := by
  simp [D, Dg]

lemma D_gateAt (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (D n C) j = newGate (S n (C.gates.take j)) C.gates[j] := by
  rw [gateAt_eq (by rw [D_len]; exact hj)]
  simp [D, Dg]

lemma inv (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x : List Bool) (hx : x.length = n) :
    ∀ w, w < n + C.gates.length →
      (rs (S n C.gates) w = none → val (D n C) x w = val C x w) ∧
      (∀ b, rs (S n C.gates) w = some b → val C x w = b) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  by_cases hwn : w < n
  · rw [S_input n _ w hwn, val_input hx hwn, val_input hx hwn]
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have hjD : j < (D n C).gates.length := by rw [D_len]; exact hj
    rw [S_gate n _ j hj, val_gate hx hj, val_gate hx hjD, D_gateAt n C j hj, gateAt_eq hj]
    have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
    obtain ⟨hop, hl⟩ := hM _ hmem
    have hop' : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
      simpa using hop
    have key := gate_ok (S n (C.gates.take j)) C.gates[j] hop' hl
      (fun i => if i < n + j then val C x i else false)
      (fun i => if i < n + j then val (D n C) x i else false) (by
        intro i _
        by_cases hi : i < n + j
        · rw [← S_prefix n C.gates j i hj.le hi]
          simp only [hi, ite_true]
          exact ih i hi (by omega)
        · have hl2 : (S n (C.gates.take j)).length ≤ i := by
            rw [S_length]; simp; omega
          rw [rs_ge _ _ hl2]
          simp [hi])
    exact ⟨fun h => key.2 h, key.1⟩


lemma headD_mem (l : List ℕ) (h : l ≠ []) : l.headD 0 ∈ l := by
  cases l <;> simp_all

lemma rev_headD_mem (l : List ℕ) (h : l ≠ []) : l.reverse.headD 0 ∈ l := by
  have := headD_mem l.reverse (by simpa using h)
  simpa using this

lemma main (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (h0 : circuitFun n C (fun _ => false) = false) :
    ∃ E : Circuit, IsAO2 n E ∧ E.size ≤ C.size ∧ circuitFun n E = circuitFun n C := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨⟨[], 0⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro g hg; simp at hg
    · intro j hj; simp at hj
    · intro g hg; simp at hg
    · simp [Circuit.size]
    · funext x
      have ex : x = fun _ => false := funext (fun i => Fin.elim0 i)
      subst ex
      rw [h0]
      simp [circuitFun, Circuit.eval, Circuit.wires]
  · refine ⟨D n C, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro g hg
      simp only [D, Dg, List.mem_ofFn] at hg
      obtain ⟨j, rfl⟩ := hg
      unfold newGate
      split_ifs
      · have hmem : C.gates[j.1] ∈ C.gates := List.getElem_mem j.2
        have := (hM _ hmem).1
        simpa using this
      · simp
    · intro j hj i hi
      rw [D_len] at hj
      rw [D_gateAt n C j hj] at hi
      unfold newGate at hi
      split_ifs at hi with hs
      · have hne : reals (S n (C.gates.take j)) C.gates[j] ≠ [] := by
          intro he
          unfold newStat at hs
          split_ifs at hs
        have hmem : i ∈ reals (S n (C.gates.take j)) C.gates[j] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact headD_mem _ hne
          · exact rev_headD_mem _ hne
        simp only [reals, List.mem_filter, decide_eq_true_eq] at hmem
        have := rs_lt _ _ (by rw [hmem.2]; simp)
        rw [S_length] at this
        simp at this
        omega
      · simp at hi; omega
    · intro g hg
      simp only [D, Dg, List.mem_ofFn] at hg
      obtain ⟨j, rfl⟩ := hg
      unfold newGate
      split_ifs <;> simp
    · simp [Circuit.size, D_len]
    · funext x
      have hx : (List.ofFn x).length = n := by simp
      have I := inv n C hM (List.ofFn x) hx
      show val (D n C) (List.ofFn x) (D n C).output = val C (List.ofFn x) C.output
      have hSl := S_length n C.gates
      cases hs : rs (S n C.gates) C.output with
      | none =>
        have ho : C.output < n + C.gates.length := by
          have := rs_lt _ _ (by rw [hs]; simp); omega
        have hD : (D n C).output = C.output := by simp [D, hs]
        rw [hD]
        exact (I _ ho).1 hs
      | some b =>
        have hD : (D n C).output = n + C.gates.length := by simp [D, hs]
        rw [hD, val_ge hx (by rw [D_len])]
        by_cases ho : C.output < n + C.gates.length
        · have e := (I _ ho).2 b hs
          cases b
          · exact e.symm
          · have I0 := inv n C hM (List.ofFn (fun _ : Fin n => false)) (by simp)
            have e0 := (I0 _ ho).2 true hs
            have : circuitFun n C (fun _ => false) = true := e0
            rw [h0] at this
            exact absurd this (by simp)
        · exact (val_ge hx (by omega)).symm

end PEqualNP.Outside.L_meta_4342

theorem PEqualNP.Outside.L_meta_4342 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x4 : Fin x1) => Bool.false) = Bool.false → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x5 ∧ x5.size ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  intro n C hM h0
  exact PEqualNP.Outside.L_meta_4342.main n C hM h0

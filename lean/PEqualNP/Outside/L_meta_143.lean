import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta143

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- A number for each operation. -/
def code : GateOp → ℕ
  | GateOp.and => 0
  | GateOp.or => 1
  | GateOp.not => 2
  | _ => 3

/-- The value of a gate of fan-in at most two, from its operation number, a flag for "reads
no wire", and the values of the (at most two) wires it reads. -/
def gval (o : ℕ) (m pa pb : Bool) : Bool :=
  match o with
  | 0 => m || (pa && pb)
  | 1 => !m && (pa || pb)
  | 2 => m || !pa
  | _ => false

theorem gate_form (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) :
    ∃ (m : Bool) (i j : ℕ), (g.op = GateOp.not → j = 0) ∧ ∀ v : ℕ → Bool,
      g.op.eval (g.inputs.map v) = gval (code g.op) m (v i) (v j) := by
  obtain ⟨op, inputs⟩ := g
  simp only at hop hlen
  rcases hop with h | h | h <;> subst h
  · match inputs, hlen with
    | [], _ => exact ⟨true, 0, 0, by simp, fun v => by simp [GateOp.eval, gval, code]⟩
    | [i], _ => exact ⟨false, i, i, by simp, fun v => by simp [GateOp.eval, gval, code]⟩
    | [i, j], _ => exact ⟨false, i, j, by simp, fun v => by simp [GateOp.eval, gval, code]⟩
    | _ :: _ :: _ :: _, h => simp at h
  · match inputs, hlen with
    | [], _ => exact ⟨true, 0, 0, by simp, fun v => by simp [GateOp.eval, gval, code]⟩
    | [i], _ => exact ⟨false, i, i, by simp, fun v => by simp [GateOp.eval, gval, code]⟩
    | [i, j], _ => exact ⟨false, i, j, by simp, fun v => by simp [GateOp.eval, gval, code]⟩
    | _ :: _ :: _ :: _, h => simp at h
  · match inputs, hlen with
    | [], _ => exact ⟨true, 0, 0, by simp, fun v => by simp [GateOp.eval, gval, code]⟩
    | [i], _ => exact ⟨false, i, 0, by simp, fun v => by simp [GateOp.eval, gval, code]⟩
    | [i, j], _ => exact ⟨false, i, 0, by simp, fun v => by simp [GateOp.eval, gval, code]⟩
    | _ :: _ :: _ :: _, h => simp at h

theorem code_lt (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) : code g.op < 3 := by
  rcases hop with h | h | h <;> rw [h] <;> simp [code]

theorem clamp (L : List Bool) (i : ℕ) : L.getD i false = L.getD (min i L.length) false := by
  by_cases h : i < L.length
  · rw [Nat.min_eq_left h.le]
  · have h' : L.length ≤ i := Nat.le_of_not_lt h
    rw [Nat.min_eq_right h', List.getD_eq_default _ _ h', List.getD_eq_default _ _ le_rfl]

/-- The function in question. -/
def tgt (x0 x1 x2 : Bool) : Bool := (x0 && x1) || (x1 && x2)

def out0 (e : ℕ) (x0 x1 x2 : Bool) : Bool := [x0, x1, x2].getD e false

def out1 (o1 : ℕ) (m1 : Bool) (a b e : ℕ) (x0 x1 x2 : Bool) : Bool :=
  let w3 := gval o1 m1 ([x0, x1, x2].getD a false) ([x0, x1, x2].getD b false)
  [x0, x1, x2, w3].getD e false

def out2 (o1 : ℕ) (m1 : Bool) (a b o2 : ℕ) (m2 : Bool) (c d e : ℕ) (x0 x1 x2 : Bool) : Bool :=
  let w3 := gval o1 m1 ([x0, x1, x2].getD a false) ([x0, x1, x2].getD b false)
  let w4 := gval o2 m2 ([x0, x1, x2, w3].getD c false) ([x0, x1, x2, w3].getD d false)
  [x0, x1, x2, w3, w4].getD e false

/-- All eight inputs. -/
def all8 (p : Bool → Bool → Bool → Bool) : Bool :=
  p false false false && p false false true && p false true false && p false true true &&
  p true false false && p true false true && p true true false && p true true true

theorem all8_of (p : Bool → Bool → Bool → Bool) (h : ∀ x0 x1 x2, p x0 x1 x2 = true) :
    all8 p = true := by
  simp [all8, h]

theorem key0 : ∀ e < 4, all8 (fun x0 x1 x2 => out0 e x0 x1 x2 == tgt x0 x1 x2) = false := by
  decide +kernel

theorem key1 : ∀ o1 < 3, ∀ m1 : Bool, ∀ a < 4, ∀ b < 4, ∀ e < 5,
    all8 (fun x0 x1 x2 => out1 o1 m1 a b e x0 x1 x2 == tgt x0 x1 x2) = false := by
  decide +kernel

def allN (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).all p

theorem allN_spec {n : ℕ} {p : ℕ → Bool} (h : allN n p = true) (k : ℕ) (hk : k < n) :
    p k = true := by
  simp only [allN, List.all_eq_true, List.mem_range] at h
  exact h k hk

def allB (p : Bool → Bool) : Bool := p false && p true

theorem allB_spec {p : Bool → Bool} (h : allB p = true) (b : Bool) : p b = true := by
  simp only [allB, Bool.and_eq_true] at h
  cases b
  · exact h.1
  · exact h.2

/-- The first gate is a NOT gate and the output is the second gate. -/
def chkA : Bool :=
  allB fun m1 => allN 4 fun a => allN 3 fun o2 => allB fun m2 => allN 5 fun c => allN 5 fun d =>
    !all8 (fun x0 x1 x2 => out2 2 m1 a 0 o2 m2 c d 4 x0 x1 x2 == tgt x0 x1 x2)

/-- The second gate is a NOT gate and is the output. -/
def chkB : Bool :=
  allN 3 fun o1 => allB fun m1 => allN 4 fun a => allN 4 fun b => allB fun m2 => allN 5 fun c =>
    !all8 (fun x0 x1 x2 => out2 o1 m1 a b 2 m2 c 0 4 x0 x1 x2 == tgt x0 x1 x2)

theorem chkA_true : chkA = true := by
  decide +kernel

theorem chkB_true : chkB = true := by
  decide +kernel

theorem keyA (m1 : Bool) (a : ℕ) (ha : a < 4) (o2 : ℕ) (h2 : o2 < 3) (m2 : Bool)
    (c : ℕ) (hc : c < 5) (d : ℕ) (hd : d < 5) :
    all8 (fun x0 x1 x2 => out2 2 m1 a 0 o2 m2 c d 4 x0 x1 x2 == tgt x0 x1 x2) = false := by
  have := allN_spec (allN_spec (allB_spec (allN_spec (allN_spec (allB_spec chkA_true m1)
    a ha) o2 h2) m2) c hc) d hd
  simpa using this

theorem keyB (o1 : ℕ) (h1 : o1 < 3) (m1 : Bool) (a : ℕ) (ha : a < 4) (b : ℕ) (hb : b < 4)
    (m2 : Bool) (c : ℕ) (hc : c < 5) :
    all8 (fun x0 x1 x2 => out2 o1 m1 a b 2 m2 c 0 4 x0 x1 x2 == tgt x0 x1 x2) = false := by
  have := allN_spec (allB_spec (allN_spec (allN_spec (allB_spec (allN_spec chkB_true o1 h1)
    m1) a ha) b hb) m2) c hc
  simpa using this

theorem drop_last (x0 x1 x2 w3 w4 : Bool) (e : ℕ) (he : e ≠ 4) :
    [x0, x1, x2, w3, w4].getD e false = [x0, x1, x2, w3].getD e false := by
  match e, he with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, h => exact absurd rfl h
  | n + 5, _ => simp

theorem ofFn3 (x : Fin 3 → Bool) : List.ofFn x = [x 0, x 1, x 2] := by
  simp [List.ofFn_succ]

theorem lt4 (i : ℕ) : min i 3 < 4 := by omega
theorem lt5 (i : ℕ) : min i 4 < 5 := by omega
theorem lt6 (i : ℕ) : min i 5 < 6 := by omega

/-- The circuit with two gates. -/
def D : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩], 4⟩

theorem D_fanin : FanInTwo D := by
  intro g hg
  simp [D] at hg
  rcases hg with h | h <;> subst h <;> simp

theorem D_fun : circuitFun 3 D = fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) := by
  funext x
  simp only [circuitFun, ofFn3, Circuit.eval, Circuit.wires, D, List.foldl_cons, List.foldl_nil]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> simp [GateOp.eval]

theorem main (C : Circuit) (hmin : IsMinimalCircuit 3 C)
    (hf : circuitFun 3 C = fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2)) :
    C.size = 2 ∧ ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  obtain ⟨hfan, hle⟩ := hmin
  have hsize : C.size ≤ 2 := by
    have := hle D D_fanin (by rw [D_fun, hf])
    simpa [D, Circuit.size] using this
  have hpt : ∀ x0 x1 x2 : Bool, C.eval [x0, x1, x2] = tgt x0 x1 x2 := by
    intro x0 x1 x2
    have := congrFun hf ![x0, x1, x2]
    simpa [circuitFun, ofFn3, tgt] using this
  have hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hfan g hg
    simpa using this
  obtain ⟨gates, out⟩ := C
  simp only [Circuit.size] at hsize ⊢
  simp only at hops
  match gates, hsize with
  | [], _ =>
    exfalso
    have hk := key0 (min out 3) (lt4 out)
    rw [all8_of] at hk
    · exact absurd hk (by simp)
    · intro x0 x1 x2
      have := hpt x0 x1 x2
      simp only [Circuit.eval, Circuit.wires, List.foldl_nil] at this
      rw [clamp] at this
      simpa [out0] using this
  | [g1], _ =>
    exfalso
    obtain ⟨hop1, hlen1⟩ := hops g1 (by simp)
    obtain ⟨m1, i1, j1, -, h1⟩ := gate_form g1 hop1 hlen1
    have hk := key1 (code g1.op) (code_lt g1 hop1) m1 (min i1 3) (lt4 i1) (min j1 3) (lt4 j1)
      (min out 4) (lt5 out)
    rw [all8_of] at hk
    · exact absurd hk (by simp)
    · intro x0 x1 x2
      have := hpt x0 x1 x2
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, h1] at this
      rw [clamp] at this
      rw [clamp [x0, x1, x2] i1, clamp [x0, x1, x2] j1] at this
      simpa [out1] using this
  | [g1, g2], _ =>
    obtain ⟨hop1, hlen1⟩ := hops g1 (by simp)
    obtain ⟨hop2, hlen2⟩ := hops g2 (by simp)
    obtain ⟨m1, i1, j1, hj1, h1⟩ := gate_form g1 hop1 hlen1
    obtain ⟨m2, i2, j2, hj2, h2⟩ := gate_form g2 hop2 hlen2
    by_cases hout : out = 4
    · subst hout
      have hw : ∀ x0 x1 x2 : Bool,
          out2 (code g1.op) m1 (min i1 3) (min j1 3) (code g2.op) m2 (min i2 4) (min j2 4) 4
            x0 x1 x2 = tgt x0 x1 x2 := by
        intro x0 x1 x2
        have := hpt x0 x1 x2
        simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, h1, h2] at this
        rw [clamp [x0, x1, x2] i1, clamp [x0, x1, x2] j1] at this
        rw [clamp _ i2, clamp _ j2] at this
        simpa [out2] using this
      refine ⟨rfl, ?_⟩
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h <;> subst h <;> intro hnot
      · have hc : code g.op = 2 := by rw [hnot]; rfl
        have hj := hj1 hnot
        subst hj
        rw [hc] at hw
        have hk := keyA m1 (min i1 3) (lt4 i1) (code g2.op) (code_lt g2 hop2) m2
          (min i2 4) (lt5 i2) (min j2 4) (lt5 j2)
        rw [all8_of] at hk
        · exact absurd hk (by simp)
        · intro x0 x1 x2
          have := hw x0 x1 x2
          simpa using this
      · have hc : code g.op = 2 := by rw [hnot]; rfl
        have hj := hj2 hnot
        subst hj
        rw [hc] at hw
        have hk := keyB (code g1.op) (code_lt g1 hop1) m1 (min i1 3) (lt4 i1) (min j1 3) (lt4 j1)
          m2 (min i2 4) (lt5 i2)
        rw [all8_of] at hk
        · exact absurd hk (by simp)
        · intro x0 x1 x2
          have := hw x0 x1 x2
          simpa using this
    · exfalso
      have hk := key1 (code g1.op) (code_lt g1 hop1) m1 (min i1 3) (lt4 i1) (min j1 3) (lt4 j1)
        (min out 4) (lt5 out)
      rw [all8_of] at hk
      · exact absurd hk (by simp)
      · intro x0 x1 x2
        have := hpt x0 x1 x2
        simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, h1] at this
        simp only [List.cons_append, List.nil_append] at this
        rw [drop_last _ _ _ _ _ _ hout] at this
        rw [clamp] at this
        rw [clamp [x0, x1, x2] i1, clamp [x0, x1, x2] j1] at this
        simpa [out1] using this
  | _ :: _ :: _ :: _, h => simp at h

end PEqualNP.Outside.Meta143

theorem PEqualNP.Outside.L_meta_143 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalCircuit 3 C → PEqualNP.MetaComplexity.circuitFun 3 C = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2)) → C.size = 2 ∧ ∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not :=
  PEqualNP.Outside.Meta143.main

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_143

open PEqualNP.CircuitLowerBounds

lemma getD3 {i : ℕ} (h : 3 ≤ i) (a b c : Bool) : [a, b, c].getD i false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma getD4 {i : ℕ} (h : 4 ≤ i) (a b c d : Bool) : [a, b, c, d].getD i false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma getD5 {i : ℕ} (h : 5 ≤ i) (a b c d e : Bool) :
    [a, b, c, d, e].getD i false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma ofFn3 (x : Fin 3 → Bool) : List.ofFn x = [x 0, x 1, x 2] := by simp [List.ofFn_succ]

lemma split3 (i : ℕ) : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i := by omega
lemma split4 (i : ℕ) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i := by omega

def D : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩], 4⟩

lemma D_fan : PEqualNP.MetaComplexity.FanInTwo D := by
  intro g hg
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

lemma D_eval : ∀ a b c : Bool, D.eval [a, b, c] = ((a && b) || (b && c)) := by decide

lemma one_gate (op : GateOp) (l : List ℕ) (o : ℕ) (fl : Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : l.length ≤ 2)
    (h : ∀ a b c : Bool, (Circuit.eval ⟨[⟨op, l⟩], o⟩ [a, b, c]) = (fl ^^ ((a && b) || (b && c)))) :
    False := by
  have h110 := h true true false
  have h011 := h false true true
  have h100 := h true false false
  have h010 := h false true false
  have h001 := h false false true
  have h000 := h false false false
  have h101 := h true false true
  have h111 := h true true true
  clear h
  simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.cons_append,
    List.nil_append] at h110 h011 h100 h010 h001 h000 h101 h111
  rcases split4 o with rfl | rfl | rfl | rfl | ho
  · cases fl <;> simp_all
  · cases fl <;> simp_all
  · cases fl <;> simp_all
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · rcases hop with rfl | rfl | rfl <;> cases fl <;> simp_all [GateOp.eval]
    · rcases split3 i with rfl | rfl | rfl | hi <;>
        rcases hop with rfl | rfl | rfl <;> cases fl <;> simp_all [GateOp.eval, getD3]
    · rcases split3 i with rfl | rfl | rfl | hi <;> rcases split3 j with rfl | rfl | rfl | hj <;>
        rcases hop with rfl | rfl | rfl <;> cases fl <;> simp_all [GateOp.eval, getD3]
    · simp at hl
  · cases fl <;> simp_all [getD4]

lemma wires2 (g1 g2 : Gate) (o : ℕ) (a b c : Bool) :
    Circuit.eval ⟨[g1, g2], o⟩ [a, b, c] =
      [a, b, c, g1.op.eval (g1.inputs.map fun i => [a, b, c].getD i false),
        g2.op.eval (g2.inputs.map fun i =>
          [a, b, c, g1.op.eval (g1.inputs.map fun i => [a, b, c].getD i false)].getD i false)].getD
        o false := by
  simp [Circuit.eval, Circuit.wires]

lemma wires1 (g1 : Gate) (o : ℕ) (a b c : Bool) :
    Circuit.eval ⟨[g1], o⟩ [a, b, c] =
      [a, b, c, g1.op.eval (g1.inputs.map fun i => [a, b, c].getD i false)].getD o false := by
  simp [Circuit.eval, Circuit.wires]

set_option maxHeartbeats 4000000 in
lemma not_bin (l1 l2 : List ℕ) (op2 : GateOp) (hop2' : op2 = GateOp.and ∨ op2 = GateOp.or)
    (hl2 : l2.length ≤ 2)
    (h : ∀ a b c : Bool, Circuit.eval ⟨[⟨GateOp.not, l1⟩, ⟨op2, l2⟩], 4⟩ [a, b, c] =
      ((a && b) || (b && c))) : False := by
  have h110 := h true true false
  have h011 := h false true true
  have h100 := h true false false
  have h010 := h false true false
  have h001 := h false false true
  have h000 := h false false false
  have h101 := h true false true
  have h111 := h true true true
  clear h
  rw [wires2] at h110 h011 h100 h010 h001 h000 h101 h111
  simp only [GateOp.eval, List.map_cons, List.map_nil] at h110 h011 h100 h010 h001 h000 h101 h111
  rcases l1 with _ | ⟨i, l1⟩
  · rcases l2 with _ | ⟨p, _ | ⟨q, _ | ⟨r, l2⟩⟩⟩
    · rcases hop2' with rfl | rfl <;> simp_all
    · rcases split4 p with rfl | rfl | rfl | rfl | hp <;>
        rcases hop2' with rfl | rfl <;> simp_all [getD4]
    · rcases split4 p with rfl | rfl | rfl | rfl | hp <;>
        rcases split4 q with rfl | rfl | rfl | rfl | hq <;>
        rcases hop2' with rfl | rfl <;> simp_all [getD4]
    · simp at hl2
  · rcases l2 with _ | ⟨p, _ | ⟨q, _ | ⟨r, l2⟩⟩⟩
    · rcases split3 i with rfl | rfl | rfl | hi <;>
        rcases hop2' with rfl | rfl <;> simp_all [getD3]
    · rcases split3 i with rfl | rfl | rfl | hi <;> rcases split4 p with rfl | rfl | rfl | rfl | hp <;>
        rcases hop2' with rfl | rfl <;> simp_all [getD3, getD4]
    · rcases split3 i with rfl | rfl | rfl | hi <;> rcases split4 p with rfl | rfl | rfl | rfl | hp <;>
        rcases split4 q with rfl | rfl | rfl | rfl | hq <;>
        rcases hop2' with rfl | rfl <;> simp_all [getD3, getD4]
    · simp at hl2

lemma two_gate (op1 op2 : GateOp) (l1 l2 : List ℕ) (o : ℕ)
    (hop1 : op1 = GateOp.and ∨ op1 = GateOp.or ∨ op1 = GateOp.not) (hl1 : l1.length ≤ 2)
    (hop2 : op2 = GateOp.and ∨ op2 = GateOp.or ∨ op2 = GateOp.not) (hl2 : l2.length ≤ 2)
    (hnot : op1 = GateOp.not ∨ op2 = GateOp.not)
    (h : ∀ a b c : Bool, Circuit.eval ⟨[⟨op1, l1⟩, ⟨op2, l2⟩], o⟩ [a, b, c] =
      ((a && b) || (b && c))) : False := by
  rcases split4 o with rfl | rfl | rfl | rfl | ho
  · exact one_gate op1 l1 0 false hop1 hl1 (fun a b c => by
      rw [wires1]; have := h a b c; rw [wires2] at this; simpa using this)
  · exact one_gate op1 l1 1 false hop1 hl1 (fun a b c => by
      rw [wires1]; have := h a b c; rw [wires2] at this; simpa using this)
  · exact one_gate op1 l1 2 false hop1 hl1 (fun a b c => by
      rw [wires1]; have := h a b c; rw [wires2] at this; simpa using this)
  · exact one_gate op1 l1 3 false hop1 hl1 (fun a b c => by
      rw [wires1]; have := h a b c; rw [wires2] at this; simpa using this)
  · rcases Nat.lt_or_ge o 5 with ho5 | ho5
    · have ho4 : o = 4 := by omega
      subst ho4
      by_cases h2 : op2 = GateOp.not
      · subst h2
        rcases l2 with _ | ⟨i, l2⟩
        · have := h false false false
          rw [wires2] at this; simp [GateOp.eval] at this
        · rcases split4 i with rfl | rfl | rfl | rfl | hi
          · have := h false false false; rw [wires2] at this; simp [GateOp.eval] at this
          · have := h false false false; rw [wires2] at this; simp [GateOp.eval] at this
          · have := h false false false; rw [wires2] at this; simp [GateOp.eval] at this
          · exact one_gate op1 l1 3 true hop1 hl1 (fun a b c => by
              rw [wires1]; have := h a b c; rw [wires2] at this
              simp [GateOp.eval] at this ⊢
              cases hv : (GateOp.eval op1 (List.map (fun i => [a, b, c].getD i false) l1)) <;>
                simp_all)
          · have := h false false false; rw [wires2] at this
            simp only [GateOp.eval, List.map_cons, List.headD_cons, getD4 hi] at this
            simp at this
      · have h1 : op1 = GateOp.not := by tauto
        subst h1
        exact not_bin l1 l2 op2 (by tauto) hl2 h
    · have := h true true false
      rw [wires2, getD5 ho5] at this
      simp at this

end PEqualNP.Outside.L_meta_143

theorem PEqualNP.Outside.L_meta_143 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalCircuit 3 C → PEqualNP.MetaComplexity.circuitFun 3 C = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2)) → C.size = 2 ∧ ∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
  intro C hmin hf
  obtain ⟨hfan, hle⟩ := hmin
  have hT : ∀ a b c : Bool, C.eval [a, b, c] = ((a && b) || (b && c)) := by
    intro a b c
    have := congrFun hf ![a, b, c]
    simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.Outside.L_meta_143.ofFn3] using this
  have hsz : C.size ≤ 2 := by
    apply hle PEqualNP.Outside.L_meta_143.D PEqualNP.Outside.L_meta_143.D_fan
    funext x
    simp only [PEqualNP.MetaComplexity.circuitFun]
    rw [PEqualNP.Outside.L_meta_143.ofFn3, PEqualNP.Outside.L_meta_143.D_eval, hT]
  obtain ⟨gs, o⟩ := C
  have hop : ∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
      ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    exact ⟨by simpa using h1, h2⟩
  rcases gs with _ | ⟨⟨op1, l1⟩, _ | ⟨⟨op2, l2⟩, _ | ⟨g3, gs⟩⟩⟩
  · exfalso
    have e : ∀ a b c : Bool, [a, b, c].getD o false = ((a && b) || (b && c)) := by
      intro a b c
      have := hT a b c
      simpa [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
        using this
    rcases PEqualNP.Outside.L_meta_143.split3 o with rfl | rfl | rfl | ho
    · have := e true false false; simp at this
    · have := e false true false; simp at this
    · have := e false false true; simp at this
    · have := e true true false
      rw [PEqualNP.Outside.L_meta_143.getD3 ho] at this
      simp at this
  · exfalso
    obtain ⟨h1, h2⟩ := hop ⟨op1, l1⟩ (by simp)
    exact PEqualNP.Outside.L_meta_143.one_gate op1 l1 o false h1 h2
      (fun a b c => by simpa using hT a b c)
  · refine ⟨rfl, ?_⟩
    intro g hg hgn
    obtain ⟨h1, h2⟩ := hop ⟨op1, l1⟩ (by simp)
    obtain ⟨h3, h4⟩ := hop ⟨op2, l2⟩ (by simp)
    have hn : op1 = PEqualNP.CircuitLowerBounds.GateOp.not ∨
        op2 = PEqualNP.CircuitLowerBounds.GateOp.not := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact Or.inl hgn
      · exact Or.inr hgn
    exact PEqualNP.Outside.L_meta_143.two_gate op1 op2 l1 l2 o h1 h2 h3 h4 hn hT
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hsz

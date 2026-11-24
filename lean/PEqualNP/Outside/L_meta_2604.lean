import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2604

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wf_append (pre post : List Gate) (w : List Bool) :
    wf (pre ++ post) w = wf post (wf pre w) := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_ext : ∀ (gs : List Gate) (w : List Bool), ∃ E : List Bool, wf gs w = w ++ E := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], (List.append_nil w).symm⟩
  | cons g gs ih =>
    intro w
    obtain ⟨E, hE⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: E, ?_⟩
    rw [wf_cons, hE, List.append_assoc]
    rfl

theorem getD_left (A L : List Bool) (a : ℕ) (ha : a < A.length) :
    (A ++ L).getD a false = A.getD a false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha]

theorem getD_last (W : List Bool) (v : Bool) : (W ++ [v]).getD W.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem or1 (a : Bool) : GateOp.or.eval [a] = a := by
  cases a <;> rfl

theorem or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem core (n : ℕ) (pre post : List Gate) (u t o : ℕ) (X : List Bool) (hX : X.length = n)
    (ht : t < n + pre.length)
    (himp : (wf (pre ++ Gate.mk GateOp.or [u, t] :: post) X).getD t false = true →
      (wf (pre ++ Gate.mk GateOp.or [u, t] :: post) X).getD o false = true) :
    (wf ((pre ++ Gate.mk GateOp.or [u] :: post) ++ [Gate.mk GateOp.or [o, t]]) X).getD
        (n + (pre ++ Gate.mk GateOp.or [u, t] :: post).length) false
      = (wf (pre ++ Gate.mk GateOp.or [u, t] :: post) X).getD o false := by
  have hA : (wf pre X).length = n + pre.length := by rw [wf_len, hX]
  obtain ⟨A, hAdef⟩ : ∃ A : List Bool, wf pre X = A := ⟨_, rfl⟩
  rw [hAdef] at hA
  have hold : wf (pre ++ Gate.mk GateOp.or [u, t] :: post) X
      = wf post (A ++ [A.getD u false || A.getD t false]) := by
    rw [wf_append, wf_cons, hAdef]
    show wf post (A ++ [GateOp.or.eval [A.getD u false, A.getD t false]]) = _
    rw [or2]
  have hnew : wf ((pre ++ Gate.mk GateOp.or [u] :: post) ++ [Gate.mk GateOp.or [o, t]]) X
      = wf post (A ++ [A.getD u false]) ++
        [(wf post (A ++ [A.getD u false])).getD o false ||
          (wf post (A ++ [A.getD u false])).getD t false] := by
    rw [wf_append, wf_append, wf_cons, hAdef]
    show wf [Gate.mk GateOp.or [o, t]] (wf post (A ++ [GateOp.or.eval [A.getD u false]])) = _
    rw [or1]
    show wf post (A ++ [A.getD u false]) ++
        [GateOp.or.eval [(wf post (A ++ [A.getD u false])).getD o false,
          (wf post (A ++ [A.getD u false])).getD t false]] = _
    rw [or2]
  have hlen : n + (pre ++ Gate.mk GateOp.or [u, t] :: post).length
      = (wf post (A ++ [A.getD u false])).length := by
    rw [wf_len]
    simp only [List.length_append, List.length_cons, List.length_nil, hA]
    omega
  have htA : ∀ v : Bool, (wf post (A ++ [v])).getD t false = A.getD t false := by
    intro v
    obtain ⟨E, hE⟩ := wf_ext post (A ++ [v])
    rw [hE, List.append_assoc]
    exact getD_left A _ t (by omega)
  rw [hold] at himp ⊢
  rw [hnew, hlen, getD_last, htA]
  rw [htA] at himp
  by_cases h : A.getD t false = true
  · rw [h] at himp ⊢
    rw [himp rfl]
    exact Bool.or_true _
  · have h2 : A.getD t false = false := Bool.eq_false_iff.mpr h
    rw [h2]
    simp only [Bool.or_false]

theorem main (n : ℕ) (C : Circuit) (j u t : ℕ) (hj : j < C.gates.length)
    (hg : C.gates[j]? = some (Gate.mk GateOp.or [u, t])) (ht : t < n + j)
    (himp : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      circuitFun n C x = true) :
    circuitFun n (Circuit.mk (C.gates.set j (Gate.mk GateOp.or [u]) ++
        [Gate.mk GateOp.or [C.output, t]]) (n + C.gates.length)) = circuitFun n C := by
  funext x
  obtain ⟨pre, post, hC, hpl⟩ : ∃ pre post : List Gate,
      C.gates = pre ++ Gate.mk GateOp.or [u, t] :: post ∧ pre.length = j := by
    refine ⟨C.gates.take j, C.gates.drop (j + 1), ?_, ?_⟩
    · have e : C.gates[j] = Gate.mk GateOp.or [u, t] := by
        rw [List.getElem?_eq_getElem hj] at hg
        exact Option.some.inj hg
      rw [← e, List.cons_getElem_drop_succ, List.take_append_drop]
    · rw [List.length_take]
      omega
  subst hpl
  have h2 : (wf C.gates (List.ofFn x)).getD t false = true →
      (wf C.gates (List.ofFn x)).getD C.output false = true := himp x
  have hset : C.gates.set pre.length (Gate.mk GateOp.or [u])
      = pre ++ Gate.mk GateOp.or [u] :: post := by
    rw [hC]
    simp
  show (wf (C.gates.set pre.length (Gate.mk GateOp.or [u]) ++
      [Gate.mk GateOp.or [C.output, t]]) (List.ofFn x)).getD (n + C.gates.length) false
    = (wf C.gates (List.ofFn x)).getD C.output false
  rw [hset, hC]
  rw [hC] at h2
  exact core n pre post u t C.output (List.ofFn x) List.length_ofFn ht h2

end PEqualNP.Outside.L_meta_2604

theorem PEqualNP.Outside.L_meta_2604 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ), PEqualNP.MetaComplexity.Monotone2 C → j < C.gates.length → C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } → t < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } = PEqualNP.MetaComplexity.circuitFun n C := by
  intro n C j u t _ hj hg ht himp
  exact PEqualNP.Outside.L_meta_2604.main n C j u t hj hg ht himp

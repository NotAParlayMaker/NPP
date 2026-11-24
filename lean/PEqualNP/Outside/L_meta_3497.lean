import PEqualNP.Defs
import Mathlib.Data.Finset.Union

namespace PEqualNP.Outside.L_meta_3497
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev CNF (n : ℕ) := Finset (Finset (Fin n))

def Satisfied {n : ℕ} (x : List Bool) (A : CNF n) : Prop :=
  ∀ a ∈ A, ∃ p ∈ a, x.getD p.val false = true

def disjoin {n : ℕ} (A B : CNF n) : CNF n :=
  A.biUnion fun a => B.image fun b => a ∪ b

lemma satisfied_conjoin {n : ℕ} (x : List Bool) (A B : CNF n) :
    Satisfied x (A ∪ B) ↔ Satisfied x A ∧ Satisfied x B := by
  simp [Satisfied, Finset.mem_union, or_imp, forall_and]

lemma satisfied_disjoin {n : ℕ} (x : List Bool) (A B : CNF n) :
    Satisfied x (disjoin A B) ↔ Satisfied x A ∨ Satisfied x B := by
  classical
  constructor
  · intro all
    by_cases yesA : Satisfied x A
    · exact Or.inl yesA
    · right
      intro b hb
      by_contra bmiss
      apply yesA
      intro a ha
      have kab : a ∪ b ∈ disjoin A B :=
        Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨b,hb,rfl⟩⟩
      obtain ⟨p, hp, on⟩ := all (a ∪ b) kab
      rcases Finset.mem_union.mp hp with left | right
      · exact ⟨p,left,on⟩
      · exact (bmiss ⟨p,right,on⟩).elim
  · intro any clause hClause
    change clause ∈ A.biUnion (fun a => B.image fun b => a ∪ b) at hClause
    obtain ⟨a,ha,hab⟩ := Finset.mem_biUnion.mp hClause
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hab
    rcases any with hA | hB
    · obtain ⟨p,hp,on⟩ := hA a ha
      exact ⟨p,Finset.mem_union_left _ hp,on⟩
    · obtain ⟨p,hp,on⟩ := hB b hb
      exact ⟨p,Finset.mem_union_right _ hp,on⟩

def pins (g : Gate) : ℕ × ℕ := (g.inputs.getD 0 0, g.inputs.getD 1 0)

def Sorted (n : ℕ) (C : Circuit) : Prop :=
  ∀ i (hi : i < C.size), let g := C.gates[i]'hi
    g.inputs = [(pins g).1, (pins g).2] ∧ (pins g).1 < (pins g).2 ∧ (pins g).2 < n + i

def clauses (n : ℕ) (C : Circuit) (order : Sorted n C) (j : ℕ) : CNF n :=
  if h : j < n then {{⟨j,h⟩}} else
  if hi : j-n < C.size then
    let g := C.gates[j-n]'hi
    have second : (pins g).2 < j := by
      have bound := (order (j-n) hi).2.2
      change (pins g).2 < n + (j-n) at bound
      omega
    have first : (pins g).1 < j := (order (j-n) hi).2.1.trans second
    let L := clauses n C order (pins g).1
    let R := clauses n C order (pins g).2
    if g.op.eval [false,true] = true then disjoin L R else L ∪ R
  else {∅}
termination_by j

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun j => acc.getD j false)]) x

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (x ++ [_])).length = _
    rw [ih]
    simp
    omega

lemma run_preserves (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    (run gs x).getD j false = x.getD j false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [_])).getD j false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hj]

lemma run_split (xs ys : List Gate) (x : List Bool) :
    run (xs ++ ys) x = run ys (run xs x) := by
  simp [run, List.foldl_append]

lemma gate_at (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < C.size)
    (a b : ℕ) (ha : a < x.length + i) (hb : b < x.length + i)
    (hInputs : C.gates[i].inputs = [a,b]) :
    (C.wires x).getD (x.length + i) false =
      C.gates[i].op.eval [(C.wires x).getD a false, (C.wires x).getD b false] := by
  change i < C.gates.length at hi
  let pre := run (C.gates.take i) x
  have hi' : i < C.gates.length := hi
  have cut : pre.length = x.length + i := by
    simp [pre, run_length, Nat.min_eq_left (Nat.le_of_lt hi')]
  have before (j : ℕ) (hj : j < x.length + i) :
      (C.wires x).getD j false = pre.getD j false := by
    change (run C.gates x).getD j false = _
    nth_rw 1 [← List.take_append_drop i C.gates]
    rw [run_split]
    apply run_preserves
    change j < pre.length
    omega
  have after (j : ℕ) (hj : j < x.length + i + 1) :
      (C.wires x).getD j false = (run (C.gates.take (i+1)) x).getD j false := by
    change (run C.gates x).getD j false = _
    nth_rw 1 [← List.take_append_drop (i+1) C.gates]
    rw [run_split, run_preserves]
    rw [run_length, List.length_take, Nat.min_eq_left (show i+1 ≤ C.gates.length by omega)]
    omega
  rw [before a ha, before b hb, after _ (by omega)]
  rw [List.take_succ_eq_append_getElem hi', run_split]
  change (pre ++ [C.gates[i].op.eval (C.gates[i].inputs.map fun j => pre.getD j false)]).getD
    (x.length + i) false = _
  rw [← cut, hInputs]
  simp

lemma clauseOnWire (n : ℕ) (C : Circuit) (hMono : Monotone2 C) (order : Sorted n C)
    (x : List Bool) (hx : x.length = n) (j : ℕ) :
    (C.wires x).getD j false = true ↔ Satisfied x (clauses n C order j) := by
  induction j using Nat.strong_induction_on with
  | ind j earlier =>
    rw [clauses]
    by_cases input : j < n
    · change (run C.gates x).getD j false = true ↔ _
      rw [run_preserves C.gates x j (by omega)]
      simp [input, Satisfied]
    · rw [dite_eq_right input]
      by_cases hi : j-n < C.size
      · rw [dite_eq_left hi]
        let i := j - n
        let g := C.gates[i]'hi
        obtain ⟨pinsEq, ab, bi⟩ := order i hi
        let a := (pins g).1
        let b := (pins g).2
        change a < b at ab
        change b < n + i at bi
        have bj : b < j := by omega
        have aj : a < j := ab.trans bj
        have ji : x.length + i = j := by omega
        have eq := gate_at C x i hi a b (by omega) (by omega) pinsEq
        rw [ji] at eq
        have ops := (hMono g (List.getElem_mem hi)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops
        change _ ↔ Satisfied x (if g.op.eval [false,true] = true then
          disjoin (clauses n C order a) (clauses n C order b) else
            clauses n C order a ∪ clauses n C order b)
        rcases ops with hAnd | hOr
        · rw [eq]
          change g.op.eval _ = _ ↔ _
          simp only [hAnd, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq,
            Bool.false_eq_true, ite_false, Bool.and_eq_true_iff, satisfied_conjoin,
            earlier a aj, earlier b bj]
        · rw [eq]
          change g.op.eval _ = _ ↔ _
          simp only [hOr, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq,
            Bool.false_or, ite_true, Bool.or_eq_true, satisfied_disjoin,
            earlier a aj, earlier b bj]
      · rw [dite_eq_right hi]
        have hout : (C.wires x).length ≤ j := by
          change (run C.gates x).length ≤ j
          rw [run_length, hx]
          change ¬ j-n < C.gates.length at hi
          omega
        rw [List.getD_eq_default _ _ hout]
        simp [Satisfied]

end PEqualNP.Outside.L_meta_3497

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3497 in
theorem PEqualNP.Outside.L_meta_3497 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x4]? = Option.some x5 → ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 < x8 ∧ x8 < x1 + x4) → ∃ (x5 : ℕ → Finset (Finset (Fin x1))), (∀ (x6 : Fin x1), x5 ↑x6 = {{x6}}) ∧ (∀ (x6 : ℕ) (x7 : x6 < x2.size), ∃ (x8 : ℕ) (x9 : ℕ), x2.gates[x6].inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x6 ∧ x5 (x1 + x6) = if x2.gates[x6].op.eval [Bool.false, Bool.true] = Bool.true then (x5 x8).biUnion fun (x10 : Finset (Fin x1)) => Finset.image (fun (x11 : Finset (Fin x1)) => x10 ∪ x11) (x5 x9) else x5 x8 ∪ x5 x9) ∧ ∀ (x6 : List Bool), x6.length = x1 → ∀ (x8 : ℕ), (x2.wires x6).getD x8 Bool.false = Bool.true ↔ ∀ x9 ∈ x5 x8, ∃ x11 ∈ x9, x6.getD (↑x11) Bool.false = Bool.true := by
  intro n C mono before
  have order : Sorted n C := by
    intro i hi
    obtain ⟨a,b,input,ab,bi⟩ := before i C.gates[i] (List.getElem?_eq_getElem hi)
    simp [pins, input, ab, bi]
  refine ⟨clauses n C order, ?_, ?_, fun x hx w => clauseOnWire n C mono order x hx w⟩
  · intro p
    rw [clauses, dite_eq_left p.isLt]
  · intro i hi
    let g := C.gates[i]'hi
    obtain ⟨pinsEq, ab, bi⟩ := order i hi
    refine ⟨(pins g).1, (pins g).2, pinsEq, ab, bi, ?_⟩
    rw [clauses, dite_eq_right (by omega : ¬ n+i < n)]
    have sub : n+i-n = i := by omega
    simp only [sub, dite_eq_left hi, disjoin]
    rfl

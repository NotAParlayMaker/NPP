import Mathlib.Data.List.Count
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The two forced output values give a lower and upper set of rows for the selector.
-- A prefix wire fitting the same constraints bypasses the inverter and saves a gate.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_3594_718
    (splitAtNot : ∀ (gs : List Gate), FanInTwo ⟨gs, 0⟩ →
      (∀ g ∈ gs, g.op = GateOp.not → ∃ i, g.inputs = [i]) →
      gs.countP (fun g => g.op.eval [false]) = 1 →
      ∃ (P S : List Gate) (i : Nat), gs = P ++ [⟨GateOp.not,[i]⟩] ++ S ∧
        Monotone2 ⟨P,0⟩ ∧ Monotone2 ⟨S,0⟩)
    (bypass : ∀ (P S : List Gate) (o j : ℕ), j < 9+P.length →
    FanInTwo ⟨P++S,0⟩ → ∃ D : Circuit, FanInTwo D ∧ D.size = P.length+S.length ∧
      ∀ x : Fin 9 → Bool, let w := (Circuit.mk P 0).wires (List.ofFn x)
        circuitFun 9 D x = (Circuit.mk S o).eval (w ++ [w.getD j false]))
    (uniformTail : ∀ (P S : List Gate), Monotone2 ⟨P,0⟩ → ∀
    (b : Bool), (∀ g ∈ S, g.op = (if b then GateOp.and else GateOp.or)) → ∀
    (i : ℕ) (o : ℕ) (T : (Fin 9 → Bool) → Bool),
    (∀ t : Bool, T (fun _ => t) = t) →
    (∀ x, let w := (Circuit.mk P 0).wires (List.ofFn x ++ [x 0 || x 3])
      (Circuit.mk S o).eval (w ++ [!(w.getD i false)]) = T x) →
    ∃ j < 10+P.length, ∀ x, let w := (Circuit.mk P 0).wires (List.ofFn x ++ [x 0 || x 3])
      (Circuit.mk S o).eval (w ++ [w.getD j false]) = T x)
    (exchange : ∀ (P S : List Gate), P.length + S.length = 13 →
      Monotone2 ⟨P,0⟩ → Monotone2 ⟨S,0⟩ →
      (∃ a ∈ S, a.op = GateOp.and) → (∃ a ∈ S, a.op = GateOp.or) →
      let w := fun x : Fin 9 → Bool => (Circuit.mk P 0).wires (List.ofFn x ++ [x 0 || x 3])
      let f := fun x t => (Circuit.mk S 23).eval (w x ++ [t])
      let target := fun x : Fin 9 → Bool => ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any
        (fun e => (List.finRange 9).all (fun i => !(e.testBit i) || x i))
      let fits := fun q : (Fin 9 → Bool) → Bool =>
        (∀ x, f x true ≠ target x → q x = false) ∧ (∀ x, f x false ≠ target x → q x = true)
      (∃ i ≤ 10+P.length, fits (fun x => !((w x).getD i false))) →
      ∃ j < 10+P.length, fits (fun x => (w x).getD j false)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (x1.gates.length = (15 : ℕ) ∧ x1.output = (23 : ℕ) ∧ x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length), (∃ x4 < (9 : ℕ) + x2, x1.gates[x2] = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x4] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x4 : ℕ) (x5 : ℕ), x4 < (9 : ℕ) + x2 ∧ x5 < (9 : ℕ) + x2 ∧ x4 < x5 ∧ (x1.gates[x2] = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.gates[x2] = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate })) → List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) := by
  classical
  have orVal (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have notVal (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have wireVal (C : Circuit) (v : List Bool) : C.wires v =
      C.gates.foldl (fun a g => a ++ [g.op.eval (g.inputs.map (fun i => a.getD i false))]) v := rfl
  have evalVal (C : Circuit) (v : List Bool) : C.eval v = (C.wires v).getD C.output false := rfl
  intro C shape count minimal eq
  obtain ⟨gs,o⟩ := C
  rcases shape with ⟨hl,ho,head,legal⟩
  cases gs with
  | nil => simp at hl
  | cons g tail =>
    change some g = some _ at head
    cases Option.some.inj head
    change o = 23 at ho
    subst o
    let first : Gate := ⟨GateOp.or, [0,3]⟩
    have fan : FanInTwo ⟨tail,0⟩ := fun a ha => minimal.1 a (List.mem_cons_of_mem _ ha)
    have norm : ∀ a ∈ tail, a.op = GateOp.not → ∃ i, a.inputs = [i] := by
      intro a ha hop
      obtain ⟨j,hj,he⟩ := List.getElem_of_mem ha
      have h := legal (j+1) (by simpa using hj)
      simp only [List.getElem_cons_succ] at h
      rcases h with ⟨i,_,h⟩ | ⟨i,k,_,_,_,h|h⟩
      · exact ⟨i, by rw [←he,h]⟩
      all_goals rw [←he,h] at hop; contradiction
    change (first :: tail).countP _ = 1 at count
    have cnt : tail.countP (fun a => a.op.eval [false]) = 1 := by
      simpa [first,List.countP_cons,orVal] using count
    obtain ⟨P,S,i,ht,hP,hS⟩ := splitAtNot tail fan norm cnt
    change (first :: tail).length = 15 at hl
    rw [ht] at hl
    simp only [List.length_cons,List.length_append,List.length_nil] at hl
    have hlen : P.length + S.length = 13 := by omega
    let w := fun x : Fin 9 → Bool => (Circuit.mk P 0).wires (List.ofFn x ++ [x 0 || x 3])
    let target := fun x : Fin 9 → Bool => ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any
        (fun e => (List.finRange 9).all (fun i => !(e.testBit i) || x i))
    have graph : ∀ x : Fin 9 → Bool, target x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by decide +kernel
    let f := fun x t => (Circuit.mk S 23).eval (w x ++ [t])
    have sem (x : Fin 9 → Bool) : f x (!((w x).getD i false)) = target x := by
      have e := congrFun eq x
      rw [graph]
      change (Circuit.mk (first :: tail) 23).eval (List.ofFn _) = _ at e
      rw [ht] at e
      simpa [f,evalVal,wireVal, List.foldl_append,first, orVal,notVal,w,List.getD] using e
    let k := min i (10 + P.length)
    have wlen (x : Fin 9 → Bool) : (w x).length = 10+P.length := by
      have aux (l : List Gate) (v : List Bool) : ((Circuit.mk l 0).wires v).length = v.length + l.length := by
        induction l generalizing v with
        | nil => rfl
        | cons g l ih =>
          change ((Circuit.mk l 0).wires (v ++ [_])).length = _
          rw [ih]
          simp [Nat.add_comm,Nat.add_left_comm]
      simp [w,aux]
    have clamp (x : Fin 9 → Bool) : (w x).getD k false = (w x).getD i false := by
      by_cases h : i ≤ 10+P.length
      · simp [k,min_eq_left h]
      · have hi : (w x).length ≤ i := by rw [wlen]; omega
        simp [k,min_eq_right (by omega : 10+P.length ≤ i),List.getD, List.getElem?_eq_none hi,
          List.getElem?_eq_none (wlen x).le]
    have found : ∃ j < 10+P.length, ∀ x, f x ((w x).getD j false) = target x := by
      by_cases both : (∃ a ∈ S, a.op = GateOp.and) ∧ (∃ a ∈ S, a.op = GateOp.or)
      ·
        have E := exchange P S hlen hP hS both.1 both.2
        obtain ⟨j,hj,passOne,passZero⟩ := E ⟨k,Nat.min_le_right ..,by
          constructor <;> intro x hx
          all_goals
            change (!((w x).getD k false)) = _
            rw [clamp]
            have t := sem x
            cases h : (w x).getD i false <;> rw [h] at t <;> first | rfl | exact (hx t).elim⟩
        have pass (x : Fin 9 → Bool) : f x ((w x).getD j false) = target x := by
          by_contra bad
          cases h : (w x).getD j false with
          | false =>
            rw [h] at bad
            exact Bool.noConfusion (h.symm.trans (passZero x bad))
          | true =>
            rw [h] at bad
            exact Bool.noConfusion (h.symm.trans (passOne x bad))
        exact ⟨j,hj,pass⟩
      · have uni : ∃ b : Bool, ∀ g ∈ S, g.op = (if b then GateOp.and else GateOp.or) := by
          by_cases ha : ∃ g ∈ S, g.op = GateOp.and
          · refine ⟨true,?_⟩
            intro g hg
            rcases (hS g hg).1 with h|h
            · exact h
            · exact (both ⟨ha,g,hg,h⟩).elim
          · refine ⟨false,?_⟩
            intro g hg
            rcases (hS g hg).1 with h|h
            · exact (ha ⟨g,hg,h⟩).elim
            · exact h
        obtain ⟨b,hb⟩ := uni
        exact uniformTail P S hP b hb i 23 target (by decide +kernel) sem
    obtain ⟨j,hj,pass⟩ := found
    have monoFan (l : List Gate) (hm : Monotone2 ⟨l,0⟩) : FanInTwo ⟨l,0⟩ := by
      intro g hg
      obtain ⟨op,len⟩ := hm g hg
      rcases op with h|h
      · exact ⟨Or.inl h,len⟩
      · exact ⟨Or.inr (Or.inl h),len⟩
    have ok : FanInTwo ⟨(first :: P) ++ S,0⟩ := by
      intro g mem
      rcases List.mem_append.mp mem with h|h
      · rcases List.mem_cons.mp h with rfl|h
        · exact ⟨Or.inr (Or.inl rfl),by decide⟩
        · exact monoFan _ hP _ h
      · exact monoFan _ hS _ h
    obtain ⟨D, adm, sz, hx⟩ := bypass (first :: P) S 23 j (by simpa [Nat.add_comm,Nat.add_left_comm] using hj) ok
    have same : circuitFun 9 D = circuitFun 9 ⟨first :: tail,23⟩ := by
      rw [eq]
      funext x
      rw [hx,←graph]
      simpa [f,w,first,wireVal,orVal,List.getD] using pass x
    have lb := minimal.2 D adm same
    change (first::tail).length ≤ D.size at lb
    rw [ht] at lb
    simp only [List.length_append,List.length_cons,List.length_nil] at sz lb
    omega

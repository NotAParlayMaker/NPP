import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- The automorphism (1 5)(2 8)(6 7) fixes vertex 0 and its negation. Encode a pair
   (a,b) as 11*a+b, with 9 for the negation and 10 for a missing operand.
   Reindexing reads absorbs every duplicate input and every OR with a missing
   operand, apart from the constant-false empty OR. The remaining pairs fall
   into the two finite lists below. -/
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3122_2
    (ordinaryBound : ∀ a b : Fin 11, 11 * a.val + b.val ∈ ([1, 2, 3, 4, 6, 13, 14, 15, 16, 17, 18, 19, 25, 26, 28, 29, 30, 37, 39, 50, 73, 120] : List ℕ) →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
        let u := List.ofFn x ++ [!x 0]
        C.eval (u ++ [u.getD a.val false || u.getD b.val false]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (complementedBound : ∀ a b : Fin 11, 11 * a.val + b.val ∈ ([9, 20, 31, 42, 53, 75] : List ℕ) →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
        let u := List.ofFn x ++ [!x 0]
        C.eval (u ++ [u.getD a.val false || u.getD b.val false]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
 :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro ops hlen C fan hs _
  classical
  by_contra! good
  -- Relabel the eleven input ports while retaining every gate output index.
  have reindex (f : Fin 11 → Fin 11) (C : Circuit) (hc : FanInTwo C) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ ∀ y : Fin 11 → Bool,
        D.eval (List.ofFn y) = C.eval (List.ofFn (fun j => y (f j))) := by
    let readWire (j : ℕ) := if hj : j < 11 then (f ⟨j,hj⟩).val else j
    let changeGate (g : Gate) : Gate := ⟨g.op, g.inputs.map readWire⟩
    let D : Circuit := ⟨C.gates.map changeGate, readWire C.output⟩
    refine ⟨D, ?_, by simp [D, Circuit.size], ?_⟩
    · intro g hg
      change g ∈ C.gates.map changeGate at hg
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hc old hold).1, by simpa [changeGate] using (hc old hold).2⟩
    intro y
    let z : Fin 11 → Bool := fun i => y (f i)
    have input (v : Fin 11 → Bool) (i : Fin 11) : (List.ofFn v).getD i.val false = v i := by
      fin_cases i <;> rfl
    have readEq (s : List Bool) (j : ℕ) :
        (List.ofFn y ++ s).getD (readWire j) false = (List.ofFn z ++ s).getD j false := by
      by_cases h : j < 11
      · simp only [readWire, dite_eq_left h]
        rw [List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simpa using h)]
        exact (input y (f ⟨j,h⟩)).trans (input z ⟨j,h⟩).symm
      · have hi : 11 ≤ j := Nat.le_of_not_gt h
        simp only [readWire, dite_eq_right h]
        rw [List.getD_append_right _ _ _ _ (by simpa using hi),
            List.getD_append_right _ _ _ _ (by simpa using hi)]
        simp
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
    have tails (gs : List Gate) (s : List Bool) : ∃ t : List Bool,
        (gs.map changeGate).foldl step (List.ofFn y ++ s) = List.ofFn y ++ t ∧
        gs.foldl step (List.ofFn z ++ s) = List.ofFn z ++ t := by
      induction gs generalizing s with
      | nil => exact ⟨s,rfl,rfl⟩
      | cons g gs ih =>
        let v := g.op.eval (g.inputs.map fun j => (List.ofFn z ++ s).getD j false)
        have eqv : (changeGate g).op.eval ((changeGate g).inputs.map fun j =>
            (List.ofFn y ++ s).getD j false) = v := by
          simp only [changeGate, List.map_map, Function.comp_def, readEq, v]
        have left : step (List.ofFn y ++ s) (changeGate g) = List.ofFn y ++ (s ++ [v]) := by
          change (List.ofFn y ++ s) ++ [_] = _
          rw [eqv, List.append_assoc]
        have right : step (List.ofFn z ++ s) g = List.ofFn z ++ (s ++ [v]) := List.append_assoc _ _ _
        simp only [List.map_cons, List.foldl_cons, left, right]
        exact ih (s ++ [v])
    obtain ⟨t, hd, hc'⟩ := tails C.gates []
    simp only [List.append_nil] at hd hc'
    change ((C.gates.map changeGate).foldl step (List.ofFn y)).getD (readWire C.output) false =
      (C.gates.foldl step (List.ofFn z)).getD C.output false
    rw [hd, hc']
    exact readEq t C.output
  let u (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  let raw (x : Fin 9 → Bool) (j : Fin 11) := (u x).getD j.val false
  let slot (a b : Fin 11) (x : Fin 9 → Bool) : Fin 11 → Bool :=
    ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,!x 0,raw x a || raw x b]
  let edge (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let ordinary := ([1, 2, 3, 4, 6, 13, 14, 15, 16, 17, 18, 19, 25, 26, 28, 29, 30, 37, 39, 50, 73, 120] : List ℕ)
  let negative := ([9, 20, 31, 42, 53, 75] : List ℕ)
  let listed (a b : Fin 11) := 11 * a.val + b.val ∈ ordinary ++ negative
  let clamp (j : ℕ) : Fin 11 := if h : j < 10 then ⟨j, by omega⟩ else 10
  have getClamp (x : Fin 9 → Bool) (j : ℕ) : (u x).getD j false = raw x (clamp j) := by
    by_cases h : j < 10
    · simp [raw, clamp, h]
    · have hj : (u x).length ≤ j := by simp [u]; omega
      rw [List.getD_eq_default _ _ hj]
      simp only [clamp, dite_eq_right h]
      rfl
  have normalize : ∃ a b : Fin 11, ∀ x : Fin 9 → Bool,
      GateOp.or.eval (ops.map fun j => (u x).getD j false) = (raw x a || raw x b) := by
    cases ops with
    | nil => exact ⟨10,10,fun _ => rfl⟩
    | cons a ops =>
      cases ops with
      | nil =>
        refine ⟨clamp a,10,?_⟩
        intro x
        change ((u x).getD a false || false) = (raw x _ || false)
        rw [getClamp]
      | cons b ops =>
        cases ops with
        | nil =>
          refine ⟨clamp a,clamp b,?_⟩
          intro x
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, getClamp]
        | cons c cs => simp at hlen
  obtain ⟨a,b,hn⟩ := normalize
  have computed (x : Fin 9 → Bool) : C.eval (List.ofFn (slot a b x)) = edge x := by
    have h := good x
    change ¬ C.eval (u x ++ [GateOp.or.eval (ops.map fun j => (u x).getD j false)]) ≠ edge x at h
    have eq := not_ne_iff.mp h
    rw [hn] at eq
    exact eq
  let σ : Bool → Fin 9 → Fin 9 := fun p => if p then ![0,5,8,3,4,1,7,6,2] else id
  let τ : Bool → Fin 11 → Fin 11 := fun p => if p then ![0,5,8,3,4,1,7,6,2,9,10] else id
  have invariant : ∀ (p : Bool) (x : Fin 9 → Bool), edge (x ∘ σ p) = edge x := by decide +kernel
  have rawPerm (p : Bool) (x : Fin 9 → Bool) (j : Fin 11) : raw (x ∘ σ p) j = raw x (τ p j) := by
    cases p <;> fin_cases j <;> rfl
  have canonical (r s : Fin 11) (hr : listed r s) (f : Fin 11 → Fin 11) (p : Bool)
      (portMap : ∀ x : Fin 9 → Bool, (slot r s x ∘ f) = slot a b (x ∘ σ p)) : False := by
    obtain ⟨D, hd, hsize, hev⟩ := reindex f C fan
    have sizeD : D.size ≤ 13 := hsize.trans_le hs
    have witness : ∃ x : Fin 9 → Bool, D.eval (List.ofFn (slot r s x)) ≠ edge x := by
      rcases List.mem_append.mp hr with h | h
      · exact ordinaryBound r s h D hd sizeD
      · exact complementedBound r s h D hd sizeD
    obtain ⟨x, bad⟩ := witness
    apply bad
    exact (hev (slot r s x)).trans ((congrArg (fun v => C.eval (List.ofFn v)) (portMap x)).trans
      ((computed (x ∘ σ p)).trans (invariant p x)))
  have classify : ∀ i j : Fin 11,
      (∃ k : Fin 10, (i = k.castSucc ∧ (j = k.castSucc ∨ j = 10)) ∨
                     (j = k.castSucc ∧ i = 10)) ∨
      ∃ p : Bool, listed (τ p i) (τ p j) ∨ listed (τ p j) (τ p i) := by decide +kernel
  rcases classify a b with ⟨k,hk⟩ | ⟨p,hp⟩
  · let f (j : Fin 11) := if j = 10 then k.castSucc else j
    apply canonical 0 1 (by decide +kernel) f false
    intro x
    funext j
    by_cases last : j = 10
    · subst j
      change slot 0 1 x k.castSucc = (raw x a || raw x b)
      have hk' : slot 0 1 x k.castSucc = raw x k.castSucc := by fin_cases k <;> rfl
      rw [hk']
      have zero : raw x 10 = false := rfl
      rcases hk with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> simp [zero]
    · fin_cases j <;> first | rfl | contradiction
  · have transport (r s : Fin 11)
        (order : (r = τ p a ∧ s = τ p b) ∨ (r = τ p b ∧ s = τ p a)) :
        ∀ x : Fin 9 → Bool, (slot r s x ∘ τ p) = slot a b (x ∘ σ p) := by
      intro x
      funext j
      by_cases last : j = 10
      · subst j
        have fixed : τ p 10 = 10 := by cases p <;> rfl
        change slot r s x (τ p 10) = (raw (x ∘ σ p) a || raw (x ∘ σ p) b)
        rw [fixed, rawPerm, rawPerm]
        change (raw x r || raw x s) = (raw x (τ p a) || raw x (τ p b))
        rcases order with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rfl
        · exact Bool.or_comm _ _
      · cases p <;> fin_cases j <;> first | rfl | contradiction
    rcases hp with forward | backward
    · exact canonical _ _ forward (τ p) p (transport _ _ (Or.inl ⟨rfl,rfl⟩))
    · exact canonical _ _ backward (τ p) p (transport _ _ (Or.inr ⟨rfl,rfl⟩))

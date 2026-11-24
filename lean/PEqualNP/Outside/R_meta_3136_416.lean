import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The monotonicity argument follows the parent reduction R_meta_2768_315.
-- Removing a redundant final factor gives a circuit of size at most fourteen.
-- A last negation reads only monotone gates. If it passes the all-true input,
-- it is constant true. The other live cases leave three distinct sources and twelve gates.
theorem PEqualNP.Outside.R_meta_3136_416
    (small : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
        (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 14)
    (three : ∀ (gs : List Gate), gs.length = 12 → FanInTwo (⟨gs,0⟩ : Circuit) →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 → ∀ a b c : Fin 23,
      a ≠ b → a ≠ c → b ≠ c →
      ∃ x : Fin 9 → Bool,
        let w := (⟨gs,0⟩ : Circuit).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD a false && (w.getD b false && w.getD c false)) ≠
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
        (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x)
    (mixed : ∀ (gs : List Gate), gs.length = 12 → FanInTwo (⟨gs,0⟩ : Circuit) →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 → ∀ a b c : Fin 23,
      a ≠ b → a ≠ c → b ≠ c →
      ∃ x : Fin 9 → Bool,
        let w := (⟨gs,0⟩ : Circuit).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD a false && (w.getD b false || w.getD c false)) ≠
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
        (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             ∃ (x9 : Fin (9 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);               (x10.getD x2 Bool.false && x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  classical
  intro whole i j length fan budget _ _
  let f := (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
        (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  have andEval (v : List Bool) : GateOp.and.eval v = v.all id := rfl
  have orEval (v : List Bool) : GateOp.or.eval v = v.any id := rfl
  have notEval (v : List Bool) : GateOp.not.eval v = !v.headD false := rfl
  let seed : Gate := ⟨.or, [0,3]⟩
  let start (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 3]
  let step (v : List Bool) (g : Gate) := v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)]
  have seedVal (x : Fin 9 → Bool) : step (List.ofFn x) seed = start x := by
    simp [step, seed, start, orEval]
  have seedOK : seed.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      seed.inputs.length ≤ 2 := by simp [seed]
  have total (gates : List Gate) (v : List Bool) :
      (gates.foldl step v).length = v.length + gates.length := by
    induction gates generalizing v with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
  have nonempty : whole ≠ [] := by intro h; simp [h] at length
  let gs := whole.dropLast
  let g := whole.getLast nonempty
  have split : whole = gs ++ [g] := (List.dropLast_concat_getLast nonempty).symm
  have ng : gs.length = 12 := by simp [gs,length]
  have good : FanInTwo (⟨gs,0⟩ : Circuit) := by
    intro t ht
    apply fan t
    change t ∈ whole
    rw [split]
    exact List.mem_append_left _ ht
  have memg : g ∈ whole := by rw [split]; simp
  have gop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using (fan g memg).1
  have gb := (fan g memg).2
  have count : gs.countP (fun t => t.op.eval [false]) + (if g.op.eval [false] then 1 else 0) ≤ 1 := by
    simpa only [split, List.countP_append, List.countP_singleton] using budget
  have countGs : gs.countP (fun t => t.op.eval [false]) ≤ 1 := by omega
  let full (x : Fin 9 → Bool) := whole.foldl step (start x)
  let w (x : Fin 9 → Bool) := gs.foldl step (start x)
  let old (k : ℕ) (x : Fin 9 → Bool) := (w x).getD k false
  let z (x : Fin 9 → Bool) := g.op.eval (g.inputs.map fun k => old k x)
  have nw (x) : (w x).length = 22 := by simp [w,total,start,ng]
  have tailEq (x) : full x = w x ++ [z x] := by
    change whole.foldl step (start x) = _
    rw [split, List.foldl_append]
    rfl
  have nf (x) : (full x).length = 23 := by simp [tailEq,nw]
  have atLast (x) : (full x).getD 22 false = z x := by
    rw [tailEq, List.getD_append_right _ _ _ _ (by rw [nw]), nw]
    rfl
  have earlier (k : ℕ) (hk : k ≠ 22) (x) : (full x).getD k false = old k x := by
    by_cases h : k < 22
    · rw [tailEq, List.getD_append _ _ _ _ (by simpa [nw] using h)]
    · change (full x).getD k false = (w x).getD k false
      rw [List.getD_eq_default _ _ (show (full x).length ≤ k by rw [nf]; omega),
        List.getD_eq_default _ _ (show (w x).length ≤ k by rw [nw]; omega)]
  have noSingle (k : ℕ) (agree : ∀ x, (full x).getD k false = f x) : False := by
    apply small
    refine ⟨⟨seed :: whole,k⟩, ?_, ?_, ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with e | member
      · exact e ▸ seedOK
      · exact fan t member
    · change (seed :: whole).length ≤ 14
      simp [length]
    · intro x
      change ((seed :: whole).foldl step (List.ofFn x)).getD k false = _
      rw [List.foldl_cons,seedVal]
      exact agree x
  have noPair (a b : ℕ) (agree : ∀ x, (old a x && old b x) = f x) : False := by
    apply small
    let meet : Gate := ⟨.and,[a,b]⟩
    refine ⟨⟨seed :: (gs ++ [meet]),22⟩, ?_, ?_, ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with eq | member
      · exact eq ▸ seedOK
      rcases List.mem_append.mp member with h | h
      · exact good t h
      · obtain rfl := List.mem_singleton.mp h
        simp [meet]
    · change (seed :: (gs ++ [meet])).length ≤ 14
      simp [ng]
    · intro x
      change ((seed :: (gs ++ [meet])).foldl step (List.ofFn x)).getD 22 false = _
      rw [List.foldl_cons,seedVal,List.foldl_append]
      have meetVal : step (w x) meet = (w x) ++ [old a x && old b x] := by
        simp [step,meet,andEval,old]
      change (step (w x) meet).getD 22 false = _
      rw [meetVal, List.getD_append_right _ _ _ _ (by rw [nw]), nw]
      exact agree x
  let top : Fin 9 → Bool := fun _ => true
  have edgeTop : f top = true := rfl
  have impossibleLast (a : ℕ) (agree : ∀ x, (old a x && z x) = f x) : False := by
    have noOld (eq : ∀ x, old a x = f x) : False :=
      noPair a a (fun x => by simpa only [Bool.and_self] using eq x)
    have invert (b : ℕ) (inv : g.op = .not) (eq : ∀ x, z x = !old b x) : False := by
      have countZero : gs.countP (fun t => t.op.eval [false]) = 0 := by
        rw [inv] at count
        change gs.countP (fun t => t.op.eval [false]) + 1 ≤ 1 at count
        omega
      have monotone (l : List Gate)
          (pos : ∀ t ∈ l, t.op = .and ∨ t.op = .or)
          (u v : List Bool) (len : u.length = v.length)
          (ord : ∀ k, u.getD k false = true → v.getD k false = true) :
          ∀ k, (l.foldl step u).getD k false = true → (l.foldl step v).getD k false = true := by
        induction l generalizing u v with
        | nil => exact ord
        | cons t l ih =>
          have gateOrd : t.op.eval (t.inputs.map fun k => u.getD k false) = true →
              t.op.eval (t.inputs.map fun k => v.getD k false) = true := by
            rcases pos t (by simp) with e | e
            · simp only [e,andEval,List.all_eq_true,List.mem_map,id_eq]
              intro h d hd
              obtain ⟨k,hk,rfl⟩ := hd
              exact ord k (h _ ⟨k,hk,rfl⟩)
            · simp only [e,orEval,List.any_eq_true,List.mem_map,id_eq]
              rintro ⟨d, ⟨k,hk,rfl⟩, h⟩
              exact ⟨true,⟨k,hk,ord k h⟩,rfl⟩
          simp only [List.foldl_cons]
          apply ih (fun j hj => pos j (by simp [hj])) (step u t) (step v t) (by simp [step,len])
          intro k
          by_cases isOld : k < u.length
          · simpa only [step, List.getD_append _ _ _ _ isOld,
                List.getD_append _ _ _ _ (len ▸ isOld)] using ord k
          · have ku : u.length ≤ k := by omega
            have kv : v.length ≤ k := by omega
            simp only [step,List.getD_append_right _ _ _ _ ku,List.getD_append_right _ _ _ _ kv,←len]
            cases k - u.length with
            | zero => exact gateOrd
            | succ d => simp
      have pos : ∀ t ∈ gs, t.op = .and ∨ t.op = .or := by
        intro t ht
        have o : t.op = .and ∨ t.op = .or ∨ t.op = .not := by simpa using (good t ht).1
        rcases o with e | e | e
        · exact Or.inl e
        · exact Or.inr e
        · have hn := List.countP_eq_zero.mp countZero t ht
          simp [e,notEval] at hn
      have rawTop : start top = List.replicate 10 true := by decide
      have topFalse : old b top = false := by
        have h := agree top
        rw [edgeTop,eq] at h
        cases e : old b top <;> simp_all
      apply noOld
      intro x
      have ord : ∀ k, (start x).getD k false = true → (start top).getD k false = true := by
        intro k hk
        by_cases h : k < 10
        · rw [rawTop,List.getD_replicate true h]
        · rw [List.getD_eq_default _ _ (by simp [start]; omega)] at hk
          contradiction
      have under := monotone gs pos (start x) (start top) (by simp [start]) ord b
      have off : old b x = false := by
        cases e : old b x with
        | false => rfl
        | true => exact False.elim (Bool.noConfusion ((under e).symm.trans topFalse))
      simpa [eq,off] using agree x
    let cap (k : ℕ) : Fin 23 := ⟨min k 22, by omega⟩
    have clip (k : ℕ) (x) : old (cap k).val x = old k x := by
      by_cases h : k ≤ 22
      · simp [cap,Nat.min_eq_left h]
      · change (w x).getD (min k 22) false = (w x).getD k false
        rw [Nat.min_eq_right (by omega : 22 ≤ k),
          List.getD_eq_default _ _ (show (w x).length ≤ 22 by rw [nw]),
          List.getD_eq_default _ _ (show (w x).length ≤ k by rw [nw]; omega)]
    have binary (b c : ℕ) (d : Bool)
        (eq : ∀ x, z x = if d then (old b x || old c x) else (old b x && old c x)) : False := by
      have imp (x) : (old (cap a).val x && (if d then (old (cap b).val x || old (cap c).val x)
            else (old (cap b).val x && old (cap c).val x))) = f x := by
        simpa only [clip,←eq] using agree x
      have absorb (u v : Bool) : (u && (u || v)) = u := by cases u <;> rfl
      have absorbRight (u v : Bool) : (u && (v || u)) = u := by cases u <;> cases v <;> rfl
      by_cases ab : cap a = cap b
      · cases d
        · apply noPair (cap a).val (cap c).val
          intro x
          simpa [←ab,Bool.and_assoc] using imp x
        · apply noOld
          intro x
          have h := imp x
          rw [←ab] at h
          simpa [clip,absorb] using h
      by_cases ac : cap a = cap c
      · cases d
        · apply noPair (cap a).val (cap b).val
          intro x
          simpa [←ac,Bool.and_left_comm,Bool.and_comm,Bool.and_assoc] using imp x
        · apply noOld
          intro x
          have h := imp x
          rw [←ac] at h
          simpa [clip,absorbRight] using h
      by_cases bc : cap b = cap c
      · apply noPair (cap a).val (cap b).val
        intro x
        cases d <;> simpa [←bc] using imp x
      cases d with
      | false =>
        obtain ⟨x,h⟩ := three gs ng good countGs (cap a) (cap b) (cap c) ab ac bc
        exact h (imp x)
      | true =>
        obtain ⟨x,h⟩ := mixed gs ng good countGs (cap a) (cap b) (cap c) ab ac bc
        exact h (imp x)
    cases ins : g.inputs with
    | nil =>
      have const (x) : z x = g.op.eval [] := by simp [z,ins]
      cases val : g.op.eval [] with
      | false => simpa [const,val,edgeTop] using agree top
      | true => exact noOld (fun x => by simpa [const,val] using agree x)
    | cons b rest =>
      cases rest with
      | nil =>
        rcases gop with andOp | orOp | inv
        · exact noPair a b (fun x => by simpa [z,ins,andOp,andEval] using agree x)
        · exact noPair a b (fun x => by simpa [z,ins,orOp,orEval] using agree x)
        · exact invert b inv (fun x => by simp [z,ins,inv,notEval])
      | cons c tail =>
        have n : tail = [] := by
          have h : (b::c::tail).length ≤ 2 := ins ▸ gb
          simpa using h
        subst tail
        rcases gop with andOp | orOp | inv
        · exact binary b c false (fun x => by simp [z,ins,andOp,andEval])
        · exact binary b c true (fun x => by simp [z,ins,orOp,orEval])
        · exact invert b inv (fun x => by simp [z,ins,inv,notEval])
  by_contra! h
  have agree (x) : ((full x).getD i false && (full x).getD j false) = f x := Classical.byContradiction (h x)
  by_cases hi : i = 22
  · by_cases hj : j = 22
    · apply noSingle 22
      intro x
      simpa [hi,hj] using agree x
    · apply impossibleLast j
      intro x
      simpa only [hi,atLast,earlier j hj,Bool.and_comm] using agree x
  · by_cases hj : j = 22
    · exact impossibleLast i (fun x => by simpa only [hj,earlier i hi,atLast] using agree x)
    · exact noPair i j (fun x => by simpa only [earlier i hi,earlier j hj] using agree x)

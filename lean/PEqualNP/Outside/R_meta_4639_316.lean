import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_4639_316
    (skipSeed :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
        C.size = 8 → C.output = 0 → (∀ g ∈ C.gates, ∀ w ∈ g.inputs, w ≤ 17) →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
        ∀ S ⊆ Finset.range 17, S.card = 6 → 9 ∉ S →
        (∃ w ∈ S, 10 ≤ w) →
        (∀ u v : Fin 9, u < v → u.val ∉ S → v.val ∉ S →
          ∃ g ∈ C.gates.drop 1, ¬ (u.val ∈ g.inputs ↔ v.val ∈ g.inputs)) →
        ∃ x y : Fin 9 → Bool, (∀ w ∈ S,
          (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false) ∧
          f x ≠ f y)
    (readSeed :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
        C.size = 8 → C.output = 0 → (∀ g ∈ C.gates, ∀ w ∈ g.inputs, w ≤ 17) →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
        ∀ S ⊆ Finset.range 17, S.card = 6 → 9 ∈ S → (0 ∉ S ∨ 2 ∉ S) →
        (∃ w ∈ S, 10 ≤ w) →
        (∀ u v : Fin 9, u < v → u.val ∉ S → v.val ∉ S →
          ∃ g ∈ C.gates.drop 1, ¬ (u.val ∈ g.inputs ↔ v.val ∈ g.inputs)) →
        ∃ x y : Fin 9 → Bool, (∀ w ∈ S,
          (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false) ∧
          f x ≠ f y) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size = (8 : ℕ) → x2.output = (0 : ℕ) → (∀ x6 ∈ x2.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (17 : ℕ)) → (∀ (x7 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = (x7 (0 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)))) → ∀ x8 ⊆ Finset.range (17 : ℕ), x8.card ≤ (6 : ℕ) → ∃ (x11 : Fin (9 : ℕ) → Bool) (x12 : Fin (9 : ℕ) → Bool), (∀ x13 ∈ x8, (x2.wires (List.ofFn x11)).getD x13 Bool.false = (x2.wires (List.ofFn x12)).getD x13 Bool.false) ∧ x1 x11 ≠ x1 x12 := by
  let target (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))

  let row (r : ℕ) (i : Fin 9) : Bool := r.testBit i.val

  let pos : List ℕ :=
    [0,6,12,12,37,21,21,132,21,
     0,0,3,3,6,6,3,3,3,
     0,0,0,133,17,33,13,13,133,
     0,0,0,0,12,12,12,24,12,
     0,0,0,0,0,24,17,17,17,
     0,0,0,0,0,0,33,33,33,
     0,0,0,0,0,0,0,66,66,
     0,0,0,0,0,0,0,0,132,
     0,0,0,0,0,0,0,0,0]

  let neg : List ℕ :=
    [0,5,9,5,52,52,84,5,276,
     0,0,5,9,20,36,65,129,257,
     0,0,0,137,5,5,73,137,385,
     0,0,0,0,20,36,68,144,260,
     0,0,0,0,0,40,65,129,257,
     0,0,0,0,0,0,65,129,257,
     0,0,0,0,0,0,0,130,258,
     0,0,0,0,0,0,0,0,260,
     0,0,0,0,0,0,0,0,0]

  have swapWitness (u v : Fin 9) (ordered : u < v) :
      ∃ x y : Fin 9 → Bool,
        target x ≠ target y ∧ (x 0 || x 2) = (y 0 || y 2) ∧
          x u = y v ∧ x v = y u ∧ (∀ w : Fin 9, w ≠ u → w ≠ v → x w = y w) := by
    refine ⟨row (pos.getD (9*u.val+v.val) 0),row (neg.getD (9*u.val+v.val) 0),?_⟩
    revert ordered
    fin_cases u <;> fin_cases v <;> decide +kernel

  let step (s : List Bool) (g : Gate) : List Bool :=
    s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]

  have step_length (s : List Bool) (g : Gate) : (step s g).length = s.length+1 := by
    simp [step]

  have prefixRead (p : List Gate) (s : List Bool) (i : ℕ) (within : i < s.length) :
      (p.foldl step s).getD i false = s.getD i false := by
    induction p generalizing s with
    | nil => rfl
    | cons g p ih =>
      change (p.foldl step (step s g)).getD i false = _
      rw [ih _ (by rw [step_length]; omega)]
      exact List.getD_append _ _ _ _ within

  let Swapped (u v : ℕ) (a b : List Bool) : Prop :=
    a.length = b.length ∧ u < a.length ∧ v < a.length ∧
    a.getD u false = b.getD v false ∧ a.getD v false = b.getD u false ∧
    ∀ i, i ≠ u → i ≠ v → a.getD i false = b.getD i false

  have appendSwapped {u v : ℕ} {a b : List Bool} (h : Swapped u v a b) (x : Bool) :
      Swapped u v (a++[x]) (b++[x]) := by
    refine ⟨by simp [h.1],by simp; have := h.2.1; omega,
      by simp; have := h.2.2.1; omega,?_,?_,?_⟩
    · rw [List.getD_append _ _ _ _ h.2.1,
        List.getD_append _ _ _ _ (h.1 ▸ h.2.2.1)]
      exact h.2.2.2.1
    · rw [List.getD_append _ _ _ _ h.2.2.1,
        List.getD_append _ _ _ _ (h.1 ▸ h.2.1)]
      exact h.2.2.2.2.1
    · intro i nu nv
      by_cases early : i < a.length
      · rw [List.getD_append _ _ _ _ early,List.getD_append _ _ _ _ (h.1 ▸ early)]
        exact h.2.2.2.2.2 i nu nv
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by have := h.1; omega),h.1]

  have ofFnRead (x : Fin 9 → Bool) {i : ℕ} (hi : i < 9) :
      (List.ofFn x).getD i false = x ⟨i,hi⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn]

  have initialSwapped (u v : Fin 9) (x y : Fin 9 → Bool)
      (one : x u = y v) (two : x v = y u)
      (rest : ∀ w : Fin 9, w ≠ u → w ≠ v → x w = y w) :
      Swapped u.val v.val (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,by simpa using u.isLt,by simpa using v.isLt,?_,?_,?_⟩
    · simpa only [ofFnRead _ u.isLt,ofFnRead _ v.isLt] using one
    · simpa only [ofFnRead _ u.isLt,ofFnRead _ v.isLt] using two
    · intro i nu nv
      by_cases early : i < 9
      · rw [ofFnRead _ early,ofFnRead _ early]
        exact rest _ (fun e => nu (congrArg Fin.val e)) (fun e => nv (congrArg Fin.val e))
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt early),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt early)]

  have pairInputs {u v : ℕ} (distinct : u ≠ v) (l : List ℕ) (len : l.length ≤ 2)
      (uRead : u ∈ l) (vRead : v ∈ l) : l = [u,v] ∨ l = [v,u] := by
    cases l with
    | nil => simp at uRead
    | cons a rest =>
      cases rest with
      | nil =>
        simp only [List.mem_singleton] at uRead vRead
        exact False.elim (distinct (uRead.trans vRead.symm))
      | cons b rest =>
        have tail : rest = [] := List.length_eq_zero_iff.mp (by
          simp only [List.length_cons] at len
          omega)
        subst rest
        simp only [List.mem_cons,List.not_mem_nil,or_false] at uRead vRead
        rcases uRead with uA | uB <;> rcases vRead with vA | vB
        · exact False.elim (distinct (uA.trans vA.symm))
        · exact Or.inl (by rw [uA,vB])
        · exact Or.inr (by rw [vA,uB])
        · exact False.elim (distinct (uB.trans vB.symm))

  let evalGate (s : List Bool) (g : Gate) : Bool :=
    g.op.eval (g.inputs.map fun i => s.getD i false)

  have evalAnd (a b : Bool) : GateOp.eval .and [a,b] = (a && b) := by
    change (a && (b && true)) = (a && b)
    rw [Bool.and_true]
  have evalOr (a b : Bool) : GateOp.eval .or [a,b] = (a || b) := by
    change (a || (b || false)) = (a || b)
    rw [Bool.or_false]

  have gateUnchanged {u v : ℕ} {a b : List Bool} (h : Swapped u v a b) (different : u ≠ v)
      (g : Gate) (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2)
      (inseparable : u ∈ g.inputs ↔ v ∈ g.inputs) :
      evalGate a g = evalGate b g := by
    unfold evalGate
    by_cases seesU : u ∈ g.inputs
    · have seesV := inseparable.mp seesU
      rcases pairInputs different g.inputs arity seesU seesV with eq | eq
      · rw [eq]
        rcases op with hop | hop
        · simp only [hop,List.map_cons,List.map_nil,evalAnd,h.2.2.2.1,h.2.2.2.2.1]
          exact Bool.and_comm _ _
        · simp only [hop,List.map_cons,List.map_nil,evalOr,h.2.2.2.1,h.2.2.2.2.1]
          exact Bool.or_comm _ _
      · rw [eq]
        rcases op with hop | hop
        · simp only [hop,List.map_cons,List.map_nil,evalAnd,h.2.2.2.1,h.2.2.2.2.1]
          exact Bool.and_comm _ _
        · simp only [hop,List.map_cons,List.map_nil,evalOr,h.2.2.2.1,h.2.2.2.2.1]
          exact Bool.or_comm _ _
    · have seesV : v ∉ g.inputs := fun yes => seesU (inseparable.mpr yes)
      congr 1
      apply List.map_congr_left
      intro i mem
      exact h.2.2.2.2.2 i (fun e => seesU (e ▸ mem)) (fun e => seesV (e ▸ mem))

  have suffixSwapped {u v : ℕ} (different : u ≠ v) (gs : List Gate)
      (shape : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      (unpaired : ∀ g ∈ gs, u ∈ g.inputs ↔ v ∈ g.inputs)
      {a b : List Bool} (h : Swapped u v a b) :
      Swapped u v (gs.foldl step a) (gs.foldl step b) := by
    induction gs generalizing a b with
    | nil => exact h
    | cons g gs ih =>
      have gateShape := shape g (by simp)
      have same := gateUnchanged h different g gateShape.1 gateShape.2 (unpaired g (by simp))
      change Swapped u v (gs.foldl step (a ++ [evalGate a g])) (gs.foldl step (b ++ [evalGate b g]))
      rw [← same]
      exact ih (fun t ht => shape t (by simp [ht])) (fun t ht => unpaired t (by simp [ht]))
        (appendSwapped h _)

  let W (C : Circuit) (x : Fin 9 → Bool) (w : ℕ) : Bool :=
    (C.wires (List.ofFn x)).getD w false

  let Collides (C : Circuit) (S : Finset ℕ) : Prop :=
    ∃ x y : Fin 9 → Bool, (∀ w ∈ S, W C x w = W C y w) ∧ target x ≠ target y

  let PairDistinguished (C : Circuit) (S : Finset ℕ) : Prop :=
    ∀ u v : Fin 9, u < v → u.val ∉ S → v.val ∉ S →
      ∃ g ∈ C.gates.drop 1, ¬ (u.val ∈ g.inputs ↔ v.val ∈ g.inputs)

  have collisionWithoutPairDistinguished (C : Circuit) (S : Finset ℕ)
      (model : Monotone2 C) (size : C.size = 8)
      (seed : ∀ x : Fin 9 → Bool, W C x 9 = (x 0 || x 2))
      (missing : ¬ PairDistinguished C S) : Collides C S := by
    classical
    unfold PairDistinguished at missing
    push Not at missing
    obtain ⟨u,v,ordered,uOut,vOut,sameRead⟩ := missing
    obtain ⟨x,y,changed,seedSame,left,right,rest⟩ := swapWitness u v ordered
    cases C with
    | mk gates output =>
      cases gates with
      | nil =>
        change (0 : ℕ) = 8 at size
        omega
      | cons g gs =>
        let a := List.ofFn x
        let b := List.ofFn y
        have seedValue (z : Fin 9 → Bool) :
            evalGate (List.ofFn z) g = (z 0 || z 2) := by
          have top := seed z
          change (gs.foldl step (step (List.ofFn z) g)).getD 9 false = _ at top
          rw [prefixRead gs _ _ (by rw [step_length]; simp)] at top
          simpa [step,evalGate] using top
        have same := (seedValue x).trans (seedSame.trans (seedValue y).symm)
        have prep : Swapped u.val v.val a b := initialSwapped u v x y left right rest
        have proof := suffixSwapped (show u.val ≠ v.val from Nat.ne_of_lt ordered) gs
          (fun t mem => model t (List.mem_cons_of_mem _ mem))
          (fun t mem => sameRead t (by simpa using mem))
          (appendSwapped prep (evalGate a g))
        refine ⟨x,y,?_,changed⟩
        intro w mem
        change (gs.foldl step (a++[evalGate a g])).getD w false =
          (gs.foldl step (b++[evalGate b g])).getD w false
        rw [← same]
        exact proof.2.2.2.2.2 w (fun e => uOut (e ▸ mem)) (fun e => vOut (e ▸ mem))

  have singleWitness (u : Fin 9) :
      ∃ x y : Fin 9 → Bool, target x ≠ target y ∧ (x 0 || x 2) = (y 0 || y 2) ∧
        (∀ w : Fin 9, w ≠ u → x w = y w) := by
    let positives : Fin 9 → ℕ := ![21,3,133,24,17,33,66,132,264]
    let negatives : Fin 9 → ℕ := ![20,1,129,16,1,1,2,4,8]
    refine ⟨row (positives u),row (negatives u),?_⟩
    fin_cases u <;> decide +kernel

  have rawWire (C : Circuit) (x : Fin 9 → Bool) {w : ℕ} (hw : w < 9) :
      W C x w = x ⟨w,hw⟩ := by
    change (C.gates.foldl step (List.ofFn x)).getD w false = _
    rw [prefixRead _ _ _ (by simpa using hw),ofFnRead _ hw]

  have rawCutCollides (C : Circuit) (S : Finset ℕ) (small : S.card ≤ 6)
      (raw : ∀ w ∈ S, w ≤ 9) (seed : ∀ x : Fin 9 → Bool, W C x 9 = (x 0 || x 2)) :
      Collides C S := by
    have absent : ∃ u : Fin 9, u.val ∉ S := by
      by_contra! every
      have h : Finset.range 9 ⊆ S := fun i hi => every ⟨i,Finset.mem_range.mp hi⟩
      have := Finset.card_le_card h
      rw [Finset.card_range] at this
      omega
    obtain ⟨u,missing⟩ := absent
    obtain ⟨x,y,different,seedSame,rest⟩ := singleWitness u
    refine ⟨x,y,?_,different⟩
    intro w mem
    by_cases isSeed : w = 9
    · simpa only [isSeed,seed] using seedSame
    · have bound : w < 9 := by have := raw w mem; omega
      rw [rawWire _ _ bound,rawWire _ _ bound]
      exact rest _ (fun e => missing ((congrArg Fin.val e) ▸ mem))

  have trimCollision {C : Circuit} {S T : Finset ℕ} (h : Collides C T) (sub : S ⊆ T) :
      Collides C S := by
    obtain ⟨x,y,agree,opposite⟩ := h
    exact ⟨x,y,fun w mem => agree w (sub mem),opposite⟩

  have restoreCollisionSeed {C : Circuit} {S : Finset ℕ} (h : Collides C (S.erase 9))
      (raw0 : 0 ∈ S) (raw2 : 2 ∈ S)
      (seed : ∀ x : Fin 9 → Bool, W C x 9 = (x 0 || x 2)) : Collides C S := by
    obtain ⟨x,y,agree,opposite⟩ := h
    refine ⟨x,y,?_,opposite⟩
    have eq0 := agree 0 (Finset.mem_erase.mpr ⟨by decide,raw0⟩)
    have eq2 := agree 2 (Finset.mem_erase.mpr ⟨by decide,raw2⟩)
    rw [rawWire C x (by decide),rawWire C y (by decide)] at eq0 eq2
    change x 0 = y 0 at eq0
    change x 2 = y 2 at eq2
    intro w mem
    by_cases isSeed : w = 9
    · subst w
      rw [seed x,seed y,eq0,eq2]
    · exact agree w (Finset.mem_erase.mpr ⟨isSeed,mem⟩)

  have restrictCut (C : Circuit) (model : Monotone2 C) (size : C.size = 8)
      (seed : ∀ x : Fin 9 → Bool, W C x 9 = (x 0 || x 2)) (S : Finset ℕ)
      (bound : S ⊆ Finset.range 17) (small : S.card ≤ 6)
      (skip : ∀ T ⊆ Finset.range 17, T.card = 6 → 9 ∉ T →
        (∃ w ∈ T, 10 ≤ w) → PairDistinguished C T → Collides C T)
      (use : ∀ T ⊆ Finset.range 17, T.card = 6 → 9 ∈ T → (0 ∉ T ∨ 2 ∉ T) →
        (∃ w ∈ T, 10 ≤ w) → PairDistinguished C T → Collides C T) : Collides C S := by
    have reduceSkip (T : Finset ℕ) (inRange : T ⊆ Finset.range 17) (exactly : T.card = 6)
        (noSeed : 9 ∉ T) : Collides C T := by
      by_cases deep : ∃ w ∈ T, 10 ≤ w
      · by_cases pair : PairDistinguished C T
        · exact skip T inRange exactly noSeed deep pair
        · exact collisionWithoutPairDistinguished C T model size seed pair
      · exact rawCutCollides C T (by omega)
          (fun w mem => Nat.le_of_not_gt (fun h => deep ⟨w,mem,Nat.succ_le_of_lt h⟩)) seed
    obtain ⟨T,contains,inRange,exactly⟩ := Finset.exists_subsuperset_card_eq bound small
      (by rw [Finset.card_range]; decide)
    apply trimCollision _ contains
    by_cases hasSeed : 9 ∈ T
    · by_cases both : 0 ∈ T ∧ 2 ∈ T
      · apply restoreCollisionSeed _ both.1 both.2 seed
        have erased : T.erase 9 ⊆ (Finset.range 17).erase 9 := by
          intro w mem
          obtain ⟨different,member⟩ := Finset.mem_erase.mp mem
          exact Finset.mem_erase.mpr ⟨different,inRange member⟩
        obtain ⟨U,keep,URange,exact⟩ := Finset.exists_subsuperset_card_eq (n := 6) erased
          (by have := Finset.card_erase_le (a := 9) (s := T); omega)
          (by decide +kernel)
        have noSeed : 9 ∉ U := fun h => Finset.notMem_erase _ _ (URange h)
        exact trimCollision (reduceSkip U (URange.trans (Finset.erase_subset _ _)) exact noSeed) keep
      · have oneAbsent : 0 ∉ T ∨ 2 ∉ T := by tauto
        by_cases deep : ∃ w ∈ T, 10 ≤ w
        · by_cases pair : PairDistinguished C T
          · exact use T inRange exactly hasSeed oneAbsent deep pair
          · exact collisionWithoutPairDistinguished C T model size seed pair
        · exact rawCutCollides C T (by omega)
            (fun w mem => Nat.le_of_not_gt (fun h => deep ⟨w,mem,Nat.succ_le_of_lt h⟩)) seed
    · exact reduceSkip T inRange exactly hasSeed
  intro f C model size out bounded seed S inRange small
  exact restrictCut C model size seed S inRange small
    (skipSeed C model size out bounded seed) (readSeed C model size out bounded seed)

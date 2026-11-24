import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A projection fixes one endpoint of the promise edge to false. The twelve
-- relabelings expose each eligible free OR in both vertex deletions.
-- After the first five gates and j further gates, discard the branch if at
-- most j + 2 gates reproduce its projected wires. The remaining gates would
-- give a circuit of size at most fourteen for the deletion.
-- Count distinct wire functions on 512 assignments outside the nine inputs,
-- two constants and the free OR. Each first occurrence costs one gate.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4137_674
    (deletion : ∀ (A D : Circuit) (indices : List ℕ), FanInTwo A → FanInTwo D → A.size+D.size ≤ 14 →
      ∃ x : Fin 9 → Bool, D.eval (indices.map (fun i =>
        (A.wires (List.ofFn x ++ [false,true,x 0 || x 1])).getD i false)) ≠
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
    (tailBound : ∀ (P D : Circuit), FanInTwo P → FanInTwo D → P.size ≤ 5 → D.size ≤ 12 →
      (∀ k ∈ ([8253761049,2813675049,8035461279,815643279,5180672349,1520768349,5287301694,1826305794,3084521697,1806523497,8156032794,2517038694] : List ℕ), ∀ (j : Fin 13) (A : Circuit) (indices : List ℕ), FanInTwo A → A.size ≤ 2+j.val →
        ∃ x : Fin 9 → Bool,
          (⟨D.gates.take j.val,0⟩ : Circuit).wires (P.wires ((List.range 10).map (fun i => (List.ofFn x).getD (k / 10^i % 10) false))) ≠
          indices.map (fun i => (A.wires (List.ofFn x ++ [false,true,x 0 || x 1])).getD i false)) →
      ∃ x : Fin 10 → Bool, (x 0 && x 1)=false ∧
        D.eval (P.wires (List.ofFn x)) ≠ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ))) = Bool.false ∧ x1.eval (List.ofFn x4) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C legal size
  let P : Circuit := ⟨C.gates.take 5,0⟩
  let D : Circuit := ⟨C.gates.drop 5,C.output⟩
  have pLegal : FanInTwo P := fun g hg => legal g (List.mem_of_mem_take hg)
  have dLegal : FanInTwo D := fun g hg => legal g (List.mem_of_mem_drop hg)
  have pSize : P.size≤5 := by change (C.gates.take 5).length ≤ 5; simp
  have dSize : D.size≤12 := by
    change C.gates.length≤17 at size
    change (C.gates.drop 5).length ≤ 12
    rw [List.length_drop]; omega
  have split (w : List Bool) : C.eval w=D.eval (P.wires w) := by
    unfold Circuit.eval Circuit.wires
    simp only [P,D,←List.foldl_append,List.take_append_drop]
  let edges := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10))
  let smallEdges := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9))
  have target (x : Fin 10 → Bool) : edges.any (fun e => x e.1 && x e.2) = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x := by
    simp [edges,Bool.or_assoc]
  by_contra! correct
  have computes (x : Fin 10 → Bool) (guard : (x 0 && x 1)=false) :
      D.eval (P.wires (List.ofFn x))=edges.any (fun e => x e.1 && x e.2) := by
    rw [←split,target]; exact correct x guard
  let keys : List ℕ := [8253761049,2813675049,8035461279,815643279,5180672349,1520768349,5287301694,1826305794,3084521697,1806523497,8156032794,2517038694]
  let ix (k i : ℕ) := k / 10^i % 10
  have blank : ∀ k∈keys, ix k 0=9 ∨ ix k 1=9 := by decide +kernel
  have mapped : ∀ k∈keys, ((edges.filter (fun e => ix k e.1 < 9 && ix k e.2 < 9)).map
      (fun e => (min (ix k e.1) (ix k e.2),max (ix k e.1) (ix k e.2)))).toFinset =
        (smallEdges.map (fun e => (min e.1.val e.2.val,max e.1.val e.2.val))).toFinset := by decide +kernel
  have agrees (k) (hk : k∈keys) (y : Fin 9 → Bool) :
      let z := fun i : Fin 10 => (List.ofFn y).getD (ix k i) false
      (z 0 && z 1)=false ∧ edges.any (fun e => z e.1 && z e.2)=smallEdges.any (fun e => y e.1 && y e.2) := by
    dsimp only
    constructor
    · rcases blank k hk with h|h <;> simp [h,List.getD_eq_getElem?_getD]
    · let val (j : Nat) := (List.ofFn y).getD j false
      let test (e : ℕ × ℕ) := val e.1 && val e.2
      have order (a b : Nat) : test (min a b,max a b) = (val a && val b) := by
        rcases le_total a b with l|l
        · simp [test,min_eq_left l,max_eq_right l]
        · simp [test,min_eq_right l,max_eq_left l,Bool.and_comm]
      have real (j) (on : val j=true) : j<9 := by
        by_contra! large
        have zero : val j=false := List.getD_eq_default _ _ (by simpa using large)
        simp [zero] at on
      have raw (i : Fin 9) : val i.val=y i := by
        change (List.ofFn y).getD i.val false = _
        rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true,Bool.and_eq_true]
      constructor
      · rintro ⟨e,he,ha,hb⟩
        have h : (min (ix k e.1) (ix k e.2),max (ix k e.1) (ix k e.2)) ∈
            (smallEdges.map (fun e => (min e.1.val e.2.val,max e.1.val e.2.val))).toFinset := by
          rw [←mapped k hk]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,List.mem_filter.mpr ⟨he,by simp [real _ ha,real _ hb]⟩,rfl⟩)
        obtain ⟨f,hf,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
        have on := congrArg test eq
        rw [order,order,raw,raw] at on
        change val (ix k e.1)=true at ha
        change val (ix k e.2)=true at hb
        rw [ha,hb] at on
        exact ⟨f,hf,by simpa only [Bool.and_true,Bool.and_eq_true] using on⟩
      · rintro ⟨e,he,ha,hb⟩
        have h : (min e.1.val e.2.val,max e.1.val e.2.val) ∈
            (smallEdges.map (fun f => (min f.1.val f.2.val,max f.1.val f.2.val))).toFinset :=
          List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)
        rw [←mapped k hk] at h
        obtain ⟨f,hf,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
        have on := congrArg test eq
        rw [order,order,raw,raw] at on
        rw [show (y e.1 && y e.2)=true by simp [ha,hb]] at on
        exact ⟨f,(List.mem_filter.mp hf).1,by simpa only [Bool.and_true,Bool.and_eq_true] using on⟩
  apply (show ¬ ∃ x : Fin 10 → Bool, (x 0 && x 1)=false ∧ D.eval (P.wires (List.ofFn x)) ≠
      edges.any (fun e => x e.1 && x e.2) from by rintro ⟨x,h,ne⟩; exact ne (computes x h))
  apply tailBound P D pLegal dLegal pSize dSize
  intro k hk j A indices aLegal aSize
  let Q : Circuit := ⟨D.gates.take j.val,0⟩
  let R : Circuit := ⟨D.gates.drop j.val,D.output⟩
  have piece (w : List Bool) : D.eval w=R.eval (Q.wires w) := by
    unfold Circuit.eval Circuit.wires
    simp only [Q,R,←List.foldl_append,List.take_append_drop]
  have rLegal : FanInTwo R := fun g hg => dLegal g (List.mem_of_mem_drop hg)
  have cost : A.size+R.size≤14 := by
    change D.gates.length≤12 at dSize
    change A.size+(D.gates.drop j.val).length≤14
    rw [List.length_drop]; have := j.isLt; omega
  obtain ⟨y,miss⟩ := deletion A R indices aLegal rLegal cost
  refine ⟨y,fun layout => miss ?_⟩
  rw [←layout]
  obtain ⟨guard,value⟩ := agrees k hk y
  let z := fun i : Fin 10 => (List.ofFn y).getD (ix k i) false
  have layoutZ : (List.range 10).map (fun i => (List.ofFn y).getD (ix k i) false) = List.ofFn z := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,z]
  rw [layoutZ]
  change R.eval (Q.wires (P.wires _))=_
  rw [←piece]
  exact (computes _ guard).trans value

import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

set_option maxRecDepth 16000 in
set_option maxHeartbeats 9000000 in
theorem PEqualNP.Outside.R_meta_8225_742
    (ownership : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      AndOrOnly C → circuitFun n C = graphFun G ∅ → EveryEdgeOwned n G C)
    (small :
      let G := edgeGraph 26 ((List.finRange 13).flatMap fun l =>
      ([0, 1, 3, 9] : List (Fin 13)).map fun s => ((l + s).val, 13 + l.val))
      let valid := fun (C : Circuit) => ∀ i g, C.gates[i]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+i ∧ b < 26+i
      ∀ C : Circuit, valid C → circuitFun 26 C = graphFun G ∅ → C.size < 64 →
        ∃ D : Circuit, valid D ∧ circuitFun 26 D = graphFun G ∅ ∧ D.size ≤ C.size ∧
          HasStarProfile 26 G D) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) ∧ x4.size ≤ x1.size ∧ ∃ (x5 : SimpleGraph (Fin (26 : ℕ))), x5 = PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x6 : Fin (13 : ℕ)) => List.map (fun (x7 : Fin (13 : ℕ)) => (↑x6, (13 : ℕ) + ↑x7)) (List.filter (fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)))) (List.finRange (13 : ℕ)))) (List.finRange (13 : ℕ))) ∧ PEqualNP.EdgeOwnership.HasStarProfile (26 : ℕ) x5 x4 ∧ PEqualNP.EdgeOwnership.EveryEdgeOwned (26 : ℕ) x5 x4 := by
  intro C hvalid hc
  let G := edgeGraph 26 ((List.finRange 13).flatMap fun l =>
      ([0, 1, 3, 9] : List (Fin 13)).map fun s => ((l + s).val, 13 + l.val))
  let G' := edgeGraph 26 ((List.finRange 13).flatMap fun p =>
    ((List.finRange 13).filter fun l => decide (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9)).map
      fun l => (p.val,13+l.val))
  let valid := fun (D : Circuit) => ∀ i g, D.gates[i]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+i ∧ b < 26+i
  let target (x : Fin 26 → Bool) :=
    ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  have same : G = G' := by
    apply SimpleGraph.ext
    have h : ∀ u v : Fin 26, G.Adj u v ↔ G'.Adj u v := by decide +kernel
    funext u v
    exact propext (h u v)
  have bip : ∀ u v : Fin 26, G.Adj u v →
      (u.val < 13 ∧ 13 ≤ v.val) ∨ (v.val < 13 ∧ 13 ≤ u.val) := by decide +kernel
  have incidence : ∀ p l : Fin 13, G.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 l) ↔
      (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) := by decide +kernel
  have oriented (x : Fin 26 → Bool) {u v : Fin 26} (adj : G.Adj u v)
      (hu : u.val < 13) (hv : 13 ≤ v.val) (xu : x u = true) (xv : x v = true) : target x := by
    let p : Fin 13 := ⟨u.val,hu⟩
    let l : Fin 13 := ⟨v.val-13,by omega⟩
    have ep : Fin.castAdd 13 p = u := Fin.ext rfl
    have el : Fin.natAdd 13 l = v := Fin.ext (by change 13 + (v.val-13) = v.val; omega)
    have h : G.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 l) := by rw [ep,el]; exact adj
    exact ⟨p,l,(incidence p l).mp h,ep ▸ xu,el ▸ xv⟩
  have wireTarget (x : Fin 26 → Bool) : graphFun G ∅ x = true ↔ target x := by
    unfold graphFun
    simp only [Finset.notMem_empty,false_and,exists_const,decide_false,Bool.false_or,
      decide_eq_true_eq]
    constructor
    · rintro ⟨u,v,adj,hu,hv⟩
      rcases bip u v adj with h | h
      · exact oriented x adj h.1 h.2 hu hv
      · exact oriented x adj.symm h.1 h.2 hv hu
    · rintro ⟨p,l,adj,hp,hl⟩
      exact ⟨_,_,(incidence p l).2 adj,hp,hl⟩
  have hcorrect : circuitFun 26 C = graphFun G ∅ := by
    funext x
    exact Bool.eq_iff_iff.mpr ((hc x).trans (wireTarget x).symm)
  have finish (D : Circuit) (wf : valid D) (correct : circuitFun 26 D = graphFun G ∅)
      (budget : D.size ≤ C.size) (star : HasStarProfile 26 G D) :
      valid D ∧ (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔ target x) ∧
        D.size ≤ C.size ∧ ∃ K, K = G' ∧ HasStarProfile 26 K D ∧ EveryEdgeOwned 26 K D := by
    have ops : AndOrOnly D := by
      intro g hg
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hg
      apply (wf i g _).1
      rw [List.getElem?_eq_getElem hi, he]
    have owns : EveryEdgeOwned 26 G D := ownership 26 G D ops correct
    have eval : ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔ target x := by
      intro x
      change circuitFun 26 D x = true ↔ _
      rw [correct]
      exact wireTarget x
    exact And.intro wf (And.intro eval (And.intro budget
      (Exists.intro G (And.intro same (And.intro star owns)))))
  by_cases short : C.size < 64
  · obtain ⟨D,wf,f,b,s⟩ := small C hvalid hcorrect short
    exact ⟨D, finish D wf f b s⟩
  let T : Circuit :=
    ⟨[⟨.or,[0,1]⟩, ⟨.or,[26,3]⟩, ⟨.or,[27,9]⟩, ⟨.and,[28,13]⟩,
      ⟨.or,[1,2]⟩, ⟨.or,[30,4]⟩, ⟨.or,[31,10]⟩, ⟨.and,[32,14]⟩,
      ⟨.or,[2,3]⟩, ⟨.or,[34,5]⟩, ⟨.or,[35,11]⟩, ⟨.and,[36,15]⟩,
      ⟨.or,[3,4]⟩, ⟨.or,[38,6]⟩, ⟨.or,[39,12]⟩, ⟨.and,[40,16]⟩,
      ⟨.or,[4,5]⟩, ⟨.or,[42,7]⟩, ⟨.or,[43,0]⟩, ⟨.and,[44,17]⟩,
      ⟨.or,[5,6]⟩, ⟨.or,[46,8]⟩, ⟨.or,[47,1]⟩, ⟨.and,[48,18]⟩,
      ⟨.or,[6,7]⟩, ⟨.or,[50,9]⟩, ⟨.or,[51,2]⟩, ⟨.and,[52,19]⟩,
      ⟨.or,[7,8]⟩, ⟨.or,[54,10]⟩, ⟨.or,[55,3]⟩, ⟨.and,[56,20]⟩,
      ⟨.or,[8,9]⟩, ⟨.or,[58,11]⟩, ⟨.or,[59,4]⟩, ⟨.and,[60,21]⟩,
      ⟨.or,[9,10]⟩, ⟨.or,[62,12]⟩, ⟨.or,[63,5]⟩, ⟨.and,[64,22]⟩,
      ⟨.or,[10,11]⟩, ⟨.or,[66,0]⟩, ⟨.or,[67,6]⟩, ⟨.and,[68,23]⟩,
      ⟨.or,[11,12]⟩, ⟨.or,[70,1]⟩, ⟨.or,[71,7]⟩, ⟨.and,[72,24]⟩,
      ⟨.or,[12,0]⟩, ⟨.or,[74,2]⟩, ⟨.or,[75,8]⟩, ⟨.and,[76,25]⟩,
      ⟨.or,[29,33]⟩, ⟨.or,[78,37]⟩, ⟨.or,[79,41]⟩, ⟨.or,[80,45]⟩,
      ⟨.or,[81,49]⟩, ⟨.or,[82,53]⟩, ⟨.or,[83,57]⟩, ⟨.or,[84,61]⟩,
      ⟨.or,[85,65]⟩, ⟨.or,[86,69]⟩, ⟨.or,[87,73]⟩, ⟨.or,[88,77]⟩], 89⟩
  have cardT : T.size = 64 := rfl
  let _ := gateOpDecEq
  have closedInputs : ∀ j : Fin 64,
      let g := gateAt T j.val
      let a := g.inputs.getD 0 0
      let b := g.inputs.getD 1 0
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j.val ∧ b < 26+j.val := by decide
  have validT : valid T := by
    intro i g hg
    have h : i < T.gates.length := List.getElem?_eq_some_iff.mp hg |>.1
    have hi : i < 64 := by exact h
    have eq : gateAt T i = g := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD,hg]
      rfl
    have a := closedInputs ⟨i,hi⟩
    dsimp only at a
    rw [eq] at a
    exact ⟨a.1,_,_,a.2⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let partialWires (i : ℕ) (x : Fin 26 → Bool) := (T.gates.take i).foldl step (List.ofFn x)
  let v26 (x : Fin 26 → Bool) := x 0 || (x 1 || false)
  let v27 (x : Fin 26 → Bool) := v26 x || (x 3 || false)
  let v28 (x : Fin 26 → Bool) := v27 x || (x 9 || false)
  let v29 (x : Fin 26 → Bool) := v28 x && (x 13 && true)
  let v30 (x : Fin 26 → Bool) := x 1 || (x 2 || false)
  let v31 (x : Fin 26 → Bool) := v30 x || (x 4 || false)
  let v32 (x : Fin 26 → Bool) := v31 x || (x 10 || false)
  let v33 (x : Fin 26 → Bool) := v32 x && (x 14 && true)
  let v34 (x : Fin 26 → Bool) := x 2 || (x 3 || false)
  let v35 (x : Fin 26 → Bool) := v34 x || (x 5 || false)
  let v36 (x : Fin 26 → Bool) := v35 x || (x 11 || false)
  let v37 (x : Fin 26 → Bool) := v36 x && (x 15 && true)
  let v38 (x : Fin 26 → Bool) := x 3 || (x 4 || false)
  let v39 (x : Fin 26 → Bool) := v38 x || (x 6 || false)
  let v40 (x : Fin 26 → Bool) := v39 x || (x 12 || false)
  let v41 (x : Fin 26 → Bool) := v40 x && (x 16 && true)
  let v42 (x : Fin 26 → Bool) := x 4 || (x 5 || false)
  let v43 (x : Fin 26 → Bool) := v42 x || (x 7 || false)
  let v44 (x : Fin 26 → Bool) := v43 x || (x 0 || false)
  let v45 (x : Fin 26 → Bool) := v44 x && (x 17 && true)
  let v46 (x : Fin 26 → Bool) := x 5 || (x 6 || false)
  let v47 (x : Fin 26 → Bool) := v46 x || (x 8 || false)
  let v48 (x : Fin 26 → Bool) := v47 x || (x 1 || false)
  let v49 (x : Fin 26 → Bool) := v48 x && (x 18 && true)
  let v50 (x : Fin 26 → Bool) := x 6 || (x 7 || false)
  let v51 (x : Fin 26 → Bool) := v50 x || (x 9 || false)
  let v52 (x : Fin 26 → Bool) := v51 x || (x 2 || false)
  let v53 (x : Fin 26 → Bool) := v52 x && (x 19 && true)
  let v54 (x : Fin 26 → Bool) := x 7 || (x 8 || false)
  let v55 (x : Fin 26 → Bool) := v54 x || (x 10 || false)
  let v56 (x : Fin 26 → Bool) := v55 x || (x 3 || false)
  let v57 (x : Fin 26 → Bool) := v56 x && (x 20 && true)
  let v58 (x : Fin 26 → Bool) := x 8 || (x 9 || false)
  let v59 (x : Fin 26 → Bool) := v58 x || (x 11 || false)
  let v60 (x : Fin 26 → Bool) := v59 x || (x 4 || false)
  let v61 (x : Fin 26 → Bool) := v60 x && (x 21 && true)
  let v62 (x : Fin 26 → Bool) := x 9 || (x 10 || false)
  let v63 (x : Fin 26 → Bool) := v62 x || (x 12 || false)
  let v64 (x : Fin 26 → Bool) := v63 x || (x 5 || false)
  let v65 (x : Fin 26 → Bool) := v64 x && (x 22 && true)
  let v66 (x : Fin 26 → Bool) := x 10 || (x 11 || false)
  let v67 (x : Fin 26 → Bool) := v66 x || (x 0 || false)
  let v68 (x : Fin 26 → Bool) := v67 x || (x 6 || false)
  let v69 (x : Fin 26 → Bool) := v68 x && (x 23 && true)
  let v70 (x : Fin 26 → Bool) := x 11 || (x 12 || false)
  let v71 (x : Fin 26 → Bool) := v70 x || (x 1 || false)
  let v72 (x : Fin 26 → Bool) := v71 x || (x 7 || false)
  let v73 (x : Fin 26 → Bool) := v72 x && (x 24 && true)
  let v74 (x : Fin 26 → Bool) := x 12 || (x 0 || false)
  let v75 (x : Fin 26 → Bool) := v74 x || (x 2 || false)
  let v76 (x : Fin 26 → Bool) := v75 x || (x 8 || false)
  let v77 (x : Fin 26 → Bool) := v76 x && (x 25 && true)
  let v78 (x : Fin 26 → Bool) := v29 x || (v33 x || false)
  let v79 (x : Fin 26 → Bool) := v78 x || (v37 x || false)
  let v80 (x : Fin 26 → Bool) := v79 x || (v41 x || false)
  let v81 (x : Fin 26 → Bool) := v80 x || (v45 x || false)
  let v82 (x : Fin 26 → Bool) := v81 x || (v49 x || false)
  let v83 (x : Fin 26 → Bool) := v82 x || (v53 x || false)
  let v84 (x : Fin 26 → Bool) := v83 x || (v57 x || false)
  let v85 (x : Fin 26 → Bool) := v84 x || (v61 x || false)
  let v86 (x : Fin 26 → Bool) := v85 x || (v65 x || false)
  let v87 (x : Fin 26 → Bool) := v86 x || (v69 x || false)
  let v88 (x : Fin 26 → Bool) := v87 x || (v73 x || false)
  let v89 (x : Fin 26 → Bool) := v88 x || (v77 x || false)
  let bank4 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x]
  have wires4 (x : Fin 26 → Bool) : partialWires 4 x = bank4 x := rfl

  let bank8 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x]
  have wires8 (x : Fin 26 → Bool) : partialWires 8 x = bank8 x := by
    have split : T.gates.take 8 = T.gates.take 4 ++ (T.gates.drop 4).take 4 := rfl
    change ((T.gates.take 8).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 4).take 4).foldl step (partialWires 4 x) = _
    rw [wires4]
    rfl

  let bank12 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x]
  have wires12 (x : Fin 26 → Bool) : partialWires 12 x = bank12 x := by
    have split : T.gates.take 12 = T.gates.take 8 ++ (T.gates.drop 8).take 4 := rfl
    change ((T.gates.take 12).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 8).take 4).foldl step (partialWires 8 x) = _
    rw [wires8]
    rfl

  let bank16 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x]
  have wires16 (x : Fin 26 → Bool) : partialWires 16 x = bank16 x := by
    have split : T.gates.take 16 = T.gates.take 12 ++ (T.gates.drop 12).take 4 := rfl
    change ((T.gates.take 16).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 12).take 4).foldl step (partialWires 12 x) = _
    rw [wires12]
    rfl

  let bank20 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x]
  have wires20 (x : Fin 26 → Bool) : partialWires 20 x = bank20 x := by
    have split : T.gates.take 20 = T.gates.take 16 ++ (T.gates.drop 16).take 4 := rfl
    change ((T.gates.take 20).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 16).take 4).foldl step (partialWires 16 x) = _
    rw [wires16]
    rfl

  let bank24 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x]
  have wires24 (x : Fin 26 → Bool) : partialWires 24 x = bank24 x := by
    have split : T.gates.take 24 = T.gates.take 20 ++ (T.gates.drop 20).take 4 := rfl
    change ((T.gates.take 24).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 20).take 4).foldl step (partialWires 20 x) = _
    rw [wires20]
    rfl

  let bank28 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x]
  have wires28 (x : Fin 26 → Bool) : partialWires 28 x = bank28 x := by
    have split : T.gates.take 28 = T.gates.take 24 ++ (T.gates.drop 24).take 4 := rfl
    change ((T.gates.take 28).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 24).take 4).foldl step (partialWires 24 x) = _
    rw [wires24]
    rfl

  let bank32 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x]
  have wires32 (x : Fin 26 → Bool) : partialWires 32 x = bank32 x := by
    have split : T.gates.take 32 = T.gates.take 28 ++ (T.gates.drop 28).take 4 := rfl
    change ((T.gates.take 32).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 28).take 4).foldl step (partialWires 28 x) = _
    rw [wires28]
    rfl

  let bank36 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x]
  have wires36 (x : Fin 26 → Bool) : partialWires 36 x = bank36 x := by
    have split : T.gates.take 36 = T.gates.take 32 ++ (T.gates.drop 32).take 4 := rfl
    change ((T.gates.take 36).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 32).take 4).foldl step (partialWires 32 x) = _
    rw [wires32]
    rfl

  let bank40 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x]
  have wires40 (x : Fin 26 → Bool) : partialWires 40 x = bank40 x := by
    have split : T.gates.take 40 = T.gates.take 36 ++ (T.gates.drop 36).take 4 := rfl
    change ((T.gates.take 40).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 36).take 4).foldl step (partialWires 36 x) = _
    rw [wires36]
    rfl

  let bank44 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x]
  have wires44 (x : Fin 26 → Bool) : partialWires 44 x = bank44 x := by
    have split : T.gates.take 44 = T.gates.take 40 ++ (T.gates.drop 40).take 4 := rfl
    change ((T.gates.take 44).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 40).take 4).foldl step (partialWires 40 x) = _
    rw [wires40]
    rfl

  let bank48 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x]
  have wires48 (x : Fin 26 → Bool) : partialWires 48 x = bank48 x := by
    have split : T.gates.take 48 = T.gates.take 44 ++ (T.gates.drop 44).take 4 := rfl
    change ((T.gates.take 48).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 44).take 4).foldl step (partialWires 44 x) = _
    rw [wires44]
    rfl

  let bank52 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x]
  have wires52 (x : Fin 26 → Bool) : partialWires 52 x = bank52 x := by
    have split : T.gates.take 52 = T.gates.take 48 ++ (T.gates.drop 48).take 4 := rfl
    change ((T.gates.take 52).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 48).take 4).foldl step (partialWires 48 x) = _
    rw [wires48]
    rfl

  let bank56 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x]
  have wires56 (x : Fin 26 → Bool) : partialWires 56 x = bank56 x := by
    have split : T.gates.take 56 = T.gates.take 52 ++ (T.gates.drop 52).take 4 := rfl
    change ((T.gates.take 56).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 52).take 4).foldl step (partialWires 52 x) = _
    rw [wires52]
    rfl

  let bank60 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x, v82 x, v83 x, v84 x, v85 x]
  have wires60 (x : Fin 26 → Bool) : partialWires 60 x = bank60 x := by
    have split : T.gates.take 60 = T.gates.take 56 ++ (T.gates.drop 56).take 4 := rfl
    change ((T.gates.take 60).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 56).take 4).foldl step (partialWires 56 x) = _
    rw [wires56]
    rfl

  let bank64 (x : Fin 26 → Bool) := List.ofFn x ++ [v26 x, v27 x, v28 x, v29 x, v30 x, v31 x, v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x, v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x, v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x, v80 x, v81 x, v82 x, v83 x, v84 x, v85 x, v86 x, v87 x, v88 x, v89 x]
  have wires64 (x : Fin 26 → Bool) : partialWires 64 x = bank64 x := by
    have split : T.gates.take 64 = T.gates.take 60 ++ (T.gates.drop 60).take 4 := rfl
    change ((T.gates.take 64).foldl step (List.ofFn x)) = _
    rw [split,List.foldl_append]
    change ((T.gates.drop 60).take 4).foldl step (partialWires 60 x) = _
    rw [wires60]
    rfl

  have wires (x : Fin 26 → Bool) : T.wires (List.ofFn x) = bank64 x :=
    wires64 x
  have evalT (x : Fin 26 → Bool) :
      T.eval (List.ofFn x) = ((((((((((((((((x 0 || x 1) || x 3) || x 9) && x 13) ||
      ((((x 1 || x 2) || x 4) || x 10) && x 14)) ||
      ((((x 2 || x 3) || x 5) || x 11) && x 15)) ||
      ((((x 3 || x 4) || x 6) || x 12) && x 16)) ||
      ((((x 4 || x 5) || x 7) || x 0) && x 17)) ||
      ((((x 5 || x 6) || x 8) || x 1) && x 18)) ||
      ((((x 6 || x 7) || x 9) || x 2) && x 19)) ||
      ((((x 7 || x 8) || x 10) || x 3) && x 20)) ||
      ((((x 8 || x 9) || x 11) || x 4) && x 21)) ||
      ((((x 9 || x 10) || x 12) || x 5) && x 22)) ||
      ((((x 10 || x 11) || x 0) || x 6) && x 23)) ||
      ((((x 11 || x 12) || x 1) || x 7) && x 24)) ||
      ((((x 12 || x 0) || x 2) || x 8) && x 25)) := by
    unfold Circuit.eval
    rw [wires]
    change ((((((((((((((((x 0 || (x 1 || false)) || (x 3 || false)) || (x 9 || false)) && (x 13 && true)) || (((((x 1 || (x 2 || false)) || (x 4 || false)) || (x 10 || false)) && (x 14 && true)) || false)) || (((((x 2 || (x 3 || false)) || (x 5 || false)) || (x 11 || false)) && (x 15 && true)) || false)) || (((((x 3 || (x 4 || false)) || (x 6 || false)) || (x 12 || false)) && (x 16 && true)) || false)) || (((((x 4 || (x 5 || false)) || (x 7 || false)) || (x 0 || false)) && (x 17 && true)) || false)) || (((((x 5 || (x 6 || false)) || (x 8 || false)) || (x 1 || false)) && (x 18 && true)) || false)) || (((((x 6 || (x 7 || false)) || (x 9 || false)) || (x 2 || false)) && (x 19 && true)) || false)) || (((((x 7 || (x 8 || false)) || (x 10 || false)) || (x 3 || false)) && (x 20 && true)) || false)) || (((((x 8 || (x 9 || false)) || (x 11 || false)) || (x 4 || false)) && (x 21 && true)) || false)) || (((((x 9 || (x 10 || false)) || (x 12 || false)) || (x 5 || false)) && (x 22 && true)) || false)) || (((((x 10 || (x 11 || false)) || (x 0 || false)) || (x 6 || false)) && (x 23 && true)) || false)) || (((((x 11 || (x 12 || false)) || (x 1 || false)) || (x 7 || false)) && (x 24 && true)) || false)) || (((((x 12 || (x 0 || false)) || (x 2 || false)) || (x 8 || false)) && (x 25 && true)) || false)) = _
    simp only [Bool.or_false,Bool.and_true]
  have targetExpand (x : Fin 26 → Bool) :
      target x ↔ ((((((((((((((((x 0 || x 1) || x 3) || x 9) && x 13) ||
      ((((x 1 || x 2) || x 4) || x 10) && x 14)) ||
      ((((x 2 || x 3) || x 5) || x 11) && x 15)) ||
      ((((x 3 || x 4) || x 6) || x 12) && x 16)) ||
      ((((x 4 || x 5) || x 7) || x 0) && x 17)) ||
      ((((x 5 || x 6) || x 8) || x 1) && x 18)) ||
      ((((x 6 || x 7) || x 9) || x 2) && x 19)) ||
      ((((x 7 || x 8) || x 10) || x 3) && x 20)) ||
      ((((x 8 || x 9) || x 11) || x 4) && x 21)) ||
      ((((x 9 || x 10) || x 12) || x 5) && x 22)) ||
      ((((x 10 || x 11) || x 0) || x 6) && x 23)) ||
      ((((x 11 || x 12) || x 1) || x 7) && x 24)) ||
      ((((x 12 || x 0) || x 2) || x 8) && x 25)) = true := by
    let left (l : Fin 13) :=
      x (Fin.castAdd 13 l) = true ∨ x (Fin.castAdd 13 (l+1)) = true ∨
        x (Fin.castAdd 13 (l+3)) = true ∨ x (Fin.castAdd 13 (l+9)) = true
    have left_iff (l : Fin 13) :
        (∃ p : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true) ↔ left l := by
      simp only [left,or_and_right,exists_or,exists_eq_left]
    have grouped : target x ↔ ∃ l, left l ∧ x (Fin.natAdd 13 l) = true := by
      constructor
      · rintro ⟨p,l,h,hp,hl⟩
        exact ⟨l,(left_iff l).1 ⟨p,h,hp⟩,hl⟩
      · rintro ⟨l,h,hl⟩
        obtain ⟨p,inc,hp⟩ := (left_iff l).2 h
        exact ⟨p,l,inc,hp,hl⟩
    rw [grouped]
    simp only [Fin.exists_fin_succ,Fin.exists_fin_zero,or_false,left,Bool.or_eq_true,
      Bool.and_eq_true,or_assoc]
    rfl
  have correctT : circuitFun 26 T = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change T.eval (List.ofFn x) = true ↔ _
    rw [evalT]
    exact (targetExpand x).symm.trans (wireTarget x).symm
  have gateIsAnd : ∀ j : Fin 64, (gateAt T j.val).op = GateOp.and →
      j.val ∈ ([3,7,11,15,19,23,27,31,35,39,43,47,51] : List ℕ) := by decide
  have firesCenter (j : ℕ) (hj : j ∈ ([3,7,11,15,19,23,27,31,35,39,43,47,51] : List ℕ)) (x : Fin 26 → Bool)
      (fire : gateVal 26 T j x = true) : x (⟨13+j/4,by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide⟩ : Fin 26) = true := by
    change (T.wires (List.ofFn x)).getD (26+j) false = true at fire
    rw [wires] at fire
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change ((((x 0 || (x 1 || false)) || (x 3 || false)) || (x 9 || false)) && (x 13 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 1 || (x 2 || false)) || (x 4 || false)) || (x 10 || false)) && (x 14 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 2 || (x 3 || false)) || (x 5 || false)) || (x 11 || false)) && (x 15 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 3 || (x 4 || false)) || (x 6 || false)) || (x 12 || false)) && (x 16 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 4 || (x 5 || false)) || (x 7 || false)) || (x 0 || false)) && (x 17 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 5 || (x 6 || false)) || (x 8 || false)) || (x 1 || false)) && (x 18 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 6 || (x 7 || false)) || (x 9 || false)) || (x 2 || false)) && (x 19 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 7 || (x 8 || false)) || (x 10 || false)) || (x 3 || false)) && (x 20 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 8 || (x 9 || false)) || (x 11 || false)) || (x 4 || false)) && (x 21 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 9 || (x 10 || false)) || (x 12 || false)) || (x 5 || false)) && (x 22 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 10 || (x 11 || false)) || (x 0 || false)) || (x 6 || false)) && (x 23 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 11 || (x 12 || false)) || (x 1 || false)) || (x 7 || false)) && (x 24 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
    · change ((((x 12 || (x 0 || false)) || (x 2 || false)) || (x 8 || false)) && (x 25 && true)) = true at fire
      simp only [Bool.and_true] at fire
      exact (Bool.and_eq_true_iff.mp fire).2
  have starT : HasStarProfile 26 G T := by
    intro j hj hand
    have indices := gateIsAnd ⟨j,by exact hj⟩ hand
    right
    let c : Fin 26 := ⟨13+j/4,by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at indices
      rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide⟩
    refine ⟨c,fun u v _ owner => ?_⟩
    have h : pairInput u v c = true := firesCenter j indices (pairInput u v) owner.2.2.1
    exact (of_decide_eq_true h).imp Eq.symm Eq.symm
  exact ⟨T, finish T validT correctT (by omega) starT⟩

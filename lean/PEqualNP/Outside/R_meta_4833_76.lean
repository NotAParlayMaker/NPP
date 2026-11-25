import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4833_76
    (fixing :
      let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (i : Fin 11) (C : PEqualNP.CircuitLowerBounds.Circuit), i.val < 4 →
      PEqualNP.TopForm.IsAO2 11 C →
      (∀ x : Fin 11 → Bool, x i = false →
        PEqualNP.MetaComplexity.circuitFun 11 C x = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) →
      let W := C.wires [false,false,false,false,true,true,true,true,true,true,true]
      let k := (C.gates.filter (fun g => g.inputs.any (fun a => !(W.getD a false)))).length
      11 + k ≤ C.size)
    (few :
      let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (i : Fin 11) (C : PEqualNP.CircuitLowerBounds.Circuit), i.val < 4 →
      PEqualNP.TopForm.IsAO2 11 C →
      (∀ x : Fin 11 → Bool, x i = false →
        PEqualNP.MetaComplexity.circuitFun 11 C x = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) →
      let W := C.wires [false,false,false,false,true,true,true,true,true,true,true]
      let k := (C.gates.filter (fun g => g.inputs.any (fun a => !(W.getD a false)))).length
      k ≤ 7 → 19 ≤ C.size) :
  let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (19 : ℕ) ≤ x3.size := by
  intro G i C hi ao yes
  have lower := fixing i C hi ao yes
  have rest := few i C hi ao yes
  dsimp only at lower rest
  omega

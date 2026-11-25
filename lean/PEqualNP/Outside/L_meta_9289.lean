import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9289

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def targetCircuit : Circuit where
  gates :=
    [ ⟨GateOp.or, [4, 8]⟩
    , ⟨GateOp.or, [1, 11]⟩
    , ⟨GateOp.or, [5, 10]⟩
    , ⟨GateOp.or, [2, 7]⟩
    , ⟨GateOp.or, [0, 3]⟩
    , ⟨GateOp.and, [6, 16]⟩
    , ⟨GateOp.and, [9, 16]⟩
    , ⟨GateOp.or, [13, 14]⟩
    , ⟨GateOp.or, [12, 15]⟩
    , ⟨GateOp.or, [0, 19]⟩
    , ⟨GateOp.or, [3, 20]⟩
    , ⟨GateOp.or, [6, 13]⟩
    , ⟨GateOp.or, [9, 12]⟩
    , ⟨GateOp.or, [18, 23]⟩
    , ⟨GateOp.or, [17, 24]⟩
    , ⟨GateOp.or, [14, 26]⟩
    , ⟨GateOp.or, [15, 25]⟩
    , ⟨GateOp.and, [27, 28]⟩
    , ⟨GateOp.and, [21, 22]⟩
    , ⟨GateOp.or, [29, 30]⟩
    ]
  output := 31

lemma targetCircuit_monotone : Monotone2 targetCircuit := by
  simp [Monotone2, targetCircuit]

lemma targetCircuit_size : targetCircuit.size ≤ 22 := by
  decide

lemma targetCircuit_represents :
    Represents (fun u v : Fin 6 => (42746759055 : ℕ).testBit (6 * u.val + v.val)) targetCircuit := by
  decide

end PEqualNP.Outside.L_meta_9289

theorem PEqualNP.Outside.L_meta_9289 :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 6 => (42746759055 : ℕ).testBit (6 * u.val + v.val)) 22 :=
  ⟨PEqualNP.Outside.L_meta_9289.targetCircuit,
    PEqualNP.Outside.L_meta_9289.targetCircuit_monotone,
    PEqualNP.Outside.L_meta_9289.targetCircuit_size,
    PEqualNP.Outside.L_meta_9289.targetCircuit_represents⟩

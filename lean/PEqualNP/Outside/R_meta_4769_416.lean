import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.R_meta_4769_416
    (compile : let step := fun (W : List ℕ) (g : Bool × Fin 40 × Fin 40) =>
        let a := W.getD g.2.1.val 0
        let b := W.getD g.2.2.val 0
        W ++ [if g.1 then a ||| b else a &&& b]
    ∀ (A : List ℕ) (P : List (Bool × Fin 40 × Fin 40)) (t : ℕ), t ∈ P.foldl step A →
      ∃ C : Circuit, Monotone2 C ∧ C.size = P.length ∧
        ∀ j : ℕ, C.eval (A.map fun k => k.testBit j) = t.testBit j)
    (synth : ∃ P : List (Bool × Fin 40 × Fin 40), P.length ≤ 22 ∧
      (524287 : ℕ) ∈ P.foldl (fun (W : List ℕ) (g : Bool × Fin 40 × Fin 40) =>
        let a := W.getD g.2.1.val 0
        let b := W.getD g.2.2.val 0
        W ++ [if g.1 then a ||| b else a &&& b]) [66039408500993, 34907293144846346, 1059587756802128, 192904318583080068, 116192899568831008, 360991657631416327, 432398340785700920, 382849987448406208, 306845143544201216, 460213923392520960, 573149364730593280, 383556429357777920, 460267715261630464, 575268812979699712, 541553459158061056, 575334852396605440, 576460750156333056, 576460752270360576]) :
    have x1 : List ℕ → ℕ → Fin (18 : ℕ) → Bool := fun (x1 : List ℕ) (x2 : ℕ) (x3 : Fin (18 : ℕ)) => (x1.getD (x2 / (3 : ℕ)) (0 : ℕ)).testBit ((18 : ℕ) * (x2 % (3 : ℕ)) + ↑x3); ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (22 : ℕ) ∧ (∀ (x3 : Fin (19 : ℕ)), PEqualNP.MetaComplexity.circuitFun (18 : ℕ) x2 (x1 [(2748787982369 : ℕ), (5497575964738 : ℕ), (35253127217284 : ℕ), (282575027307024 : ℕ), (2252083281805314 : ℕ), (13581476935368968 : ℕ), (204801 : ℕ)] ↑x3) = Bool.true) ∧ ∀ (x3 : Fin (40 : ℕ)), PEqualNP.MetaComplexity.circuitFun (18 : ℕ) x2 (x1 [(150839794335775 : ℕ), (422694713036815 : ℕ), (10135127528966407 : ℕ), (10573287142082581 : ℕ), (13723262631478299 : ℕ), (14075863940142091 : ℕ), (14216052114924046 : ℕ), (14708841020862478 : ℕ), (15160192239357073 : ℕ), (15517191257677852 : ℕ), (16327395760634660 : ℕ), (16879903704853650 : ℕ), (17843491875054616 : ℕ), (262112 : ℕ)] ↑x3) = Bool.false := by
  intro data
  let A : List ℕ := [66039408500993, 34907293144846346, 1059587756802128, 192904318583080068, 116192899568831008, 360991657631416327, 432398340785700920, 382849987448406208, 306845143544201216, 460213923392520960, 573149364730593280, 383556429357777920, 460267715261630464, 575268812979699712, 541553459158061056, 575334852396605440, 576460750156333056, 576460752270360576]
  obtain ⟨P,hP,hmem⟩ := synth
  obtain ⟨C,hC,hs,hval⟩ := compile A P 524287 hmem
  refine ⟨C,hC,by omega,?_,?_⟩
  · have eqP : ∀ j : Fin 19, A.map (fun a => a.testBit j.val) = List.ofFn (data [2748787982369,5497575964738,35253127217284,282575027307024,2252083281805314,13581476935368968,204801] j.val) := by
      dsimp only [A,data]
      decide +kernel
    have expected : ∀ j : Fin 19, (524287 : ℕ).testBit j.val = true := by decide +kernel
    intro j
    change C.eval (List.ofFn _) = true
    simpa only [eqP j, expected j] using hval j.val
  · have eqN : ∀ j : Fin 40, A.map (fun a => a.testBit (j.val+19)) = List.ofFn (data [150839794335775,422694713036815,10135127528966407,10573287142082581,13723262631478299,14075863940142091,14216052114924046,14708841020862478,15160192239357073,15517191257677852,16327395760634660,16879903704853650,17843491875054616,262112] j.val) := by
      dsimp only [A,data]
      decide +kernel
    have expected : ∀ j : Fin 40, (524287 : ℕ).testBit (j.val+19) = false := by decide +kernel
    intro j
    change C.eval (List.ofFn _) = false
    simpa only [eqN j, expected j] using hval (j.val+19)

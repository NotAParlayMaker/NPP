import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_7893_1
    (plain : ∀ C : Circuit, IsAO2 10 C → C.size ≤ 18 →
      (∀ p ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ), circuitFun 10 C (fun i => p.testBit i.val) = true) →
      ∃ n ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ), circuitFun 10 C (fun i => n.testBit i.val) = true)
    (rename : ∀ (C : Circuit) (w : ℕ) (σ : Fin 10 → Fin 10), Function.Injective σ → σ 0 = 0 →
      IsAO2 10 C → w ≠ 0 → w < 10+C.size →
      (∀ j g, 10+j ≤ w → C.gates[j]? = some g → 0 ∉ g.inputs) →
      ∃ (D : Circuit) (v : ℕ), IsAO2 10 D ∧ D.size = C.size ∧ v ≠ 0 ∧ v < 10+D.size ∧
        (∀ j g, 10+j ≤ v → D.gates[j]? = some g → 0 ∉ g.inputs) ∧
        ∀ x : Fin 10 → Bool, circuitFun 10 D x = circuitFun 10 C (x ∘ σ) ∧
          (D.wires (List.ofFn x)).getD v false = (C.wires (List.ofFn (x ∘ σ))).getD w false)
    (active : ∀ (C : Circuit) (w : ℕ), IsAO2 10 C → 16 ≤ C.size ∧ C.size ≤ 18 →
      (w ≠ 0 ∧ w < 10+C.size ∧ ∀ j g, 10+j ≤ w → C.gates[j]? = some g → 0 ∉ g.inputs) →
      let b := fun (n : ℕ) (i : Fin 10) => n.testBit i.val
      let f := fun n => (C.wires (List.ofFn (Function.update (b n) 0 false))).getD w false
      (f 6 = true ∨ f 12 = true) →
      (∀ n ∈ ([50, 104, 116, 138, 208, 276, 402, 548, 554, 770] : List ℕ), f n = false) →
      (∀ n ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ), circuitFun 10 C (b n) = false) →
      ∃ p ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ), circuitFun 10 C (Function.update (b p) 0 (b p 0 || f p)) = false) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 →     (16 : ℕ) ≤ x1.size ∧ x1.size ≤ (18 : ℕ) →       (x2 ≠ (0 : ℕ) ∧ x2 < (10 : ℕ) + x1.size ∧ ∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), (10 : ℕ) + x5 ≤ x2 → x1.gates[x5]? = Option.some x6 → (0 : ℕ) ∉ x6.inputs) →         have x6 : ℕ → Fin (10 : ℕ) → Bool := fun (x6 : ℕ) (x7 : Fin (10 : ℕ)) => x6.testBit ↑x7;         have x7 : ℕ → Bool := fun (x7 : ℕ) => (x1.wires (List.ofFn (Function.update (x6 x7) (0 : Fin (10 : ℕ)) Bool.false))).getD x2 Bool.false;         have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 (Function.update (x6 x8) (0 : Fin (10 : ℕ)) (x6 x8 (0 : Fin (10 : ℕ)) || x7 x8));         (∀ x9 ∈ [(50 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ)], x7 x9 = Bool.false) → ¬((∀ x10 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x8 x10 = Bool.true) ∧ ∀ x10 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x8 x10 = Bool.false) := by
  intro C w ok size valid
  let b (n : ℕ) (i : Fin 10) := n.testBit i.val
  let f (n : ℕ) := (C.wires (List.ofFn (Function.update (b n) 0 false))).getD w false
  let aug (n : ℕ) := Function.update (b n) 0 (b n 0 || f n)
  change (∀ r ∈ ([50, 104, 116, 138, 208, 276, 402, 548, 554, 770] : List ℕ), f r = false) → ¬ ((∀ r ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ), circuitFun 10 C (aug r) = true) ∧
    ∀ r ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ), circuitFun 10 C (aug r) = false)
  intro zero good
  have negBits : ∀ r ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ), b r 0 = true ∨ r ∈ ([50, 104, 116, 138, 208, 276, 402, 548, 554, 770] : List ℕ) := by decide +kernel
  have neg (r : ℕ) (hr : r ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ)) : circuitFun 10 C (b r) = false := by
    have eq : aug r = b r := by
      unfold aug
      rcases negBits r hr with h|h
      · simp [h]
      · simp [zero r h]
    rw [← eq]; exact good.2 r hr
  obtain ⟨p,hp,off,hit⟩ : ∃ p ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ), b p 0 = false ∧ f p = true := by
    by_contra! h
    obtain ⟨n,hn,yes⟩ := plain C ok size.2 (fun r hr => by
      have eq : aug r = b r := by
        unfold aug
        cases hb : b r 0 with
        | false => simp [hb,h r hr hb]
        | true => simp [hb]
      change circuitFun 10 C (b r) = true
      rw [← eq]; exact good.1 r hr)
    change circuitFun 10 C (b n) = true at yes
    rw [neg n hn] at yes
    contradiction
  let perms : Fin 12 → (Fin 10 → Fin 10) := ![
    ![0,1,2,3,4,5,6,7,8,9],
    ![0,1,2,7,5,4,6,3,9,8],
    ![0,1,6,8,5,4,2,9,3,7],
    ![0,1,6,9,4,5,2,8,7,3],
    ![0,4,3,2,1,5,9,8,7,6],
    ![0,4,3,8,5,1,9,2,6,7],
    ![0,4,9,6,1,5,3,7,8,2],
    ![0,4,9,7,5,1,3,6,2,8],
    ![0,5,7,2,1,4,8,9,3,6],
    ![0,5,7,9,4,1,8,2,6,3],
    ![0,5,8,3,4,1,7,6,2,9],
    ![0,5,8,6,1,4,7,3,9,2]]
  let code (k : Fin 12) (r : ℕ) : ℕ := ∑ i : Fin 10, if b r (perms k i) then 2^i.val else 0
  have pick : ∀ r ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ), b r 0 = false → ∃ k : Fin 12, code k 6 = r ∨ code k 12 = r := by decide +kernel
  obtain ⟨k,hk⟩ := pick p hp off
  let σ := perms k
  let t := code k
  have cert : ∀ k : Fin 12, Function.Injective (perms k) ∧ perms k 0 = 0 ∧
      (∀ r ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ), code k r ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ)) ∧ (∀ r ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ), code k r ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ)) ∧
      (∀ r ∈ ([50, 104, 116, 138, 208, 276, 402, 548, 554, 770] : List ℕ), code k r ∈ ([50, 104, 116, 138, 208, 276, 402, 548, 554, 770] : List ℕ)) ∧
      (∀ r ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ) ++ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ), ∀ i : Fin 10, b (code k r) i = b r (perms k i)) := by decide +kernel
  obtain ⟨inj,fix,pp,nn,zz,bits⟩ := cert k
  obtain ⟨D,v,okD,szD,nz,lt,reads,eval⟩ :=
    rename C w σ inj fix ok valid.1 valid.2.1 valid.2.2
  have upd (x : Fin 10 → Bool) (a : Bool) :
      (Function.update x 0 a) ∘ σ = Function.update (x ∘ σ) 0 a := by
    funext i
    by_cases hi : i=0
    · subst i; simp [Function.comp_apply,show σ 0=0 from fix]
    · have hn : σ i ≠ 0 := fun h => hi (inj (h.trans fix.symm))
      simp [Function.comp_apply,Function.update_of_ne hi,Function.update_of_ne hn]
  let g (r : ℕ) := (D.wires (List.ofFn (Function.update (b r) 0 false))).getD v false
  have bEq (r : ℕ) (h : r ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ) ++ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ)) : b r ∘ σ = b (t r) := funext (fun i => (bits r h i).symm)
  have wEq (r : ℕ) (h : r ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ) ++ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ)) : g r = f (t r) := by
    unfold g f
    rw [(eval _).2,upd,bEq r h]
  have h6 : 6 ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ) ++ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ) := by decide
  have h12 : 12 ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ) ++ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ) := by decide
  have fires : g 6 = true ∨ g 12 = true := by
    rcases hk with h|h
    · left; rw [wEq _ h6,show t 6=p from h,hit]
    · right; rw [wEq _ h12,show t 12=p from h,hit]
  have zsub : ∀ n ∈ ([50, 104, 116, 138, 208, 276, 402, 548, 554, 770] : List ℕ), n ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ) := by decide
  obtain ⟨a,ha,bad⟩ := active D v okD (szD ▸ size) ⟨nz,lt,reads⟩ fires
    (fun n hn => (wEq n (List.mem_append_right _ (zsub n hn))).trans (zero _ (zz n hn)))
    (fun n hn => by rw [(eval _).1,bEq n (List.mem_append_right _ hn)]; exact neg _ (nn n hn))
  have mem := List.mem_append_left ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ) ha
  change circuitFun 10 D (Function.update (b a) 0 (b a 0 || g a)) = false at bad
  rw [(eval _).1,upd,bEq a mem,wEq a mem] at bad
  have hb : b (t a) 0 = b a 0 := (bits a mem 0).trans (congrArg (b a) fix)
  rw [← hb] at bad
  have yes := good.1 _ (pp a ha)
  change circuitFun 10 C (Function.update (b (t a)) 0 (b (t a) 0 || f (t a))) = true at yes
  simp [yes] at bad

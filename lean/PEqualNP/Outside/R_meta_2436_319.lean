import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The pencil through point 4 has five lines. Its other twenty points form
-- five groups of four. Their subset disjunctions are shared with the affine part.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2436_319 :
    (∃ K : Circuit, Monotone2 K ∧ NestedCover.ReadsBack 44 K ∧ K.size = 27 ∧ K.output = 70 ∧
      let mask := fun (x : Fin 42 → Bool) (m : ℕ) => (List.finRange 21).any (fun i => m.testBit i.val && x (Fin.ofNat 42 i.val))
      let hints := fun x : Fin 42 → Bool => ([3, 81920, 81923, 136, 655360, 655496, 288, 1310720, 1311008, 516, 9216, 9732, 2112, 36864, 38976] : List ℕ).map (mask x)
      let seed := fun x : Fin 42 → Bool => List.ofFn x ++ [x 0 || x 1, x 14 || x 16]
      ∀ x : Fin 42 → Bool, (∃ tail : List Bool, tail.length = 14 ∧ K.wires (seed x) = List.ofFn x ++ hints x ++ tail) ∧
        (K.eval (seed x) = true ↔ ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ v.val ∈ ([21, 24, 25, 30, 32] : List ℕ) ∧ x u = true ∧ x v = true)) →
    (∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 71 D ∧ D.size ≤ 94 ∧ D.output < 71 + D.size ∧
      (∀ i ∈ ([0,1,14,16] : List ℕ), ∃ g ∈ D.gates, i ∈ g.inputs) ∧
      let mask := fun (x : Fin 42 → Bool) (m : ℕ) => (List.finRange 21).any (fun i => m.testBit i.val && x (Fin.ofNat 42 i.val))
      let hints := fun x : Fin 42 → Bool => ([3, 81920, 81923, 136, 655360, 655496, 288, 1310720, 1311008, 516, 9216, 9732, 2112, 36864, 38976] : List ℕ).map (mask x)
      ∀ (x : Fin 42 → Bool) (tail : List Bool), tail.length = 14 →
        (D.eval (List.ofFn x ++ hints x ++ tail) = true ↔ ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ v.val ∉ ([21, 24, 25, 30, 32] : List ℕ) ∧ x u = true ∧ x v = true)) →
    ∃ (x1 : Fin (42 : ℕ)) (x2 : Fin (43 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ))) ∧     x2 < x3 ∧       (x2, x3) ≠ ((0 : Fin (43 : ℕ)), x1.castSucc) ∧         (x3 = Fin.last (42 : ℕ) → x2 ≠ (0 : Fin (43 : ℕ)) ∧ x2 ≠ x1.castSucc) ∧           (∀ (x5 : Fin (42 : ℕ)), List.count ↑x5 [(0 : ℕ), ↑x1, ↑x2, ↑x3] = (1 : ℕ) → ∃ x7 ∈ x4.gates, ↑x5 ∈ x7.inputs) ∧             PEqualNP.MetaComplexity.Monotone2 x4 ∧               PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 ∧                 x4.size ≤ (122 : ℕ) ∧                   ∀ (x5 : Fin (42 : ℕ) → Bool),                     have x6 : Fin (43 : ℕ) → Bool := fun (x6 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x5 (0 : Fin (42 : ℕ)) || x5 x1) x5 x6;                     x4.eval (List.ofFn fun (x7 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 x2 || x6 x3) x6 x7) = Bool.true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true := by
  let mask := fun (x : Fin 42 → Bool) (m : ℕ) => (List.finRange 21).any (fun i => m.testBit i.val && x (Fin.ofNat 42 i.val))
  let hints := fun x : Fin 42 → Bool => ([3, 81920, 81923, 136, 655360, 655496, 288, 1310720, 1311008, 516, 9216, 9732, 2112, 36864, 38976] : List ℕ).map (mask x)
  let seed := fun x : Fin 42 → Bool => List.ofFn x ++ [x 0 || x 1, x 14 || x 16]
  intro first second
  obtain ⟨K, kMono, kBack, kSize, kOut, kEval⟩ := first
  obtain ⟨D, dMono, dBack, dSize, dOut, reused, dEval⟩ := second
  let M := Circuit.mk (K.gates ++ D.gates) D.output
  let lastGate := Gate.mk .or [K.output,D.output]
  let Z := Circuit.mk (M.gates ++ [lastGate]) (44 + M.size)
  have kLen : K.gates.length = 27 := kSize
  have mSize : M.size = 27 + D.size := by
    change (K.gates ++ D.gates).length = 27 + D.gates.length
    rw [List.length_append,kLen]
  have compose (n : ℕ) (A B : Circuit) (o : ℕ)
      (ha : NestedCover.ReadsBack n A) (hb : NestedCover.ReadsBack (n + A.size) B) :
        NestedCover.ReadsBack n (Circuit.mk (A.gates ++ B.gates) o) := by
    intro j hj i hi
    change j < (A.gates ++ B.gates).length at hj
    change i ∈ ((A.gates ++ B.gates).getD j ⟨.or,[]⟩).inputs at hi
    by_cases h : j < A.gates.length
    · rw [List.getD_append _ _ _ _ h] at hi
      exact ha j h i hi
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      simp only [List.length_append] at hj
      have b := hb (j-A.gates.length) (by omega) i hi
      change i < n + A.gates.length + (j-A.gates.length) at b
      omega
  have mBack : NestedCover.ReadsBack 44 M := compose 44 K D _ kBack (by simpa only [kSize] using dBack)
  have zBack : NestedCover.ReadsBack 44 Z := by
    apply compose 44 M (Circuit.mk [lastGate] 0) _ mBack
    intro j hj i hi
    change j < 1 at hj
    have e : j=0 := by omega
    subst j
    change i ∈ [K.output,D.output] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl <;> omega
  have zMon : Monotone2 Z := by
    intro g hg
    rcases List.mem_append.mp hg with hm | hf
    · rcases List.mem_append.mp hm with hk | hd
      · exact kMono g hk
      · exact dMono g hd
    · have e := List.mem_singleton.mp hf
      subst g
      exact ⟨Or.inr rfl, by change 2 ≤ 2; decide⟩
  have zSize : Z.size ≤ 122 := by
    change (M.gates ++ [lastGate]).length ≤ 122
    simp only [List.length_append,List.length_singleton]
    change M.size + 1 ≤ 122
    omega
  refine ⟨1,14,16,Z, Or.inl rfl, by decide, by decide, by decide, ?_, zMon, zBack, zSize, ?_⟩
  · intro i count
    have which : ∀ k : Fin 42, ([0,1,14,16] : List ℕ).count k.val = 1 → k.val ∈ ([0,1,14,16] : List ℕ) := by decide
    obtain ⟨g,hg,hi⟩ := reused i.val (which i count)
    exact ⟨g,List.mem_append_left _ (List.mem_append_right K.gates hg),hi⟩
  · intro x
    let y : Fin 43 → Bool := Fin.lastCases (motive := fun _ => Bool) (x 0 || x 1) x
    have snoc {n : ℕ} (f : Fin n → Bool) (b : Bool) :
        List.ofFn (Fin.lastCases (motive := fun _ => Bool) b f) = List.ofFn f ++ [b] := by
      rw [List.ofFn_succ_last]
      simp
    have input : List.ofFn (Fin.lastCases (motive := fun _ => Bool) (y 14 || y 16) y) = seed x := by
      rw [snoc]
      change List.ofFn (Fin.lastCases (motive := fun _ => Bool) (x 0 || x 1) x) ++ [x 14 || x 16] = _
      rw [snoc,List.append_assoc]
      rfl
    change Z.eval (List.ofFn (Fin.lastCases (motive := fun _ => Bool) (y 14 || y 16) y)) = true ↔ _
    rw [input]
    let init := seed x
    let kBank := K.wires init
    let wires := D.wires kBank
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have extension (gs : List Gate) (w : List Bool) :
        ∃ rest : List Bool, gs.foldl step w = w ++ rest ∧ rest.length = gs.length := by
      induction gs generalizing w with
      | nil => exact ⟨[], (List.append_nil w).symm, rfl⟩
      | cons g gs ih =>
        obtain ⟨rest,he,hl⟩ := ih (step w g)
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: rest, ?_, ?_⟩
        · rw [List.foldl_cons,he]
          simp only [step,List.append_assoc,List.singleton_append]
        · simp only [List.length_cons,hl]
    obtain ⟨kextra,ke,kl⟩ := extension K.gates init
    obtain ⟨dextra,de,dl⟩ := extension D.gates kBank
    change kBank = init ++ kextra at ke
    change wires = kBank ++ dextra at de
    have il : init.length = 44 := by simp [init,seed]
    have kb : kBank.length = 71 := by rw [ke,List.length_append,il,kl,kLen]
    have wl : wires.length = 44 + M.size := by
      rw [de,List.length_append,kb,dl]
      change 71 + D.size = 44 + M.size
      omega
    have keep : wires.getD K.output false = K.eval init := by
      rw [de,List.getD_append _ _ _ _ (by omega)]
      rfl
    have endGate : Z.eval init = (K.eval init || D.eval kBank) := by
      change ((M.gates ++ [lastGate]).foldl step init).getD (44 + M.size) false = _
      rw [List.foldl_append]
      change ((K.gates ++ D.gates).foldl step init ++
        [lastGate.op.eval (lastGate.inputs.map fun i => ((K.gates ++ D.gates).foldl step init).getD i false)]).getD (44 + M.size) false = _
      rw [List.foldl_append]
      change (wires ++ [wires.getD K.output false || (wires.getD D.output false || false)]).getD (44+M.size) false = _
      rw [List.getD_append_right _ _ _ _ (by omega),wl,Nat.sub_self]
      change (wires.getD K.output false || (wires.getD D.output false || false)) = _
      rw [keep,Bool.or_false]
      rfl
    obtain ⟨⟨tail,tl,shape⟩,pencil⟩ := kEval x
    change kBank = List.ofFn x ++ hints x ++ tail at shape
    have affine := dEval x tail tl
    rw [← shape] at affine
    rw [endGate,Bool.or_eq_true,pencil,affine]
    constructor
    · rintro (⟨u,v,edge,_,hu,hv⟩ | ⟨u,v,edge,_,hu,hv⟩) <;> exact ⟨u,v,edge,hu,hv⟩
    · rintro ⟨u,v,edge,hu,hv⟩
      by_cases p : v.val ∈ ([21,24,25,30,32] : List ℕ)
      · exact Or.inl ⟨u,v,edge,p,hu,hv⟩
      · exact Or.inr ⟨u,v,edge,p,hu,hv⟩

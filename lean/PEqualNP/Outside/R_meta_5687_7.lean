import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 24000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_5687_7
    (hEdge : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x1 →
      x1.size ≤ (18 : ℕ) →
      x1.gates ≠ [] →
      ∃ x6 ∈ ([((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)] : List (ℕ × Bool)),
        have x7 : List Bool := List.ofFn fun (x7 : Fin (10 : ℕ)) => x6.1.testBit ↑x7;
        x1.eval (x7 ++ [x7.getD 0 Bool.false || x7.getD 1 Bool.false]) ≠ x6.2)
    (hNonEdge : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x1 →
      x1.size ≤ (18 : ℕ) →
      x1.gates ≠ [] →
      ∃ x6 ∈ ([((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)] : List (ℕ × Bool)),
        have x7 : List Bool := List.ofFn fun (x7 : Fin (10 : ℕ)) => x6.1.testBit ↑x7;
        x1.eval (x7 ++ [x7.getD 0 Bool.false || x7.getD 2 Bool.false]) ≠ x6.2) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (18 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ x6 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],           have x7 : List Bool := List.ofFn fun (x7 : Fin (10 : ℕ)) => x6.1.testBit ↑x7;           x1.eval (x7 ++ [(List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x2).any id]) ≠ x6.2 := by
  classical
  let rows : List (ℕ × Bool) := [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)]
  let autTable : List (Bool × ℕ × ℕ) := [
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (false, 654820258320, 654820258320),
    (false, 507495416640, 427756169040),
    (true, 560008100160, 177020692560),
    (true, 628794603600, 628794603600),
    (false, 238409782800, 238409782800),
    (false, 232600672080, 232600672080),
    (false, 628794603600, 628794603600),
    (false, 560008100160, 177020692560),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654013059090, 654013059090),
    (false, 641686831395, 641686831395),
    (false, 580712305665, 247034180865),
    (false, 633308873985, 633308873985),
    (true, 237340479510, 362928379410),
    (false, 568606392615, 382374273315),
    (false, 498907545960, 414754297635),
    (false, 228311957865, 27137447715),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 40071424050, 559745994825),
    (false, 436349240370, 508307836995),
    (false, 431798420850, 442803703875),
    (false, 362928379410, 237340479510),
    (true, 35520604530, 172124229705),
    (false, 38996898360, 550649598585),
    (false, 34718626425, 34718626425),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 508307836995, 436349240370),
    (false, 624752330115, 624752330115),
    (false, 30419490435, 212640990585),
    (false, 27137447715, 228311957865),
    (true, 38996898360, 550649598585),
    (false, 90738950985, 14302652310),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (false, 164039726085, 228841388385),
    (false, 159844992150, 91813476675),
    (false, 554959176855, 107479201155),
    (false, 487787398200, 483540473475),
    (true, 559745994825, 40071424050),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (false, 156557706630, 349774047555),
    (true, 233145765975, 369502950450),
    (true, 628259950680, 620154542130),
    (false, 212640990585, 30419490435),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (false, 13222905495, 81642554745),
    (true, 9683958120, 138265712745),
    (true, 9956505705, 9956505705),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (false, 86439794520, 206764005270),
    (true, 34718626425, 34718626425),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (false, 9956505705, 9956505705),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320),
    (true, 654820258320, 654820258320)
  ]
  let getNib (code i : ℕ) : ℕ := (code >>> (4 * i)) &&& 15
  let permMask (pCode r : ℕ) : ℕ :=
    (List.finRange 10).foldl (fun acc (i : Fin 10) =>
      if r.testBit i.val then acc ||| (1 <<< getNib pCode i.val) else acc) 0
  have getD_ofFn10 (g : Fin 10 → Bool) (i : ℕ) (hi : i < 10) :
      (List.ofFn g).getD i false = g ⟨i, hi⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hi]
  have empty_case (C : Circuit) (x2 : List ℕ) (hzero : C.gates = []) :
      ∃ x6 ∈ rows,
        have x7 : List Bool := List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7;
        C.eval (x7 ++ [(List.map (fun x8 => x7.getD x8 false) x2).any id]) ≠ x6.2 := by
    have eval_eq (r : ℕ × Bool) :
        let x7 : List Bool := List.ofFn fun (x7 : Fin 10) => r.1.testBit ↑x7;
        C.eval (x7 ++ [(List.map (fun x8 => x7.getD x8 false) x2).any id]) =
          (x7 ++ [(List.map (fun x8 => x7.getD x8 false) x2).any id]).getD C.output false := by
      simp [Circuit.eval, Circuit.wires, hzero]
    by_cases hout : C.output < 10
    · have frow : ∀ k : Fin 10, ∃ r ∈ rows, r.2 = false ∧ r.1.testBit k.val = true := by decide +kernel
      obtain ⟨r, hr, hrf, hrt⟩ := frow ⟨C.output, hout⟩
      refine ⟨r, hr, ?_⟩
      dsimp only
      rw [eval_eq r, List.getD_append _ _ _ _ (by simp [hout]), getD_ofFn10 _ _ hout]
      simp [hrt, hrf]
    · by_cases h10 : C.output = 10
      · by_cases hsmall : ∃ a ∈ x2, a < 10
        · obtain ⟨a, ha_mem, ha_lt⟩ := hsmall
          have frow : ∀ k : Fin 10, ∃ r ∈ rows, r.2 = false ∧ r.1.testBit k.val = true := by decide +kernel
          obtain ⟨r, hr, hrf, hrt⟩ := frow ⟨a, ha_lt⟩
          refine ⟨r, hr, ?_⟩
          dsimp only
          rw [eval_eq r, h10, List.getD_append_right _ _ _ _ (by simp),
              show (List.ofFn fun (x7 : Fin 10) => r.1.testBit ↑x7).length = 10 by simp, Nat.sub_self,
              List.getD_cons_zero, hrf]
          simp only [ne_eq, Bool.not_eq_false]
          rw [List.any_eq_true]
          refine ⟨true, List.mem_map.mpr ⟨a, ha_mem, ?_⟩, rfl⟩
          rw [getD_ofFn10 _ _ ha_lt]
          exact hrt
        · push_neg at hsmall
          refine ⟨(3, true), by decide +kernel, ?_⟩
          dsimp only
          rw [eval_eq (3, true), h10, List.getD_append_right _ _ _ _ (by simp),
              show (List.ofFn fun (x7 : Fin 10) => (3 : ℕ).testBit ↑x7).length = 10 by simp, Nat.sub_self,
              List.getD_cons_zero]
          simp only [ne_eq, Bool.not_eq_true]
          rw [Bool.eq_false_iff]
          intro htrue
          rw [List.any_eq_true] at htrue
          obtain ⟨b, hb_mem, hb_id⟩ := htrue
          simp only [id_eq] at hb_id
          subst hb_id
          rw [List.mem_map] at hb_mem
          obtain ⟨a, ha_mem, ha_eq⟩ := hb_mem
          have hge : 10 ≤ a := hsmall a ha_mem
          rw [List.getD_eq_default _ _ (by simp; omega)] at ha_eq
          cases ha_eq
      · refine ⟨(3, true), by decide +kernel, ?_⟩
        dsimp only
        rw [eval_eq (3, true), List.getD_eq_default _ _ (by simp; omega)]
        exact Bool.false_ne_true
  let rGate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩
  let rCirc (f : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (rGate f), f C.output⟩
  have remap_mono (f : ℕ → ℕ) (C : Circuit) (hC : Monotone2 C) : Monotone2 (rCirc f C) := by
    intro g' hg'
    simp only [rCirc, List.mem_map] at hg'
    obtain ⟨g, hg, rfl⟩ := hg'
    exact ⟨(hC g hg).1, by simpa [rGate] using (hC g hg).2⟩
  have remap_size (f : ℕ → ℕ) (C : Circuit) : (rCirc f C).size = C.size := by
    simp [rCirc, Circuit.size]
  have remap_ne_nil (f : ℕ → ℕ) (C : Circuit) (hC : C.gates ≠ []) : (rCirc f C).gates ≠ [] := by
    simp [rCirc, hC]
  have remap_eval (f : ℕ → ℕ) (C : Circuit) (u v : List Bool)
      (hu : u.length = 11) (hv : v.length = 11)
      (hf_in : ∀ k < 11, (if f k < 11 then u.getD (f k) false else false) = v.getD k false)
      (hf_gap : ∀ k < 11, f k < 11 ∨ 11 + C.gates.length ≤ f k)
      (hf_hi : ∀ k, 11 ≤ k → f k = k) :
      (rCirc f C).eval u = C.eval v := by
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have getD_remap (tail : List Bool) (htail : 11 + tail.length ≤ 11 + C.gates.length) (k : ℕ) :
        (u ++ tail).getD (f k) false = (v ++ tail).getD k false := by
      by_cases hk : k < 11
      · rcases hf_gap k hk with hlt | hge
        · rw [List.getD_append _ _ _ _ (hu.symm ▸ hlt), List.getD_append _ _ _ _ (hv.symm ▸ hk)]
          have hin := hf_in k hk
          rwa [ite_eq_left_iff.mpr (fun hn => absurd hlt hn)] at hin
        · have hge' : (u ++ tail).length ≤ f k := by
            rw [List.length_append, hu]
            omega
          rw [List.getD_eq_default _ _ hge', List.getD_append _ _ _ _ (hv.symm ▸ hk)]
          have hin := hf_in k hk
          have hnot : ¬ f k < 11 := by omega
          rw [ite_eq_right_iff.mpr (fun ht => absurd ht hnot)] at hin
          exact hin
      · have hfk : f k = k := hf_hi k (Nat.le_of_not_lt hk)
        rw [hfk]
        by_cases hlen : k < 11 + tail.length
        · have hk1 : (u ++ tail).getD k false = tail.getD (k - 11) false := by
            rw [List.getD_append_right _ _ _ _ (by rw [hu]; omega), hu]
          have hk2 : (v ++ tail).getD k false = tail.getD (k - 11) false := by
            rw [List.getD_append_right _ _ _ _ (by rw [hv]; omega), hv]
          rw [hk1, hk2]
        · rw [List.getD_eq_default _ _ (by rw [List.length_append, hu]; omega),
              List.getD_eq_default _ _ (by rw [List.length_append, hv]; omega)]
    have wires_eq : ∀ (gs : List Gate) (tail : List Bool),
        11 + tail.length + gs.length ≤ 11 + C.gates.length →
        ∃ tail', tail'.length = tail.length + gs.length ∧
          (gs.map (rGate f)).foldl step (u ++ tail) = u ++ tail' ∧
          gs.foldl step (v ++ tail) = v ++ tail' := by
      intro gs
      induction gs with
      | nil =>
        intro tail _
        exact ⟨tail, rfl, rfl, rfl⟩
      | cons g gs ih =>
        intro tail hlen
        have hlen1 : 11 + tail.length ≤ 11 + C.gates.length := by simp at hlen; omega
        have hinputs : (rGate f g).inputs.map (fun i => (u ++ tail).getD i false) =
            g.inputs.map (fun i => (v ++ tail).getD i false) := by
          simp only [rGate, List.map_map]
          congr 1
          funext i
          exact getD_remap tail hlen1 i
        have hbit : (rGate f g).op.eval ((rGate f g).inputs.map fun i => (u ++ tail).getD i false) =
            g.op.eval (g.inputs.map fun i => (v ++ tail).getD i false) := by
          simp only [rGate, hinputs]
        have hu' : step (u ++ tail) (rGate f g) = u ++ (tail ++ [g.op.eval (g.inputs.map fun i => (v ++ tail).getD i false)]) := by
          simp only [step, hbit, List.append_assoc]
        have hv' : step (v ++ tail) g = v ++ (tail ++ [g.op.eval (g.inputs.map fun i => (v ++ tail).getD i false)]) := by
          simp only [step, List.append_assoc]
        obtain ⟨tail', htlen, h1, h2⟩ := ih (tail ++ [g.op.eval (g.inputs.map fun i => (v ++ tail).getD i false)]) (by simp at hlen ⊢; omega)
        refine ⟨tail', by simp at htlen ⊢; omega, ?_, ?_⟩
        · simpa only [List.map_cons, List.foldl_cons, hu'] using h1
        · simpa only [List.foldl_cons, hv'] using h2
    obtain ⟨tail', htlen, hw1, hw2⟩ := wires_eq C.gates [] (by simp)
    change ((C.gates.map (rGate f)).foldl step u).getD (f C.output) false = (C.gates.foldl step v).getD C.output false
    have hw1' : (C.gates.map (rGate f)).foldl step u = u ++ tail' := by
      simpa only [List.append_nil] using hw1
    have hw2' : C.gates.foldl step v = v ++ tail' := by
      simpa only [List.append_nil] using hw2
    have htail_len : tail'.length = C.gates.length := by
      simpa using htlen
    rw [hw1', hw2']
    exact getD_remap tail' (by omega) C.output
  have reduce_false (C : Circuit) (hC : Monotone2 C) (hSz : C.size ≤ 18) (hNe : C.gates ≠ []) :
      ∃ x6 ∈ rows,
        have x7 : List Bool := List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7;
        C.eval (x7 ++ [false]) ≠ x6.2 := by
    let f (k : ℕ) : ℕ := if k = 10 then 11 + C.gates.length else k
    obtain ⟨x6, hx6, hbad⟩ := hEdge (rCirc f C) (remap_mono f C hC) (by rw [remap_size]; exact hSz) (remap_ne_nil f C hNe)
    refine ⟨x6, hx6, ?_⟩
    dsimp only
    have heq := remap_eval f C
      ((List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7) ++ [(List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7).getD 0 false || (List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7).getD 1 false])
      ((List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7) ++ [false])
      (by simp) (by simp)
      (fun k hk => by
        by_cases h10 : k = 10
        · subst h10
          have hf10 : f 10 = 11 + C.gates.length := if_pos rfl
          rw [hf10, if_neg (by omega), List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
        · have hk10 : k < 10 := by omega
          have hfk : f k = k := if_neg h10
          rw [hfk, if_pos hk, List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)])
      (fun k hk => by
        by_cases h10 : k = 10
        · right
          have hf10 : f k = 11 + C.gates.length := if_pos h10
          omega
        · left
          have hfk : f k = k := if_neg h10
          omega)
      (fun k hk => by
        have h10 : k ≠ 10 := by omega
        exact if_neg h10)
    rw [← heq]
    exact hbad
  have reduce_single (C : Circuit) (hC : Monotone2 C) (hSz : C.size ≤ 18) (hNe : C.gates ≠ []) (a : ℕ) (ha : a < 10) :
      ∃ x6 ∈ rows,
        have x7 : List Bool := List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7;
        C.eval (x7 ++ [x7.getD a false]) ≠ x6.2 := by
    let f (k : ℕ) : ℕ := if k = 10 then a else k
    obtain ⟨x6, hx6, hbad⟩ := hEdge (rCirc f C) (remap_mono f C hC) (by rw [remap_size]; exact hSz) (remap_ne_nil f C hNe)
    refine ⟨x6, hx6, ?_⟩
    dsimp only
    have heq := remap_eval f C
      ((List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7) ++ [(List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7).getD 0 false || (List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7).getD 1 false])
      ((List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7) ++ [(List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7).getD a false])
      (by simp) (by simp)
      (fun k hk => by
        by_cases h10 : k = 10
        · subst h10
          have hf10 : f 10 = a := if_pos rfl
          rw [hf10, if_pos (by omega), List.getD_append _ _ _ _ (by simp; omega),
              List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
        · have hk10 : k < 10 := by omega
          have hfk : f k = k := if_neg h10
          rw [hfk, if_pos hk, List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)])
      (fun k hk => by
        left
        by_cases h10 : k = 10
        · have hfk : f k = a := if_pos h10
          omega
        · have hfk : f k = k := if_neg h10
          omega)
      (fun k hk => by
        have h10 : k ≠ 10 := by omega
        exact if_neg h10)
    rw [← heq]
    exact hbad
  have aut_rows_edge : ∀ (a b : Fin 10), a.val < b.val →
      (autTable.getD (10 * a.val + b.val) (true, 0, 0)).1 = true →
      ∀ r ∈ rows, (permMask (autTable.getD (10 * a.val + b.val) (true, 0, 0)).2.1 r.1, r.2) ∈ rows := by
    decide +kernel
  have aut_rows_nonedge : ∀ (a b : Fin 10), a.val < b.val →
      (autTable.getD (10 * a.val + b.val) (true, 0, 0)).1 = false →
      ∀ r ∈ rows, (permMask (autTable.getD (10 * a.val + b.val) (true, 0, 0)).2.1 r.1, r.2) ∈ rows := by
    decide +kernel
  have aut_bits_ok : ∀ (a b : Fin 10), a.val < b.val →
      let entry := autTable.getD (10 * a.val + b.val) (true, 0, 0)
      (∀ k : Fin 10, getNib entry.2.2 k.val < 10) ∧
      (∀ r ∈ rows, ∀ k : Fin 10, (permMask entry.2.1 r.1).testBit k.val = r.1.testBit (getNib entry.2.2 k.val)) ∧
      (∀ r ∈ rows, ((permMask entry.2.1 r.1).testBit a.val || (permMask entry.2.1 r.1).testBit b.val) =
        (r.1.testBit 0 || r.1.testBit (if entry.1 then 1 else 2))) := by
    decide +kernel
  have reduce_pair (C : Circuit) (hC : Monotone2 C) (hSz : C.size ≤ 18) (hNe : C.gates ≠ [])
      (a b : Fin 10) (hab : a.val < b.val) :
      ∃ x6 ∈ rows,
        have x7 : List Bool := List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7;
        C.eval (x7 ++ [x7.getD a.val false || x7.getD b.val false]) ≠ x6.2 := by
    let entry := autTable.getD (10 * a.val + b.val) (true, 0, 0)
    let f (k : ℕ) : ℕ := if k < 10 then getNib entry.2.2 k else k
    obtain ⟨hklt, hbits, hpair⟩ := aut_bits_ok a b hab
    let s : ℕ := if entry.1 then 1 else 2
    have hfail : ∃ r ∈ rows, (rCirc f C).eval ((List.ofFn fun (x7 : Fin 10) => r.1.testBit ↑x7) ++
        [(List.ofFn fun (x7 : Fin 10) => r.1.testBit ↑x7).getD 0 false ||
         (List.ofFn fun (x7 : Fin 10) => r.1.testBit ↑x7).getD s false]) ≠ r.2 ∧
        (permMask entry.2.1 r.1, r.2) ∈ rows := by
      by_cases he : entry.1 = true
      · obtain ⟨r, hr, hbad⟩ := hEdge (rCirc f C) (remap_mono f C hC) (by rw [remap_size]; exact hSz) (remap_ne_nil f C hNe)
        refine ⟨r, hr, ?_, aut_rows_edge a b hab he r hr⟩
        simpa [s, he] using hbad
      · have he_f : entry.1 = false := Bool.eq_false_iff.mpr he
        obtain ⟨r, hr, hbad⟩ := hNonEdge (rCirc f C) (remap_mono f C hC) (by rw [remap_size]; exact hSz) (remap_ne_nil f C hNe)
        refine ⟨r, hr, ?_, aut_rows_nonedge a b hab he_f r hr⟩
        simpa [s, he_f] using hbad
    obtain ⟨r, hr, hbad, hperm_mem⟩ := hfail
    refine ⟨(permMask entry.2.1 r.1, r.2), hperm_mem, ?_⟩
    dsimp only
    have hs_lt : s < 10 := by dsimp [s]; split_ifs <;> omega
    have heq := remap_eval f C
      ((List.ofFn fun (x7 : Fin 10) => r.1.testBit ↑x7) ++
        [(List.ofFn fun (x7 : Fin 10) => r.1.testBit ↑x7).getD 0 false ||
         (List.ofFn fun (x7 : Fin 10) => r.1.testBit ↑x7).getD s false])
      ((List.ofFn fun (x7 : Fin 10) => (permMask entry.2.1 r.1).testBit ↑x7) ++
        [(List.ofFn fun (x7 : Fin 10) => (permMask entry.2.1 r.1).testBit ↑x7).getD a.val false ||
         (List.ofFn fun (x7 : Fin 10) => (permMask entry.2.1 r.1).testBit ↑x7).getD b.val false])
      (by simp) (by simp)
      (fun k hk => by
        by_cases hk10 : k < 10
        · have hq : getNib entry.2.2 k < 10 := hklt ⟨k, hk10⟩
          have hf : f k = getNib entry.2.2 k := if_pos hk10
          rw [hf, if_pos (by omega)]
          rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
          rw [getD_ofFn10 _ _ hq, getD_ofFn10 _ _ hk10]
          exact (hbits r hr ⟨k, hk10⟩).symm
        · have hk_eq : k = 10 := by omega
          subst hk_eq
          have hf : f 10 = 10 := if_neg (by omega)
          rw [hf, if_pos (by omega)]
          rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
          simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
          rw [getD_ofFn10 _ 0 (by omega), getD_ofFn10 _ s hs_lt, getD_ofFn10 _ a.val a.isLt, getD_ofFn10 _ b.val b.isLt]
          exact (hpair r hr).symm)
      (fun k hk => by
        left
        by_cases hk10 : k < 10
        · have hq : getNib entry.2.2 k < 10 := hklt ⟨k, hk10⟩
          have hf : f k = getNib entry.2.2 k := if_pos hk10
          rw [hf]
          exact Nat.lt_trans hq (by decide)
        · have hf : f k = k := if_neg hk10
          omega)
      (fun k hk => if_neg (by omega))
    rw [← heq]
    exact hbad
  intro x1 x2 hm hs hl
  by_cases hzero : x1.gates = []
  · exact empty_case x1 x2 hzero
  · rcases x2 with _ | ⟨a, _ | ⟨b, t⟩⟩
    · obtain ⟨x6, hx6, hbad⟩ := reduce_false x1 hm hs hzero
      refine ⟨x6, hx6, ?_⟩
      dsimp only
      exact hbad
    · by_cases ha : a < 10
      · obtain ⟨x6, hx6, hbad⟩ := reduce_single x1 hm hs hzero a ha
        refine ⟨x6, hx6, ?_⟩
        dsimp only
        rw [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact hbad
      · obtain ⟨x6, hx6, hbad⟩ := reduce_false x1 hm hs hzero
        refine ⟨x6, hx6, ?_⟩
        dsimp only
        rw [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false,
            List.getD_eq_default _ _ (by simp; omega)]
        exact hbad
    · have ht : t = [] := by
        simp only [List.length_cons] at hl
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst ht
      by_cases ha : a < 10 <;> by_cases hb : b < 10
      · by_cases hab : a = b
        · subst hab
          obtain ⟨x6, hx6, hbad⟩ := reduce_single x1 hm hs hzero a ha
          refine ⟨x6, hx6, ?_⟩
          dsimp only
          rw [List.map_cons, List.map_cons, List.map_nil, List.any_cons, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.or_self]
          exact hbad
        · rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
          · obtain ⟨x6, hx6, hbad⟩ := reduce_pair x1 hm hs hzero ⟨a, ha⟩ ⟨b, hb⟩ hlt
            refine ⟨x6, hx6, ?_⟩
            dsimp only
            rw [List.map_cons, List.map_cons, List.map_nil, List.any_cons, List.any_cons, List.any_nil,
                id_eq, Bool.or_false]
            exact hbad
          · obtain ⟨x6, hx6, hbad⟩ := reduce_pair x1 hm hs hzero ⟨b, hb⟩ ⟨a, ha⟩ hgt
            refine ⟨x6, hx6, ?_⟩
            dsimp only
            rw [List.map_cons, List.map_cons, List.map_nil, List.any_cons, List.any_cons, List.any_nil,
                id_eq, Bool.or_false, Bool.or_comm]
            exact hbad
      · obtain ⟨x6, hx6, hbad⟩ := reduce_single x1 hm hs hzero a ha
        refine ⟨x6, hx6, ?_⟩
        dsimp only
        have hb' : (List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7).getD b false = false :=
          List.getD_eq_default _ _ (by simp; omega)
        rw [List.map_cons, List.map_cons, List.map_nil, List.any_cons, List.any_cons, List.any_nil]
        dsimp only [id_eq]
        rw [Bool.or_false, hb', Bool.or_false]
        exact hbad
      · obtain ⟨x6, hx6, hbad⟩ := reduce_single x1 hm hs hzero b hb
        refine ⟨x6, hx6, ?_⟩
        dsimp only
        have ha' : (List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7).getD a false = false :=
          List.getD_eq_default _ _ (by simp; omega)
        rw [List.map_cons, List.map_cons, List.map_nil, List.any_cons, List.any_cons, List.any_nil]
        dsimp only [id_eq]
        rw [Bool.or_false, ha', Bool.false_or]
        exact hbad
      · obtain ⟨x6, hx6, hbad⟩ := reduce_false x1 hm hs hzero
        refine ⟨x6, hx6, ?_⟩
        dsimp only
        have ha' : (List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7).getD a false = false :=
          List.getD_eq_default _ _ (by simp; omega)
        have hb' : (List.ofFn fun (x7 : Fin 10) => x6.1.testBit ↑x7).getD b false = false :=
          List.getD_eq_default _ _ (by simp; omega)
        rw [List.map_cons, List.map_cons, List.map_nil, List.any_cons, List.any_cons, List.any_nil]
        dsimp only [id_eq]
        rw [Bool.or_false, ha', hb', Bool.false_or]
        exact hbad

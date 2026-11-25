import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fuse the equivalent line columns and precompute one pendant incidence.
-- Drop the unused auxiliary columns. The remaining search has 16 inputs.
-- The 44-row geometric cover and monotonicity argument follow the earlier cut.
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_2712_86
    (finiteSynthesis :
      let table := fun (t : List ℕ) (j : ℕ) (i : Fin 16) => (t.getD (j / 3) 0).testBit (16 * (j % 3) + i.val)
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 21 ∧
        (∀ j : Fin 19, circuitFun 16 C (table [171800920097,343601840194,1133880279172,2267776352528,17661040264196,70377871253505,32769] j) = true) ∧
        ∀ j : Fin 33, circuitFun 16 C (table [5029475581983,9925813274647,18722031864851,26418680107534,39694582881030,69828484934802,79256174018589,88018049386548,97879423799820,110055814945572,140602033859760] j) = false)
    (negativeCover :
      let pin (x : Fin 26 → Bool) (i : Fin 20) :=
        if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else
          if i.val < 14 then i.val+8 else i.val+9))
        else (decide (i.val ≠ 18) && (x 16 || x 18)) ||
          (decide (i.val ≠ 17) && (x 19 || x 23))
      let I := fun p l : Fin 13 => ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d
      ∀ x : Fin 26 → Bool,
        (∀ p l, x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 l) = true → ¬ I p l) →
        ((∃ l, ∀ p, x (Fin.castAdd 13 p) = true → I p l) ∨
          ∃ p, ∀ l, x (Fin.natAdd 13 l) = true → I p l) →
        ∃ j : Fin 44, ∀ i, pin x i = true →
          ((([4665232155738143,13518504604999695,725368754528096277,730724029253162005,866973350870287389,875963053248350355,884986756446568478,903000063497490454,954792603833647132,1012212425860929682,1041183516279060867,1062218301194542225,1078371242023506996,1142983005070916482,1099479117384] : List ℕ).getD (j.val / 3) 0).testBit (20 * (j.val % 3) + i.val)) = true)
    (liftPrefix :
      let compact := fun (x : Fin 20 → Bool) (i : Fin 16) =>
        if i.val = 14 then x 10 || x 15
        else if i.val = 15 then x 0 && x 14
        else x (([0,1,2,3,4,5,6,7,8,9,11,12,13,16] : List (Fin 20)).getD i.val 0)
      ∀ C : Circuit, Monotone2 C → ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size + 2 ∧
        ∀ x : Fin 20 → Bool, circuitFun 20 D x = circuitFun 16 C (compact x)) :
    let pin (x : Fin 26 → Bool) (i : Fin 20) :=
      if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else if i.val < 14 then i.val+8 else i.val+9))
      else (decide (i.val ≠ 18) && (x 16 || x 18)) || (decide (i.val ≠ 17) && (x 19 || x 23))
    let I := fun p l : Fin 13 => ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 23 ∧
      (∀ p l : Fin 13, p.val < 5 → I p l →
        circuitFun 20 C (pin (fun z => decide (z = Fin.castAdd 13 p ∨ z = Fin.natAdd 13 l))) = true) ∧
      ∀ x : Fin 26 → Bool,
        (∀ p l : Fin 13, x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 l) = true → ¬ I p l) →
        ((∃ l : Fin 13, ∀ p : Fin 13, x (Fin.castAdd 13 p) = true → I p l) ∨
          ∃ p : Fin 13, ∀ l : Fin 13, x (Fin.natAdd 13 l) = true → I p l) →
        circuitFun 20 C (pin x) = false := by
  dsimp only
  let pin (x : Fin 26 → Bool) (i : Fin 20) :=
    if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else
      if i.val < 14 then i.val+8 else i.val+9))
    else (decide (i.val ≠ 18) && (x 16 || x 18)) ||
      (decide (i.val ≠ 17) && (x 19 || x 23))
  let I := fun p l : Fin 13 => ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d
  let no : Fin 44 → Fin 20 → Bool := fun j i =>
    ((([4665232155738143,13518504604999695,725368754528096277,730724029253162005,866973350870287389,875963053248350355,884986756446568478,903000063497490454,954792603833647132,1012212425860929682,1041183516279060867,1062218301194542225,1078371242023506996,1142983005070916482,1099479117384] : List ℕ).getD (j.val / 3) 0).testBit (20 * (j.val % 3) + i.val))
  let sel (i : Fin 16) : Fin 20 := ([0,1,2,3,4,5,6,7,8,9,11,12,13,16] : List (Fin 20)).getD i.val 0
  let compress (v : Fin 20 → Bool) (i : Fin 16) :=
    if i.val = 14 then v 10 || v 15 else if i.val = 15 then v 0 && v 14 else v (sel i)
  let tbl (ns : List ℕ) (j : ℕ) (i : Fin 16) := (ns.getD (j / 3) 0).testBit (16 * (j % 3) + i.val)
  let good (j : Fin 19) := tbl [171800920097,343601840194,1133880279172,2267776352528,17661040264196,70377871253505,32769] j.val
  let bad (j : Fin 33) := tbl [5029475581983,9925813274647,18722031864851,26418680107534,39694582881030,69828484934802,79256174018589,88018049386548,97879423799820,110055814945572,140602033859760] j.val
  have posMap : ∀ p l : Fin 13, p.val < 5 → I p l → ∃ j : Fin 19, ∀ i,
      good j i = true → compress (pin (fun z => decide (z = Fin.castAdd 13 p ∨ z = Fin.natAdd 13 l))) i = true := by
    decide +kernel
  have negMap : ∀ j : Fin 44, ∃ k : Fin 33, ∀ i,
      compress (no j) i = true → bad k i = true := by decide +kernel
  obtain ⟨C,hm,hs,hyes,hno⟩ := finiteSynthesis

  have monotoneEval (x y : Fin 16 → Bool) (hxy : ∀ i, x i = true → y i = true) :
      circuitFun 16 C x = true → circuitFun 16 C y = true := by
    let V (w : List Bool) (i : ℕ) := w.getD i false
    let R (w z : List Bool) := w.length = z.length ∧ ∀ i, V w i = true → V z i = true
    have step (g : Gate) (hg : g ∈ C.gates) (w z : List Bool) (hr : R w z) :
        g.op.eval (g.inputs.map (V w)) = true →
        g.op.eval (g.inputs.map (V z)) = true := by
      have hops := (hm g hg).1
      change g.op = .and ∨ g.op = .or at hops
      rcases hops with h | h <;> rw [h]
      · change (g.inputs.map (V w)).all id = true → (g.inputs.map (V z)).all id = true
        simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
        exact fun all i hi => hr.2 i (all i hi)
      · change (g.inputs.map (V w)).any id = true → (g.inputs.map (V z)).any id = true
        simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
        rintro ⟨i,hi,hval⟩
        exact ⟨i,hi,hr.2 i hval⟩
    let evalStep (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map (V w))]
    have run (gs : List Gate) (hsub : ∀ g ∈ gs, g ∈ C.gates) (w z : List Bool) (hr : R w z) :
        R (gs.foldl evalStep w) (gs.foldl evalStep z) := by
      induction gs generalizing w z with
      | nil => exact hr
      | cons g gs ih =>
        apply ih (fun h hh => hsub h (List.mem_cons_of_mem _ hh))
        refine ⟨by simp only [evalStep,List.length_append,List.length_singleton,hr.1], ?_⟩
        intro i
        change (w ++ [_]).getD i false = true → (z ++ [_]).getD i false = true
        by_cases h : i < w.length
        · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (by simpa only [← hr.1] using h)]
          exact hr.2 i
        · rw [List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by rw [← hr.1]; omega),← hr.1]
          cases i-w.length with
          | zero => exact step g (hsub g List.mem_cons_self) w z hr
          | succ k => simp
    have hi : R (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp only [List.length_ofFn], ?_⟩
      intro i
      by_cases h : i < 16
      · change (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true
        have hx : i < (List.ofFn x).length := by rw [List.length_ofFn]; exact h
        have hy : i < (List.ofFn y).length := by rw [List.length_ofFn]; exact h
        rw [List.getD_eq_getElem _ _ hx,List.getD_eq_getElem _ _ hy,
          List.getElem_ofFn,List.getElem_ofFn]
        exact hxy ⟨i,h⟩
      · change (List.ofFn x).getD i false = true → _
        rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
        intro hf; cases hf
    exact (run C.gates (fun _ h => h) _ _ hi).2 C.output
  obtain ⟨liftC,legal,small,simulate⟩ := liftPrefix C hm
  refine ⟨liftC,legal,by omega,?_,?_⟩
  · intro p l hp hpl
    obtain ⟨j,h⟩ := posMap p l hp hpl
    change circuitFun 20 liftC (pin (fun z => decide (z = Fin.castAdd 13 p ∨ z = Fin.natAdd 13 l))) = true
    rw [simulate]
    exact monotoneEval (good j) _ h (hyes j)
  · intro x hind hdeg
    obtain ⟨j,hj⟩ := negativeCover x hind hdeg
    obtain ⟨k,hk⟩ := negMap j
    have hcomp (i : Fin 16) : compress (pin x) i = true → compress (no j) i = true := by
      by_cases he : i.val = 14
      · simp only [compress,ite_eq_left he,Bool.or_eq_true]
        exact fun h => h.imp (hj 10) (hj 15)
      · by_cases h15 : i.val = 15
        · simp only [compress,ite_eq_right he,ite_eq_left h15,Bool.and_eq_true]
          exact fun h => ⟨hj 0 h.1, hj 14 h.2⟩
        · simpa only [compress,ite_eq_right he,ite_eq_right h15] using hj (sel i)
    change circuitFun 20 liftC (pin x) = false
    rw [simulate]
    cases h : circuitFun 16 C (compress (pin x)) with
    | false => rfl
    | true =>
      have contradiction := monotoneEval _ (bad k) (fun i hb => hk i (hcomp i hb)) h
      exact Bool.noConfusion (contradiction.symm.trans (hno k))

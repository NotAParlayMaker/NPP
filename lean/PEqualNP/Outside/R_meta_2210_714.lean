import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The only reader of the extra input must compute a truth table that no ordinary
-- single gate can realize from the available wires. This test uses the prefix alone.
-- In the reader mask, bit four times the wire number plus the count permits that count.
-- Wires zero, two and nine have one reader. Four, six and seven have at most two.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_2210_714
    (lower : ¬ HasCircuitSize 9 (fun x => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)))) 14)
    (search : ∀ (A B : List Gate) (g : Gate) (o : ℕ),
      let C : Circuit := ⟨A ++ g :: B,o⟩
      let readers := fun v => C.gates.countP (fun h => decide (v ∈ h.inputs))
      FanInTwo C → ReadsBack 10 C → C.size = 14 →
      (∀ h ∈ C.gates, if h.op.eval [false,false] then h.inputs.length = 1 else
        h.inputs.length = 2 ∧ h.inputs.Nodup) →
      g.op = GateOp.or → 9 ∈ g.inputs →
      (∀ v : Fin 10, readers v.val ≤ 3 ∧
        (203876201202 : ℕ).testBit (4*v.val + readers v.val) = true) →
      (∀ h : Gate, FanInTwo ⟨[h],0⟩ → 9 ∉ h.inputs →
        ∃ x : Fin 9 → Bool,
          let w := (⟨A,0⟩ : Circuit).wires (List.ofFn x ++ [x 0 && x 2])
          let val := fun (h : Gate) => h.op.eval (h.inputs.map fun i => w.getD i false)
          val h ≠ val g) →
      ¬ ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2]) = ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 → (∀ x4 ∈ x1.gates, (x4.op = PEqualNP.CircuitLowerBounds.GateOp.not → x4.inputs.length = (1 : ℕ)) ∧ (x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x4.inputs.length = (2 : ℕ) ∧ x4.inputs.Nodup)) → x1.size = (14 : ℕ) → (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide ((9 : ℕ) ∈ x7.inputs)) x1.gates = [x6]) → (∀ x7 ∈ [(0 : ℕ), (2 : ℕ)], (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (x7 ∈ x9.inputs)) x1.gates).length = (1 : ℕ)) → (∀ x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)], (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (x8 ∈ x10.inputs)) x1.gates).length ≤ (2 : ℕ)) → (∀ (x9 : Fin (9 : ℕ)), (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x9 ∈ x10.inputs)) x1.gates).length ≤ (3 : ℕ)) → ¬∀ (x10 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ))]) = (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  classical
  intro C fan back clean sz aux single twice thrice good
  let target := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)))
  have computes (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 0 && x 2]) = target x := by
    rw [good]
    simp [target,List.any_cons,Bool.or_assoc]; rfl
  obtain ⟨g,gOr,filterG⟩ := aux
  have gin : g ∈ C.gates.filter (fun h => decide (9 ∈ h.inputs)) := by rw [filterG]; simp
  obtain ⟨member,reads⟩ := List.mem_filter.mp gin
  have nine : 9 ∈ g.inputs := of_decide_eq_true reads
  obtain ⟨A,B,splitG⟩ := List.append_of_mem member
  have rest : ∀ h ∈ A ++ B, 9 ∉ h.inputs := by
    let p := fun h : Gate => decide (9 ∈ h.inputs)
    have filt : A.filter p ++ g :: B.filter p = [g] := by
      simpa [p,splitG,List.filter_append,nine] using filterG
    have lengths := congrArg List.length filt
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    intro h hm hit
    rcases List.mem_append.mp hm with ha | hb
    · have mem : h ∈ A.filter p := List.mem_filter.mpr ⟨ha,decide_eq_true hit⟩
      have := List.length_pos_of_mem mem
      omega
    · have mem : h ∈ B.filter p := List.mem_filter.mpr ⟨hb,decide_eq_true hit⟩
      have := List.length_pos_of_mem mem
      omega
  let shift := fun i : ℕ => if i < 9 then i else i-1
  let trim := fun h : Gate => (⟨h.op,h.inputs.map shift⟩ : Gate)
  let val := fun (w : List Bool) (h : Gate) => h.op.eval (h.inputs.map fun i => w.getD i false)
  let step := fun (w : List Bool) (h : Gate) => w ++ [val w h]
  have wire (base tail : List Bool) (b : Bool) (len : base.length = 9) (i : ℕ) (hi : i ≠ 9) :
      (base ++ tail).getD (shift i) false = ((base ++ [b]) ++ tail).getD i false := by
    by_cases low : i < 9
    · simp only [shift,ite_eq_left low]
      rw [List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by simp [len];omega),
        List.getD_append _ _ _ _ (by omega)]
    · simp only [shift,ite_eq_right low]
      rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by simp [len];omega)]
      congr 1
      simp [len]
      omega
  have value (base tail : List Bool) (b : Bool) (len : base.length = 9) (h : Gate) (miss : 9 ∉ h.inputs) :
      val (base ++ tail) (trim h) = val ((base ++ [b]) ++ tail) h := by
    unfold val trim
    simp only [List.map_map]
    apply congrArg h.op.eval
    apply List.map_congr_left
    intro i hi
    exact wire _ _ _ len _ (fun e => miss (e ▸ hi))
  have compact (gs : List Gate) (base tail : List Bool) (b : Bool) (len : base.length = 9)
      (miss : ∀ h ∈ gs, 9 ∉ h.inputs) :
      ∃ t : List Bool, (gs.map trim).foldl step (base ++ tail) = base ++ t ∧
        gs.foldl step ((base ++ [b]) ++ tail) = (base ++ [b]) ++ t := by
    induction gs generalizing tail with
    | nil => exact ⟨tail,rfl,rfl⟩
    | cons h hs ih =>
      let z := val ((base ++ [b]) ++ tail) h
      have eq := value base tail b len h (miss _ List.mem_cons_self)
      obtain ⟨t,one,two⟩ := ih (tail ++ [z]) (fun a ha => miss a (List.mem_cons_of_mem _ ha))
      refine ⟨t,?_,?_⟩
      · simpa only [List.map_cons,List.foldl_cons,step,eq,List.append_assoc,z] using one
      · simpa only [List.foldl_cons,step,List.append_assoc,z] using two
  have noOut : C.output ≠ 9 := by
    intro he
    let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
    have bit := computes x
    have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons h hs ih =>
        change (hs.foldl step (step w h)).getD i false = _
        rw [ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
    change (C.gates.foldl step _).getD C.output false = target x at bit
    rw [he,keep _ _ _ (by simp)] at bit
    exact Bool.noConfusion (show false = true from bit)
  have feasible (h : Gate) (hf : FanInTwo ⟨[h],0⟩) (miss : 9 ∉ h.inputs) :
      ∃ x : Fin 9 → Bool,
        let w := A.foldl step (List.ofFn x ++ [x 0 && x 2])
        val w h ≠ val w g := by
    by_contra! same
    let D : Circuit := ⟨(A ++ h :: B).map trim, shift C.output⟩
    apply lower
    refine ⟨D,?_,?_,?_⟩
    · intro t ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      have ok : u.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ u.inputs.length ≤ 2 := by
        rcases List.mem_append.mp hu with ha | hb
        · exact fan _ (splitG ▸ List.mem_append_left _ ha)
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hf _ List.mem_cons_self
        · exact fan _ (splitG ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hb))
      simpa [trim] using ok
    · change ((A ++ h :: B).map trim).length ≤ 14
      have lengthC : C.gates.length = 14 := sz
      simpa only [splitG,List.length_map,List.length_append,List.length_cons] using le_of_eq lengthC
    · intro x
      let base := List.ofFn x
      let b := x 0 && x 2
      have len : base.length = 9 := List.length_ofFn
      obtain ⟨t,hnew,hold⟩ := compact A base [] b len (fun u hu => rest u (List.mem_append_left _ hu))
      simp only [List.append_nil] at hnew hold
      let z := val ((base ++ [b]) ++ t) g
      have hz : val (base ++ t) (trim h) = z := by
        rw [value _ _ _ len h miss]
        change val _ h = val _ g
        rw [← hold]
        exact Classical.not_not.mp (same x)
      obtain ⟨t',newEnd,oldEnd⟩ := compact B base (t ++ [z]) b len
        (fun u hu => rest u (List.mem_append_right _ hu))
      have newRun : D.wires base = base ++ t' := by
        change ((A ++ h :: B).map trim).foldl step base = _
        simpa only [List.map_append,List.map_cons,List.foldl_append,List.foldl_cons,hnew,step,hz,
          List.append_assoc] using newEnd
      have oldRun : C.wires (base ++ [b]) = (base ++ [b]) ++ t' := by
        change C.gates.foldl step _ = _
        rw [splitG,List.foldl_append,List.foldl_cons,hold]
        simpa only [step,List.append_assoc,z] using oldEnd
      change (D.wires base).getD (shift C.output) false = target x
      rw [← computes,newRun]
      change _ = (C.wires (base ++ [b])).getD C.output false
      rw [oldRun,wire _ _ _ len _ noOut]
  have finish := search A B g C.output
  dsimp only at finish
  rw [← splitG] at finish
  apply finish fan back sz ?_ gOr nine ?_ feasible computes
  · intro h hh
    have ops : h.op = .and ∨ h.op = .or ∨ h.op = .not := (fan h hh).1
    rcases ops with ha | ho | hn
    · have bit : h.op.eval [false,false] = false := by rw [ha]; rfl
      simpa only [bit,Bool.false_eq_true,ite_false] using (clean h hh).2 (by rw [ha]; intro e; cases e)
    · have bit : h.op.eval [false,false] = false := by rw [ho]; rfl
      simpa only [bit,Bool.false_eq_true,ite_false] using (clean h hh).2 (by rw [ho]; intro e; cases e)
    · have bit : h.op.eval [false,false] = true := by rw [hn]; rfl
      simpa only [bit,ite_true] using (clean h hh).1 hn
  · let c := fun v => C.gates.countP (fun h => decide (v ∈ h.inputs))
    have nineCount : c 9 = 1 := by simp [c,List.countP_eq_length_filter,filterG]
    have rule : ∀ (v : Fin 10) (k : Fin 4),
        (v.val ∈ ([0,2,9] : List ℕ) → k.val = 1) →
        (v.val ∈ ([4,6,7] : List ℕ) → k.val ≤ 2) →
        (203876201202 : ℕ).testBit (4*v.val + k.val) = true := by decide
    intro v
    have mx : c v.val ≤ 3 := by
      by_cases eq : v.val = 9
      · rw [eq,nineCount]; decide
      · simpa only [c,List.countP_eq_length_filter] using thrice (⟨v.val,by have := v.isLt;omega⟩ : Fin 9)
    refine ⟨mx,rule v ⟨c v.val,by omega⟩ ?_ ?_⟩
    · intro hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      change c v.val = 1
      rcases hv with hv|hv|hv
      · rw [hv]; simpa only [c,List.countP_eq_length_filter] using single 0 (by decide)
      · rw [hv]; simpa only [c,List.countP_eq_length_filter] using single 2 (by decide)
      · rw [hv,nineCount]
    · intro hv
      simpa only [c,List.countP_eq_length_filter] using twice v.val hv

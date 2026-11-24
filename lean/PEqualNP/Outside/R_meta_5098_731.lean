import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Two negations leave twelve binary gates. Fixing a multiply read input
-- removes two binary gates after minimum size has ruled out redundant reads.
-- The remaining search tests a single eight-variable cofactor.
theorem PEqualNP.Outside.R_meta_5098_731
  (leastBound : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x4 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x3 x4.1 && x3 x4.2) → (15 : ℕ) ≤ x1.size)
  (restrict : ∀ (n : ℕ) (X : Set (List Bool)) (C : Circuit) (w : Fin n),
    (∀ x ∈ X, x.length = n) → FanInTwo C →
    (∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) →
    (∀ D : Circuit, FanInTwo D → (∀ x ∈ X, D.eval x = C.eval x) → C.size ≤ D.size) →
    2 ≤ (C.gates.flatMap Gate.inputs).count w.val →
    let neg := fun (g : Gate) => g.op.eval [false]
    ∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
      D.gates.countP neg ≤ C.gates.countP neg ∧
      D.gates.countP (fun g => !(neg g)) + 2 ≤ C.gates.countP (fun g => !(neg g)) ∧
      ∀ x ∈ X, x.getD w.val false = false → D.eval x = C.eval x)
  (cofactor : ∀ w ∈ ([0,1,2,4,7,8] : List ℕ), ∀ D : Circuit, FanInTwo D →
    D.size ≤ 12 → D.gates.countP (fun g => g.op.eval [false]) ≤ 2 →
    (∀ r : ℕ, r < 512 → r.testBit w = false →
      D.eval (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 || r.testBit 2]) =
        ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ).any (fun e => r &&& e == e)) →
    11 ≤ D.gates.countP (fun g => !(g.op.eval [false])))
  : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (14 : ℕ) →       x1.output = (23 : ℕ) →         (∀ x5 ∈ x1.gates, x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ)) →           (∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), x6 < x7 ∧ (3 : ℕ) ≤ ↑x6 ∧ ↑x6 ≤ (6 : ℕ) ∧ ↑x7 < (13 : ℕ) ∧ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x8 : Fin x1.gates.length), (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → x8 = x6 ∨ x8 = x7) →             have x7 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates;             have x8 : ℕ → Prop := fun (x8 : ℕ) => x1.eval ((List.ofFn fun (x9 : Fin (9 : ℕ)) => x8.testBit ↑x9) ++ [x8.testBit (0 : ℕ) || x8.testBit (2 : ℕ)]) = [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)].any fun (x9 : ℕ) => x8 &&& x9 == x9;             (∀ x9 < (23 : ℕ), x9 ∈ x7) → {x10 ∈ Finset.range (23 : ℕ) | (2 : ℕ) ≤ List.count x10 x7}.card ≤ (3 : ℕ) → (∀ x11 < (512 : ℕ), x8 x11) → ∀ x12 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (8 : ℕ)], List.count x12 x7 ≤ (1 : ℕ) := by
  intro C fan size _ unit two
  dsimp only
  intro _used _budget correct w hw
  by_contra! multi
  let row (r : ℕ) := List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 || r.testBit 2]
  let target (r : ℕ) := ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ).any (fun e => r &&& e == e)
  let X : Set (List Bool) := Set.range (fun r : Fin 512 => row r.val)
  have cx (r : Fin 512) : C.eval (row r.val) = target r.val := correct r.val r.isLt
  have small : w < 9 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    omega
  let port : Fin 10 := ⟨w,by omega⟩
  have len (x) (hx : x ∈ X) : x.length = 10 := by
    obtain ⟨r,rfl⟩ := hx
    simp [row]
  have minimal (D : Circuit) (fd : FanInTwo D) (same : ∀ x ∈ X, D.eval x = C.eval x) : C.size ≤ D.size := by
    let first : Gate := ⟨.or,[0,2]⟩
    let E : Circuit := ⟨first :: D.gates,D.output⟩
    have fe : FanInTwo E := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | tail
      · exact ⟨by simp [first],by decide⟩
      · exact fd g tail
    have pre : ∀ z : Fin 9 → Bool,
        first.op.eval (first.inputs.map (fun i => (List.ofFn z).getD i false)) = (z 0 || z 2) := by
      decide +kernel
    have ev (z : Fin 9 → Bool) : circuitFun 9 E z = D.eval (List.ofFn z ++ [z 0 || z 2]) := by
      change D.eval (List.ofFn z ++ [first.op.eval (first.inputs.map fun i => (List.ofFn z).getD i false)]) = _
      rw [pre]
    have bits : ∀ z : Fin 9 → Bool, tableIndex z < 512 ∧
        List.ofFn z ++ [z 0 || z 2] = row (tableIndex z) ∧ target (tableIndex z) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => z e.1 && z e.2) := by
      decide +kernel
    have lo := leastBound E fe (by
      funext z
      obtain ⟨h,he,ht⟩ := bits z
      rw [ev,he,same _ (Set.mem_range.mpr ⟨⟨_,h⟩,rfl⟩),cx ⟨_,h⟩,ht])
    have hd : E.size = D.size+1 := rfl
    omega
  obtain ⟨D,fd,count,negs,binary,equiv⟩ := restrict 10 X C port len fan unit minimal (by exact multi)
  let neg (g : Gate) := g.op.eval [false]
  obtain ⟨a,b,hab,_,_,_,ha,hb,only⟩ := two
  have op (i : Fin C.gates.length) : neg (C.gates.get i) = true ↔ (C.gates.get i).op = .not := by
    have ht := (fan (C.gates.get i) (List.get_mem ..)).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
    change (C.gates.get i).op.eval [false] = true ↔ (C.gates.get i).op = .not
    rcases ht with t | t | t <;> rw [t] <;> constructor <;> intro h <;> first | rfl | cases h
  let K := (List.finRange C.gates.length).filter (fun k => neg (C.gates.get k))
  have kn : K.Nodup := List.Nodup.filter _ (List.nodup_finRange _)
  have keep : K.toFinset = {a,b} := by
    ext k
    simp only [K,List.mem_toFinset,List.mem_filter,List.mem_finRange,true_and,Finset.mem_insert,Finset.mem_singleton,op]
    exact ⟨only k, fun h => h.elim (fun hh => hh ▸ ha) (fun hh => hh ▸ hb)⟩
  have num : C.gates.countP neg = 2 := by
    rw [List.countP_eq_length_filter]
    have hk : K.map C.gates.get = C.gates.filter neg := by
      change ((List.finRange _).filter (neg ∘ C.gates.get)).map C.gates.get = _
      rw [← List.filter_map, List.map_get_finRange]
    rw [← hk,List.length_map,← List.toFinset_card_of_nodup kn,keep]
    simp [ne_of_lt hab]
  have total := C.gates.length_eq_countP_add_countP neg
  have complement : (fun g => decide (¬neg g=true)) = (fun g => !(neg g)) := by
    funext g
    cases neg g <;> rfl
  rw [complement,num] at total
  have szD : D.size ≤ 12 := by omega
  change D.gates.countP neg ≤ C.gates.countP neg at negs
  have numD : D.gates.countP neg ≤ 2 := negs.trans num.le
  change C.gates.length = 14 at size
  have get {n : ℕ} (z : Fin n → Bool) (t : List Bool) (i : Fin n) :
      (List.ofFn z ++ t).getD i.val false = z i := by
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [List.getD]
  have low := cofactor w hw D fd szD numD (by
    intro rr bounded off
    let r : Fin 512 := ⟨rr,bounded⟩
    have input : (row r.val).getD port.val false = false := by
      exact (get (fun i : Fin 9 => r.val.testBit i.val) _ ⟨w,small⟩).trans off
    exact (equiv (row r.val) (Set.mem_range.mpr ⟨r,rfl⟩) input).trans (cx r))
  change D.gates.countP (fun g => !(neg g))+2 ≤ C.gates.countP (fun g => !(neg g)) at binary
  change 11 ≤ D.gates.countP (fun g => !(neg g)) at low
  omega

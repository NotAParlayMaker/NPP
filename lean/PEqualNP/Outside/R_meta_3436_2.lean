import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_3436_2
    (ordinary : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (constantCase : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     x1 = [] ∨ x1.headD (10 : ℕ) = (0 : ℕ) ∨ (9 : ℕ) ≤ x1.headD (10 : ℕ) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (bounded : ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (11 : ℕ) * ↑x1 + ↑x2 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (20 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (29 : ℕ), (30 : ℕ), (31 : ℕ), (37 : ℕ), (39 : ℕ), (42 : ℕ), (50 : ℕ), (53 : ℕ), (73 : ℕ), (75 : ℕ)] →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size = (13 : ℕ) → x3.output = 23 → (∀ g ∈ x3.gates, (∀ i ∈ g.inputs, i ≤ 24) ∧ g.inputs.Pairwise (· ≤ ·) ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2) :
    ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (11 : ℕ) * ↑x1 + ↑x2 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (20 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (29 : ℕ), (30 : ℕ), (31 : ℕ), (37 : ℕ), (39 : ℕ), (42 : ℕ), (50 : ℕ), (53 : ℕ), (73 : ℕ), (75 : ℕ)] →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2 := by
  intro a b c hab hfan hsize
  let edges : List (Fin 9 × Fin 9) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  let target (x : Fin 9 → Bool) := edges.any (fun e => x e.1 && x e.2)
  have targetEq (x : Fin 9 → Bool) : target x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    simp [target, edges, Bool.or_assoc]
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  let feed (x : Fin 9 → Bool) := base x ++ [(base x).getD a.val false || (base x).getD b.val false]
  let bits (k : BitVec 9) (i : Fin 9) := k.getLsbD i.val
  have encode (x : Fin 9 → Bool) : ∃ k : BitVec 9, bits k = x := by
    refine ⟨BitVec.ofBoolListLE [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8], ?_⟩
    funext i
    dsimp only [bits]
    rw [BitVec.getLsbD_ofBoolListLE]
    fin_cases i <;> rfl
  change ∃ k : BitVec 9, c.eval (feed (bits k)) ≠ target (bits k)
  by_contra! hno
  have same (x : Fin 9 → Bool) : c.eval (feed x) = target x := by
    obtain ⟨k,hk⟩ := encode x
    simpa only [hk] using hno k
  by_cases trivialCase : 11 * a.val + b.val = 9
  · have ha : a = 0 := Fin.ext (by have := b.isLt; omega)
    have hb : b = 9 := Fin.ext (by have := a.isLt; have := b.isLt; omega)
    subst a
    subst b
    obtain ⟨x, hx⟩ := constantCase [] (by decide) (Or.inl rfl) c hfan hsize
    apply hx
    have hbase0 : (base x).getD 0 false = x 0 := by
      simp [base, List.getD_eq_getElem?_getD]
    have hbase9 : (base x).getD 9 false = !x 0 := by
      simp [base, List.getD_eq_getElem?_getD]
    have hfeed : feed x = base x ++ [true] := by
      change base x ++ [(base x).getD 0 false || (base x).getD 9 false] = _
      rw [hbase0, hbase9]; cases x 0 <;> rfl
    have hs := same x
    rw [hfeed] at hs
    exact hs.trans (targetEq x)
  have shorter (D : Circuit) (hd : FanInTwo D)
      (hcorrect : ∀ x, D.eval (feed x) = target x) : 13 ≤ D.size := by
    let leadGates : List Gate := [⟨.not,[0]⟩,⟨.or,[a.val,b.val]⟩]
    let E : Circuit := ⟨leadGates ++ D.gates,D.output⟩
    have heFan : FanInTwo E := by
      intro g hg
      change g ∈ leadGates ++ D.gates at hg
      rcases List.mem_append.mp hg with h | h
      · simp only [leadGates, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> simp
      · exact hd g h
    have hs := ordinary E heFan (by
      funext x
      change E.eval (List.ofFn x) = _
      have read0 : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD_eq_getElem?_getD]
      let run := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have first : run (List.ofFn x) ⟨.not,[0]⟩ = base x := by
        change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = List.ofFn x ++ [!x 0]
        rw [read0]
      have second : run (base x) ⟨.or,[a.val,b.val]⟩ = feed x := by
        change base x ++ [((base x).getD a.val false || ((base x).getD b.val false || false))] = _
        simp only [Bool.or_false]; rfl
      change (D.gates.foldl run (run (run (List.ofFn x) ⟨.not,[0]⟩) ⟨.or,[a.val,b.val]⟩)).getD D.output false = _
      rw [first,second]
      exact (hcorrect x).trans (targetEq x))
    change 15 ≤ (leadGates ++ D.gates).length at hs
    simp only [leadGates, List.length_append, List.length_cons, List.length_nil] at hs
    change 13 ≤ D.gates.length
    omega
  have h13 : c.size = 13 := Nat.le_antisymm hsize (shorter c hfan same)
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wlen (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
  have feedlen (x : Fin 9 → Bool) : (feed x).length = 11 := by simp [feed, base]
  have out : c.output = 23 := by
    by_contra ho
    have hn : c.gates ≠ [] := by intro h; change c.gates.length = 13 at h13; simp [h] at h13
    let D : Circuit := ⟨c.gates.dropLast,c.output⟩
    have hd : FanInTwo D := fun g hg => hfan g (List.mem_of_mem_dropLast hg)
    have hh := shorter D hd (fun x => by
      rw [← same x]
      change (c.gates.dropLast.foldl step (feed x)).getD c.output false =
        (c.gates.foldl step (feed x)).getD c.output false
      conv_rhs => rw [← List.dropLast_append_getLast hn]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      let w := c.gates.dropLast.foldl step (feed x)
      have hl : w.length = 23 := by
        change c.gates.length = 13 at h13
        simp [w, wlen, feedlen, List.length_dropLast, h13]
      change w.getD c.output false = (w ++ [_]).getD c.output false
      by_cases h : c.output < w.length
      · simp [List.getD_eq_getElem?_getD, List.getElem?_append, h]
      · have h1 : w.length ≤ c.output := by omega
        have h2 : w.length+1 ≤ c.output := by omega
        rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ (by simpa using h2)])
    change 13 ≤ c.gates.dropLast.length at hh
    change c.gates.length = 13 at h13
    simp [List.length_dropLast,h13] at hh
  let clamp := fun i : ℕ => min i 24
  let le := fun (i j : ℕ) => decide (i ≤ j)
  have bitAnd : GateOp.and.eval [false] = false := rfl
  have bitOr : GateOp.or.eval [false] = false := rfl
  have bitNot : GateOp.not.eval [false] = true := rfl
  let clean := fun g : Gate => let q := g.inputs.map clamp
    (⟨g.op, if g.op.eval [false] then q.take 1 else q.mergeSort le⟩ : Gate)
  let D : Circuit := ⟨c.gates.map clean,c.output⟩
  have fanD : FanInTwo D := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    rcases t with ⟨op,ins⟩
    obtain ⟨ha,hn⟩ := hfan _ ht
    cases op <;> simp_all [clean]
  have canonical : ∀ g ∈ D.gates, (∀ i ∈ g.inputs, i ≤ 24) ∧ g.inputs.Pairwise (· ≤ ·) ∧
      (g.op = GateOp.not → g.inputs.length ≤ 1) := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    have lim : ∀ i ∈ t.inputs.map clamp, i ≤ 24 := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      exact Nat.min_le_right _ _
    have sorted := List.pairwise_mergeSort (le := le)
      (fun a b c h1 h2 => by simpa [le] using Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))
      (fun a b => by simpa [le] using Nat.le_total a b) (t.inputs.map clamp)
    cases t with
    | mk op ins =>
      obtain h | h | h := (hfan _ ht).1
      all_goals change op = _ at h; subst op
      all_goals simp only [clean,bitAnd,bitOr,bitNot, Bool.false_eq_true, ↓reduceIte]
      all_goals first | exact ⟨(fun i h => lim i (List.mem_mergeSort.mp h)),sorted.imp (fun h => of_decide_eq_true h),by simp⟩
                      | exact ⟨(fun i h => lim i (List.mem_of_mem_take h)), (by cases ins <;> simp),by simp⟩
  have simulates : ∀ (gs : List Gate) (w : List Bool), w.length + gs.length ≤ 24 →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) →
      ((gs.map clean).foldl step w) = gs.foldl step w := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro w hlen hall
      have reads : ∀ i, w.getD (clamp i) false = w.getD i false := by
        intro i
        by_cases hi : i ≤ 24
        · simp [clamp, Nat.min_eq_left hi]
        · rw [show clamp i = 24 from Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have pins : ((g.inputs.map clamp).map (fun i => w.getD i false)) = g.inputs.map (fun i => w.getD i false) := by
        simp only [List.map_map, Function.comp_def, reads]
      have perm := ((g.inputs.map clamp).mergeSort_perm le).map (fun i => w.getD i false)
      have agree : step w (clean g) = step w g := by
        rcases g with ⟨op,ins⟩
        have hh := hall ⟨op,ins⟩ (by simp)
        rcases hh with h | h | h <;> change op = _ at h <;> subst op
        · exact congrArg (fun b => w ++ [b]) (by exact perm.all_eq.trans (congrArg (fun q : List Bool => q.all id) pins))
        · exact congrArg (fun b => w ++ [b]) (by exact perm.any_eq.trans (congrArg (fun q : List Bool => q.any id) pins))
        · change w ++ [!((((ins.map clamp).take 1).map (fun i => w.getD i false)).headD false)] =
              w ++ [!((ins.map (fun i => w.getD i false)).headD false)]
          cases ins with
          | nil => rfl
          | cons i t => exact congrArg (fun b : Bool => w ++ [!b]) (reads i)
      simp only [List.map_cons, List.foldl_cons, agree]
      apply ih
      · simp [step] at *; omega
      · exact fun t ht => hall t (List.mem_cons_of_mem _ ht)
  have cm : 11 * a.val + b.val ∈ ([1,2,3,4,6,13,14,15,16,17,18,19,20,25,26,28,29,30,31,37,39,42,50,53,73,75] : List ℕ) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hab ⊢
    tauto
  obtain ⟨k,hk⟩ := bounded a b D cm fanD (by change (c.gates.map clean).length = 13; rw [List.length_map]; exact h13) out canonical
  apply hk
  change ((c.gates.map clean).foldl step (feed (bits k))).getD c.output false = target (bits k)
  rw [simulates _ _ (by change c.gates.length = 13 at h13; rw [feedlen,h13]) (fun g hg => (hfan g hg).1)]
  exact same (bits k)

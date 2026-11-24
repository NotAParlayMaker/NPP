import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The two residuals distinguish side signals depending on two primary bits
-- from those requiring at least three. With two bits the pair must be an
-- edge, and the signal must be its AND or its complement. The triangular
-- adjacency mask has bit j*(j-1)/2+i for each graph edge i<j.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_2850_347
    (sibling : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (pair_case :
      let F := fun x : Fin 9 → Bool => decide (∃ i j : Fin 9, i < j ∧
  (27992852069 : Nat).testBit (j.val*(j.val-1)/2+i.val) ∧ x i ∧ x j)
      ∀ (p s : List Gate) (g : Gate) (j o : ℕ),
        let C : Circuit := ⟨p ++ g :: s,o⟩
        let A := fun y : Fin 8 → Bool => circuitFun 9 ⟨p,j⟩ (Fin.cons false y)
        FanInTwo C → C.size = 14 →
        (∀ E : Circuit, FanInTwo E → circuitFun 9 E = circuitFun 9 C → C.size ≤ E.size) →
        9 ≤ j → j < 9 + p.length →
        (g.op = .and ∨ g.op = .or) → (g.inputs = [0,j] ∨ g.inputs = [j,0]) →
        (∀ h ∈ p ++ s, 0 ∉ h.inputs) → (∃ h ∈ s, h.op = .not) →
        (∃ a b : Fin 8, F (Fin.cons false fun i => decide (i=a ∨ i=b)) = true ∧
          ∀ y, A y = (if y a && y b then g.op.eval [true,false] else !g.op.eval [true,false])) →
        (∀ x, circuitFun 9 C (fun i : Fin 9 => if i = 0 then !x 0 else x i) = F x) → 15 ≤ C.size)
    (larger_case :
      let F := fun x : Fin 9 → Bool => decide (∃ i j : Fin 9, i < j ∧
  (27992852069 : Nat).testBit (j.val*(j.val-1)/2+i.val) ∧ x i ∧ x j)
      ∀ (p s : List Gate) (g : Gate) (j o : ℕ),
        let C : Circuit := ⟨p ++ g :: s,o⟩
        let A := fun y : Fin 8 → Bool => circuitFun 9 ⟨p,j⟩ (Fin.cons false y)
        FanInTwo C → C.size = 14 →
        (∀ E : Circuit, FanInTwo E → circuitFun 9 E = circuitFun 9 C → C.size ≤ E.size) →
        9 ≤ j → j < 9 + p.length →
        (g.op = .and ∨ g.op = .or) → (g.inputs = [0,j] ∨ g.inputs = [j,0]) →
        (∀ h ∈ p ++ s, 0 ∉ h.inputs) → (∃ h ∈ s, h.op = .not) →
        (¬ ∃ (a b : Fin 8) (q : Bool → Bool → Bool), ∀ y, A y = q (y a) (y b)) →
        (∀ y, F (Fin.cons false y) ≠ F (Fin.cons true y) → A y = !g.op.eval [true,false]) →
        (∀ x, circuitFun 9 C (fun i : Fin 9 => if i = 0 then !x 0 else x i) = F x) → 15 ≤ C.size)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → x2 = Bool.true → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  classical
  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have eval_not (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have size_eq (c : Circuit) : c.size = c.gates.length := rfl
  let F (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5

  -- The bit numbered j*(j-1)/2+i codes the unordered pair i<j.
  let encoded (x : Fin 9 → Bool) : Bool := decide (∃ i j : Fin 9, i < j ∧
    (27992852069 : Nat).testBit (j.val*(j.val-1)/2+i.val) ∧ x i ∧ x j)

  have encoded_correct : ∀ x : Fin 9 → Bool, F x = encoded x := by
    dsimp only [F,encoded]
    decide +kernel

  let run (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  let flip (x : Fin 9 → Bool) (i : Fin 9) : Bool := if i = 0 then !x 0 else x i

  let reads (g : Gate) : Bool := g.inputs.contains 0

  have first_eq (gs : List Gate) (b : Bool) (t : List Bool) :
      (run gs (b :: t)).getD 0 false = b := by
    induction gs generalizing t with
    | nil => rfl
    | cons g gs ih => exact ih _

  have common (gs : List Gate) (hn : ∀ g ∈ gs, reads g = false)
      (t : List Bool) : ∃ u, ∀ b : Bool, run gs (b :: t) = b :: u := by
    induction gs generalizing t with
    | nil => exact ⟨t,fun _ => rfl⟩
    | cons g gs ih =>
      have free : 0 ∉ g.inputs := by simpa [reads] using hn g List.mem_cons_self
      let val := g.op.eval (g.inputs.map fun i => (false :: t).getD i false)
      have he (b : Bool) : g.op.eval (g.inputs.map fun i => (b :: t).getD i false) = val := by
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro i hi
        cases i with
        | zero => exact (free hi).elim
        | succ i => rfl
      obtain ⟨u,hu⟩ := ih (fun h hh => hn h (List.mem_cons_of_mem g hh)) (t ++ [val])
      refine ⟨u, fun b => ?_⟩
      change run gs (b :: (t ++ [_])) = _
      rw [he]
      exact hu b

  have read_cut (gs : List Gate) (one : (gs.filter reads).length ≤ 1) :
      (∀ g ∈ gs, reads g = false) ∨
      ∃ p g s, gs = p ++ g :: s ∧ reads g = true ∧
        (∀ h ∈ p, reads h = false) ∧ (∀ h ∈ s, reads h = false) := by
    induction gs with
    | nil => simp
    | cons a l ih =>
      cases h : reads a with
      | true =>
        have empty : l.filter reads = [] := List.length_eq_zero_iff.mp (by simpa [h] using one)
        refine Or.inr ⟨[],a,l,rfl,h,by simp,?_⟩
        intro g hg
        cases z : reads g with
        | false => rfl
        | true =>
          have hm : g ∈ l.filter reads := List.mem_filter.mpr ⟨hg,z⟩
          simp [empty] at hm
      | false =>
        rcases ih (by simpa [h] using one) with na | ⟨p,g,s,hg,r,fp,fs⟩
        · exact Or.inl (by simpa [h] using And.intro h na)
        · refine Or.inr ⟨a::p,g,s,by simp [hg],r,?_,fs⟩
          simpa using And.intro h fp

  have eval_cut (p : List Gate) (g : Gate) (s : List Gate)
      (hp : ∀ h ∈ p, reads h = false) (hs : ∀ h ∈ s, reads h = false)
      (o : ℕ) (ho : o ≠ 0) (t : List Bool) :
      ∃ u : List Bool, ∃ K : Bool → Bool,
        (∀ b : Bool, run p (b :: t) = b :: u) ∧
        ∀ b : Bool, (run (p ++ g :: s) (b :: t)).getD o false =
          K (g.op.eval (g.inputs.map fun i => (b :: u).getD i false)) := by
    obtain ⟨u,hu⟩ := common p hp t
    let K := fun z : Bool => (run s (false :: (u ++ [z]))).getD o false
    refine ⟨u,K,hu,fun b => ?_⟩
    simp only [run, List.foldl_append, List.foldl_cons]
    change (run s (run p (b :: t) ++
      [g.op.eval (g.inputs.map fun i => (run p (b :: t)).getD i false)])).getD o false = _
    rw [hu b]
    obtain ⟨v,hv⟩ := common s hs (u ++ [g.op.eval (g.inputs.map fun i => (b :: u).getD i false)])
    change (run s (b :: (u ++ [_]))).getD o false = (run s (false :: (u ++ [_]))).getD o false
    rw [hv b,hv false]
    cases o with
    | zero => contradiction
    | succ o => rfl

  have first_wires (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (w ++ [_])).getD i false = _
      rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]

  have flip_cons (b : Bool) (y : Fin 8 → Bool) :
      List.ofFn (flip (Fin.cons b y)) = (!b) :: List.ofFn y := by
    rw [List.ofFn_succ]
    simp [flip,Fin.cons_zero,Fin.cons_succ]

  let witnessMask (d : Bool) (j : Fin 8) : Nat :=
    if d then ![1,10,5,8,16,40,65,129] j else ![8,1,1,1,1,1,1,1] j

  have pivot (j : Fin 8) (d : Bool) : ∃ y : Fin 8 → Bool, y j = d ∧
      F (Fin.cons false y) = false ∧ F (Fin.cons true y) = true := by
    refine ⟨fun i => (witnessMask d j).testBit i.val, ?_⟩
    fin_cases j <;> cases d <;> dsimp only [F,witnessMask] <;> decide

  let edgePair (i j : Fin 8) : Bool :=
    F (Fin.cons false fun k => decide (k=i ∨ k=j))

  let row (i j : Fin 8) (a b : Bool) : Fin 8 → Bool :=
    let witnesses : Fin 8 → Fin 32 → Nat :=
      ![![8,0,0,1,8,10,1,0,8,20,1,5,16,8,1,9,8,16,1,17,8,40,1,0,8,72,1,65,8,136,1,129],
        ![8,1,10,0,1,0,0,10,1,5,10,0,1,8,18,10,1,16,10,18,1,40,10,42,1,65,10,0,1,129,10,138],
        ![8,1,20,5,1,10,5,0,1,0,0,5,1,8,5,0,1,16,5,20,1,40,5,52,1,65,5,69,1,129,5,0],
        ![16,1,8,9,1,18,8,10,1,5,8,0,1,0,0,8,1,16,8,24,1,48,8,40,1,65,8,72,1,129,8,136],
        ![8,1,16,17,1,10,16,18,1,5,16,20,1,8,16,24,1,0,0,16,1,40,16,48,1,65,16,0,1,129,16,0],
        ![8,1,40,0,1,10,40,42,1,5,40,52,1,8,48,40,1,16,40,48,1,0,0,40,1,65,40,104,1,129,40,0],
        ![8,1,72,65,1,10,65,0,1,5,65,69,1,8,65,72,1,16,65,0,1,40,65,104,1,0,0,65,1,129,65,193],
        ![8,1,136,129,1,10,129,138,1,5,129,0,1,8,129,136,1,16,129,0,1,40,129,0,1,65,129,193,1,0,0,129]]
    let code := Fin.ofNat 32 (4*j.val + (if a then 2 else 0) + (if b then 1 else 0))
    fun k => (witnesses i code).testBit k.val

  have row_checked : ∀ (i j : Fin 8) (a b : Bool),
      (i = j → a = b) → (a && b && edgePair i j) = false →
      let y := row i j a b
      y i = a ∧ y j = b ∧ F (Fin.cons false y) = false ∧ F (Fin.cons true y) = true := by
    dsimp only [row,edgePair,F]
    decide +kernel

  have two_variables (A : (Fin 8 → Bool) → Bool) (d : Bool)
      (varying : ∀ b, ∃ y, A y = b)
      (critical : ∀ y : Fin 8 → Bool, F (Fin.cons false y) ≠ F (Fin.cons true y) → A y = d)
      (i j : Fin 8) (q : Bool → Bool → Bool) (eqn : ∀ y : Fin 8 → Bool, A y = q (y i) (y j)) :
      edgePair i j = true ∧ ∀ y, A y = (if y i && y j then !d else d) := by
    have pin (y : Fin 8 → Bool) (absent : ((y i && y j) && edgePair i j) = false) : A y = d := by
      obtain ⟨hi,hj,h0,h1⟩ := row_checked i j (y i) (y j) (fun h => congrArg y h) absent
      have v := critical (row i j (y i) (y j)) (by rw [h0,h1]; decide)
      rwa [eqn,hi,hj,← eqn y] at v
    obtain ⟨z,hz⟩ := varying (!d)
    have ne : A z ≠ d := by rw [hz]; cases d <;> decide
    have active : ((z i && z j) && edgePair i j) = true := by
      cases h : ((z i && z j) && edgePair i j)
      · exact (ne (pin z h)).elim
      · rfl
    obtain ⟨⟨hi,hj⟩,edge⟩ := Bool.and_eq_true_iff.mp active
      |>.imp_left Bool.and_eq_true_iff.mp
    have hh : q true true = !d := by simpa [eqn z,hi,hj] using hz
    refine ⟨edge, fun y => ?_⟩
    cases pair : y i && y j with
    | false => simpa using pin y (by rw [pair]; rfl)
    | true =>
      obtain ⟨yi,yj⟩ := Bool.and_eq_true_iff.mp pair
      simpa [eqn y,yi,yj] using hh

  let allowed (g : Gate) : Prop :=
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

  have negAllowed (a : Nat) : allowed ⟨.not,[a]⟩ :=
    ⟨Or.inr (Or.inr rfl), by change 1 ≤ 2; decide⟩

  have idAllowed : allowed ⟨.or,[0]⟩ :=
    ⟨Or.inr (Or.inl rfl), by decide⟩

  let ev (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

  -- Supply the inverted first coordinate by one real gate and shift all gate
  -- references. This works for unrestricted fan-out and for invalid references.
  have prepend_not (D : Circuit) (hf : FanInTwo D) :
      ∃ E : Circuit, FanInTwo E ∧ E.size = D.size+1 ∧
        ∀ x : Fin 9 → Bool, circuitFun 9 E x = circuitFun 9 D (flip x) := by
    let sh := fun i : ℕ => if i = 0 then 9 else if i < 9 then i else i+1
    let ren := fun g : Gate => (⟨g.op,g.inputs.map sh⟩ : Gate)
    let inv : Gate := ⟨.not,[0]⟩
    let E : Circuit := ⟨inv :: D.gates.map ren,sh D.output⟩
    refine ⟨E,?_,by simp [E,size_eq],?_⟩
    · intro g hg
      change g ∈ inv :: D.gates.map ren at hg
      rcases List.mem_cons.mp hg with rfl | hm
      · exact negAllowed 0
      · obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hm
        exact ⟨(hf h hh).1,by simpa [ren] using (hf h hh).2⟩
    intro x
    let a := List.ofFn x ++ [!x 0]
    let b := List.ofFn (flip x)
    have lookup (r : List Bool) (i : ℕ) :
        (a ++ r).getD (sh i) false = (b ++ r).getD i false := by
      by_cases z : i = 0
      · subst i
        simp only [a,b,sh,ite_true]
        rw [List.getD_append _ _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)]
        rw [List.getD_append _ _ _ _ (by simp)]
        simp [flip]
      by_cases short : i < 9
      · simp only [a,b,sh,z,short,ite_false,ite_true]
        rw [List.getD_append _ _ _ _ (by simp; omega),List.getD_append _ _ _ _ (by simp; omega)]
        rw [List.getD_append _ _ _ _ (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simpa using short),List.getD_eq_getElem _ _ (by simpa using short)]
        simp only [List.getElem_ofFn]
        have nz : (⟨i,short⟩ : Fin 9) ≠ 0 := fun h => z (congrArg Fin.val h)
        change x ⟨i,short⟩ = (if (⟨i,short⟩ : Fin 9) = 0 then !x 0 else x ⟨i,short⟩)
        rw [if_neg nz]
      · simp only [a,b,sh,z,short,ite_false]
        rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_append,List.length_ofFn,List.length_singleton]
        congr 1 <;> omega
    have simulate (gs : List Gate) (r : List Bool) :
        ∃ t, run (gs.map ren) (a ++ r) = a ++ t ∧ run gs (b ++ r) = b ++ t := by
      induction gs generalizing r with
      | nil => exact ⟨r,rfl,rfl⟩
      | cons g gs ih =>
        have equal : ev (ren g) (a ++ r) = ev g (b ++ r) := by
          change g.op.eval ((g.inputs.map sh).map _) = _
          rw [List.map_map]
          exact congrArg g.op.eval (List.map_congr_left (fun i _ => lookup r i))
        obtain ⟨t,h1,h2⟩ := ih (r ++ [ev g (b ++ r)])
        refine ⟨t,?_,?_⟩
        · change run (gs.map ren) ((a ++ r) ++ [ev (ren g) (a ++ r)]) = _
          rw [equal,List.append_assoc,h1]
        · change run gs ((b ++ r) ++ [ev g (b ++ r)]) = _
          rw [List.append_assoc,h2]
    obtain ⟨t,h1,h2⟩ := simulate D.gates []
    simp only [List.append_nil] at h1 h2
    have real : ev inv (List.ofFn x) = !x 0 := by simp [ev,inv,eval_not]
    change (run (D.gates.map ren) (List.ofFn x ++ [ev inv (List.ofFn x)])).getD (sh D.output) false =
      (run D.gates b).getD D.output false
    rw [real]
    change (run (D.gates.map ren) a).getD (sh D.output) false = _
    rw [h1,h2,lookup]

  have replace_gate (H : (Fin 9 → Bool) → Bool) (p : List Gate) (g h : Gate) (s : List Gate) (o : ℕ)
      (hp : ∀ a ∈ p, reads a = false) (hs : ∀ a ∈ s, reads a = false) (ho : o ≠ 0)
      (eqv : ∀ (b : Bool) (y : Fin 8 → Bool),
        ev h (run p (b :: List.ofFn y)) = ev g (run p ((!b) :: List.ofFn y)))
      (fits : ∀ x, circuitFun 9 ⟨p ++ g :: s,o⟩ (flip x) = H x) :
      circuitFun 9 ⟨p ++ h :: s,o⟩ = H := by
    funext x
    obtain ⟨b,y,rfl⟩ := Fin.consCases (motive := fun x : Fin 9 → Bool => ∃ b y, x = Fin.cons b y)
      (fun b y => ⟨b,y,rfl⟩) x
    have old := fits (Fin.cons b y)
    change (run (p ++ g :: s) (List.ofFn (flip (Fin.cons b y)))).getD o false = _ at old
    rw [flip_cons] at old
    change (run (p ++ h :: s) (List.ofFn (Fin.cons b y))).getD o false = _
    rw [List.ofFn_succ]
    simp only [Fin.cons_zero,Fin.cons_succ]
    rw [← old]
    have parts (a : Gate) (v : List Bool) :
        run (p ++ a :: s) v = run s ((run p v) ++ [ev a (run p v)]) := by
      simp only [run,ev,List.foldl_append,List.foldl_cons]
    rw [parts,parts,eqv b y]
    obtain ⟨u,hu⟩ := common p hp (List.ofFn y)
    rw [hu b, hu (!b)]
    obtain ⟨v,hv⟩ := common s hs (u ++ [ev g ((!b) :: u)])
    change (run s (b :: (u ++ [_]))).getD o false = (run s ((!b) :: (u ++ [_]))).getD o false
    rw [hv b,hv (!b)]
    cases o with
    | zero => contradiction
    | succ o => rfl

  -- A single gate receiving only the distinguished bit can absorb a reversal
  -- of the bit simply by replacing that gate. A genuinely mixed binary gate is
  -- the only exception, even when NOT ignores a second syntactic operand.
  have shape (g : Gate) (hg : allowed g) (hr : reads g = true) :
      (∃ h : Gate, allowed h ∧ ∀ (b : Bool) (u : List Bool), ev h (b::u) = ev g ((!b)::u)) ∨
      (∃ j : ℕ, j ≠ 0 ∧ (g.op = .and ∨ g.op = .or) ∧
        (g.inputs = [0,j] ∨ g.inputs = [j,0])) := by
    obtain ⟨op,l⟩ := g
    obtain ⟨ops, len⟩ := hg
    change (op = .and ∨ op = .or ∨ op = .not) at ops
    change l.length ≤ 2 at len
    change l.contains 0 = true at hr
    cases l with
    | nil => contradiction
    | cons a l =>
      cases l with
      | nil =>
        have az : a = 0 := Eq.symm (by simpa using hr)
        subst a
        rcases ops with rfl | rfl | rfl
        · exact Or.inl ⟨⟨.not,[0]⟩,negAllowed _,fun b _ => by cases b <;> rfl⟩
        · exact Or.inl ⟨⟨.not,[0]⟩,negAllowed _,fun b _ => by cases b <;> rfl⟩
        · exact Or.inl ⟨⟨.or,[0]⟩,idAllowed,fun b _ => by cases b <;> rfl⟩
      | cons c l =>
        have le : l.length = 0 := by change l.length + 1 + 1 ≤ 2 at len; omega
        have empty := List.length_eq_zero_iff.mp le
        subst l
        have hits' : 0 = a ∨ 0 = c := by simpa using hr
        have hits : a = 0 ∨ c = 0 := hits'.imp Eq.symm Eq.symm
        by_cases ha : a = 0 <;> by_cases hc : c = 0
        · subst a; subst c
          rcases ops with rfl | rfl | rfl
          · exact Or.inl ⟨⟨.not,[0]⟩,negAllowed _,fun b _ => by cases b <;> rfl⟩
          · exact Or.inl ⟨⟨.not,[0]⟩,negAllowed _,fun b _ => by cases b <;> rfl⟩
          · exact Or.inl ⟨⟨.or,[0]⟩,idAllowed,fun b _ => by cases b <;> rfl⟩
        · subst a
          rcases ops with h | h | rfl
          · exact Or.inr ⟨c,hc,Or.inl h,Or.inl rfl⟩
          · exact Or.inr ⟨c,hc,Or.inr h,Or.inl rfl⟩
          · exact Or.inl ⟨⟨.or,[0]⟩,idAllowed,fun b _ => by cases b <;> rfl⟩
        · subst c
          rcases ops with h | h | rfl
          · exact Or.inr ⟨a,ha,Or.inl h,Or.inr rfl⟩
          · exact Or.inr ⟨a,ha,Or.inr h,Or.inr rfl⟩
          · refine Or.inl ⟨⟨.not,[a]⟩,negAllowed a,fun b u => ?_⟩
            cases a with
            | zero => contradiction
            | succ a => rfl
        · exact (hits.elim ha hc).elim

  let side (p : List Gate) (j : ℕ) (y : Fin 8 → Bool) : Bool :=
    (run p (false :: List.ofFn y)).getD j false

  have value (g : Gate) (j : ℕ) (hj : j ≠ 0)
      (ops : g.op = .and ∨ g.op = .or) (ins : g.inputs = [0,j] ∨ g.inputs = [j,0])
      (b : Bool) (u : List Bool) :
      ev g (b::u) =
        if g.op.eval [true,false] then b || (false::u).getD j false
        else b && (false::u).getD j false := by
    have same : (b::u).getD j false = (false::u).getD j false := by
      cases j <;> first | contradiction | rfl
    simp only [List.getD_eq_getElem?_getD] at same
    rcases ops with h | h <;> rcases ins with k | k <;>
      simp [ev,h,k,eval_and,eval_or,same,Bool.and_comm,Bool.or_comm]

  have run_length (p : List Gate) (w : List Bool) :
      (run p w).length = w.length + p.length := by
    induction p generalizing w with
    | nil => simp [run]
    | cons g p ih =>
      change (run p (w ++ [_])).length = _
      rw [ih]
      simp; omega

  have increasing (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (a b : List Bool) (len : a.length = b.length)
      (ord : ∀ i, a.getD i false = true → b.getD i false = true) :
      ∀ i, (run gs a).getD i false = true → (run gs b).getD i false = true := by
    induction gs generalizing a b with
    | nil => exact ord
    | cons g gs ih =>
      have mono : ev g a = true → ev g b = true := by
        rcases ops g List.mem_cons_self with hop | hop
        · simpa only [ev,hop,eval_and,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
            using (fun (h : ∀ i ∈ g.inputs, a.getD i false = true) i hi => ord i (h i hi))
        · simp only [ev,hop,eval_or,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
          rintro ⟨i,hi,ha⟩
          exact ⟨i,hi,ord i ha⟩
      apply ih (fun h hh => ops h (List.mem_cons_of_mem _ hh)) (a ++ [ev g a]) (b ++ [ev g b])
        (by simp [len])
      intro i
      by_cases before : i < a.length
      · rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ (by omega)]
        exact ord i
      by_cases here : i = a.length
      · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
        simpa [here,← len] using mono
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        exact fun h => (Bool.false_ne_true h).elim

  have mixed (H : (Fin 9 → Bool) → Bool) (k : ℕ)
      (zero : H (Fin.cons false (fun _ => false)) = false)
      (piv : ∀ (j : Fin 8) (d : Bool), ∃ y : Fin 8 → Bool, y j = d ∧
        H (Fin.cons false y) = false ∧ H (Fin.cons true y) = true)
      (lower : ¬ HasCircuitSize 9 H k)
      (D : Circuit) (fan : FanInTwo D) (small : D.size ≤ k)
      (one : (D.gates.filter reads).length ≤ 1)
      (good : ∀ x : Fin 9 → Bool, circuitFun 9 D (flip x) = H x) :
      ∃ (p : List Gate) (g : Gate) (s : List Gate) (j : ℕ),
        D.gates = p ++ g :: s ∧ 9 ≤ j ∧ j < 9+p.length ∧
        (g.op = .and ∨ g.op = .or) ∧ (g.inputs = [0,j] ∨ g.inputs = [j,0]) ∧
        (∀ h ∈ p ++ s, 0 ∉ h.inputs) ∧
        (∃ h ∈ s, h.op = .not) ∧
        (∀ b : Bool, ∃ y : Fin 8 → Bool, side p j y = b) ∧
        (∀ y : Fin 8 → Bool, H (Fin.cons false y) ≠ H (Fin.cons true y) →
          side p j y = !g.op.eval [true,false]) := by
    obtain ⟨gs,o⟩ := D
    change ∀ x, (run gs (List.ofFn (flip x))).getD o false = H x at good
    have ho : o ≠ 0 := by
      rintro rfl
      have h := good (Fin.cons false (fun _ => false))
      rw [zero,flip_cons,first_eq] at h
      contradiction
    obtain no | ⟨p,g,s,rfl,hr,hp,hs⟩ := read_cut gs one
    · obtain ⟨y,_,h0,h1⟩ := piv 0 false
      have a := good (Fin.cons false y)
      have b := good (Fin.cons true y)
      obtain ⟨u,hu⟩ := common gs no (List.ofFn y)
      rw [flip_cons,hu,h0] at a
      rw [flip_cons,hu,h1] at b
      cases o with
      | zero => contradiction
      | succ o => exact (Bool.false_ne_true (a.symm.trans b)).elim
    have gmem : g ∈ p ++ g :: s := by simp
    have noReplace (h : Gate) (hok : allowed h)
        (equal : ∀ (b : Bool) (y : Fin 8 → Bool),
          ev h (run p (b::List.ofFn y)) = ev g (run p ((!b)::List.ofFn y))) : False := by
      apply lower
      let C : Circuit := ⟨p ++ h :: s,o⟩
      refine ⟨C,?_,?_,?_⟩
      · intro a ha
        change a ∈ p ++ h :: s at ha
        simp only [List.mem_append,List.mem_cons] at ha
        rcases ha with ha | rfl | ha
        · exact fan a (List.mem_append_left _ ha)
        · exact hok
        · exact fan a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
      · simpa [C,size_eq] using small
      · exact congrFun (replace_gate H p g h s o hp hs ho equal good)
    obtain ⟨h,hok,absorb⟩ | ⟨j,hj,ops,ins⟩ := shape g (fan g gmem) hr
    · exact (noReplace h hok (fun b y => by
        obtain ⟨u,hu⟩ := common p hp (List.ofFn y)
        rw [hu b,hu (!b)]
        exact absorb b u)).elim
    have critical (y : Fin 8 → Bool) (different : H (Fin.cons false y) ≠ H (Fin.cons true y)) :
        side p j y = !g.op.eval [true,false] := by
      obtain ⟨u,K,hu,eqK⟩ := eval_cut p g s hp hs o ho (List.ofFn y)
      have transfer (b : Bool) :
          H (Fin.cons b y) = K (if g.op.eval [true,false] then (!b) || side p j y
            else (!b) && side p j y) := by
        rw [← good (Fin.cons b y),flip_cons,eqK]
        apply congrArg K
        change ev g ((!b)::u) = _
        rw [value g j hj ops ins]
        simp only [side,hu false]
      have a := transfer false
      have b := transfer true
      rw [a,b] at different
      cases h : g.op.eval [true,false] <;> cases v : side p j y <;>
        simp [h,v] at different ⊢
    have lo : 9 ≤ j := by
      by_contra! lt
      let i : Fin 8 := ⟨j-1,by omega⟩
      obtain ⟨y,hd,h0,h1⟩ := piv i (g.op.eval [true,false])
      have selected := critical y (by rw [h0,h1]; decide)
      have keep : side p j y = y i := by
        change (run p (false :: List.ofFn y)).getD j false = y i
        rw [first_wires _ _ _ (by simp; omega)]
        obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        change (List.ofFn y).getD j false = y _
        rw [List.getD_eq_getElem _ _ (by simp; omega),List.getElem_ofFn]
        rfl
      rw [keep,hd] at selected
      cases hval : g.op.eval [true,false] <;> simp [hval] at selected
    have varying (b : Bool) : ∃ y : Fin 8 → Bool, side p j y = b := by
      by_cases hb : b = !g.op.eval [true,false]
      · obtain ⟨y,_,h0,h1⟩ := piv 0 false
        exact ⟨y,(critical y (by rw [h0,h1]; decide)).trans hb.symm⟩
      by_contra! never
      apply noReplace ⟨.not,[0]⟩ (negAllowed 0)
      intro a y
      have fixed : side p j y = !g.op.eval [true,false] := by
        have n := never y
        cases b <;> cases h : g.op.eval [true,false] <;> cases v : side p j y <;>
          simp only [h,v,Bool.not_true,Bool.not_false] at hb n ⊢ <;> first | rfl | contradiction
      obtain ⟨u,hu⟩ := common p hp (List.ofFn y)
      simp only [side,hu false] at fixed
      rw [hu a,hu (!a),value g j hj ops ins,fixed]
      cases h : g.op.eval [true,false] <;> simp [ev,eval_not]
    have hi : j < 9+p.length := by
      by_contra! out
      obtain ⟨y,hy⟩ := varying true
      have outside : side p j y = false := by
        apply List.getD_eq_default
        rw [run_length]
        simpa using out
      rw [outside] at hy
      contradiction
    have later : ∃ h ∈ s, h.op = .not := by
      by_contra! missing
      have pos : ∀ h ∈ g::s, h.op = .and ∨ h.op = .or := by
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hm
        · exact ops
        · have ok : allowed h := fan h (List.mem_append_right _ (List.mem_cons_of_mem _ hm))
          rcases ok.1 with e | e | e
          · exact Or.inl e
          · exact Or.inr e
          · exact (missing h hm e).elim
      obtain ⟨y,_,h0,h1⟩ := piv 0 false
      obtain ⟨u,hu⟩ := common p hp (List.ofFn y)
      have atBit (b : Bool) : (run (g::s) ((!b)::u)).getD o false = H (Fin.cons b y) := by
        have original := good (Fin.cons b y)
        rw [flip_cons] at original
        change (run (p ++ g :: s) ((!b) :: List.ofFn y)).getD o false = _ at original
        have join (w : List Bool) : run (p ++ g :: s) w = run (g::s) (run p w) :=
          List.foldl_append
        rwa [join,hu] at original
      have rising := increasing (g::s) pos (false::u) (true::u) rfl
        (fun i => by cases i <;> simp) o ((atBit true).trans h1)
      exact Bool.false_ne_true (((atBit false).trans h0).symm.trans rising)
    have off (h : Gate) (mem : h ∈ p++s) : 0 ∉ h.inputs := by
      rcases List.mem_append.mp mem with hm | hm
      · simpa [reads] using hp h hm
      · simpa [reads] using hs h hm
    exact ⟨p,g,s,j,rfl,lo,hi,ops,ins,off,later,varying,critical⟩

  have add_first (E : Circuit) (hE : FanInTwo E) :
      ∃ C : Circuit, FanInTwo C ∧ C.size = E.size + 1 ∧
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 && x 6)) ∧
        circuitFun 9 C = circuitFun 9 E := by
    let sh (i : ℕ) := if i < 9 then i else i+1
    let ren (g : Gate) : Gate := ⟨g.op, g.inputs.map sh⟩
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have lookup (x : Fin 9 → Bool) (r : List Bool) (b : Bool) (i : ℕ) :
        ((List.ofFn x ++ [b]) ++ r).getD (sh i) false = (List.ofFn x ++ r).getD i false := by
      by_cases short : i < 9
      · simp only [sh, short, ite_true]
        rw [List.getD_append _ _ _ _ (by simp; omega)]
        rw [List.getD_append _ _ _ _ (by simpa using short)]
        rw [List.getD_append _ _ _ _ (by simpa using short)]
      · simp only [sh, short, ite_false]
        rw [List.getD_append_right _ _ _ _ (by simp; omega)]
        rw [List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_append, List.length_ofFn, List.length_singleton]
        congr 1 <;> omega
    have run (rs : List Gate) (x : Fin 9 → Bool) (b : Bool) : ∀ r : List Bool,
        ∃ t, rs.foldl step (List.ofFn x ++ r) = List.ofFn x ++ t ∧
          (rs.map ren).foldl step ((List.ofFn x ++ [b]) ++ r) = (List.ofFn x ++ [b]) ++ t := by
      induction rs with
      | nil => intro r; exact ⟨r,rfl,rfl⟩
      | cons h rs ih =>
        intro r
        let v := h.op.eval (h.inputs.map fun i => (List.ofFn x ++ r).getD i false)
        have same : (ren h).op.eval ((ren h).inputs.map
            fun i => ((List.ofFn x ++ [b]) ++ r).getD i false) = v := by
          change h.op.eval ((h.inputs.map sh).map _) = _
          rw [List.map_map]
          apply congrArg h.op.eval
          apply List.map_congr_left
          intro i _
          exact lookup x r b i
        obtain ⟨t, h1, h2⟩ := ih (r ++ [v])
        refine ⟨t, ?_, ?_⟩
        · simpa only [List.foldl_cons, step, List.append_assoc, v] using h1
        · change (rs.map ren).foldl step ((((List.ofFn x ++ [b]) ++ r) ++
              [(ren h).op.eval ((ren h).inputs.map fun i => ((List.ofFn x ++ [b]) ++ r).getD i false)])) =
              (List.ofFn x ++ [b]) ++ t
          rw [same]
          simpa only [List.append_assoc] using h2
    let g : Gate := ⟨.and,[4,6]⟩
    let C : Circuit := ⟨g :: E.gates.map ren, sh E.output⟩
    have hv (x : Fin 9 → Bool) : step (List.ofFn x) g = List.ofFn x ++ [x 4 && x 6] := by
      simp [g, step, eval_and, List.getD_eq_getElem?_getD]
    refine ⟨C, ?_, by simp [C, size_eq], ?_, ?_⟩
    · intro h hh
      change h ∈ g :: E.gates.map ren at hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact ⟨Or.inl rfl, by decide⟩
      · obtain ⟨h', hE', rfl⟩ := List.mem_map.mp hh
        exact ⟨(hE h' hE').1, by simpa [ren] using (hE h' hE').2⟩
    · intro x
      obtain ⟨t, _, qr⟩ := run E.gates x (x 4 && x 6) []
      simp only [List.append_nil] at qr
      change ((E.gates.map ren).foldl step (step (List.ofFn x) g)).getD 9 false = _
      rw [hv, qr, List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
      simp
    · funext x
      obtain ⟨t, ql, qr⟩ := run E.gates x (x 4 && x 6) []
      simp only [List.append_nil] at ql qr
      change ((E.gates.map ren).foldl step (step (List.ofFn x) g)).getD (sh E.output) false =
        (E.gates.foldl step (List.ofFn x)).getD E.output false
      rw [hv, ql, qr]
      exact lookup x t (x 4 && x 6) E.output

  have lower : ¬ HasCircuitSize 9 F 14 := by
    rintro ⟨E,hE,hk,ok⟩
    obtain ⟨C,hC,hsize,head,same⟩ := add_first E hE
    have target : circuitFun 9 C = F := same.trans (funext ok)
    have bound := sibling C hC head target
    omega
  intro D b hf hk hcount hb
  subst b
  by_contra! correct
  have good (x : Fin 9 → Bool) : circuitFun 9 D (flip x) = F x := by
    simpa only [flip,Bool.true_bne] using correct x
  have signed_lower (E : Circuit) (ok : FanInTwo E) (ef : ∀ x, circuitFun 9 E (flip x) = F x) :
      14 ≤ E.size := by
    by_contra! cheap
    obtain ⟨C,hC,cost,sim⟩ := prepend_not E ok
    exact lower ⟨C,hC,by omega,fun x => (sim x).trans (ef x)⟩
  have exactSize := Nat.le_antisymm hk (signed_lower D hf good)
  have minimum (E : Circuit) (ok : FanInTwo E) (eq : circuitFun 9 E = circuitFun 9 D) :
      D.size ≤ E.size := hk.trans (signed_lower E ok (fun x => (congrFun eq (flip x)).trans (good x)))
  obtain ⟨p,g,s,j,split,lo,hi,ops,ins,off,later,varying,critical⟩ :=
    mixed F 14 (by rfl) pivot lower D hf hk hcount good
  obtain ⟨gs,o⟩ := D
  change gs = p ++ g :: s at split
  subst gs
  let A := fun y : Fin 8 → Bool => side p j y
  have wire (y : Fin 8 → Bool) : circuitFun 9 ⟨p,j⟩ (Fin.cons false y) = A y := by
    change (run p (List.ofFn (Fin.cons false y))).getD j false = _
    rw [List.ofFn_succ]
    rfl
  have computes (x : Fin 9 → Bool) : circuitFun 9 ⟨p ++ g::s,o⟩ (flip x) = encoded x :=
    (good x).trans (encoded_correct x)
  by_cases low : ∃ (a b : Fin 8) (q : Bool → Bool → Bool), ∀ y, A y = q (y a) (y b)
  · obtain ⟨a,b,q,rep⟩ := low
    obtain ⟨edge,truth⟩ := two_variables A (!g.op.eval [true,false]) varying critical a b q rep
    have bound := pair_case p s g j o hf exactSize minimum lo hi ops ins off later (by
      refine ⟨a,b,?_,fun y => ?_⟩
      · exact (encoded_correct _).symm.trans edge
      · exact (wire y).trans (by simpa only [Bool.not_not] using truth y)) computes
    omega
  · have bound := larger_case p s g j o hf exactSize minimum lo hi ops ins off later (by
      rintro ⟨a,b,q,h⟩
      exact low ⟨a,b,q,fun y => (wire y).symm.trans (h y)⟩) (by
      intro y diff
      exact (wire y).trans (critical y (fun eq => diff ((encoded_correct _).symm.trans
        (eq.trans (encoded_correct _)))))) computes
    omega

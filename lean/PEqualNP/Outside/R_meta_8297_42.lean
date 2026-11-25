import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_8297_42
    (pinned : ∀ (D : Circuit) (u : Bool → Bool → Bool) (j : Fin 10), j = 1 ∨ j = 2 →
      (u false false = u false true ∨ ∃ b, u false b = u true b) → FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [u (x 0) (x j)]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) → 16 ≤ D.gates.countP (fun g => !g.op.eval [false] && decide (g.inputs.length = 2)))
    (one : ∀ (D : Circuit) (u : Bool → Bool), FanInTwo D → D.size ≤ 18 → 16 ≤ D.gates.countP (fun g => !g.op.eval [false] && decide (g.inputs.length = 2)) →
      ¬ ∀ x : Fin 10 → Bool,
        D.eval (List.ofFn x ++ [u (x 0)]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)))
    (adjacent : ∀ (D : Circuit) (useAnd : Bool), FanInTwo D → D.size ≤ 18 → 16 ≤ D.gates.countP (fun g => !g.op.eval [false] && decide (g.inputs.length = 2)) →
      (∃ g ∈ D.gates, g.op = GateOp.not) → ¬ ∀ x : Fin 10 → Bool,
        D.eval (List.ofFn x ++ [if useAnd then x 0 && x 1 else x 0 || x 1]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)))
    (apart : ∀ (D : Circuit) (useAnd : Bool), FanInTwo D → D.size ≤ 18 → 16 ≤ D.gates.countP (fun g => !g.op.eval [false] && decide (g.inputs.length = 2)) →
      (∃ g ∈ D.gates, g.op = GateOp.not) → ¬ ∀ x : Fin 10 → Bool,
        D.eval (List.ofFn x ++ [if useAnd then x 0 && x 2 else x 0 || x 2]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)))
    : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.Monotone2 x3 → x2.size + x3.size ≤ (18 : ℕ) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x3.eval (x2.wires (List.ofFn x7) ++ [!x2.eval (List.ofFn x7)]) = x1 x7 := by
  dsimp only
  intro A B hA hB budget computes
  let F (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let toZero : Fin 10 → Fin 10 → Fin 10 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7], ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8], ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6], ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5], ![1, 2, 3, 8, 6, 0, 7, 4, 5, 9], ![2, 1, 6, 8, 3, 7, 0, 9, 5, 4], ![2, 3, 4, 9, 7, 1, 8, 0, 6, 5], ![2, 3, 8, 5, 7, 1, 4, 6, 0, 9], ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0]]
  let stabilizer : Fin 10 → Fin 10 → Fin 10 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6], ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6], ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7], ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7], ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7], ![0, 4, 9, 7, 5, 1, 3, 6, 2, 8], ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2]]
  let maps (k : Fin 10 × Fin 10) := stabilizer (toZero k.1 k.2) ∘ toZero k.1
  let choice (a b : Fin 10) := (a,b)
  let adj (a b : Fin 10) := ([50,69,138,276,521,385,770,548,104,208] : List Nat).getD a.val 0 |>.testBit b.val
  have spec : ∀ x : Fin 10 → Bool, F x = decide (∃ a b : Fin 10, adj a b = true ∧ x a = true ∧ x b = true) := by decide +kernel
  have pair : ∀ a b : Fin 10, maps (choice a b) a = 0 ∧
      (maps (choice a b) b = 0 ∨ maps (choice a b) b = 1 ∨ maps (choice a b) b = 2) := by decide +kernel
  have zeroIso : ∀ a, (∀ i j, adj (toZero a i) (toZero a j) = adj i j) ∧
      (∀ j, ∃ i, toZero a i = j) := by decide +kernel
  have stabIso : ∀ a, (∀ i j, adj (stabilizer a i) (stabilizer a j) = adj i j) ∧
      (∀ j, ∃ i, stabilizer a i = j) := by decide +kernel
  have properties (k : Fin 10 × Fin 10) : (∀ a b, adj (maps k a) (maps k b) = adj a b) ∧
      (∀ j, ∃ i, maps k i = j) := by
    constructor
    · intro a b
      exact ((stabIso _).1 _ _).trans ((zeroIso _).1 a b)
    · intro j
      obtain ⟨r,hr⟩ := (stabIso (toZero k.1 k.2)).2 j
      obtain ⟨i,hi⟩ := (zeroIso k.1).2 r
      exact ⟨i, (congrArg (stabilizer (toZero k.1 k.2)) hi).trans hr⟩
  have symmF (k) (x : Fin 10 → Bool) : F (x ∘ maps k) = F x := by
    rw [spec, spec]
    simp only [decide_eq_decide]
    constructor
    · rintro ⟨a,b,h,ha,hb⟩
      exact ⟨_,_,((properties k).1 a b).trans h,ha,hb⟩
    · rintro ⟨a,b,h,ha,hb⟩
      obtain ⟨i,rfl⟩ := (properties k).2 a
      obtain ⟨j,rfl⟩ := (properties k).2 b
      exact ⟨i,j,((properties k).1 i j).symm.trans h,ha,hb⟩
  let ng : Gate := ⟨.not,[A.output]⟩
  let G := A.gates ++ ng :: B.gates
  let valid (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
  have allOK : ∀ g ∈ G, valid g := by
    intro g hg
    rcases List.mem_append.mp hg with ha | hb
    · exact hA g ha
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨Or.inr (Or.inr rfl),by simp [ng]⟩
      · obtain ⟨hop,cap⟩ := hB g hb
        exact ⟨by rcases hop with ha|ho; exact Or.inl ha; exact Or.inr (Or.inl ho),cap⟩
  have hasNot : ∃ g ∈ G, g.op = .not := ⟨ng,List.mem_append_right _ (by simp),rfl⟩
  have cost : G.length ≤ 19 := by simp [G]; change A.gates.length + B.gates.length ≤ 18 at budget; omega
  let val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
  let step (w : List Bool) (g : Gate) := w ++ [val g w]
  have hit (x : Fin 10 → Bool) : (G.foldl step (List.ofFn x)).getD B.output false = F x := by
    simpa only [G,List.foldl_append,List.foldl_cons,step,val,ng,GateOp.eval,List.map_cons,List.map_nil,
      List.headD_cons,Circuit.eval,Circuit.wires] using computes x
  cases gh : G with
  | nil => simp [gh] at hasNot
  | cons g tail =>
    have legal := allOK g (by simp [gh])
    have tailSize : tail.length ≤ 18 := by simp [gh] at cost; omega
    have tailOK (z) (hz : z ∈ tail) := allOK z (gh ▸ List.mem_cons_of_mem g hz)
    let args (i : Nat) (x : Fin 10 → Bool) := (List.ofFn x).getD i false
    have raw (x : Fin 10 → Bool) (i : Nat) : args i x = if h : i < 10 then x ⟨i,h⟩ else false := by
      by_cases hi : i < 10
      · rw [dite_eq_left hi]
        unfold args
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),List.getElem_ofFn]
      · rw [dite_eq_right hi]
        exact List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)
    have transport (k) (feature : (Fin 10 → Bool) → Bool)
        (hfeat : ∀ x, val g (List.ofFn (x ∘ maps k)) = feature x) :
        ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 18 ∧
          ((∃ z ∈ tail, z.op = GateOp.not) → ∃ z ∈ D.gates, z.op = GateOp.not) ∧
          ∀ x, D.eval (List.ofFn x ++ [feature x]) = F x := by
      let ren (i : Nat) := if h : i < 10 then (maps k ⟨i,h⟩).val else i
      let rg (a : Gate) : Gate := ⟨a.op,a.inputs.map ren⟩
      let D : Circuit := ⟨tail.map rg,ren B.output⟩
      refine ⟨D,?_,by simpa [D,Circuit.size] using tailSize,?_,?_⟩
      · intro a ha
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
        simpa [rg,valid,Set.mem_insert_iff,Set.mem_singleton_iff] using tailOK z hz
      · rintro ⟨a,ha,hn⟩
        exact ⟨rg a,List.mem_map.mpr ⟨a,ha,rfl⟩,hn⟩
      · intro x
        have snoc (v w : List Bool) (b : Bool) (ln : w.length = v.length) (big : 10 ≤ v.length)
            (agree : ∀ i, w.getD (ren i) false = v.getD i false) :
            ∀ i, (w ++ [b]).getD (ren i) false = (v ++ [b]).getD i false := by
          intro i
          by_cases hi : i < 10
          · have hr : ren i < w.length := by
              have jr := (maps k ⟨i,hi⟩).isLt
              simp only [ren,hi,↓reduceDIte]; omega
            simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left hr,
              List.getElem?_append_left (show i < v.length by omega)] using agree i
          · have same : ren i = i := by simp [ren,hi]
            by_cases small : i < v.length
            · simpa only [same,List.getD_eq_getElem?_getD,List.getElem?_append_left small,
                List.getElem?_append_left (show i < w.length by omega)] using agree i
            · simp [same,List.getD_eq_getElem?_getD,List.getElem?_append_right (show w.length ≤ i by omega),
                List.getElem?_append_right (show v.length ≤ i by omega),ln]
        have fold (gs : List Gate) (v w : List Bool) (ln : w.length = v.length) (big : 10 ≤ v.length)
            (agree : ∀ i, w.getD (ren i) false = v.getD i false) :
            ∀ i, ((gs.map rg).foldl step w).getD (ren i) false = (gs.foldl step v).getD i false := by
          induction gs generalizing v w with
          | nil => exact agree
          | cons z zs ih =>
            have eq : val (rg z) w = val z v := by simp only [val,rg,List.map_map,Function.comp_def,agree]
            simp only [List.map_cons,List.foldl_cons]
            apply ih (step v z) (step w (rg z)) (by simp [step,ln]) (by simp [step]; omega)
            simpa only [step,eq] using snoc v w (val z v) ln big agree
        have initial (i : Nat) : (List.ofFn x).getD (ren i) false = (List.ofFn (x ∘ maps k)).getD i false := by
          change args (ren i) x = args i (x ∘ maps k)
          rw [raw,raw]
          by_cases hi : i < 10 <;> simp [ren,hi]
        have sim := fold tail _ _ (by simp) (by simp)
          (snoc _ _ (feature x) (by simp) (by simp) initial) B.output
        have orig := hit (x ∘ maps k)
        rw [gh,List.foldl_cons,symmF] at orig
        change ((tail.map rg).foldl step _).getD (ren B.output) false = F x
        exact sim.trans (by simpa only [step,hfeat] using orig)
    have unary (a : Fin 10) (u : Bool → Bool)
        (h : ∀ x, val g (List.ofFn x) = u (x a)) : False := by
      let k := choice a a
      have ha := (pair a a).1
      obtain ⟨D,legalD,cap,_,out⟩ := transport k (fun x => u (x 0))
        (fun x => by rw [h]; simp [k,ha])
      exact one D u legalD cap (pinned D (fun v _ => u v) 1 (Or.inl rfl) (Or.inl rfl) legalD out) out
    have binary (a b : Fin 10) (useAnd : Bool) (hn : g.op ≠ .not)
        (h : ∀ x, val g (List.ofFn x) = if useAnd then x a && x b else x a || x b) : False := by
      let k := choice a b
      have ha := (pair a b).1
      obtain ⟨z,hz,zo⟩ := hasNot
      rcases List.mem_cons.mp (gh ▸ hz) with same | hm
      · exact hn (same ▸ zo)
      have tn : ∃ t ∈ tail, t.op = GateOp.not := ⟨z,hm,zo⟩
      have run (j : Fin 10) (hj : maps k b = j) := transport k
        (fun x => if useAnd then x 0 && x j else x 0 || x j)
        (fun x => by rw [h]; simp only [Function.comp_apply,show maps k a = 0 from ha,hj])
      rcases (pair a b).2 with same | near | far
      · obtain ⟨D,ok,cap,_,out⟩ := run 0 same
        have sameOut : ∀ x, D.eval (List.ofFn x ++ [id (x 0)]) = F x := by simpa using out
        exact one D id ok cap (pinned D (fun v _ => v) 1 (Or.inl rfl) (Or.inl rfl) ok sameOut) sameOut
      · obtain ⟨D,ok,cap,n,out⟩ := run 1 near
        have low := pinned D (fun a b => if useAnd then a && b else a || b) 1 (Or.inl rfl)
          (by cases useAnd <;> decide) ok out
        exact adjacent D useAnd ok cap low (n tn) out
      · obtain ⟨D,ok,cap,n,out⟩ := run 2 far
        have low := pinned D (fun a b => if useAnd then a && b else a || b) 2 (Or.inr rfl)
          (by cases useAnd <;> decide) ok out
        exact apart D useAnd ok cap low (n tn) out
    have useRaw (i : Nat) (u : Bool → Bool) (h : ∀ x, val g (List.ofFn x) = u (args i x)) : False := by
      by_cases hi : i < 10
      · apply unary ⟨i,hi⟩ u
        intro x
        rw [h,raw]; simp [hi]
      · apply unary 0 (fun _ => u false)
        intro x
        rw [h,raw]; simp [hi]
    obtain ⟨op, ar⟩ := legal
    change g.inputs.length ≤ 2 at ar
    cases q : g.inputs with
    | nil =>
      apply unary 0 (fun _ => g.op.eval [])
      simp [val,q]
    | cons i xs =>
      by_cases hn : g.op = .not
      · apply useRaw i Bool.not
        simp [val,hn,q,GateOp.eval,args]
      have ao : g.op = .and ∨ g.op = .or := by tauto
      cases qs : xs with
      | nil =>
        apply useRaw i id
        rcases ao with ha | ho <;> simp [val, *, GateOp.eval,args]
      | cons j rest =>
        have er : rest = [] := List.length_eq_zero_iff.mp (by simp only [q,qs,List.length_cons] at ar; omega)
        subst rest
        by_cases hi : i < 10
        · by_cases hj : j < 10
          · have read (x : Fin 10 → Bool) (k : Nat) (hk : k < 10) :
                (List.ofFn x).getD k false = x ⟨k,hk⟩ := by simpa only [dite_eq_left hk] using raw x k
            rcases ao with ha | ho
            · apply binary ⟨i,hi⟩ ⟨j,hj⟩ true hn
              intro x
              simp only [val,ha,q,qs,List.map_cons,List.map_nil,read x i hi,read x j hj,GateOp.eval]
              simp
            · apply binary ⟨i,hi⟩ ⟨j,hj⟩ false hn
              intro x
              simp only [val,ho,q,qs,List.map_cons,List.map_nil,read x i hi,read x j hj,GateOp.eval]
              simp
          · apply useRaw i (fun a => g.op.eval [a,false])
            intro x
            have ej := raw x j
            simp only [dite_eq_right hj] at ej
            simpa only [val,q,qs,List.map_cons,List.map_nil,args] using congrArg (fun t => g.op.eval [args i x,t]) ej
        · apply useRaw j (fun b => g.op.eval [false,b])
          intro x
          have ei := raw x i
          simp only [dite_eq_right hi] at ei
          simpa only [val,q,qs,List.map_cons,List.map_nil,args] using congrArg (fun t => g.op.eval [t,args j x]) ei

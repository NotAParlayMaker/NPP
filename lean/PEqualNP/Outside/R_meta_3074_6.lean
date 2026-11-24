import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_3074_6
  (case_and : let use (i : Nat) (g : Gate) := (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains i; ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → x1.gates.countP (use 9)=1 → (∀ i ∈ ([0,3] : List Nat), x1.gates.countP (fun g => (use i) g && !((use 9) g))=1) → (∀ g ∈ x1.gates, use 0 g=true → use 3 g=false) → (∃ g ∈ x1.gates, (use 9) g=true ∧ g.op=GateOp.and) → (15 : ℕ) ≤ x1.size)
  (case_or : let use (i : Nat) (g : Gate) := (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains i; ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → x1.gates.countP (use 9)=1 → (∀ i ∈ ([0,3] : List Nat), x1.gates.countP (fun g => (use i) g && !((use 9) g))=1) → (∀ g ∈ x1.gates, use 0 g=true → use 3 g=false) → (∃ g ∈ x1.gates, (use 9) g=true ∧ g.op=GateOp.or ∧ (use 0) g=false ∧ (use 3) g=false) → (15 : ℕ) ≤ x1.size)
  (case_not : let use (i : Nat) (g : Gate) := (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains i; ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → x1.gates.countP (use 9)=1 → (∀ i ∈ ([0,3] : List Nat), x1.gates.countP (fun g => (use i) g && !((use 9) g))=1) → (∀ g ∈ x1.gates, use 0 g=true → use 3 g=false) → (∃ g ∈ x1.gates, (use 9) g=true ∧ g.op=GateOp.not) → (15 : ℕ) ≤ x1.size)
  : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ))])) → (∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x4 ++ [Bool.false])) → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (∀ x6 ∈ [(0 : ℕ), (3 : ℕ)], (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => [x6, (9 : ℕ)].any fun (x9 : ℕ) => (if x8.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains x9) x1.gates).length ≤ (2 : ℕ)) → (15 : ℕ) ≤ x1.size := by
  have andRule (xs : List Bool) : GateOp.and.eval xs=xs.all id := rfl
  have orRule (xs : List Bool) : GateOp.or.eval xs=xs.any id := rfl
  have notRule (xs : List Bool) : GateOp.not.eval xs= !(xs.headD false) := rfl
  let eff (g : Gate) := if g.op.eval [false]=true then g.inputs.take 1 else g.inputs
  let reads (i : Nat) (g : Gate) := (eff g).contains i
  let value (g : Gate) (f : Nat→Bool) := g.op.eval (g.inputs.map f)
  let advance (w : List Bool) (g : Gate) := w++[value g (fun i => w.getD i false)]
  have extend (gs : List Gate) (x : List Bool) : ∃ t, gs.foldl advance x=x++t := by
    try clear value
    try clear reads
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    induction gs generalizing x with
    | nil => exact ⟨[],by simp⟩
    | cons g gs ih =>
      obtain ⟨t,ht⟩ := ih (advance x g)
      exact ⟨_::t,by simpa [advance,List.append_assoc] using ht⟩
  have output_large {C : Circuit} {target : (Fin 9→Bool)→Bool} {start : (Fin 9→Bool)→List Bool}
      (n : ∀ x,(start x).length=10) (computes : ∀ x,C.eval (start x)=target x)
      (obs : ∀ i : Fin 10, ∃ x, (start x).getD i.val false ≠ target x) : 10≤C.output := by
    try clear advance
    try clear value
    try clear reads
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    by_contra! h
    obtain ⟨x,hx⟩ := obs ⟨C.output,h⟩
    obtain ⟨s,hs⟩ := extend C.gates (start x)
    change C.wires (start x)=start x++s at hs
    have z:=computes x
    change (C.wires (start x)).getD C.output false=target x at z
    rw [hs,List.getD_append _ _ _ _ (by simpa [n] using h)] at z
    exact hx z
  have first_gate {C : Circuit} {a b : List Bool} (len : a.length=b.length) (out : a.length≤C.output)
      (diff : C.eval a ≠ C.eval b) :
      ∃ g ∈ C.gates, ∃ t : List Bool,
        value g (fun i => (a++t).getD i false) ≠ value g (fun i => (b++t).getD i false) := by
    try clear output_large
    try clear extend
    try clear reads
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    by_contra! same
    have run (gs : List Gate) (sub : ∀ g∈gs,g∈C.gates) (z : List Bool) :
        ∃ t, gs.foldl advance (a++z)=a++t ∧ gs.foldl advance (b++z)=b++t := by
      induction gs generalizing z with
      | nil => exact ⟨z,rfl,rfl⟩
      | cons g gs ih =>
        have v := same g (sub g (by simp)) z
        obtain ⟨t,ha,hb⟩ := ih (fun u hu => sub u (by simp [hu])) (z++[value g (fun i => (a++z).getD i false)])
        refine ⟨t,?_,?_⟩
        · simpa [advance,List.append_assoc] using ha
        · rw [v] at hb
          simpa [advance,List.append_assoc] using hb
    obtain ⟨t,ha,hb⟩:=run C.gates (fun _ h=>h) []
    simp only [List.append_nil] at ha hb
    change C.wires a=a++t at ha
    change C.wires b=b++t at hb
    apply diff
    change (C.wires a).getD C.output false=(C.wires b).getD C.output false
    rw [ha,hb,List.getD_append_right _ _ _ _ out,
      List.getD_append_right _ _ _ _ (len ▸ out),len]
  have same_prefix {a b : List Bool} {i : Nat} (len : a.length=b.length)
      (h : ∀ j, j≠i → a.getD j false=b.getD j false) (t : List Bool) :
      ∀ j, j≠i → (a++t).getD j false=(b++t).getD j false := by
    try clear first_gate
    try clear output_large
    try clear extend
    try clear advance
    try clear value
    try clear reads
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    intro j ne
    by_cases small : j<a.length
    · rw [List.getD_append _ _ _ _ small,List.getD_append _ _ _ _ (len ▸ small)]
      exact h j ne
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]
  let GoodGate (g : Gate) := g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2
  have reads_of_diff {g : Gate} {i : Nat} {f h : Nat→Bool} (good : GoodGate g)
      (same : ∀ j,j≠i→ f j=h j) (d : value g f ≠ value g h) : reads i g=true := by
    try clear same_prefix
    try clear first_gate
    try clear output_large
    try clear extend
    try clear advance
    try clear case_and
    try clear case_or
    try clear case_not
    obtain ⟨op,ls⟩ := g
    obtain ⟨ok,arity⟩ := good
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ok
    change ls.length≤2 at arity
    rcases ok with rfl|rfl|rfl
    all_goals
      cases ls with
      | nil => exact False.elim (d rfl)
      | cons x xs =>
        cases xs with
        | nil =>
          by_cases ex : x=i
          · subst x; simp [reads,eff,andRule,orRule,notRule]
          · exact False.elim (d (by simp [value,same x ex]))
        | cons y ys =>
          have e : ys=[] := List.length_eq_zero_iff.mp (by simpa using arity)
          subst ys
          by_cases ex : x=i
          · subst x; simp [reads,eff,andRule,orRule,notRule]
          · by_cases ey : y=i
            · subst y; first | solve | simp [reads,eff,andRule,orRule,notRule] | exact False.elim (d (by simp [value,andRule,orRule,notRule,same x ex]))
            · exact False.elim (d (by simp [value,same x ex,same y ey]))
  have shape {g : Gate} {i j : Nat} (good : GoodGate g) (ne : i≠j)
      (hi : reads i g=true) (hj : reads j g=true) :
      (g.op=.and ∨ g.op=.or) ∧ (g.inputs=[i,j] ∨ g.inputs=[j,i]) := by
    try clear reads_of_diff
    try clear same_prefix
    try clear first_gate
    try clear output_large
    try clear extend
    try clear advance
    try clear value
    try clear case_and
    try clear case_or
    try clear case_not
    obtain ⟨op,ls⟩ := g
    obtain ⟨ok,arity⟩ := good
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ok
    change ls.length≤2 at arity
    rcases ok with rfl|rfl|rfl
    all_goals
      cases ls with
      | nil => simp [reads,eff,andRule,orRule,notRule] at hi
      | cons a as =>
        cases as with
        | nil =>
          simp [reads,eff,andRule,orRule,notRule] at hi hj
          clear * - hi hj ne
          grind
        | cons b bs =>
          have z : bs=[] := List.length_eq_zero_iff.mp (by simpa using arity)
          subst bs
          simp [reads,eff,andRule,orRule,notRule] at hi hj
          clear * - hi hj ne
          grind
  have pinned {g i j f h} (good : GoodGate g) (ne : i≠j) (hi : reads i g=true)
      (hj : reads j g=true) (v : Bool) (fv : f j=v) (hv : h j=v)
      (diff : value g f≠value g h) : g.op=(if v then .and else .or) := by
    try clear reads_of_diff
    try clear same_prefix
    try clear first_gate
    try clear output_large
    try clear extend
    try clear advance
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    obtain ⟨op,shape⟩:=shape good ne hi hj
    cases v <;> rcases op with e|e <;> first | exact e | (
      exfalso; apply diff; rcases shape with s|s <;> simp [value,s,e,andRule,orRule,notRule,fv,hv])
  have find_reader {C : Circuit} (leg : FanInTwo C) {i} {a b : List Bool}
      (len : a.length=b.length) (out : a.length≤C.output)
      (same : ∀ j, j≠i → a.getD j false=b.getD j false)
      (diff : C.eval a≠C.eval b) :
      ∃ g∈C.gates, reads i g=true ∧ ∀ j, i≠j → j<a.length → ∀ v : Bool,
        a.getD j false=v → b.getD j false=v → reads j g=true → g.op=(if v then .and else .or) := by
    try clear shape
    try clear GoodGate
    try clear output_large
    try clear extend
    try clear advance
    try clear value
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    obtain ⟨g,hg,t,off⟩ := first_gate len out diff
    have hi:=reads_of_diff (leg g hg) (same_prefix len same t) off
    refine ⟨g,hg,hi,?_⟩
    intro j ne lt v va vb hj
    exact pinned (leg g hg) ne hi hj v ((List.getD_append _ _ _ _ lt).trans va)
      ((List.getD_append _ _ _ _ (len ▸ lt)).trans vb) off
  let pt (r : Nat) (i : Fin 9) := r.testBit i.val
  let edge (x : Fin 9→Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let rows (x : Fin 9→Bool) := List.ofFn x ++ [x 0 && x 3]
  have row_len (x : Fin 9→Bool) : (rows x).length=10 := by simp [rows]
  have raw_not_target : ∀ j : Fin 10, ∃ r : Fin 512, (rows (pt r.val)).getD j.val false≠ edge (pt r.val) := by decide +kernel
  have extend_small {a b : List Bool} {i : Nat} (la : a.length=10) (lb : b.length=10)
      (obs : ∀ j:Fin 10,j.val≠i→a.getD j.val false=b.getD j.val false) :
      ∀ j, j≠i → a.getD j false=b.getD j false := by
    try clear raw_not_target
    try clear row_len
    try clear rows
    try clear edge
    try clear pt
    try clear find_reader
    try clear pinned
    try clear shape
    try clear reads_of_diff
    try clear GoodGate
    try clear same_prefix
    try clear first_gate
    try clear output_large
    try clear extend
    try clear advance
    try clear value
    try clear reads
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    intro j h
    by_cases low : j<10
    · exact obs ⟨j,low⟩ h
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (show a.length≤j by omega),
        List.getElem?_eq_none (show b.length≤j by omega)]
  have raw_witness {C : Circuit} (leg : FanInTwo C) (out : 10≤C.output) (compute : ∀ x,C.eval (rows x)=edge x)
      (i r s : Nat) (lt : i<9) (e : edge (pt r)≠edge (pt s))
      (same : ∀ j:Fin 10,j.val≠i → (rows (pt r)).getD j.val false=(rows (pt s)).getD j.val false)
      (va : (rows (pt r)).getD 9 false=false) (vb : (rows (pt s)).getD 9 false=false) :
      ∃ g∈C.gates, reads i g=true ∧ (reads 9 g=true → g.op=.or) := by
    try clear raw_not_target
    try clear pinned
    try clear shape
    try clear reads_of_diff
    try clear GoodGate
    try clear same_prefix
    try clear first_gate
    try clear output_large
    try clear extend
    try clear advance
    try clear value
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    have d : C.eval (rows (pt r))≠C.eval (rows (pt s)) := by simpa only [compute] using e
    obtain ⟨g,hg,hi,pin⟩:=find_reader leg ((row_len _).trans (row_len _).symm)
      (by simpa only [row_len] using out) (extend_small (row_len _) (row_len _) same) d
    exact ⟨g,hg,hi,pin 9 (by omega) (by rw [row_len]; decide) false va vb⟩
  have seed_witness {C : Circuit} (leg : FanInTwo C) (out : 10≤C.output)
      (off : ∃ x : Fin 9→Bool, C.eval (rows x)≠C.eval (List.ofFn x++[false])) :
      ∃ g∈C.gates, reads 9 g=true ∧
        ((reads 0 g=true ∨ reads 3 g=true) → g.op=.and) := by
    try clear raw_witness
    try clear raw_not_target
    try clear edge
    try clear pt
    try clear pinned
    try clear shape
    try clear reads_of_diff
    try clear GoodGate
    try clear same_prefix
    try clear first_gate
    try clear output_large
    try clear extend
    try clear advance
    try clear value
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    obtain ⟨x,d⟩:=off
    have both : x 0 && x 3 = true := by
      by_contra! n
      have nf : (x 0 && x 3)=false := Bool.eq_false_iff.mpr n
      exact d (by simp [rows,nf])
    obtain ⟨x0,x3⟩:=Bool.and_eq_true_iff.mp both
    let b:=List.ofFn x++[false]
    have lb : b.length=10 := by simp [b]
    have common (j:Fin 10) (ne:j.val≠9) : (rows x).getD j.val false=b.getD j.val false := by
      have lt : j.val<(List.ofFn x).length := by simp; omega
      simp only [rows,b,List.getD_append _ _ _ _ lt]
    obtain ⟨g,hg,h9,pin⟩:=find_reader leg ((row_len _).trans lb.symm) (by simpa [row_len] using out)
      (extend_small (row_len _) lb common) d
    refine ⟨g,hg,h9,?_⟩
    rintro (h|h)
    · exact pin 0 (by decide) (by rw [row_len]; decide) true (by simpa [rows] using x0) (by simpa [b] using x0) h
    · exact pin 3 (by decide) (by rw [row_len]; decide) true (by simpa [rows] using x3) (by simpa [b] using x3) h
  let touch (i : Nat) (g : Gate) := reads i g || reads 9 g
  have count_touch (gs : List Gate) (i : Nat) :
      gs.countP (touch i) = gs.countP (reads 9) + gs.countP (fun g => reads i g && !reads 9 g) := by
    try clear seed_witness
    try clear raw_witness
    try clear extend_small
    try clear raw_not_target
    try clear row_len
    try clear rows
    try clear edge
    try clear pt
    try clear find_reader
    try clear pinned
    try clear shape
    try clear reads_of_diff
    try clear GoodGate
    try clear same_prefix
    try clear first_gate
    try clear output_large
    try clear extend
    try clear advance
    try clear value
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      cases a : reads i g <;> cases b : reads 9 g <;>
        simp [List.countP_cons,touch,a,b,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have one_reader {C : Circuit} (leg : FanInTwo C)
      (different : ∃ x : Fin 9→Bool, C.eval (rows x) ≠ C.eval (List.ofFn x++[false]))
      (target : ∀ x,C.eval (rows x)=edge x)
      (touches : ∀ i∈([0,3] : List Nat), C.gates.countP (touch i) ≤ 2) :
      C.gates.countP (reads 9)=1 := by
    try clear extend_small
    try clear find_reader
    try clear pinned
    try clear reads_of_diff
    try clear GoodGate
    try clear same_prefix
    try clear first_gate
    try clear extend
    try clear advance
    try clear value
    try clear case_and
    try clear case_or
    try clear case_not
    classical
    have out := output_large row_len target (by intro i; obtain ⟨r,h⟩:=raw_not_target i; exact ⟨pt r.val,h⟩)
    obtain ⟨a,am,a0,ap⟩ := raw_witness leg out target 0 3 2 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    obtain ⟨b,bm,b3,bp⟩ := raw_witness leg out target 3 12 4 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    obtain ⟨z,zm,z9,zp⟩ := seed_witness leg out different
    have pos : 0<C.gates.countP (reads 9) := by
      rw [List.countP_eq_length_filter,List.length_pos_iff_exists_mem]
      exact ⟨z,List.mem_filter.mpr ⟨zm,z9⟩⟩
    by_contra! notOne
    have two : 2≤C.gates.countP (reads 9) := by omega
    have cap := touches 0 (by simp)
    rw [count_touch] at cap
    have forces (i : Nat) (hi : i∈([0,3] : List Nat)) (g : Gate) (gm : g∈C.gates) (gr : reads i g=true) : reads 9 g=true := by
      have hc := touches i hi
      rw [count_touch] at hc
      have zero : C.gates.countP (fun g => reads i g && !reads 9 g)=0 := by omega
      have e := List.countP_eq_zero.mp zero g gm
      cases h : reads 9 g <;> simp_all
    have a9:=forces 0 (by simp) a am a0
    have b9:=forces 3 (by simp) b bm b3
    have ao:=ap a9
    have bo:=bp b9
    have ab : a≠b := by
      intro e
      have so := (shape (leg a am) (i:=0) (j:=9) (by decide) a0 a9).2
      have b' : reads 3 a=true := e ▸ b3
      rcases so with q|q <;> simp [reads,eff,ao,q,andRule,orRule,notRule] at b'
    have az : a≠z := by
      intro e
      have za:=zp (Or.inl (e ▸ a0))
      rw [←e,ao] at za
      contradiction
    have bz : b≠z := by
      intro e
      have za:=zp (Or.inr (e ▸ b3))
      rw [←e,bo] at za
      contradiction
    let fs := (C.gates.filter (reads 9)).toFinset
    have mem (g : Gate) (hm : g∈C.gates) (rd : reads 9 g=true) : g∈fs :=
      List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hm,rd⟩)
    have sub : ({a,b,z} : Finset Gate)⊆fs := by
      intro u hu
      simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with rfl|rfl|rfl
      · exact mem _ am a9
      · exact mem _ bm b9
      · exact mem _ zm z9
    have lower := Finset.card_le_card sub
    have ident : ({a,b,z} : Finset Gate).card=3 := by simp [ab,az,bz]
    have upper : fs.card≤C.gates.countP (reads 9) := by
      rw [List.countP_eq_length_filter]
      exact List.toFinset_card_le (l:=C.gates.filter (reads 9))
    omega
  have unique_hit {gs : List Gate} {g h} {p : Gate→Bool} (one : gs.countP p=1)
      (gm : g∈gs) (gr : p g=true) (hm : h∈gs) (hr : p h=true) : g=h := by
    try clear one_reader
    try clear count_touch
    try clear touch
    try clear seed_witness
    try clear raw_witness
    try clear extend_small
    try clear raw_not_target
    try clear row_len
    try clear rows
    try clear edge
    try clear pt
    try clear find_reader
    try clear pinned
    try clear shape
    try clear reads_of_diff
    try clear GoodGate
    try clear same_prefix
    try clear first_gate
    try clear output_large
    try clear extend
    try clear advance
    try clear value
    try clear reads
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    have ga := List.mem_filter.mpr (And.intro gm gr)
    have ha := List.mem_filter.mpr (And.intro hm hr)
    rw [List.countP_eq_length_filter] at one
    generalize ex : gs.filter p = xs at ga ha one
    cases xs with
    | nil => simp at one
    | cons x xs =>
      cases xs with
      | nil => simp_all
      | cons y ys => simp at one
  have normalize {C : Circuit} (leg : FanInTwo C)
      (different : ∃ x : Fin 9→Bool, C.eval (rows x) ≠ C.eval (List.ofFn x++[false]))
      (target : ∀ x, C.eval (rows x)=edge x)
      (touches : ∀ i∈([0,3] : List Nat), C.gates.countP (touch i) ≤ 2) :
      C.gates.countP (reads 9)=1 ∧
      (∀ i∈([0,3] : List Nat), C.gates.countP (fun g => reads i g && !reads 9 g)=1) ∧
      ∀ g∈C.gates, reads 9 g=true → (reads 0 g=true ∨ reads 3 g=true) → g.op=.and := by
    try clear extend_small
    try clear find_reader
    try clear pinned
    try clear shape
    try clear reads_of_diff
    try clear GoodGate
    try clear same_prefix
    try clear first_gate
    try clear extend
    try clear advance
    try clear value
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    have one := one_reader leg different target touches
    have out := output_large row_len target (by intro i; obtain ⟨r,h⟩:=raw_not_target i; exact ⟨pt r.val,h⟩)
    obtain ⟨z,hz,z9,pin⟩:=seed_witness leg out different
    have rigid (g : Gate) (hg : g∈C.gates) (r9 : reads 9 g=true) :
        (reads 0 g=true ∨ reads 3 g=true) → g.op=.and := by
      have eq := unique_hit one hg r9 hz z9
      simpa only [eq] using pin
    refine ⟨one,?_,rigid⟩
    intro i hi
    have raw : ∃ g∈C.gates, reads i g=true ∧ (reads 9 g=true → g.op=.or) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl
      · exact raw_witness leg out target 0 3 2 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      · exact raw_witness leg out target 3 12 4 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    obtain ⟨g,gm,gi,go⟩:=raw
    have no : reads 9 g=false := by
      cases eq : reads 9 g with
      | false => rfl
      | true =>
        have oo:=go eq
        have aa := rigid g gm eq (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl|rfl
          · exact Or.inl gi
          · exact Or.inr gi)
        rw [oo] at aa
        contradiction
    have p : 0<C.gates.countP (fun g => reads i g && !reads 9 g) := by
      rw [List.countP_eq_length_filter,List.length_pos_iff_exists_mem]
      exact ⟨g,List.mem_filter.mpr ⟨gm,by simp [gi,no]⟩⟩
    have cap:=touches i hi
    rw [count_touch,one] at cap
    omega
  have swap_agree (t : List Bool) (j : Nat) (ne0 : j≠0) (ne3 : j≠3) :
      (rows (pt 3)++t).getD j false=(rows (pt 10)++t).getD j false := by
    try clear normalize
    try clear unique_hit
    try clear one_reader
    try clear count_touch
    try clear touch
    try clear seed_witness
    try clear raw_witness
    try clear extend_small
    try clear raw_not_target
    try clear edge
    try clear find_reader
    try clear pinned
    try clear shape
    try clear reads_of_diff
    try clear GoodGate
    try clear same_prefix
    try clear first_gate
    try clear output_large
    try clear extend
    try clear advance
    try clear value
    try clear reads
    try clear eff
    try clear case_and
    try clear case_or
    try clear case_not
    by_cases lo : j<10
    · rw [List.getD_append (rows (pt 3)) t false j (by simpa only [row_len] using lo),
        List.getD_append (rows (pt 10)) t false j (by simpa only [row_len] using lo)]
      have ok : ∀ i:Fin 10, i.val≠0→i.val≠3→(rows (pt 3)).getD i.val false=(rows (pt 10)).getD i.val false := by decide +kernel
      exact ok ⟨j,lo⟩ ne0 ne3
    · rw [List.getD_append_right (rows (pt 3)) t false j (by rw [row_len]; omega),
        List.getD_append_right (rows (pt 10)) t false j (by rw [row_len]; omega),row_len,row_len]
  have separate {C : Circuit} (leg : FanInTwo C)
      (different : ∃ x : Fin 9→Bool, C.eval (rows x) ≠ C.eval (List.ofFn x++[false]))
      (target : ∀ x, C.eval (rows x)=edge x)
      (touches : ∀ i∈([0,3] : List Nat), C.gates.countP (touch i) ≤ 2) :
      ∀ u∈C.gates, reads 0 u=true → reads 3 u=false := by
    try clear one_reader
    try clear count_touch
    try clear seed_witness
    try clear raw_witness
    try clear extend_small
    try clear find_reader
    try clear pinned
    try clear GoodGate
    try clear same_prefix
    try clear extend
    try clear advance
    try clear case_and
    try clear case_or
    try clear case_not
    obtain ⟨one,raw,rigid⟩ := normalize leg different target touches
    have out := output_large row_len target (by intro i; obtain ⟨r,h⟩:=raw_not_target i; exact ⟨pt r.val,h⟩)
    have d : C.eval (rows (pt 3))≠C.eval (rows (pt 10)) := by rw [target,target]; decide +kernel
    obtain ⟨g,gm,t,diff⟩ := first_gate ((row_len _).trans (row_len _).symm) (by simpa only [row_len] using out) d
    let a := fun j => (rows (pt 3)++t).getD j false
    let b := fun j => (rows (pt 10)++t).getD j false
    change value g a≠value g b at diff
    let m := fun j => if j=0 then b j else a j
    have which : reads 0 g=true ∨ reads 3 g=true := by
      by_cases eq : value g a=value g m
      · right
        apply reads_of_diff (leg g gm) (f:=m) (h:=b) _ (eq ▸ diff)
        intro j ne
        by_cases z : j=0
        · simp [m,z]
        · simpa only [m,if_neg z] using swap_agree t j z ne
      · left
        apply reads_of_diff (leg g gm) (f:=a) (h:=m) _ eq
        intro j ne
        simp [m,ne]
    have a0 : a 0=true := by dsimp [a]; rw [List.getD_append _ _ _ _ (by rw [row_len]; decide)]; decide +kernel
    have b0 : b 0=false := by dsimp [b]; rw [List.getD_append _ _ _ _ (by rw [row_len]; decide)]; decide +kernel
    have a3 : a 3=false := by dsimp [a]; rw [List.getD_append _ _ _ _ (by rw [row_len]; decide)]; decide +kernel
    have b3 : b 3=true := by dsimp [b]; rw [List.getD_append _ _ _ _ (by rw [row_len]; decide)]; decide +kernel
    have a9 : a 9=false := by dsimp [a]; rw [List.getD_append _ _ _ _ (by rw [row_len]; decide)]; decide +kernel
    have b9 : b 9=false := by dsimp [b]; rw [List.getD_append _ _ _ _ (by rw [row_len]; decide)]; decide +kernel
    have no9 : reads 9 g=false := by
      cases h : reads 9 g with
      | false => rfl
      | true =>
        have op:=rigid g gm h which
        exfalso; apply diff
        rcases which with z|z
        · rcases (shape (leg g gm) (i:=0) (j:=9) (by decide) z h).2 with s|s <;> simp [value,s,op,andRule,orRule,notRule,a9,b9]
        · rcases (shape (leg g gm) (i:=3) (j:=9) (by decide) z h).2 with s|s <;> simp [value,s,op,andRule,orRule,notRule,a9,b9]
    have avoid (p : reads 0 g=true) (q : reads 3 g=true) : False := by
      obtain ⟨ops,ss⟩ := shape (leg g gm) (i:=0) (j:=3) (by decide) p q
      apply diff
      rcases ops with op|op <;> rcases ss with s|s <;> simp [value,op,s,andRule,orRule,notRule,a0,b0,a3,b3]
    intro u um u0
    cases u3 : reads 3 u with
    | false => rfl
    | true =>
      obtain ⟨ops,ss⟩ := shape (leg u um) (i:=0) (j:=3) (by decide) u0 u3
      have u9 : reads 9 u=false := by
        rcases ops with op|op <;> rcases ss with s|s <;> simp [reads,eff,s,op,andRule,orRule,notRule]
      have eqFor (i : Nat) (hi : i∈([0,3]:List Nat)) (gr : reads i g=true) (ur : reads i u=true) : g=u :=
        unique_hit (raw i hi) gm (by simp [gr,no9]) um (by simp [ur,u9])
      have e : g=u := which.elim (fun h=>eqFor 0 (by simp) h u0) (fun h=>eqFor 3 (by simp) h u3)
      exact False.elim (avoid (e ▸ u0) (e ▸ u3))
  intro C legal changed different target touches
  have caps (i : Nat) (hi : i∈([0,3] : List Nat)) : C.gates.countP (touch i)≤2 := by
    rw [List.countP_eq_length_filter]
    change (C.gates.filter (fun g => (eff g).contains i || (eff g).contains 9)).length ≤ 2
    simpa only [eff,List.any_cons,List.any_nil,Bool.or_false] using touches i hi
  obtain ⟨one,raw,rigid⟩ := normalize legal different target caps
  have disjointReads := separate legal different target caps
  have present : ∃ g∈C.gates, reads 9 g=true := by
    by_contra! missing
    have n : C.gates.countP (reads 9)=0 := List.countP_eq_zero.mpr (fun a ha => by simpa using missing a ha)
    omega
  obtain ⟨g,gm,g9⟩:=present
  have kind:=(legal g gm).1
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at kind
  rcases kind with a|o|n
  · exact case_and C legal target one raw disjointReads ⟨g,gm,g9,a⟩
  · have no (x : reads 0 g=true ∨ reads 3 g=true) : False := by
      have eq:=rigid g gm g9 x
      rw [o] at eq
      contradiction
    have n0 : reads 0 g=false := Bool.eq_false_iff.mpr (fun v => no (Or.inl v))
    have n3 : reads 3 g=false := Bool.eq_false_iff.mpr (fun v => no (Or.inr v))
    exact case_or C legal target one raw disjointReads ⟨g,gm,g9,o,n0,n3⟩
  · exact case_not C legal target one raw disjointReads ⟨g,gm,g9,n⟩

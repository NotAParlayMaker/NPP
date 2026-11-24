import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

-- Unfolding preserves truth values and bounds the number of leaves, including for
-- empty gates, dead gates and missing wires. Negation only changes the signs.
-- The two remaining claims are a formula bound and a circuit bound restricted
-- to outputs whose expression grows large enough when shared wires are copied.
set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_4031_17
    (formulas : ∀ f : DMFormula 10, (∀ x, f.eval x = (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) →
      let positive := DMFormula.rec (motive := fun _ : DMFormula 10 => Prop) (fun _ b => b=true)
        (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) f
      19 ≤ f.leaves ∧ (positive → 21 ≤ f.leaves))
    (shared : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
      let count (g : Gate) (l : List ℕ) : ℕ := if g.op.eval [false] then l.headD 0 else l.sum
      let sizes := C.gates.foldl (fun (w : List ℕ) (g : Gate) =>
        w ++ [count g (g.inputs.map (fun i => w.getD i 0))]) (List.replicate 10 1)
      (if C.gates.any (fun g => g.op.eval [false]) then 19 else 21) ≤ sizes.getD C.output 0 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ¬PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) (fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ))) (18 : ℕ) := by
  classical
  rintro ⟨C,allowed,small,works⟩
  let F := Sum Bool (DMFormula 10)
  let val : F → (Fin 10 → Bool) → Bool := Sum.elim (fun b _ => b) DMFormula.eval
  let mass : F → ℕ := Sum.elim (fun _ => 0) DMFormula.leaves
  let positive (f : DMFormula 10) := DMFormula.rec (motive := fun _ : DMFormula 10 => Prop)
    (fun _ b => b=true) (fun _ _ a b => a∧b) (fun _ _ a b => a∧b) f
  let pos : F → Prop := Sum.elim (fun _ => True) positive
  let join (b : Bool) (a d : F) : F := Sum.elim (fun c => if c=b then .inl c else d)
    (fun x => Sum.elim (fun c => if c=b then .inl c else .inr x)
      (fun y => .inr (if b then DMFormula.or x y else DMFormula.and x y)) d) a
  have ea (f g : DMFormula 10) (x) : (f.and g).eval x=(f.eval x && g.eval x) := rfl
  have eo (f g : DMFormula 10) (x) : (f.or g).eval x=(f.eval x || g.eval x) := rfl
  have el (i : Fin 10) (b : Bool) (x) : (DMFormula.lit i b).eval x=(if b then x i else !x i) := rfl
  have wa (f g : DMFormula 10) : (f.and g).leaves=f.leaves+g.leaves := rfl
  have wo (f g : DMFormula 10) : (f.or g).leaves=f.leaves+g.leaves := rfl
  have ga (l : List Bool) : GateOp.and.eval l=l.all id := rfl
  have go (l : List Bool) : GateOp.or.eval l=l.any id := rfl
  have gn (l : List Bool) : GateOp.not.eval l= !l.headD false := rfl
  let oper (b x y : Bool) := if b then x || y else x && y
  have jval (b) (a d : F) (x) : val (join b a d) x=oper b (val a x) (val d x) := by
    cases a <;> cases d <;> cases b <;> simp [join,val,oper,ea,eo] <;> split_ifs <;> simp_all
  have jw (b) (a d : F) : mass (join b a d) ≤ mass a + mass d := by
    cases a <;> cases d <;> cases b <;> simp [join,mass,wa,wo] <;> split_ifs <;> simp_all
  have jp (b) (a d : F) (h : pos a) (k : pos d) : pos (join b a d) := by
    cases a <;> cases d <;> cases b <;> simp_all [join,pos,positive] <;> split_ifs <;> simp_all
  let compl : DMFormula 10 → DMFormula 10 := DMFormula.rec
    (motive := fun _ => DMFormula 10) (fun i b => .lit i (!b))
    (fun _ _ a b => .or a b) (fun _ _ a b => .and a b)
  have ce (f : DMFormula 10) (x) : (compl f).eval x = !(f.eval x) := by
    induction f with
    | lit i b => cases b <;> simp [compl,el]
    | and f g a b | or f g a b =>
      first | change ((compl f).eval x || (compl g).eval x) = !(f.eval x && g.eval x)
            | change ((compl f).eval x && (compl g).eval x) = !(f.eval x || g.eval x)
      rw [a,b]
      cases f.eval x <;> cases g.eval x <;> rfl
  have cw (f : DMFormula 10) : (compl f).leaves=f.leaves := by
    induction f with
    | lit i b => rfl
    | and f g a b | or f g a b => exact congrArg₂ Nat.add a b
  let neg : F → F := Sum.elim (fun b => .inl (!b)) (fun f => .inr (compl f))
  have nv (z : F) (x) : val (neg z) x = !(val z x) := by cases z with
    | inl b => rfl | inr f => exact ce f x
  have nw (z : F) : mass (neg z) = mass z := by cases z with
    | inl b => rfl | inr f => exact cw f
  let agg (b : Bool) (l : List F) := l.foldr (join b) (.inl (!b))
  have av (b) (l : List F) (x) : val (agg b l) x =
      (if b then GateOp.or else GateOp.and).eval (l.map fun z => val z x) := by
    induction l with
    | nil => cases b <;> rfl
    | cons a l ih =>
      change val (join b a (agg b l)) x=_
      rw [jval,ih]
      cases b <;> simp [oper,ga,go]
  have aw (b) (l : List F) : mass (agg b l) ≤ (l.map mass).sum := by
    induction l with
    | nil => exact le_rfl
    | cons a l ih => exact (jw b a _).trans (Nat.add_le_add_left ih _)
  have ap (b) (l : List F) (h : ∀ z∈l, pos z) : pos (agg b l) := by
    induction l with
    | nil => trivial
    | cons a l ih => exact jp b a _ (h a (by simp)) (ih (fun z hz => h z (by simp [hz])))
  let gate (g : Gate) (l : List F) := if g.op=.not then neg (l.headD (.inl false)) else agg (g.op=.or) l
  let cost (g : Gate) (l : List ℕ) := if g.op.eval [false] then l.headD 0 else l.sum
  let stepF (w : List F) (g : Gate) := w++[gate g (g.inputs.map fun i => w.getD i (.inl false))]
  let stepN (w : List ℕ) (g : Gate) := w++[cost g (g.inputs.map fun i => w.getD i 0)]
  let stepB (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
  let clean := C.gates.any (fun g => g.op.eval [false]) = false
  have quiet (g : Gate) (hg : g∈C.gates) (nc : clean) : g.op≠.not := by
    intro e
    have bad : C.gates.any (fun g => g.op.eval [false])=true := List.any_eq_true.mpr ⟨g,hg,by rw [e]; rfl⟩
    exact Bool.false_ne_true (nc.symm.trans bad)
  let literal := fun i : Fin 10 => (Sum.inr (.lit i true) : F)
  have mapped (w : List F) (x) (i) : (w.map (fun z => val z x)).getD i false =
      val (w.getD i (.inl false)) x := by
    change (w.map (fun z => val z x)).getD i (val (.inl false) x)=_
    simp
  have realize (ls : List Gate) (ok : ∀ g∈ls, g∈C.gates) (w : List F) (x) :
      (ls.foldl stepF w).map (fun z => val z x) = ls.foldl stepB (w.map (fun z => val z x)) := by
    induction ls generalizing w with
    | nil => rfl
    | cons g ls ih =>
      simp only [List.foldl_cons]
      rw [ih (fun z hz => ok z (by simp [hz]))]
      congr 1
      simp only [stepF,stepB,List.map_append,List.map_cons,List.map_nil]
      congr 2
      let l := g.inputs.map fun i => w.getD i (.inl false)
      have reads : g.inputs.map (fun i => (w.map (fun z => val z x)).getD i false) =
          l.map (fun z => val z x) := by
        simp only [l,List.map_map,Function.comp_def]
        exact List.map_congr_left (fun i _ => mapped w x i)
      rw [reads]
      change val (gate g l) x=_
      rcases (allowed g (ok g (by simp))).1 with e|e|e
      · simpa [gate,e] using av false l x
      · simpa [gate,e] using av true l x
      · change g.op=GateOp.not at e
        simp only [gate,e,↓reduceIte,nv,gn]
        cases l <;> rfl
  have track (ls : List Gate) (ok : ∀ g∈ls,g∈C.gates) (u : List F) (v : List ℕ)
      (len : u.length=v.length) (h : ∀ i, mass (u.getD i (.inl false))≤v.getD i 0)
      (p : clean → ∀ z∈u,pos z) :
      (∀ i, mass ((ls.foldl stepF u).getD i (.inl false))≤(ls.foldl stepN v).getD i 0) ∧
      (clean → ∀ z∈ls.foldl stepF u,pos z) := by
    induction ls generalizing u v with
    | nil => exact ⟨h,p⟩
    | cons g ls ih =>
      let l := g.inputs.map fun i => u.getD i (.inl false)
      let k := g.inputs.map fun i => v.getD i 0
      have hd : mass (l.headD (.inl false))≤k.headD 0 := by
        cases e : g.inputs with
        | nil => simp [l,k,e,mass]
        | cons a t => simpa [l,k,e] using h a
      have su (t : List ℕ) : ((t.map fun i => u.getD i (.inl false)).map mass).sum ≤
          (t.map fun i => v.getD i 0).sum := by
        induction t with | nil => exact le_rfl | cons a t ht => exact Nat.add_le_add (h a) ht
      have q : mass (gate g l)≤cost g k := by
        have su' : (l.map mass).sum≤k.sum := su g.inputs
        rcases (allowed g (ok g (by simp))).1 with e|e|e
        · simpa [gate,cost,e,ga] using (aw false l).trans su'
        · simpa [gate,cost,e,go] using (aw true l).trans su'
        · change g.op=GateOp.not at e
          simpa [gate,cost,e,gn,nw] using hd
      apply ih (fun z hz => ok z (by simp [hz])) (stepF u g) (stepN v g) (by simp [stepF,stepN,len])
      · intro i
        rcases Nat.lt_trichotomy i u.length with a|a|a
        · simpa only [stepF,stepN,List.getD_append _ _ _ _ a,List.getD_append _ _ _ _ (a.trans_le len.le)] using h i
        · subst i
          have last {α} (t : List α) (a d : α) : (t++[a]).getD t.length d=a := by simp
          change mass ((u++[gate g l]).getD u.length (.inl false)) ≤ (v++[cost g k]).getD u.length 0
          rw [last,len,last]
          exact q
        · rw [List.getD_eq_default _ _ (by simp [stepF]; omega)]
          exact Nat.zero_le _
      · intro nc z hz
        rcases List.mem_append.mp hz with hu|hg
        · exact p nc z hu
        · obtain rfl := List.mem_singleton.mp hg
          change pos (gate g l)
          rw [show gate g l=agg (g.op=.or) l by simp [gate,quiet g (ok g (by simp)) nc]]
          apply ap
          intro t ht
          obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
          by_cases hi : i<u.length
          · rw [List.getD_eq_getElem _ _ hi]
            exact p nc _ (List.getElem_mem _)
          · rw [List.getD_eq_default _ _ (by omega)]
            trivial
  let start := List.ofFn literal
  let z := (C.gates.foldl stepF start).getD C.output (.inl false)
  have ze (x) : val z x=(fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x := by
    have eq := realize C.gates (fun _ => id) start x
    have init : start.map (fun t => val t x)=List.ofFn x := by simp [start,literal,val,el]
    rw [init] at eq
    rw [show val z x = ((C.gates.foldl stepF start).map (fun t => val t x)).getD C.output false from (mapped _ _ _).symm,eq]
    exact works x
  have hs (i) : mass (start.getD i (.inl false)) ≤ (List.replicate 10 1).getD i 0 := by
    by_cases h : i<10
    · interval_cases i <;> decide +kernel
    · rw [List.getD_eq_default _ _ (by simp [start]; omega)]
      exact Nat.zero_le _
  obtain ⟨measure,allpos⟩ := track C.gates (fun _ => id) start _ (by simp [start]) hs (by
    intro _ t ht
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    rfl)
  have zp (nc : clean) : pos z := by
    by_cases h : C.output<(C.gates.foldl stepF start).length
    · change pos ((C.gates.foldl stepF start).getD C.output (.inl false))
      rw [List.getD_eq_getElem _ _ h]
      exact allpos nc _ (List.getElem_mem _)
    · change pos ((C.gates.foldl stepF start).getD C.output (.inl false))
      rw [List.getD_eq_default _ _ (by omega)]
      trivial
  have high : (if C.gates.any (fun g => g.op.eval [false]) then 19 else 21) ≤ mass z := by
    cases he : z with
    | inl b =>
      have a := ze (fun _ => false)
      have c := ze (fun _ => true)
      rw [he] at a c
      change b=false at a
      change b=true at c
      simp_all
    | inr f =>
      have fl := formulas f (fun x => by simpa only [he,val,Sum.elim_inr] using ze x)
      cases nc : C.gates.any (fun g => g.op.eval [false]) with
      | false => exact fl.2 (by simpa only [he,pos,Sum.elim_inr] using zp nc)
      | true => exact fl.1
  obtain ⟨x,ne⟩ := shared C allowed small (high.trans (measure C.output))
  exact ne (works x)

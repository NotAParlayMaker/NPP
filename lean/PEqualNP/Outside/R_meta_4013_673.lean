import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_4013_673
    (deletion : ∀ D : Circuit,FanInTwo D → D.size≤15 → ∃ x : Fin 9 → Bool,D.eval (List.ofFn x)≠((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (limited : ∀ C : Circuit,FanInTwo C → C.size≤18 → (∀ g∈C.gates,g.op=GateOp.not → g.inputs.length≤1) →
      (C.gates.filter (fun g => decide (0∈g.inputs))).length≤2 →
      (C.gates.filter (fun g => decide (2∈g.inputs))).length≤2 →
      ∃ x : Fin 10 → Bool,C.eval (List.ofFn x++[x 0 || x 2])≠((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)))
    (compile : ∀ (m n : ℕ) (C : Circuit) (s : Fin m → Option (Fin n)), FanInTwo C →
      (∀ g∈C.gates,g.op=GateOp.not → g.inputs.length≤1) →
      (∃ x y : Fin n → Bool,C.eval (List.ofFn (fun j => (s j).elim false x)) ≠ C.eval (List.ofFn (fun j => (s j).elim false y))) →
      ∃ D : Circuit,FanInTwo D ∧ D.size≤C.size ∧ (∀ j : Fin m,s j=none →
        D.size+(C.gates.filter (fun g => decide (j.val∈g.inputs))).length≤C.size) ∧
        ∀ x : Fin n → Bool,D.eval (List.ofFn x)=C.eval (List.ofFn (fun j => (s j).elim false x))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → Function.Surjective x2 → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C π fan sz _
  by_contra! answers
  let F (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let H (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let extra (x : Fin 10 → Bool) : Fin 11 → Bool := Fin.snoc x (x 0 || x 2)
  have enc (x : Fin 10 → Bool) : List.ofFn (extra x)=List.ofFn x++[x 0 || x 2] := by
    rw [List.ofFn_succ']; simp only [extra,Fin.snoc_castSucc,Fin.snoc_last,List.concat_eq_append]
  have witnesses : ∃ x y : Fin 10 → Bool,F x ≠ F y :=
    ⟨fun _ => false,fun _ => true,by decide⟩
  have nineWitness : ∃ x y : Fin 9 → Bool,H x ≠ H y :=
    ⟨fun _ => false,fun _ => true,by decide⟩
  have normalize (B : Circuit) (ok : FanInTwo B) : ∃ E : Circuit, FanInTwo E ∧
      (∀ g∈E.gates,g.op=GateOp.not → g.inputs.length≤1) ∧ E.size=B.size ∧ ∀ w,E.eval w=B.eval w := by
    classical
    let trim (g : Gate) : Gate := if g.op=GateOp.not then ⟨GateOp.not,g.inputs.take 1⟩ else g
    let E : Circuit := ⟨B.gates.map trim,B.output⟩
    have action (g : Gate) (w : List Bool) : (trim g).op.eval ((trim g).inputs.map (fun i => w.getD i false))=
        g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
      obtain ⟨op,ins⟩ := g
      cases op <;> simp [trim]
      cases ins <;> rfl
    let step := fun (w : List Bool) (g : Gate) => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
    have fold (gs : List Gate) (w : List Bool) : (gs.map trim).foldl step w=gs.foldl step w := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih => simp only [List.map_cons,List.foldl_cons,ih]; congr 1; exact congrArg (fun b => w++[b]) (action g w)
    refine ⟨E,?_,?_,by change (B.gates.map trim).length=B.gates.length; simp,?_⟩
    · intro g hg
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hg
      by_cases no : b.op=GateOp.not
      · simp [trim,no]
      · simpa [trim,no] using ok b hb
    · intro g hg
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hg
      by_cases no : b.op=GateOp.not <;> simp [trim,no]
    · intro w; exact congrArg (fun v : List Bool => v.getD B.output false) (fold B.gates w)
  obtain ⟨C0,m0,t0,size0,ev0⟩ := normalize C fan
  let perm : Fin 11 → Option (Fin 11) := Fin.snoc (fun i : Fin 10 => some (π i).castSucc) (some (Fin.last 10))
  have pins (x : Fin 10 → Bool) : List.ofFn (fun j => (perm j).elim false (extra x))=List.ofFn (x ∘ π)++[x 0 || x 2] := by
    rw [List.ofFn_succ']; simp only [perm,extra,Fin.snoc_castSucc,Fin.snoc_last,List.concat_eq_append,Option.elim_some,Function.comp_def]
  have same (x : Fin 10 → Bool) : C0.eval (List.ofFn (fun j => (perm j).elim false (extra x)))=F x := by
    rw [pins,ev0]; exact answers x
  have varies : ∃ x y : Fin 11 → Bool,C0.eval (List.ofFn (fun j => (perm j).elim false x)) ≠
      C0.eval (List.ofFn (fun j => (perm j).elim false y)) := by
    obtain ⟨x,y,h⟩ := witnesses; exact ⟨extra x,extra y,by simpa only [same] using h⟩
  obtain ⟨B0,hb0,sb0,_,eb0⟩ := compile 11 11 C0 perm m0 t0 varies
  obtain ⟨B,hb,tb,sb,eb⟩ := normalize B0 hb0
  have answer (x : Fin 10 → Bool) : B.eval (List.ofFn (extra x))=F x := by rw [eb,eb0,same]
  have bs : B.size≤18 := by omega
  let idx (b : Bool) (j : Fin 10) : Option (Fin 9) := if b then
    ([some 0,some 4,none,some 6,some 1,some 5,some 3,some 7,some 8,some 2] : List (Option (Fin 9))).getD j.val none
    else ([none,some 4,some 0,some 1,some 6,some 7,some 3,some 5,some 2,some 8] : List (Option (Fin 9))).getD j.val none
  let lift (b : Bool) (x : Fin 9 → Bool) (j : Fin 10) := (idx b j).elim false x
  let restrict (b : Bool) : Fin 11 → Option (Fin 9) := Fin.snoc (idx b) (some 0)
  have target (b : Bool) (x : Fin 9 → Bool) : F (lift b x)=H x := by
    cases b <;> simp [F,H,lift,idx,Option.elim_some,Option.elim_none] <;> ac_rfl
  have hint (b : Bool) (x : Fin 9 → Bool) : (lift b x 0 || lift b x 2)=x 0 := by
    cases b <;> simp [lift,idx,Option.elim_some,Option.elim_none]
  have align (b : Bool) (x : Fin 9 → Bool) :
      (fun j => ((restrict b) j).elim false x)=extra (lift b x) := by
    funext j; induction j using Fin.lastCases with
    | last => simp only [restrict,extra,Fin.snoc_last,Option.elim_some,hint]
    | cast j => simp [restrict,extra,lift]
  have restricted (b : Bool) (x : Fin 9 → Bool) :
      B.eval (List.ofFn (fun j => (restrict b j).elim false x))=H x := by rw [align,answer,target]
  have few (b : Bool) :
      (B.gates.filter (fun g => decide ((if b then 2 else 0 : ℕ)∈g.inputs))).length ≤ 2 := by
    by_contra! many
    obtain ⟨x,y,ne⟩ := nineWitness
    obtain ⟨D,md,_,budget,eval⟩ := compile 11 9 B (restrict b) hb tb
      ⟨x,y,by simpa only [restricted] using ne⟩
    let q : Fin 11 := if b then 2 else 0
    have dead : restrict b q=none := by cases b <;> decide
    have cost := budget q dead
    have eq : q.val=(if b then 2 else 0 : ℕ) := by cases b <;> rfl
    rw [eq] at cost
    obtain ⟨z,bad⟩ := deletion D md (by omega)
    exact bad ((eval z).trans (restricted b z))
  obtain ⟨x,fail⟩ := limited B hb bs tb (few false) (few true)
  exact fail (by rw [←enc];exact answer x)

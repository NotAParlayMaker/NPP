import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.ByContra

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_8843_343
    (flagAnd : let E := fun (a b : Fin 26) => (20355639498262484902863237546719798631093146749814442681130959708626547270757391314880948051125895102489604348191062396497016095759193712135955176705373126629154065204916334193957467905828541473890304 : ℕ).testBit (26*a.val+b.val)
      let pos := fun (x : Fin 26 → Bool) => ∃ a b, E a b = true ∧ x = fun i => decide (i=a ∨ i=b)
      let neg := fun (x : Fin 26 → Bool) =>
        (∀ a b, E a b = true → x a = true → x b = false) ∧
        ∀ a, ((List.finRange 26).toFinset.filter fun b => E a b && x b).card ≤ 2
      ∀ (Q : Circuit), Monotone2 Q → Q.size ≤ 62 →
      let run := fun (x : Fin 26 → Bool) => Q.eval (List.ofFn x ++ [false,true,x 0 && x 13])
      (∀ x, pos x → run x = true) → ∃ x, neg x ∧ run x = true)
    (sideOr : let E := fun (a b : Fin 26) => (20355639498262484902863237546719798631093146749814442681130959708626547270757391314880948051125895102489604348191062396497016095759193712135955176705373126629154065204916334193957467905828541473890304 : ℕ).testBit (26*a.val+b.val)
      let pos := fun (x : Fin 26 → Bool) => ∃ a b, E a b = true ∧ x = fun i => decide (i=a ∨ i=b)
      let neg := fun (x : Fin 26 → Bool) =>
        (∀ a b, E a b = true → x a = true → x b = false) ∧
        ∀ a, ((List.finRange 26).toFinset.filter fun b => E a b && x b).card ≤ 2
      ∀ (Q : Circuit), Monotone2 Q → Q.size ≤ 62 →
      let run := fun (x : Fin 26 → Bool) => Q.eval (List.ofFn x ++ [false,true,x 0 || x 1])
      (∀ x, pos x → run x = true) → ∃ x, neg x ∧ run x = true)
    (flagOr : let E := fun (a b : Fin 26) => (20355639498262484902863237546719798631093146749814442681130959708626547270757391314880948051125895102489604348191062396497016095759193712135955176705373126629154065204916334193957467905828541473890304 : ℕ).testBit (26*a.val+b.val)
      let pos := fun (x : Fin 26 → Bool) => ∃ a b, E a b = true ∧ x = fun i => decide (i=a ∨ i=b)
      let neg := fun (x : Fin 26 → Bool) =>
        (∀ a b, E a b = true → x a = true → x b = false) ∧
        ∀ a, ((List.finRange 26).toFinset.filter fun b => E a b && x b).card ≤ 2
      ∀ (Q : Circuit), Monotone2 Q → Q.size ≤ 62 →
      let run := fun (x : Fin 26 → Bool) => Q.eval (List.ofFn x ++ [false,true,x 0 || x 13])
      (∀ x, pos x → run x = true) → ∃ x, neg x ∧ run x = true)
    (nonflagOr : let E := fun (a b : Fin 26) => (20355639498262484902863237546719798631093146749814442681130959708626547270757391314880948051125895102489604348191062396497016095759193712135955176705373126629154065204916334193957467905828541473890304 : ℕ).testBit (26*a.val+b.val)
      let pos := fun (x : Fin 26 → Bool) => ∃ a b, E a b = true ∧ x = fun i => decide (i=a ∨ i=b)
      let neg := fun (x : Fin 26 → Bool) =>
        (∀ a b, E a b = true → x a = true → x b = false) ∧
        ∀ a, ((List.finRange 26).toFinset.filter fun b => E a b && x b).card ≤ 2
      ∀ (Q : Circuit), Monotone2 Q → Q.size ≤ 62 →
      let run := fun (x : Fin 26 → Bool) => Q.eval (List.ofFn x ++ [false,true,x 0 || x 14])
      (∀ x, pos x → run x = true) → ∃ x, neg x ∧ run x = true) :
let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 (Fin.append (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x7)) = Bool.true := by
  have normalize : ∀ (n k : ℕ) (C : Circuit) (pos neg : (Fin n → Bool) → Prop),
      Monotone2 C → C.size ≤ k+1 → (∃ x, pos x) → (∃ x, neg x) →
      (∀ i, ∃ x, pos x ∧ x i = false) →
      (∀ x, pos x → C.eval (List.ofFn x) = true) → (∀ x, neg x → C.eval (List.ofFn x) = false) →
      ∃ (u v : Fin n) (c : Bool) (Q : Circuit) (w : List ℕ), u ≠ v ∧ Monotone2 Q ∧ Q.size ≤ k ∧
        (c = true → ∃ x, pos x ∧ x u = true ∧ x v = true) ∧
        let run := fun (x : Fin n → Bool) => Q.eval (w.map fun i => (List.ofFn x ++ [false,true,if c then x u && x v else x u || x v]).getD i false)
        (∀ x, pos x → run x = true) ∧ ∀ x, neg x → run x = false := by
    intro n k C pos neg mono cap hp hn misses pass reject
    let A := Bool ⊕ Fin n
    let value (x : Fin n → Bool) : A → Bool := Sum.elim id x
    let gate (c a b : Bool) := if c then a && b else a || b
    let maps (x : Fin n → Bool) (as : List A) := as.map (value x)
    let result (gs : List Gate) := ∃ (u v : Fin n) (c : Bool) (Q : Circuit) (w : List ℕ),
        u ≠ v ∧ Monotone2 Q ∧ Q.size < gs.length ∧
        (c = true → ∃ x, pos x ∧ x u = true ∧ x v = true) ∧
        let run := fun (x : Fin n → Bool) => Q.eval (w.map fun i =>
          (List.ofFn x ++ [false,true,gate c (x u) (x v)]).getD i false)
        (∀ x, pos x → run x = true) ∧ ∀ x, neg x → run x = false
    have lookup (x) (as : List A) (i) : (maps x as).getD i false = value x (as.getD i (.inl false)) :=
      List.getD_map as (.inl false) (value x)
    have extendLe {l r : List Bool} {b d : Bool} (len : l.length=r.length)
        (lo : ∀ i, l.getD i false=true → r.getD i false=true) (bit : b=true → d=true) :
        ∀ i, (l++[b]).getD i false=true → (r++[d]).getD i false=true := by
      intro i
      by_cases h : i < l.length
      · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (len ▸ h)]
        exact lo i
      · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),←len]
        cases i-l.length with
        | zero => exact bit
        | succ t => simp
    have monoTail (gs : List Gate) (tags : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) :
        ∀ (l r : List Bool), l.length=r.length → (∀ i,l.getD i false=true → r.getD i false=true) →
        ∀ j, ((Circuit.mk gs j).eval l)=true → ((Circuit.mk gs j).eval r)=true := by
      induction gs with
      | nil => intro l r _ lo; exact lo
      | cons g gs ih =>
        intro l r len lo j
        let V (s : List Bool) := g.op.eval (g.inputs.map fun i => s.getD i false)
        change (Circuit.mk gs j).eval (l++[V l]) = true → (Circuit.mk gs j).eval (r++[V r]) = true
        apply ih (fun t ht => tags t (List.mem_cons_of_mem _ ht)) _ _ (by simp [len]) (extendLe len lo ?_) j
        rcases tags g List.mem_cons_self with tag|tag
        · change g.op.eval _ = true → g.op.eval _ = true
          rw [tag]
          change (g.inputs.map _).all id = true → (g.inputs.map _).all id = true
          simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
          exact fun h i hi => lo i (h i hi)
        · change g.op.eval _ = true → g.op.eval _ = true
          rw [tag]
          change (g.inputs.map _).any id = true → (g.inputs.map _).any id = true
          simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
          rintro ⟨i,hi,h⟩; exact ⟨i,hi,lo i h⟩
    -- For AND, a new variable pair is useful only if a positive row ever contains both.
    have reducePair (c : Bool) (a b : A) :
        (∃ t : A, (∀ x, pos x → value x t = gate c (value x a) (value x b)) ∧
          ∀ x, value x t=true → gate c (value x a) (value x b)=true) ∨
        ∃ u v : Fin n, a=.inr u ∧ b=.inr v ∧ u≠v ∧ (c=true → ∃ x, pos x ∧ x u=true ∧ x v=true) := by
      cases a with
      | inl p =>
        cases c <;> cases p
        · exact Or.inl ⟨b,fun _ _ => rfl,fun _ h => h⟩
        · exact Or.inl ⟨.inl true,fun _ _ => rfl,fun _ _ => rfl⟩
        · exact Or.inl ⟨.inl false,fun _ _ => rfl,fun _ h => h⟩
        · exact Or.inl ⟨b,fun _ _ => rfl,fun _ h => h⟩
      | inr u =>
        cases b with
        | inl q =>
          cases c <;> cases q
          · exact Or.inl ⟨.inr u,fun x _ => by simp [value,gate],fun x h => by simpa [value,gate] using h⟩
          · exact Or.inl ⟨.inl true,fun x _ => by simp [value,gate],fun x _ => by simp [value,gate]⟩
          · exact Or.inl ⟨.inl false,fun x _ => by simp [value,gate],fun x h => False.elim (Bool.noConfusion h)⟩
          · exact Or.inl ⟨.inr u,fun x _ => by simp [value,gate],fun x h => by simpa [value,gate] using h⟩
        | inr v =>
          by_cases h : u=v
          · subst v; exact Or.inl ⟨.inr u,fun x _ => by cases c <;> simp [gate,value],
              fun x hx => by cases c <;> simpa [gate,value] using hx⟩
          · by_cases live : c=true → ∃ x, pos x ∧ x u=true ∧ x v=true
            · exact Or.inr ⟨u,v,rfl,rfl,h,live⟩
            · have yes : c=true := by
                cases hc : c with
                | true => rfl
                | false => exact False.elim (live (fun eq => False.elim (Bool.noConfusion (hc.symm.trans eq))))
              refine Or.inl ⟨.inl false,?_,fun _ h => False.elim (Bool.noConfusion h)⟩
              intro x hx
              change false = gate c (x u) (x v)
              cases hu : x u <;> cases hv : x v <;> simp only [yes,gate,ite_true,Bool.and_false,Bool.and_true]
              exact (live (fun _ => ⟨x,hx,hu,hv⟩)).elim
    have extract (gs : List Gate) (as : List A) (out : ℕ)
        (legal : Monotone2 ⟨gs,out⟩)
        (yes : ∀ x,pos x → (Circuit.mk gs out).eval (maps x as)=true)
        (no : ∀ x,neg x → (Circuit.mk gs out).eval (maps x as)=false) : result gs := by
      induction gs generalizing as with
      | nil =>
        exfalso
        have val (x) : (Circuit.mk [] out).eval (maps x as) = value x (as.getD out (.inl false)) := lookup _ _ _
        cases h : as.getD out (.inl false) with
        | inl bit =>
          cases bit with
          | false =>
            obtain ⟨x,hx⟩ := hp
            have wrong := yes x hx
            rw [val,h] at wrong
            exact Bool.noConfusion (show false=true from wrong)
          | true =>
            obtain ⟨x,hx⟩ := hn
            have wrong := no x hx
            rw [val,h] at wrong
            exact Bool.noConfusion (show true=false from wrong)
        | inr u =>
          obtain ⟨x,hx,off⟩ := misses u
          have h' := yes x hx; rw [val,h] at h'; exact Bool.noConfusion (off.symm.trans h')
      | cons g gs ih =>
        let tail : Circuit := ⟨gs,out⟩
        have tl : Monotone2 tail := fun t ht => legal t (List.mem_cons_of_mem _ ht)
        have tag : g.op = .and ∨ g.op = .or := (legal g List.mem_cons_self).1
        let c : Bool := GateOp.rec (motive := fun _ => Bool) true false false (fun _ => false) false g.op
        let vs := g.inputs.map (fun j => as.getD j (.inl false))
        let bit (x : Fin n → Bool) := g.op.eval (vs.map (value x))
        have run (x) : (Circuit.mk (g::gs) out).eval (maps x as) = tail.eval (maps x as ++ [bit x]) := by
          change tail.eval (_ ++ [g.op.eval (g.inputs.map _)]) = _
          simp only [bit,vs,List.map_map,Function.comp_def,lookup]
        have simple (t : A) (eq : ∀ x,pos x → value x t=bit x) (down : ∀ x,value x t=true → bit x=true) :
            result (g::gs) := by
          have y (x) (hx : pos x) : tail.eval (maps x (as++[t])) = true := by
            have same : maps x (as++[t])=maps x as ++ [bit x] := by simp [maps,eq x hx]
            rw [same]; exact (run x).symm.trans (yes x hx)
          have z (x) (hx : neg x) : tail.eval (maps x (as++[t])) = false := by
            apply Bool.eq_false_iff.mpr
            intro wrong
            change tail.eval ((as++[t]).map (value x))=true at wrong
            rw [List.map_append] at wrong
            have imp := monoTail gs (fun a ha => (tl a ha).1) _ _ (by simp)
              (extendLe rfl (fun _ h => h) (down x)) out wrong
            exact Bool.noConfusion ((run x ▸ no x hx).symm.trans imp)
          obtain ⟨u,v,c,Q,w,uv,mon,bnd,live,ok⟩ := ih (as++[t]) tl y z
          exact ⟨u,v,c,Q,w,uv,mon,Nat.lt_succ_of_lt bnd,live,ok⟩
        have args : vs.length ≤ 2 := by simpa only [vs,List.length_map] using (legal g List.mem_cons_self).2
        have shapes (s : List A) : s.length ≤ 2 → s=[] ∨ (∃ a, s=[a]) ∨ ∃ a b, s=[a,b] := by
          cases s with
          | nil => exact fun _ => Or.inl rfl
          | cons a xs =>
            cases xs with
            | nil => exact fun _ => Or.inr (Or.inl ⟨a,rfl⟩)
            | cons b xs =>
              cases xs with
              | nil => exact fun _ => Or.inr (Or.inr ⟨a,b,rfl⟩)
              | cons d rest => simp
        rcases shapes vs args with hs|⟨a,hs⟩|⟨a,b,hs⟩
        · exact simple (.inl (g.op.eval [])) (fun x _ => by simp [bit,hs,value]) (fun x h => by simpa [bit,hs,value] using h)
        ·
          have one x : bit x=value x a := by rcases tag with t|t <;> rw [show bit x = g.op.eval [value x a] by simp [bit,hs],t] <;> cases value x a <;> rfl
          exact simple a (fun x _ => (one x).symm) (fun x h => (one x).trans h)
        ·
          have two x : bit x=gate c (value x a) (value x b) := by
            rcases tag with t|t <;> simp only [bit,hs,List.map_cons,List.map_nil,c,t] <;>
              cases value x a <;> cases value x b <;> rfl
          rcases reducePair c a b with ⟨t,ter,small⟩|⟨u,v,ha,hb,uv,live⟩
          · exact simple t (fun x hx => (ter x hx).trans (two x).symm) (fun x h => (two x).trans (small x h))
          · subst a; subst b
            let ix : A → ℕ := Sum.elim (fun b => n+b.toNat) Fin.val
            let tape (x : Fin n → Bool) := List.ofFn x ++ [false,true,gate c (x u) (x v)]
            have wire (x : Fin n → Bool) (s : A) : (tape x).getD (ix s) false = value x s := by
              cases s with
              | inl b => cases b <;> simp [tape,ix,value]
              | inr i =>
                change (List.ofFn x ++ _).getD i.val false = x i
                rw [List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
            have endwire (x) : (tape x).getD (n+2) false=bit x := by
              rw [two]
              change (List.ofFn x ++ _).getD (n+2) false = gate c (x u) (x v)
              rw [List.getD_append_right _ _ _ _ (by simp)]
              simp
            have initial (x) : (as.map ix ++ [n+2]).map (fun i => (tape x).getD i false) = maps x as ++ [bit x] := by
              simp only [List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,wire,endwire,maps]
            refine ⟨u,v,c,tail,as.map ix++[n+2],uv,tl,by change gs.length < (g::gs).length; simp,live,?_,?_⟩
            · intro x hx; exact (congrArg tail.eval (initial x)).trans ((run x).symm.trans (yes x hx))
            · intro x hx; exact (congrArg tail.eval (initial x)).trans ((run x).symm.trans (no x hx))
    let raw : List A := List.ofFn (fun i : Fin n => Sum.inr i)
    have rawValues x : maps x raw = List.ofFn x := by simp [maps,raw,List.map_ofFn,value,Function.comp_def]
    obtain ⟨u,v,c,Q,w,uv,mon,bnd,live,ok⟩ := extract C.gates raw C.output mono
      (fun x hx => by rw [rawValues]; exact pass x hx) (fun x hx => by rw [rawValues]; exact reject x hx)
    exact ⟨u,v,c,Q,w,uv,mon,by change Q.size < C.size at bnd; omega,live,ok⟩
  have rewire : ∀ (Q : Circuit) (N falseWire : ℕ) (w : List ℕ), falseWire < N →
    ∃ D : Circuit, D.size=Q.size ∧ (Monotone2 Q → Monotone2 D) ∧
    ∀ X : List Bool, X.length=N → X.getD falseWire false=false →
      Q.eval (w.map fun i => X.getD i false) = D.eval X := by
    intro Q N falseWire w below
    let r (i : ℕ) := if i < w.length then
        if w.getD i falseWire < N then w.getD i falseWire else falseWire
      else N+(i-w.length)
    let rename (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩
    let D : Circuit := ⟨Q.gates.map rename,r Q.output⟩
    refine ⟨D,List.length_map _,?_,?_⟩
    · intro mono g hg
      change g ∈ Q.gates.map rename at hg
      obtain ⟨g,old,rfl⟩ := List.mem_map.mp hg
      obtain ⟨tag,ports⟩ := mono g old
      exact ⟨tag,by simpa only [rename,List.length_map] using ports⟩
    · intro X len off
      let Y := w.map fun i => X.getD i false
      have oldLen : Y.length=w.length := List.length_map _
      have rel (vs : List Bool) (i : ℕ) : (Y++vs).getD i false = (X++vs).getD (r i) false := by
        by_cases old : i < w.length
        · rw [List.getD_append _ _ _ _ (by omega),show r i = (if w.getD i falseWire<N then w.getD i falseWire else falseWire) by simp [r,old]]
          have atOld : Y.getD i false = X.getD (w.getD i falseWire) false := by
            rw [List.getD_eq_getElem _ _ (by omega)]
            change (w.map _)[i] = _
            rw [List.getElem_map,List.getD_eq_getElem w _ old]
          rw [atOld]
          split <;> rename_i h
          · exact (List.getD_append _ _ _ _ (by omega)).symm
          · rw [List.getD_eq_default _ _ (by omega),List.getD_append _ _ _ _ (by omega),off]
        · have shift : r i = N+(i-w.length) := by simp [r,old]
          rw [shift,List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
          rw [oldLen,len,Nat.add_sub_cancel_left]
      have exec (gs : List Gate) (vs : List Bool) (out : ℕ) :
          (Circuit.mk gs out).eval (Y++vs)=(Circuit.mk (gs.map rename) (r out)).eval (X++vs) := by
        induction gs generalizing vs with
        | nil => exact rel vs out
        | cons g gs ih =>
          let b := g.op.eval (g.inputs.map (fun i => (Y++vs).getD i false))
          have same : (rename g).op.eval ((rename g).inputs.map (fun i => (X++vs).getD i false)) = b := by
            simp only [rename,List.map_map,Function.comp_def,b,rel]
          change (Circuit.mk gs out).eval ((Y++vs)++[b]) =
            (Circuit.mk (gs.map rename) (r out)).eval ((X++vs)++[(rename g).op.eval _])
          rw [same,List.append_assoc,List.append_assoc,ih]
      simpa only [List.append_nil] using exec Q.gates [] Q.output
  intro I C mono bound accepted
  let E := fun (a b : Fin 26) => (20355639498262484902863237546719798631093146749814442681130959708626547270757391314880948051125895102489604348191062396497016095759193712135955176705373126629154065204916334193957467905828541473890304 : ℕ).testBit (26*a.val+b.val)
  let pos := fun (x : Fin 26 → Bool) => ∃ a b, E a b = true ∧ x = fun i => decide (i=a ∨ i=b)
  let neg := fun (x : Fin 26 → Bool) =>
        (∀ a b, E a b = true → x a = true → x b = false) ∧
        ∀ a, ((List.finRange 26).toFinset.filter fun b => E a b && x b).card ≤ 2
  let pt (p : Fin 13) : Fin 26 := Fin.castAdd 13 p
  let ln (l : Fin 13) : Fin 26 := Fin.natAdd 13 l
  have connect : ∀ p l : Fin 13, I p l → E (pt p) (ln l) = true ∧ E (ln l) (pt p) = true := by decide +kernel
  have fromEdge : ∀ a b : Fin 26, E a b = true → ∃ p l, I p l ∧
      ((a = pt p ∧ b = ln l) ∨ (a = ln l ∧ b = pt p)) := by decide +kernel
  have hasPos : ∃ x, pos x := ⟨_,0,13,by decide +kernel,rfl⟩
  have hasNeg : ∃ x, neg x := ⟨fun _ => false, fun _ _ _ h => by contradiction, fun _ => by simp⟩
  have misses (i : Fin 26) : ∃ x, pos x ∧ x i = false := by
    have all : ∀ k : Fin 26, ∃ a b, E a b = true ∧ k ≠ a ∧ k ≠ b := by decide +kernel
    obtain ⟨a,b,h,ha,hb⟩ := all i
    exact ⟨_,⟨a,b,h,rfl⟩,by simp [ha,hb]⟩
  have positive (x) (hx : pos x) : C.eval (List.ofFn x) = true := by
    obtain ⟨a,b,h,rfl⟩ := hx
    obtain ⟨p,l,inc,h|h⟩ := fromEdge a b h
    · obtain ⟨rfl,rfl⟩ := h
      exact accepted p l inc
    · obtain ⟨rfl,rfl⟩ := h
      have hr : (fun i : Fin 26 => decide (i=ln l ∨ i=pt p)) =
          (fun i => decide (i=pt p ∨ i=ln l)) := by funext i; exact decide_eq_decide.mpr or_comm
      rw [hr]
      exact accepted p l inc
  by_contra no
  have negative (x) (hx : neg x) : C.eval (List.ofFn x) = false := by
    by_contra wrong
    have on : C.eval (List.ofFn x) = true := Bool.eq_true_of_not_eq_false wrong
    let P := Finset.univ.filter fun p : Fin 13 => x (pt p)
    let L := Finset.univ.filter fun l : Fin 13 => x (ln l)
    have hp (p) : p ∈ P ↔ x (pt p) = true := by simp [P]
    have hl (l) : l ∈ L ↔ x (ln l) = true := by simp [L]
    apply no
    refine ⟨P,L,?_,?_,?_,?_⟩
    · intro p inp l inl inc
      have off := hx.1 _ _ (connect p l inc).1 ((hp p).mp inp)
      exact Bool.noConfusion (off.symm.trans ((hl l).mp inl))
    · intro l
      apply le_trans _ (hx.2 (ln l))
      apply Finset.card_le_card_of_injOn pt _ (fun _ _ _ _ h => Fin.castAdd_inj.mp h)
      intro p membership
      obtain ⟨inp,inc⟩ := Finset.mem_filter.mp membership
      exact Finset.mem_filter.mpr ⟨by simp,by rw [(connect p l inc).2,(hp p).mp inp]; rfl⟩
    · intro p
      apply le_trans _ (hx.2 (pt p))
      apply Finset.card_le_card_of_injOn ln _ (fun _ _ _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h)))
      intro l membership
      obtain ⟨inl,inc⟩ := Finset.mem_filter.mp membership
      exact Finset.mem_filter.mpr ⟨by simp,by rw [(connect p l inc).1,(hl l).mp inl]; rfl⟩
    · have same : Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L)) = x := by
        funext i
        refine Fin.addCases (fun p => ?_) (fun l => ?_) i
        · rw [Fin.append_left]
          change decide (p ∈ P) = x (pt p)
          rw [Bool.eq_iff_iff,decide_eq_true_eq,hp]
        · rw [Fin.append_right]
          change decide (l ∈ L) = x (ln l)
          rw [Bool.eq_iff_iff,decide_eq_true_eq,hl]
      rw [same]
      exact on
  obtain ⟨u,v,c,Q,w,uv,qmono,qcap,live,yes,noQ⟩ :=
    normalize 26 62 C pos neg mono bound hasPos hasNeg misses positive negative
  let fwd (i : Fin 3) (w : Fin 26) := Fin.ofNat 26 ((([[1,2,3,4,5,6,7,8,9,10,11,12,0,14,15,16,17,18,19,20,21,22,23,24,25,13],[13,25,24,23,22,21,20,19,18,17,16,15,14,0,12,11,10,9,8,7,6,5,4,3,2,1],[0,1,2,3,10,11,7,6,12,9,4,5,8,13,14,15,20,23,24,19,16,22,21,17,18,25]] : List (List ℕ)).getD i.val []).getD w.val 0)
  let bwd (i : Fin 3) (w : Fin 26) := Fin.ofNat 26 ((([[12,0,1,2,3,4,5,6,7,8,9,10,11,25,13,14,15,16,17,18,19,20,21,22,23,24],[13,25,24,23,22,21,20,19,18,17,16,15,14,0,12,11,10,9,8,7,6,5,4,3,2,1],[0,1,2,3,10,11,7,6,12,9,4,5,8,13,14,15,20,23,24,19,16,22,21,17,18,25]] : List (List ℕ)).getD i.val []).getD w.val 0)
  have inv : ∀ i w, bwd i (fwd i w) = w ∧ fwd i (bwd i w) = w := by decide +kernel
  have invariant : ∀ i a b, E (fwd i a) (fwd i b) = E a b := by decide +kernel
  let code (a b : Fin 26) := Fin.ofNat 3 ((2115016613386899890182156607516239127374387865892453795783715195029343890345637825038350125423994674526951849234554119524100331948788119238909634952303211336995642128137254723363822137699630888955968179617487685229679080786441634992739515591056951973572815576138702515002276308278076923814867143050575898376192202965085277072070505819663662078665394458377484006779654964452636159173664304675680925992953856 : ℕ) / 4^(26*a.val+b.val) % 4)
  let base (a b : Fin 26) := decide (a=0 ∧ (b=1 ∨ b=13 ∨ b=14))
  let reach : ℕ → Fin 26 → Fin 26 → Bool := Nat.rec base (fun _ last a b =>
    base a b || last (fwd (code a b) a) (fwd (code a b) b))
  have reaches : ∀ a b : Fin 26, a ≠ b → reach 11 a b = true := by decide +kernel
  have transports (k) : ∀ a b, reach k a b = true → ∃ σ : Equiv.Perm (Fin 26),
      (∀ i j, E (σ i) (σ j) = E i j) ∧ σ a=0 ∧ (σ b=1 ∨ σ b=13 ∨ σ b=14) := by
    induction k with
    | zero =>
      intro a b h
      exact ⟨Equiv.refl _,fun _ _ => rfl,of_decide_eq_true h⟩
    | succ k ih =>
      intro a b h
      change (base a b || reach k (fwd (code a b) a) (fwd (code a b) b)) = true at h
      rw [Bool.or_eq_true] at h
      rcases h with basecase|next
      · exact ⟨Equiv.refl _,fun _ _ => rfl,of_decide_eq_true basecase⟩
      · obtain ⟨σ,hσ,ha,hb⟩ := ih _ _ next
        let g := code a b
        let π : Equiv.Perm (Fin 26) := ⟨fwd g,bwd g,fun w => (inv g w).1,fun w => (inv g w).2⟩
        exact ⟨π.trans σ,fun i j => (hσ (fwd g i) (fwd g j)).trans (invariant g i j),ha,hb⟩
  obtain ⟨σ,hσ,atU,atV⟩ := transports 11 u v (reaches u v uv)
  have posMap (x) (h : pos x) : pos (fun i => x (σ i)) := by
    obtain ⟨a,b,ab,rfl⟩ := h
    refine ⟨σ.symm a,σ.symm b,?_,?_⟩
    · simpa only [Equiv.apply_symm_apply] using (hσ (σ.symm a) (σ.symm b)).symm.trans (by simpa using ab)
    · funext i
      simp only [Equiv.eq_symm_apply]
  have negMap (x) (h : neg x) : neg (fun i => x (σ i)) := by
    refine ⟨fun a b ab => h.1 _ _ ((hσ a b).trans ab),fun a => ?_⟩
    apply le_trans _ (h.2 (σ a))
    apply Finset.card_le_card_of_injOn σ _ (fun _ _ _ _ e => σ.injective e)
    intro b hb
    obtain ⟨_,one⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨by simp,by rw [hσ]; exact one⟩
  let index (i : ℕ) := if hi : i<26 then (σ ⟨i,hi⟩).val else i
  obtain ⟨D,dsize,dm,dsim⟩ := rewire Q 29 26 (w.map index) (by decide)
  have dmono := dm qmono
  have dcap : D.size ≤ 62 := dsize.le.trans qcap
  let tape (x : Fin 26 → Bool) (b : Bool) := List.ofFn x ++ [false,true,b]
  have readIndex (x : Fin 26 → Bool) (b : Bool) (i : ℕ) :
      (tape x b).getD (index i) false = (tape (fun j => x (σ j)) b).getD i false := by
    by_cases h : i<26
    · let j : Fin 26 := ⟨i,h⟩
      have ir : index i = (σ j).val := by simp [index,h,j]
      rw [ir]
      change (List.ofFn x ++ _).getD (σ j).val false = (List.ofFn _ ++ _).getD i false
      rw [List.getD_append _ _ _ _ (by simp),List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using h),
        List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),
        List.getElem_ofFn,List.getElem_ofFn]
    · have ir : index i=i := by simp [index,h]
      rw [ir]
      change (List.ofFn x ++ _).getD i false = (List.ofFn (fun j => x (σ j)) ++ _).getD i false
      rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by simp; omega),
        List.length_ofFn,List.length_ofFn]
  let b (x : Fin 26 → Bool) := if c then x (σ u) && x (σ v) else x (σ u) || x (σ v)
  have converted (x : Fin 26 → Bool) :
      Q.eval (w.map fun i => (tape (fun j => x (σ j)) (b x)).getD i false) = D.eval (tape x (b x)) := by
    have eq : (w.map index).map (fun i => (tape x (b x)).getD i false) =
        w.map (fun i => (tape (fun j => x (σ j)) (b x)).getD i false) := by
      simp only [List.map_map,Function.comp_def,readIndex]
    rw [←eq]
    exact dsim _ (by simp [tape]) (by simp [tape])
  have edgeUV (hc : c=true) : E u v=true := by
    obtain ⟨_,⟨a,b,e,rfl⟩,ha,hb⟩ := live hc
    have comm : ∀ i j, E i j = E j i := by decide +kernel
    rcases of_decide_eq_true ha with rfl|rfl <;> rcases of_decide_eq_true hb with rfl|rfl
    · exact (uv rfl).elim
    · exact e
    · exact (comm _ _).trans e
    · exact (uv rfl).elim
  cases hc : c with
  | true =>
    have ev := (hσ u v).trans (edgeUV hc)
    rw [atU] at ev
    have mid : σ v = 13 := by
      rcases atV with one|flag|other
      · rw [one] at ev; exact (by decide +kernel : E 0 1 ≠ true) ev |>.elim
      · exact flag
      · rw [other] at ev; exact (by decide +kernel : E 0 14 ≠ true) ev |>.elim
    obtain ⟨x,hx,bad⟩ := flagAnd D dmono dcap (fun x hx => by
      simpa only [tape,b,hc,ite_true,atU,mid] using (converted x).symm.trans (yes _ (posMap x hx)))
    have off := (converted x).symm.trans (noQ _ (negMap x hx))
    simp only [tape,b,hc,ite_true,atU,mid] at off
    exact Bool.noConfusion (off.symm.trans bad)
  | false =>
    rcases atV with side|cross
    · obtain ⟨x,hx,bad⟩ := sideOr D dmono dcap (fun x hx => by
        simpa only [tape,b,hc,Bool.false_eq_true,ite_false,atU,side] using (converted x).symm.trans (yes _ (posMap x hx)))
      have off := (converted x).symm.trans (noQ _ (negMap x hx))
      simp only [tape,b,hc,Bool.false_eq_true,ite_false,atU,side] at off
      exact Bool.noConfusion (off.symm.trans bad)
    · rcases cross with flag|nonflag
      · obtain ⟨x,hx,bad⟩ := flagOr D dmono dcap (fun x hx => by
          simpa only [tape,b,hc,Bool.false_eq_true,ite_false,atU,flag] using (converted x).symm.trans (yes _ (posMap x hx)))
        have off := (converted x).symm.trans (noQ _ (negMap x hx))
        simp only [tape,b,hc,Bool.false_eq_true,ite_false,atU,flag] at off
        exact Bool.noConfusion (off.symm.trans bad)
      · obtain ⟨x,hx,bad⟩ := nonflagOr D dmono dcap (fun x hx => by
          simpa only [tape,b,hc,Bool.false_eq_true,ite_false,atU,nonflag] using (converted x).symm.trans (yes _ (posMap x hx)))
        have off := (converted x).symm.trans (noQ _ (negMap x hx))
        simp only [tape,b,hc,Bool.false_eq_true,ite_false,atU,nonflag] at off
        exact Bool.noConfusion (off.symm.trans bad)

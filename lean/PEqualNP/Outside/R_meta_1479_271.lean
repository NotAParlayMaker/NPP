import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open Relation

-- A directed edge follows an OR input, or an AND input whose other input is on.
-- Only wires that turn on between the singleton and the marked pair are needed.
-- Absence of an input-to-output route in each direction certifies a double reread.
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.R_meta_1479_271
    (extract : ∀ (C : Circuit) (n : ℕ) (B : ℕ → Bool) (seed : ℕ),seed<n →
      let R := fun (u v : ℕ) ↦ ∃ (j : ℕ) (o : GateOp) (w : ℕ), v=n+j ∧
        (C.gates[j]?=some ⟨o,[u,w]⟩ ∨ C.gates[j]?=some ⟨o,[w,u]⟩) ∧ (o=.or ∨ B w=true)
      ∃ d : ℕ → Bool, (∀ i<n,d i=decide (i=seed)) ∧
        (∀ j (g : Gate) x y,C.gates[j]?=some g → g.inputs=[x,y] →
          (g.op=.and → d (n+j)=((B x && d y) || (d x && B y))) ∧
          (g.op=.or → d (n+j)=(d x || d y))) ∧
        ∀ u,d u=true ↔ ReflTransGen R seed u)
    (trim : ∀ (n : ℕ) (C : Circuit), (∀ j (g : Gate),C.gates[j]?=some g → (g.op=.and ∨ g.op=.or) ∧
        ∃ a b : ℕ,g.inputs=[a,b] ∧ a≠b ∧ a<n+j ∧ b<n+j) → ∀ (src seed : Fin n),
      let x := fun i ↦ decide (i=src)
      let y := PEqualNP.EdgeOwnership.pairInput src seed
      let B := PEqualNP.BlindGate.wireValue C n x
      let Y := PEqualNP.BlindGate.wireValue C n y
      let R := fun (u v : ℕ) ↦ ∃ (j : ℕ) (o : GateOp) (w : ℕ), v=n+j ∧
        (C.gates[j]?=some ⟨o,[u,w]⟩ ∨ C.gates[j]?=some ⟨o,[w,u]⟩) ∧ (o=.or ∨ B w=true)
      C.eval (List.ofFn x)=false →
      (ReflTransGen R seed.val C.output ↔ ReflTransGen
        (fun u v ↦ R u v ∧ B v=false ∧ Y u=true) seed.val C.output))
    (boundaries : ∀ (n : ℕ) (C : Circuit), (∀ j (g : Gate),C.gates[j]?=some g → (g.op=.and ∨ g.op=.or) ∧
        ∃ a b : ℕ,g.inputs=[a,b] ∧ a≠b ∧ a<n+j ∧ b<n+j) → ∀ f : (Fin n → Bool) → Prop,
      (∀ x,(Minimal f x ∨ Maximal (fun y ↦ ¬f y) x) → (C.eval (List.ofFn x)=true ↔ f x)) →
      ∀ x,C.eval (List.ofFn x)=true ↔ f x)
    (search : let E (p l : Fin 7) := p=l ∨ p=l+1 ∨ p=l+3
      let hit (x : Fin 14 → Bool) := ∃ p l : Fin 7,E p l ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
      ∃ C : Circuit, C.size≤27 ∧ PEqualNP.TopForm.IsAO2 14 C ∧ (∀ g∈C.gates,g.inputs.Nodup) ∧
        (∀ x,(Minimal hit x ∨ Maximal (fun y ↦ ¬hit y) x) → (C.eval (List.ofFn x)=true ↔ hit x)) ∧
        ∃ p l : Fin 7,E p l ∧ ∀ s : Bool,
          let src : Fin 14 := if s then Fin.castAdd 7 p else Fin.natAdd 7 l
          let seed : Fin 14 := if s then Fin.natAdd 7 l else Fin.castAdd 7 p
          let x := fun i ↦ decide (i=src)
      let y := PEqualNP.EdgeOwnership.pairInput src seed
      let B := PEqualNP.BlindGate.wireValue C 14 x
      let Y := PEqualNP.BlindGate.wireValue C 14 y
      let R := fun (u v : ℕ) ↦ ∃ (j : ℕ) (o : GateOp) (w : ℕ), v=14+j ∧
        (C.gates[j]?=some ⟨o,[u,w]⟩ ∨ C.gates[j]?=some ⟨o,[w,u]⟩) ∧ (o=.or ∨ B w=true)
      ¬ ReflTransGen
            (fun u v ↦ R u v ∧ B v=false ∧ Y u=true) seed.val C.output) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  let E (p l : Fin 7) := p=l ∨ p=l+1 ∨ p=l+3
  let hit (x : Fin 14 → Bool) := ∃ p l : Fin 7,E p l ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
  obtain ⟨C,size,ao,nodup,tests,p,l,edge,blocked⟩ := search
  have legal (j : ℕ) (g : Gate) (get : C.gates[j]?=some g) :
      (g.op=.and ∨ g.op=.or) ∧ ∃ a b : ℕ,g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j := by
    have mem := List.mem_iff_getElem?.2 ⟨j,get⟩
    obtain ⟨u,v,h⟩ := List.length_eq_two.mp (ao.2.2 g mem)
    have current : PEqualNP.MetaComplexity.NestedCover.gateAt C j=g := by
      change C.gates.getD j ⟨GateOp.or,[]⟩=g
      simp [List.getD_eq_getElem?_getD,get]
    have back := ao.2.1 j (List.getElem?_eq_some_iff.1 get).1
    rw [current,h] at back
    exact ⟨ao.1 g mem,u,v,h,by simpa [h] using nodup g mem,back u (by simp),back v (by simp)⟩
  have spec := boundaries 14 C legal hit tests
  have alone : ∀ z : Fin 14,¬ hit (fun i ↦ decide (i=z)) := by decide
  have off (z : Fin 14) : C.eval (List.ofFn (fun i ↦ decide (i=z)))=false := by
    cases h : C.eval (List.ofFn (fun i ↦ decide (i=z))) with
    | false => rfl
    | true => exact (alone z ((spec _).mp h)).elim
  let B (src : Fin 14) := PEqualNP.BlindGate.wireValue C 14 (fun i ↦ decide (i=src))
  let Y (src seed : Fin 14) := PEqualNP.BlindGate.wireValue C 14 (PEqualNP.EdgeOwnership.pairInput src seed)
  let R (src : Fin 14) (u v : ℕ) := ∃ (j : ℕ) (o : GateOp) (w : ℕ), v=14+j ∧
    (C.gates[j]?=some ⟨o,[u,w]⟩ ∨ C.gates[j]?=some ⟨o,[w,u]⟩) ∧ (o=.or ∨ B src w=true)
  have getTrace (src seed : Fin 14) (nopath : ¬ReflTransGen
      (fun u v ↦ R src u v ∧ B src v=false ∧ Y src seed u=true) seed.val C.output) :
      ∃ d : ℕ → Bool, (∀ i : Fin 14,d i.val=decide (i=seed)) ∧
      (∀ j (g : Gate) x y,C.gates[j]?=some g → g.inputs=[x,y] →
        (g.op=.and → d (14+j)=((B src x && d y) || (d x && B src y))) ∧
        (g.op=.or → d (14+j)=(d x || d y))) ∧ d C.output=false := by
    obtain ⟨d,inputs,gates,correct⟩ := extract C 14 (B src) seed.val seed.isLt
    refine ⟨d,fun i ↦ ?_,gates,?_⟩
    · simpa [Fin.ext_iff] using inputs i.val i.isLt
    · cases h : d C.output with
      | false => rfl
      | true => exact (nopath ((trim 14 C legal src seed (off src)).mp ((correct _).mp h))).elim
  obtain ⟨v,vin,vg,vo⟩ := getTrace (Fin.castAdd 7 p) (Fin.natAdd 7 l) (blocked true)
  obtain ⟨w,win,wg,wo⟩ := getTrace (Fin.natAdd 7 l) (Fin.castAdd 7 p) (blocked false)
  refine ⟨C,size,legal,spec,p,l,edge,⟨v,?_,vg,vo⟩,w,?_,wg,wo⟩
  · intro i
    constructor
    · simpa [Fin.ext_iff,show i.val≠l.val+7 by omega] using vin (Fin.castAdd 7 i)
    · simpa [Fin.ext_iff,Nat.add_comm] using vin (Fin.natAdd 7 i)
  · intro i
    constructor
    · simpa [Fin.ext_iff] using win (Fin.castAdd 7 i)
    · simpa [Fin.ext_iff,Nat.add_comm 7,show i.val+7≠p.val by omega] using win (Fin.natAdd 7 i)

-- Proofs of the three general premises follow.
-- The fold lemmas are adapted from the project proof L_meta_1490 by willakone.
-- namespace Eric.FanoRouting
-- open PEqualNP.CircuitLowerBounds
-- open Relation
--
-- def arc (C : Circuit) (n : ℕ) (B : ℕ → Bool) (u v : ℕ) : Prop :=
--   ∃ (j : ℕ) (o : GateOp) (w : ℕ), v=n+j ∧
--     (C.gates[j]?=some ⟨o,[u,w]⟩ ∨ C.gates[j]?=some ⟨o,[w,u]⟩) ∧
--     (o=.or ∨ B w=true)
--
-- theorem tailInputs (C : Circuit) (n : ℕ) (B : ℕ → Bool) (j u x y : ℕ) (o : GateOp)
--     (gate : C.gates[j]?=some ⟨o,[x,y]⟩) :
--     arc C n B u (n+j) ↔ (u=x ∧ (o=.or ∨ B y=true)) ∨ (u=y ∧ (o=.or ∨ B x=true)) := by
--   constructor
--   · rintro ⟨k,q,w,eqn,loc,use⟩
--     have e : k=j := by omega
--     subst k
--     rw [gate] at loc
--     simp only [Option.some.injEq,Gate.mk.injEq,List.cons.injEq,and_true] at loc
--     rcases loc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
--     · exact Or.inl ⟨rfl,use⟩
--     · exact Or.inr ⟨rfl,use⟩
--   · rintro (⟨rfl,h⟩|⟨rfl,h⟩)
--     · exact ⟨j,o,y,rfl,Or.inl gate,h⟩
--     · exact ⟨j,o,x,rfl,Or.inr gate,h⟩
--
-- theorem pathTrace (C : Circuit) (n : ℕ) (B : ℕ → Bool) (seed : ℕ) (seedBound : seed<n) :
--     ∃ d : ℕ → Bool, (∀ i<n,d i=decide (i=seed)) ∧
--       (∀ j (g : Gate) x y,C.gates[j]?=some g → g.inputs=[x,y] →
--         (g.op=.and → d (n+j)=((B x && d y) || (d x && B y))) ∧
--         (g.op=.or → d (n+j)=(d x || d y))) ∧
--       ∀ u,d u=true ↔ ReflTransGen (arc C n B) seed u := by
--   classical
--   let path := ReflTransGen (arc C n B) seed
--   let d (u : ℕ) := decide (path u)
--   have sound (u : ℕ) : d u=true ↔ path u := by simp [d]
--   refine ⟨d,?_,?_,sound⟩
--   · intro i hi
--     rw [Bool.eq_iff_iff,sound,decide_eq_true_eq]
--     constructor
--     · intro h
--       rcases h.cases_tail with eqn|⟨v,_,j,op,w,eqn,_⟩
--       · exact eqn
--       · omega
--     · rintro rfl
--       exact ReflTransGen.refl
--   · rintro j ⟨o,ins⟩ x y hg hxy
--     change ins=[x,y] at hxy
--     subst ins
--     have step : path (n+j) ↔ (path x ∧ (o=.or ∨ B y=true)) ∨ (path y ∧ (o=.or ∨ B x=true)) := by
--       constructor
--       · intro h
--         rcases h.cases_tail with eqn|⟨u,old,last⟩
--         · omega
--         · rcases (tailInputs C n B j u x y o hg).mp last with ⟨rfl,ok⟩ | ⟨rfl,ok⟩
--           · exact Or.inl ⟨old,ok⟩
--           · exact Or.inr ⟨old,ok⟩
--       · rintro (⟨old,ok⟩|⟨old,ok⟩)
--         · exact old.tail ((tailInputs C n B j x x y o hg).mpr (Or.inl ⟨rfl,ok⟩))
--         · exact old.tail ((tailInputs C n B j y x y o hg).mpr (Or.inr ⟨rfl,ok⟩))
--     constructor
--     · rintro rfl
--       rw [Bool.eq_iff_iff,Bool.or_eq_true,Bool.and_eq_true,Bool.and_eq_true,sound,sound,sound,step]
--       simp only [reduceCtorEq,false_or]
--       tauto
--     · rintro rfl
--       rw [Bool.eq_iff_iff,Bool.or_eq_true,sound,sound,sound,step]
--       simp
--
-- theorem livePaths {α : Type} (R : α → α → Prop) (base pair : α → Bool)
--     (upBase : ∀ u v,R u v → base u=true → base v=true)
--     (upPair : ∀ u v,R u v → pair u=true → pair v=true)
--     {s t : α} (begins : pair s=true) (ends : base t=false) :
--     ReflTransGen R s t ↔
--       ReflTransGen (fun u v ↦ R u v ∧ base v=false ∧ pair u=true) s t := by
--   have fall (a b : α) (h : R a b) (off : base b=false) : base a=false := by
--     cases ha : base a with
--     | false => rfl
--     | true => exact (upBase a b h ha).symm.trans off
--   constructor
--   · intro route
--     have lift : ∀ {b : α}, ReflTransGen R s b → base b=false →
--         ReflTransGen (fun u v ↦ R u v ∧ base v=false ∧ pair u=true) s b ∧ pair b=true := by
--       intro b hb
--       induction hb with
--       | refl => intro _; exact ⟨.refl,begins⟩
--       | @tail b c _ step ih =>
--         intro off
--         obtain ⟨walk,hb⟩ := ih (fall b c step off)
--         exact ⟨walk.tail ⟨step,off,hb⟩,upPair b c step hb⟩
--     exact (lift route ends).1
--   · intro route
--     clear ends begins upBase upPair
--     induction route with
--     | refl => exact .refl
--     | tail _ step ih => exact ih.tail step.1
--
--
-- -- Basic fold lemmas from willakone, original project lemma L_meta_1490.
-- def stepWire (w : List Bool) (g : Gate) : List Bool :=
--   w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
--
-- lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
--     C.wires x = C.gates.foldl stepWire x := rfl
--
-- lemma foldl_length (gs : List Gate) (w : List Bool) :
--     (gs.foldl stepWire w).length = w.length + gs.length := by
--   induction gs generalizing w with
--   | nil => simp
--   | cons g gs ih =>
--     rw [List.foldl_cons, ih]
--     simp [stepWire]
--     omega
--
-- lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
--     (gs.foldl stepWire w).getD i false = w.getD i false := by
--   induction gs generalizing w with
--   | nil => rfl
--   | cons g gs ih =>
--     simp only [List.foldl_cons]
--     have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
--     rw [ih (stepWire w g) hlt]
--     simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
--
-- lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
--   simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
--
-- lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
--     (gs.foldl stepWire w).getD (w.length + j) false =
--       (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
--         if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
--   induction gs generalizing w j with
--   | nil => simp at hj
--   | cons g gs ih =>
--     rw [List.foldl_cons]
--     cases j with
--     | zero =>
--       have h1 : w.length < (stepWire w g).length := by simp [stepWire]
--       rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
--       simp only [List.getElem_cons_zero]
--       have h2 : (stepWire w g).getD w.length false =
--           g.op.eval (g.inputs.map fun i => w.getD i false) := by
--         simp [stepWire, List.getD_eq_getElem?_getD]
--       rw [h2]
--       congr 1
--       apply List.map_congr_left
--       intro i _
--       by_cases hi : i < w.length
--       · simp only [hi, ↓reduceIte]
--         rw [foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
--         simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
--       · simp only [hi, ↓reduceIte]; exact getD_ge w i (by omega)
--     | succ j =>
--       have hj' : j < gs.length := by simpa using hj
--       have key := ih (stepWire w g) j hj'
--       have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
--       rw [hl] at key
--       have e : w.length + (j + 1) = w.length + 1 + j := by omega
--       simp only [List.getElem_cons_succ]
--       rw [e]
--       exact key
--
--
-- abbrev WV (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) := PEqualNP.BlindGate.wireValue C n x w
-- abbrev Normal (C : Circuit) (n : ℕ) := ∀ j (g : Gate),C.gates[j]?=some g →
--   (g.op=.and ∨ g.op=.or) ∧ ∃ a b : ℕ,g.inputs=[a,b] ∧ a≠b ∧ a<n+j ∧ b<n+j
--
-- theorem rawValue {C : Circuit} {n : ℕ} (x : Fin n → Bool) (i : Fin n) : WV C n x i.val=x i := by
--   unfold WV PEqualNP.BlindGate.wireValue
--   rw [wires_eq_foldl,foldl_getD_lt _ _ _ (by simp)]
--   simp [List.getD_eq_getElem?_getD]
--
-- theorem gateValue (C : Circuit) (n : ℕ) (x : Fin n → Bool) {j a b : ℕ} {o : GateOp}
--     (g : C.gates[j]?=some ⟨o,[a,b]⟩) (ha : a<n+j) (hb : b<n+j) :
--     WV C n x (n+j)=o.eval [WV C n x a,WV C n x b] := by
--   obtain ⟨hj,eqn⟩ := List.getElem?_eq_some_iff.mp g
--   have h := foldl_getD_gate C.gates (List.ofFn x) j hj
--   rw [List.length_ofFn,eqn] at h
--   simpa [WV,PEqualNP.BlindGate.wireValue,wires_eq_foldl,ha,hb] using h
--
-- theorem wireMono (C : Circuit) (n : ℕ) (normal : Normal C n) (x y : Fin n → Bool)
--     (le : ∀ i,x i=true → y i=true) (w : ℕ) : WV C n x w=true → WV C n y w=true := by
--   induction w using Nat.strong_induction_on with
--   | _ w ih =>
--     by_cases lo : w<n
--     · simpa only [show WV C n x w=x ⟨w,lo⟩ from rawValue x ⟨w,lo⟩,
--         show WV C n y w=y ⟨w,lo⟩ from rawValue y ⟨w,lo⟩] using le ⟨w,lo⟩
--     · by_cases tooLarge : n+C.gates.length≤w
--       · have off : WV C n x w=false := by
--           unfold WV PEqualNP.BlindGate.wireValue
--           apply getD_ge
--           simpa [wires_eq_foldl,foldl_length] using tooLarge
--         simp [off]
--       · let j := w-n
--         have hj : j<C.gates.length := by dsimp [j];omega
--         have idx : n+j=w := by dsimp [j];omega
--         let g := C.gates[j]
--         have get : C.gates[j]?=some g := List.getElem?_eq_getElem hj
--         obtain ⟨mode,a,b,inputs,_,ha,hb⟩ := normal j g get
--         have data : C.gates[j]?=some ⟨g.op,[a,b]⟩ := by rw [get,←inputs]
--         have ax := ih a (by omega)
--         have byy := ih b (by omega)
--         rw [←idx,gateValue C n x data ha hb,gateValue C n y data ha hb]
--         rcases mode with h|h
--         · rw [h]; simp only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,Bool.and_eq_true]
--           exact fun h ↦ ⟨ax h.1,byy h.2⟩
--         · rw [h]; simp only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_true]
--           exact fun h ↦ h.imp ax byy
--
-- theorem edgeUp (C : Circuit) (n : ℕ) (normal : Normal C n) (x y : Fin n → Bool)
--     (le : ∀ i,x i=true → y i=true) {u v : ℕ} (step : arc C n (WV C n x) u v) :
--     WV C n y u=true → WV C n y v=true := by
--   obtain ⟨j,o,t,rfl,located,enabled⟩ := step
--   have compare := wireMono C n normal x y le t
--   have use : o=.or ∨ WV C n y t=true := enabled.imp_right compare
--   rcases located with found|found
--   · obtain ⟨mode,a,b,parts,_,ha,hb⟩ := normal j _ found
--     simp only [List.cons.injEq,and_true] at parts
--     obtain ⟨rfl,rfl⟩ := parts
--     rw [gateValue C n y found ha hb]
--     rcases mode with eqn|eqn
--     · change o=.and at eqn
--       subst o
--       simpa [GateOp.eval] using (fun hu : WV C n y u=true ↦ And.intro hu (use.resolve_left (by intro bad;cases bad)))
--     · change o=.or at eqn
--       subst o
--       simp [GateOp.eval]
--       exact Or.inl
--   · obtain ⟨mode,a,b,parts,_,ha,hb⟩ := normal j _ found
--     simp only [List.cons.injEq,and_true] at parts
--     obtain ⟨rfl,rfl⟩ := parts
--     rw [gateValue C n y found ha hb]
--     rcases mode with eqn|eqn
--     · change o=.and at eqn
--       subst o
--       simpa [GateOp.eval] using (fun hu : WV C n y u=true ↦ And.intro (use.resolve_left (by intro bad;cases bad)) hu)
--     · change o=.or at eqn
--       subst o
--       simp [GateOp.eval]
--       exact Or.inr
--
--
-- theorem restricted (n : ℕ) (C : Circuit) (norm : Normal C n) (src seed : Fin n) :
--     let x := fun i ↦ decide (i=src)
--     let y := PEqualNP.EdgeOwnership.pairInput src seed
--     let B := WV C n x
--     let Y := WV C n y
--     let R := arc C n B
--     C.eval (List.ofFn x)=false →
--     (ReflTransGen R seed.val C.output ↔
--      ReflTransGen (fun u v ↦ R u v ∧ B v=false ∧ Y u=true) seed.val C.output) := by
--   dsimp only
--   intro off
--   let x (i : Fin n) := decide (i=src)
--   let y := PEqualNP.EdgeOwnership.pairInput src seed
--   have included : ∀ i,x i=true → y i=true := by
--     intro i h
--     have eqn : i=src := of_decide_eq_true h
--     subst i
--     simp [y,PEqualNP.EdgeOwnership.pairInput]
--   have seedOn : WV C n y seed.val=true := by rw [rawValue];simp [y,PEqualNP.EdgeOwnership.pairInput]
--   exact livePaths (arc C n (WV C n x)) (WV C n x) (WV C n y)
--     (fun _ _ step ↦ edgeUp C n norm x x (fun _ h ↦ h) step)
--     (fun _ _ step ↦ edgeUp C n norm x y included step) seedOn off
--
-- theorem anyTrace (C : Circuit) (n seed : ℕ) (B d : ℕ → Bool) (norm : Normal C n)
--     (start : d seed=true)
--     (step : ∀ j (g : Gate) x y,C.gates[j]?=some g → g.inputs=[x,y] →
--       (g.op=.and → d (n+j)=((B x && d y) || (d x && B y))) ∧
--       (g.op=.or → d (n+j)=(d x || d y))) {out : ℕ}
--     (route : ReflTransGen (arc C n B) seed out) : d out=true := by
--   induction route with
--   | refl => exact start
--   | @tail u v _ edge atU =>
--     obtain ⟨j,o,t,rfl,loc,enabled⟩ := edge
--     rcases loc with found | found
--     · have rule := step j _ u t found rfl
--       obtain mode := (norm j _ found).1
--       change o=.and ∨ o=.or at mode
--       rcases mode with rfl | rfl
--       · have other := enabled.resolve_left (by intro h;cases h)
--         rw [rule.1 rfl]
--         simp [atU,other]
--       · rw [rule.2 rfl];simp [atU]
--     · have rule := step j _ t u found rfl
--       obtain mode := (norm j _ found).1
--       change o=.and ∨ o=.or at mode
--       rcases mode with rfl | rfl
--       · have other := enabled.resolve_left (by intro h;cases h)
--         rw [rule.1 rfl]
--         simp [atU,other]
--       · rw [rule.2 rfl];simp [atU]
--
--
-- theorem boundary (n : ℕ) (C : Circuit) (norm : Normal C n) (f : (Fin n → Bool) → Prop)
--     (tested : ∀ x : Fin n → Bool,(Minimal f x ∨ Maximal (fun y ↦ ¬f y) x) →
--       (C.eval (List.ofFn x)=true ↔ f x)) : ∀ x,C.eval (List.ofFn x)=true ↔ f x := by
--   have up (x y : Fin n → Bool) (le : x≤y) : C.eval (List.ofFn x)=true → C.eval (List.ofFn y)=true := by
--     apply wireMono C n norm x y
--     intro i hi
--     have os := le i
--     rw [hi] at os
--     exact Bool.eq_true_of_true_le os
--   intro x
--   constructor
--   · intro hx
--     by_contra no
--     obtain ⟨y,xy,hy⟩ := Finite.exists_le_maximal (p := fun z ↦ ¬f z) no
--     exact hy.1 ((tested y (Or.inr hy)).mp (up x y xy hx))
--   · intro hx
--     obtain ⟨y,yx,hy⟩ := @Finite.exists_le_maximal (OrderDual (Fin n → Bool)) _ _ f x hx
--     exact up y x yx ((tested y (Or.inl hy)).mpr hy.1)
--
--
-- end Eric.FanoRouting

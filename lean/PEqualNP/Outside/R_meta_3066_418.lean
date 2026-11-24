import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3066_418
    (base : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (readers : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →       (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →         x1.size ≤ (15 : ℕ) →           ∀ x6 ∈ [(4 : ℕ), (6 : ℕ)],             ∃! x8 : Fin (List.drop (1 : ℕ) x1.gates).length,               have x9 : PEqualNP.CircuitLowerBounds.Gate := (List.drop (1 : ℕ) x1.gates).get x8;               x9.inputs[(0 : ℕ)]? = Option.some x6 ∨ x9.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x6 ∈ x9.inputs)
    (narrow : let rd (v : ℕ) (g : Gate) : Prop := g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs
      ∀ (gs : List Gate) (a : Fin 12), gs.length = 13 → FanInTwo ⟨gs,0⟩ →
      (∀ g ∈ gs, ∀ i ∈ g.inputs, i ≤ 23) →
      (∀ v ∈ ([4,6] : List ℕ), ∀ i j : Fin gs.length,
        rd v (gs.get i) → rd v (gs.get j) → i = j) →
      ∃ x : Fin 9 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 4 || x 6])
        (w.getD (10+a.val) false || w.getD 22 false) ≠ (fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) x) : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  classical
  let target : (Fin 9 → Bool) → Bool := fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))
  let seed := fun x : Fin 9 → Bool => List.ofFn x ++ [x 4 || x 6]
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) := gs.foldl step w
  let first : Gate := ⟨.or,[4,6]⟩
  let build (gs : List Gate) (ps : List ℕ) : Circuit := ⟨first :: (gs ++ [⟨.or,ps⟩]),10+gs.length⟩
  have ev0 : GateOp.or.eval [] = false := rfl
  have ev1 (b : Bool) : GateOp.or.eval [b] = b := by cases b <;> rfl
  have ev2 (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
  have extend (gs : List Gate) (w : List Bool) :
      ∃ U : List Bool, run gs w = w ++ U ∧ U.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp [run],rfl⟩
    | cons g gs ih =>
      obtain ⟨U,he,hl⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: U,?_,by simp [hl]⟩
      change run gs (step w g) = _
      rw [he]
      simp only [step,List.append_assoc,List.singleton_append]
  have runLength (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    obtain ⟨U,he,hl⟩ := extend gs w
    rw [he,List.length_append,hl]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    obtain ⟨U,he,_⟩ := extend gs w
    rw [he]
    exact List.getD_append w U false i hi
  have init (x : Fin 9 → Bool) : step (List.ofFn x) first = seed x := by
    change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 4 false,(List.ofFn x).getD 6 false]] = _
    rw [ev2]
    rfl
  have buildFan (gs : List Gate) (ps : List ℕ) (hf : FanInTwo ⟨gs,0⟩) (hp : ps.length ≤ 2) :
      FanInTwo (build gs ps) := by
    intro g hg
    change g ∈ first :: (gs ++ [Gate.mk GateOp.or ps]) at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨by simp [first],by decide⟩
    · rcases List.mem_append.mp hg with hg | hg
      · exact hf g hg
      · obtain rfl := List.mem_singleton.mp hg
        exact ⟨by simp,hp⟩
  have buildSize (gs : List Gate) (ps : List ℕ) : (build gs ps).size = gs.length + 2 := by
    change (first :: (gs ++ [Gate.mk GateOp.or ps])).length = gs.length+2
    simp only [List.length_cons,List.length_append,List.length_singleton,List.length_nil]
  have buildFirst (gs : List Gate) (ps : List ℕ) (x : Fin 9 → Bool) :
      ((build gs ps).wires (List.ofFn x)).getD 9 false = (x 4 || x 6) := by
    change (run (gs ++ [Gate.mk GateOp.or ps]) (step (List.ofFn x) first)).getD 9 false = _
    rw [init,keep _ _ _ (by simp [seed])]
    change (List.ofFn x ++ [x 4 || x 6]).getD 9 false = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have buildEval (gs : List Gate) (ps : List ℕ) (x : Fin 9 → Bool) :
      (build gs ps).eval (List.ofFn x) =
      GateOp.or.eval (ps.map fun i => (run gs (seed x)).getD i false) := by
    change ((gs ++ [Gate.mk GateOp.or ps]).foldl step (step (List.ofFn x) first)).getD (10+gs.length) false = _
    rw [init,List.foldl_append]
    change (run gs (seed x) ++ [GateOp.or.eval (ps.map fun i => (run gs (seed x)).getD i false)]).getD (10+gs.length) false = _
    have len : (run gs (seed x)).length = 10+gs.length := by rw [runLength]; simp [seed]
    rw [List.getD_append_right _ _ _ _ (by omega),len]
    simp
  intro gs pins short fan bounded shortPins
  by_contra hno
  have hno : ∀ x : Fin 9 → Bool,
      GateOp.or.eval (pins.map fun i => (run gs (seed x)).getD i.val false) = target x := by
    intro x
    by_contra h
    exact hno ⟨x,h⟩
  let C := build gs (pins.map Fin.val)
  have fanC : FanInTwo C := buildFan gs _ fan (by simpa using shortPins)
  have worksC : circuitFun 9 C = target := by
    funext x
    exact (buildEval gs _ x).trans (by simpa only [List.map_map,Function.comp_def] using hno x)
  have lowerC := base C fanC worksC
  have sizeC := buildSize gs (pins.map Fin.val)
  have len : gs.length = 13 := by change 15 ≤ C.size at lowerC; dsimp only [C] at lowerC; omega
  have cannotTap (out : ℕ) (he : ∀ x : Fin 9 → Bool, (run gs (seed x)).getD out false = target x) : False := by
    let D : Circuit := ⟨first::gs,out⟩
    have hf : FanInTwo D := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by simp [first],by decide⟩
      · exact fan g hg
    have hd : circuitFun 9 D = target := by
      funext x
      change (run gs (step (List.ofFn x) first)).getD out false = target x
      rw [init]
      exact he x
    have h := base D hf hd
    change 15 ≤ gs.length+1 at h
    omega
  have plen : pins.length = 2 := by
    have le := shortPins
    cases pins with
    | nil =>
      have h := hno (fun _ => true)
      change false = target (fun _ => true) at h
      exact False.elim ((by decide +kernel : target (fun _ => true) ≠ false) h.symm)
    | cons a ps =>
      cases ps with
      | nil =>
        apply False.elim
        apply cannotTap a.val
        intro x
        have h := hno x
        change GateOp.or.eval [(run gs (seed x)).getD a.val false] = target x at h
        rwa [ev1] at h
      | cons b ps => simp only [List.length_cons] at le ⊢; omega
  obtain ⟨a,b,hpins⟩ := List.length_eq_two.mp plen
  subst pins
  have final (x : Fin 9 → Bool) :
      ((run gs (seed x)).getD a.val false || (run gs (seed x)).getD b.val false) = target x := by
    have h := hno x
    change GateOp.or.eval [_,_] = target x at h
    rwa [ev2] at h
  have diff : a ≠ b := by
    rintro rfl
    apply cannotTap a.val
    intro x
    have h := final x
    simpa only [Bool.or_self] using h
  have nw (x : Fin 9 → Bool) : (run gs (seed x)).length = 23 := by rw [runLength]; simp [seed,len]
  have z23 (x : Fin 9 → Bool) : (run gs (seed x)).getD 23 false = false :=
    List.getD_eq_default _ _ (by rw [nw])
  have lt : a.val < 23 ∧ b.val < 23 := by
    constructor
    · by_contra h
      have ae : a.val = 23 := by have := a.isLt; omega
      apply cannotTap b.val
      intro x
      simpa only [ae,z23,Bool.false_or] using final x
    · by_contra h
      have be : b.val = 23 := by have := b.isLt; omega
      apply cannotTap a.val
      intro x
      simpa only [be,z23,Bool.or_false] using final x
  have noInput (p : Fin 24) (hp : p = a ∨ p = b) (small : p.val < 10) : False := by
    have wit : ∀ i : Fin 10, ∃ x : Fin 9 → Bool, (seed x).getD i.val false = true ∧ target x = false := by
      decide +kernel
    obtain ⟨x,hx,hf⟩ := wit ⟨p.val,small⟩
    have read : (run gs (seed x)).getD p.val false = true := (keep gs (seed x) p.val (by simp [seed]; omega)).trans hx
    rcases hp with rfl | rfl
    · have h := final x; rw [read,hf] at h; simp at h
    · have h := final x; rw [read,hf] at h; simp at h
  have ge : 10 ≤ a.val ∧ 10 ≤ b.val := by
    constructor
    · by_contra h; exact noInput a (Or.inl rfl) (by omega)
    · by_contra h; exact noInput b (Or.inr rfl) (by omega)
  have last : a.val = 22 ∨ b.val = 22 := by
    by_contra hn
    have ha : a.val < 22 := by omega
    have hb : b.val < 22 := by omega
    let pre := gs.take 12
    have lp : pre.length = 12 := by simp [pre,List.length_take,len]
    have hf : FanInTwo ⟨pre,0⟩ := fun g hg => fan g (List.mem_of_mem_take hg)
    have same (x : Fin 9 → Bool) (i : ℕ) (hi : i < 22) :
        (run pre (seed x)).getD i false = (run gs (seed x)).getD i false := by
      have hlen : (run pre (seed x)).length = 22 := by rw [runLength,lp]; simp [seed]
      conv_rhs => rw [←List.take_append_drop 12 gs]
      rw [show run (gs.take 12 ++ gs.drop 12) (seed x) = run (gs.drop 12) (run pre (seed x)) by
        simp only [pre,run,List.foldl_append]]
      exact (keep _ _ i (by omega)).symm
    have hc : circuitFun 9 (build pre [a.val,b.val]) = target := by
      funext x
      rw [show circuitFun 9 (build pre [a.val,b.val]) x = (build pre [a.val,b.val]).eval (List.ofFn x) from rfl,buildEval]
      change GateOp.or.eval [_,_] = target x
      rw [ev2]
      change ((run pre (seed x)).getD a.val false || (run pre (seed x)).getD b.val false) = target x
      rw [same x a.val ha,same x b.val hb]
      exact final x
    have h := base (build pre [a.val,b.val]) (buildFan pre _ hf (by simp)) hc
    rw [buildSize,lp] at h
    omega
  let rd (v : ℕ) (g : Gate) : Prop := g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs
  have reads : ∀ v ∈ ([4,6] : List ℕ), ∀ i j : Fin gs.length,
      rd v (gs.get i) → rd v (gs.get j) → i = j := by
    intro v hv i j hi hj
    obtain ⟨k,hk,unique⟩ := readers C fanC (buildFirst gs _)
      worksC (by rw [show C.size = gs.length+2 from sizeC,len]) v hv
    let ii : Fin (C.gates.drop 1).length := ⟨i.val,by simp [C,build]⟩
    let jj : Fin (C.gates.drop 1).length := ⟨j.val,by simp [C,build]⟩
    have ei : (C.gates.drop 1).get ii = gs.get i := by simp [ii,C,build,List.get_eq_getElem,List.getElem_append_left]
    have ej : (C.gates.drop 1).get jj = gs.get j := by simp [jj,C,build,List.get_eq_getElem,List.getElem_append_left]
    have ui := unique ii (by change rd v ((C.gates.drop 1).get ii); rw [ei]; exact hi)
    have uj := unique jj (by change rd v ((C.gates.drop 1).get jj); rw [ej]; exact hj)
    have eqval : ii.val = jj.val := congrArg (fun z : Fin (C.gates.drop 1).length => z.val) (ui.trans uj.symm)
    exact Fin.ext eqval
  rcases last with ha | hb
  · have hb : b.val < 22 := by have ne : a.val ≠ b.val := fun h => diff (Fin.ext h); omega
    let p : Fin 12 := ⟨b.val-10,by omega⟩
    obtain ⟨x,hx⟩ := narrow gs p len fan bounded reads
    have add : 10+p.val = b.val := by dsimp [p]; omega
    change ((run gs (seed x)).getD (10+p.val) false || (run gs (seed x)).getD 22 false) ≠ target x at hx
    rw [add] at hx
    have h := final x
    rw [ha] at h
    exact hx ((Bool.or_comm _ _).trans h)
  · have ha : a.val < 22 := by have ne : a.val ≠ b.val := fun h => diff (Fin.ext h); omega
    let p : Fin 12 := ⟨a.val-10,by omega⟩
    obtain ⟨x,hx⟩ := narrow gs p len fan bounded reads
    have add : 10+p.val = a.val := by dsimp [p]; omega
    change ((run gs (seed x)).getD (10+p.val) false || (run gs (seed x)).getD 22 false) ≠ target x at hx
    rw [add] at hx
    have h := final x
    rw [hb] at h
    exact hx h

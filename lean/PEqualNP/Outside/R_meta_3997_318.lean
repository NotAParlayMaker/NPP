import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_3997_318
  (companion : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit), IsMinimalCircuit n C →
    (∀ x, circuitFun n C x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
    (∀ v, (G.neighborSet v).ncard = 3) →
    (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
    ∀ (v : Fin n) (g : Gate),
      C.gates.filter (fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains v.val) =
        [g] → (g.op = .and ∨ g.op = .or) →
    ∃ D : Circuit, IsMinimalCircuit n D ∧ circuitFun n D = circuitFun n C ∧ D.size = C.size ∧
      ∃ (z : Fin n) (L R : List Gate) (k : Gate) (w : ℕ),
        D.gates = L ++ k :: R ∧ (∀ a ∈ L ++ R, z.val ∉ a.inputs) ∧ n ≤ w ∧ w < n + L.length ∧
        (k.inputs = [z.val,w] ∨ k.inputs = [w,z.val]) ∧ (k.op = .and ∨ k.op = .or))
  (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit), let f := circuitFun n C
    30 ≤ n → Even n → G.Colorable 2 → (∀ v, (G.neighborSet v).ncard = 3) → (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) → (∀ x, f x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
    C.size + 1 < 2 * n → IsMinimalCircuit n C → (∃ (v : Fin n) (L R : List Gate) (g : Gate) (w : ℕ),
      C.gates = L ++ g :: R ∧ (∀ a ∈ L ++ R, v.val ∉ a.inputs) ∧ n ≤ w ∧ w < n + L.length ∧
        (g.inputs = [v.val,w] ∨ g.inputs = [w,v.val]) ∧ (g.op = .and ∨ g.op = .or)) →
    ∃ (u v : Fin n), u ≠ v ∧ ¬ G.Adj u v ∧ ∃ t, t+8 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update (Function.update x u false) v false)) t) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (30 : ℕ) ≤ x1 → Even x1 → x2.Colorable (2 : ℕ) → (∀ (x7 : Fin x1), (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x3 x10 = Bool.true ↔ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), x11 + (1 : ℕ) < (2 : ℕ) * x1 → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x11 → ∃ (x14 : Fin x1) (x15 : Fin x1), x14 ≠ x15 ∧ ¬x2.Adj x14 x15 ∧ ∃ (x16 : ℕ), x16 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x3 (Function.update (Function.update x17 x14 Bool.false) x15 Bool.false)) x16 := by
  classical
  intro n G f hn heven hcolor hdeg hgirth hedge hf s hsmall hs
  let portRD (g : Gate) : List ℕ := List.take (bif g.op.eval [false] then 1 else 2) g.inputs
  have evAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have evNot (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have evSize (K : Circuit) : K.size = K.gates.length := rfl
  have evCirc (K : Circuit) (w : List Bool) : K.eval w = (K.wires w).getD K.output false := rfl
  have evGraph {m : ℕ} (K : SimpleGraph (Fin m)) [DecidableRel K.Adj] (M : Finset (Fin m))
      (x : Fin m → Bool) : NestedCover.graphFun K M x =
        (decide (∃ a ∈ M, x a = true) || decide (∃ a b, K.Adj a b ∧ x a = true ∧ x b = true)) := rfl
  let F (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

  let OkGate (g : Gate) : Prop :=
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

  have ok_of_fan (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) (g : Gate) (hg : g ∈ C.gates) :
      OkGate g := by
    obtain ⟨h1, h2⟩ := h g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩

  have evalRd (g : Gate) (hg : OkGate g) (f f' : ℕ → Bool) (h : ∀ i ∈ portRD g, f i = f' i) :
      g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
    obtain ⟨hop, hl⟩ := hg
    rcases hop with hop | hop | hop
    · have : portRD g = g.inputs := by
        simp only [portRD, hop, evAnd,evOr,evNot]
        exact List.take_of_length_le (by simpa using hl)
      rw [this] at h
      rw [List.map_congr_left h]
    · have : portRD g = g.inputs := by
        simp only [portRD, hop, evAnd,evOr,evNot]
        exact List.take_of_length_le (by simpa using hl)
      rw [this] at h
      rw [List.map_congr_left h]
    · rw [hop]
      simp only [portRD, hop, evAnd,evOr,evNot] at h
      cases hin : g.inputs with
      | nil => simp
      | cons a t =>
        rw [hin] at h
        simp only [List.map_cons]
        rw [h a (by simp)]
        simp [evAnd,evOr,evNot]

  have fold_len (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [F, List.length_append, List.length_cons, List.length_nil]
      omega

  let dl (w i : ℕ) : ℕ := if i < w then i else i - 1

  let rg (w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (dl w)⟩

  have F_rg (Q Q' : List Bool) (w : ℕ) (g : Gate) (hg : OkGate g)
      (h : ∀ i ∈ portRD g, Q'.getD (dl w i) false = Q.getD i false) :
      (rg w g).op.eval ((rg w g).inputs.map fun i => Q'.getD i false)
        = g.op.eval (g.inputs.map fun i => Q.getD i false) := by
    simp only [rg, List.map_map]
    exact evalRd g hg _ _ h

  have stageA (w : ℕ) (A : List Gate) (hA : ∀ g ∈ A, OkGate g ∧ w ∉ portRD g) :
      ∀ Q : List Bool, Q.length + A.length ≤ w → (A.map (rg w)).foldl F Q = A.foldl F Q := by
    induction A with
    | nil => intro Q _; rfl
    | cons g A ih =>
      intro Q hQ
      simp only [List.map_cons, List.foldl_cons]
      have hg := hA g (by simp)
      have hF : F Q (rg w g) = F Q g := by
        unfold F
        rw [F_rg Q Q w g hg.1]
        intro i hi
        have hne : i ≠ w := fun h => hg.2 (h ▸ hi)
        simp only [List.length_cons] at hQ
        by_cases hiw : i < w
        · simp [dl, hiw]
        · simp only [dl, hiw, ite_false]
          rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      rw [hF]
      apply ih (fun g' hg' => hA g' (by simp [hg']))
      simp only [F, List.length_append, List.length_cons, List.length_nil, List.length_cons] at hQ ⊢
      omega

  have key (P M : List Bool) (v : Bool) (w : ℕ) (hP : P.length = w) (i : ℕ) (hi : i ≠ w) :
      (P ++ M).getD (dl w i) false = (P ++ v :: M).getD i false := by
    by_cases hiw : i < w
    · simp only [dl, hiw, ite_true]
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    · simp only [dl, hiw, ite_false]
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hP]
      obtain ⟨k, hk⟩ : ∃ k, i - w = k + 1 := ⟨i - w - 1, by omega⟩
      rw [hk, List.getD_cons_succ]
      congr 1
      omega

  have stageB (w : ℕ) (P : List Bool) (v : Bool) (hP : P.length = w) (B : List Gate)
      (hB : ∀ g ∈ B, OkGate g ∧ w ∉ portRD g) :
      ∀ M : List Bool, ∀ i, i ≠ w →
        ((B.map (rg w)).foldl F (P ++ M)).getD (dl w i) false = (B.foldl F (P ++ v :: M)).getD i false := by
    induction B with
    | nil => intro M i hi; exact key P M v w hP i hi
    | cons g B ih =>
      intro M i hi
      simp only [List.map_cons, List.foldl_cons]
      have hg := hB g (by simp)
      have h1 : F (P ++ M) (rg w g) = P ++ (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
        unfold F
        rw [F_rg (P ++ v :: M) (P ++ M) w g hg.1, List.append_assoc]
        intro i hi
        exact key P M v w hP i (fun h => hg.2 (h ▸ hi))
      have h2 : F (P ++ v :: M) g = P ++ v :: (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
        unfold F
        simp
      rw [h1, h2]
      exact ih (fun g' hg' => hB g' (by simp [hg'])) _ i hi

  have del_getD (n j : ℕ) (gs : List Gate) (hj : j < gs.length)
      (hok : ∀ g ∈ gs, OkGate g) (hw : ∀ g ∈ gs, n + j ∉ portRD g) (x : List Bool) (hx : x.length = n)
      (i : ℕ) (hi : i ≠ n + j) :
      (((gs.eraseIdx j).map (rg (n + j))).foldl F x).getD (dl (n + j) i) false
        = (gs.foldl F x).getD i false := by
    have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
      conv_lhs => rw [← List.take_append_drop j gs]
      rw [List.drop_eq_getElem_cons hj]
    have herase : gs.eraseIdx j = gs.take j ++ gs.drop (j + 1) := List.eraseIdx_eq_take_drop_succ gs j
    have hAll : ∀ g ∈ gs, OkGate g ∧ n + j ∉ portRD g := fun g hg => ⟨hok g hg, hw g hg⟩
    rw [herase, List.map_append, List.foldl_append]
    conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [stageA (n + j) (gs.take j) (fun g hg => hAll g (List.mem_of_mem_take hg)) x
      (by rw [hx, List.length_take]; omega)]
    have hP : (List.foldl F x (gs.take j)).length = n + j := by
      rw [fold_len, hx, List.length_take]; omega
    have := stageB (n + j) (List.foldl F x (gs.take j))
      (gs[j].op.eval (gs[j].inputs.map fun i => (List.foldl F x (gs.take j)).getD i false)) hP
      (gs.drop (j + 1)) (fun g hg => hAll g (List.mem_of_mem_drop hg)) [] i hi
    simpa [F] using this

  have indep (k : ℕ) (gs : List Gate) (hok : ∀ g ∈ gs, OkGate g) (hk : ∀ g ∈ gs, k ∉ portRD g) :
      ∀ Q Q' : List Bool, Q.length = Q'.length → (∀ i, i ≠ k → Q.getD i false = Q'.getD i false) →
        ∀ i, i ≠ k → (gs.foldl F Q).getD i false = (gs.foldl F Q').getD i false := by
    induction gs with
    | nil => intro Q Q' _ h i hi; exact h i hi
    | cons g gs ih =>
      intro Q Q' hl h i hi
      simp only [List.foldl_cons]
      apply ih (fun g' hg' => hok g' (by simp [hg'])) (fun g' hg' => hk g' (by simp [hg']))
      · simp [F, hl]
      · intro i' hi'
        have hv : g.op.eval (g.inputs.map fun i => Q.getD i false)
            = g.op.eval (g.inputs.map fun i => Q'.getD i false) := by
          apply evalRd g (hok g (by simp))
          intro j hj
          exact h j (fun e => hk g (by simp) (e ▸ hj))
        unfold F
        rw [hv]
        by_cases hlt : i' < Q.length
        · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
          exact h i' hi'
        · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
      · exact hi

  have count (gs : List Gate) (hok : ∀ g ∈ gs, OkGate g) :
      (gs.flatMap portRD).length + (gs.filter fun g => g.op.eval [false]).length ≤ 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      have ih' := ih (fun g' hg' => hok g' (by simp [hg']))
      have hg : (portRD g).length + (if g.op.eval [false] = true then 1 else 0) ≤ 2 := by
        rcases (hok g (by simp)).1 with h | h | h <;> simp [portRD, h, evAnd,evOr,evNot]
      rw [List.flatMap_cons, List.filter_cons, List.length_append]
      split_ifs at hg ⊢ with hc
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        omega



  have countBound (xs : List ℕ) (S : Finset ℕ) :
      ∑ i ∈ S, xs.count i ≤ xs.length := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
      by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega

  have readcount (gs : List Gate) (a : ℕ) :
      (gs.filter (fun g => (portRD g).contains a)).length ≤ (gs.flatMap portRD).count a := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.filter_cons,List.flatMap_cons,List.count_append]
      split
      next h =>
        have := List.count_pos_iff.mpr (List.contains_iff_mem.mp h)
        simp only [List.length_cons]
        omega
      next => omega




  have portLemma : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x8 → x5.size ≤ x8) → x4.card + ∑ x9 ∈ x4ᶜ, (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x10.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x10.inputs).contains ↑x9) x5.gates).length + (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => x9.op.eval [Bool.false]) x5.gates).length ≤ x5.size + (1 : ℕ) := by
    classical
    intro n G inst A C fan computes minimal
    let xs := C.output :: C.gates.flatMap portRD
    let cnt := fun i => xs.count i
    have hok := ok_of_fan C fan
    have marked (a : Fin n) (ha : a ∈ A) : 1 ≤ cnt a := by
      apply List.count_pos_iff.mpr
      by_contra h
      have hout : C.output ≠ a.val := by intro he; exact h (by simp [xs,he])
      have noRead : ∀ g ∈ C.gates, a.val ∉ portRD g :=
        fun g hg hi => h (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g,hg,hi⟩))
      let z : Fin n → Bool := fun _ => false
      let y : Fin n → Bool := fun i => decide (i = a)
      have hb : circuitFun n C z = circuitFun n C y := by
        apply indep a.val C.gates hok noRead _ _ (by simp) _ C.output hout
        intro i hi
        by_cases hin : i < n
        · simp [List.getD_eq_getElem?_getD,hin,z,y,show (⟨i,hin⟩ : Fin n) ≠ a from fun he => hi (congrArg Fin.val he)]
        · simp [List.getD_eq_getElem?_getD,hin]
      rw [computes] at hb
      have hzy : (NestedCover.graphFun G A z) = false := by rw [evGraph]; simp [z]
      have hyy : (NestedCover.graphFun G A y) = true := by
        rw [evGraph]
        simp only [Bool.or_eq_true,decide_eq_true_eq]
        exact Or.inl ⟨a,ha,by simp [y]⟩
      exact Bool.false_ne_true (hzy.symm.trans (hb.trans hyy))
    have intern (j : ℕ) (hj : j ∈ Finset.range C.gates.length) : 1 ≤ cnt (n+j) := by
      apply List.count_pos_iff.mpr
      by_contra h
      have hout : C.output ≠ n+j := by intro he; exact h (by simp [xs,he])
      have noRead : ∀ g ∈ C.gates, n+j ∉ portRD g :=
        fun g hg hi => h (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g,hg,hi⟩))
      let K : Circuit := ⟨(C.gates.eraseIdx j).map (rg (n+j)), dl (n+j) C.output⟩
      have hj' := Finset.mem_range.mp hj
      have hfun : circuitFun n K = circuitFun n C := by
        funext x
        exact del_getD n j C.gates hj' hok noRead (List.ofFn x) (by simp) C.output hout
      have hfan : FanInTwo K := by
        intro g hg
        obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
        simpa [rg] using fan g0 (List.mem_of_mem_eraseIdx hg0)
      have b := minimal K.size ⟨K,hfan,le_rfl,fun x => congrFun (hfun.trans computes) x⟩
      simp only [K,evSize,List.length_map,List.length_eraseIdx_of_lt hj'] at b
      omega
    have primary (a : Fin n) (_ : a ∈ Aᶜ) :
        (C.gates.filter (fun g => (portRD g).contains a.val)).length ≤ cnt a := by
      have h := readcount C.gates a.val
      simp only [cnt,xs,List.count_cons]
      omega
    have hA := Finset.sum_le_sum marked
    have hP := Finset.sum_le_sum primary
    have hI := Finset.sum_le_sum intern
    simp only [Finset.sum_const,smul_eq_mul,mul_one,Finset.card_range] at hA hI
    have hin := A.sum_add_sum_compl (fun a => cnt a.val)
    rw [Fin.sum_univ_eq_sum_range] at hin
    have ht := countBound xs (Finset.range (n+C.gates.length))
    change ∑ i ∈ Finset.range (n+C.gates.length), cnt i ≤ xs.length at ht
    rw [Finset.sum_range_add] at ht
    have hb := count C.gates hok
    simp only [xs,List.length_cons] at ht
    change A.card + (∑ a ∈ Aᶜ, (C.gates.filter (fun g => (portRD g).contains a.val)).length) + _ ≤ C.gates.length+1
    omega


  let readers (C : Circuit) (v : ℕ) : List Gate :=
    C.gates.filter (fun g => (portRD g).contains v)

  let isNot (g : Gate) : Bool := g.op.eval [false]

  have keep_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl F w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · exact List.getD_append _ _ _ _ hi
      · simp [F]; omega

  have singleton_rejects {n : ℕ} {G : SimpleGraph (Fin n)} {f : (Fin n → Bool) → Bool}
      (hf : ∀ x, f x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
      (v : Fin n) : f (fun i => decide (i = v)) = false := by
    rw [Bool.eq_false_iff]
    intro hz
    obtain ⟨a,b,ha,hb,hc⟩ := (hf _).mp hz
    exact ha.ne ((of_decide_eq_true hb).trans (of_decide_eq_true hc).symm)

  have reader_ne_empty {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
      (hC : FanInTwo C)
      (hf : ∀ x, circuitFun n C x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
      (hdeg : ∀ w, (G.neighborSet w).ncard = 3) (v : Fin n) :
      1 ≤ (readers C v.val).length := by
    by_contra hz
    have hlen : (readers C v.val).length = 0 := by omega
    have hno (g : Gate) (hg : g ∈ C.gates) : v.val ∉ portRD g := by
      intro hr
      have hmem : g ∈ readers C v.val := List.mem_filter.mpr ⟨hg,List.contains_iff_mem.mpr hr⟩
      exact (List.ne_nil_of_mem hmem) (List.length_eq_zero_iff.mp hlen)
    have hout : C.output ≠ v.val := by
      intro ho
      let z : Fin n → Bool := fun i => decide (i = v)
      have hfalse := singleton_rejects hf v
      change (C.gates.foldl F (List.ofFn z)).getD C.output false = false at hfalse
      rw [ho, keep_input _ _ _ (by simp)] at hfalse
      have hz' : (List.ofFn z).getD v.val false = true := by
        simp [List.getD_eq_getElem?_getD, v.isLt, z]
      exact Bool.noConfusion (hfalse.symm.trans hz')
    obtain ⟨u,hu,huv⟩ := Set.exists_ne_of_one_lt_ncard (s := G.neighborSet v)
      (show 1 < (G.neighborSet v).ncard by rw [hdeg v]; omega) v
    let x : Fin n → Bool := fun i => decide (i = u)
    let y : Fin n → Bool := fun i => decide (i = v ∨ i = u)
    have he : circuitFun n C x = circuitFun n C y := by
      apply indep v.val C.gates (ok_of_fan C hC) hno _ _ (by simp) _ C.output hout
      intro i hi
      by_cases hin : i < n
      · have hne : (⟨i,hin⟩ : Fin n) ≠ v := fun e => hi (congrArg Fin.val e)
        simp [List.getD_eq_getElem?_getD,hin,x,y,hne]
      · simp [List.getD_eq_getElem?_getD,hin]
    have htrue : circuitFun n C y = true := (hf _).mpr ⟨v,u,hu,by simp [y],by simp [y]⟩
    rw [htrue] at he
    exact Bool.noConfusion ((singleton_rejects hf u).symm.trans he)

  have cost_of_not (g : Gate) (hn : isNot g = true) : (portRD g).length ≤ 1 := by
    simp only [portRD,isNot] at hn ⊢
    rw [hn]
    change (g.inputs.take 1).length ≤ 1
    simpa only [List.length_take] using Nat.min_le_left 1 g.inputs.length

  have not_cost (C : Circuit) :
      ((C.gates.filter isNot).flatMap portRD).length ≤ (C.gates.filter isNot).length := by
    have H (gs : List Gate) (hp : ∀ g ∈ gs, g ∈ C.gates ∧ isNot g = true) :
        (gs.flatMap portRD).length ≤ gs.length := by
      induction gs with
      | nil => rfl
      | cons g gs ih =>
        have hg := hp g (by simp)
        have hb := cost_of_not g hg.2
        have hs := ih (fun a ha => hp a (by simp [ha]))
        simp only [List.flatMap_cons,List.length_append,List.length_cons]
        omega
    exact H _ (fun g hg => List.mem_filter.mp hg)

  have inexpensive_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (hm : IsMinimalCircuit n C)
      (hf : ∀ x, circuitFun n C x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
      (hdeg : ∀ v, (G.neighborSet v).ncard = 3)
      (budget : C.size + 1 < 2 * n) :
      ∃ (v : Fin n) (g : Gate), readers C v.val = [g] ∧ (g.op = .and ∨ g.op = .or) := by
    classical
    let cost (v : Fin n) := (readers C v.val).length
    let low : Finset (Fin n) := Finset.univ.filter fun v => cost v = 1
    let notGates := C.gates.filter isNot
    have hfG : circuitFun n C = NestedCover.graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      have he : NestedCover.graphFun G ∅ x = true ↔
          ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
        change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) || decide _) = true ↔ _
        simp
      exact (hf x).trans he.symm
    have hbudget := portLemma n G ∅ C hm.1 hfG (fun s hs => by
      obtain ⟨D, hD, hsize, hval⟩ := hs
      exact (hm.2 D hD (funext (fun x => (hval x).trans (congrFun hfG x).symm))).trans hsize)
    have hbudget' : (∑ v : Fin n, cost v) + notGates.length ≤ C.size + 1 := by
      rw [Finset.card_empty, Finset.compl_empty, Nat.zero_add] at hbudget
      exact hbudget
    have lower : 2 * n ≤ (∑ v : Fin n, cost v) + low.card := by
      have hD (v : Fin n) : 2 ≤ cost v + if v ∈ low then 1 else 0 := by
        have hpos := reader_ne_empty G C hm.1 hf hdeg v
        change 1 ≤ cost v at hpos
        by_cases he : cost v = 1
        · simp [low,he]
        · simp only [low, Finset.mem_filter, Finset.mem_univ, true_and, he, ite_false, Nat.add_zero]
          omega
      have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun v _ => hD v)
      have hcard : (∑ v : Fin n, if v ∈ low then 1 else 0) = low.card := by
        rw [← Finset.sum_filter]
        simp
      rw [Finset.sum_add_distrib, hcard] at hsum
      simpa [Nat.mul_comm] using hsum
    by_contra hno
    have hnof (v : Fin n) (hv : v ∈ low) :
        v.val ∈ (notGates.flatMap portRD).toFinset := by
      have hlen : (readers C v.val).length = 1 := (Finset.mem_filter.mp hv).2
      obtain ⟨g,hg⟩ := List.length_eq_one_iff.mp hlen
      have hmem : g ∈ readers C v.val := by simp [hg]
      obtain ⟨hC,hread⟩ := List.mem_filter.mp hmem
      have hnot : isNot g = true := by
        rcases (ok_of_fan C hm.1 g hC).1 with ho | ho | ho
        · exact (hno ⟨v,g,hg,Or.inl ho⟩).elim
        · exact (hno ⟨v,g,hg,Or.inr ho⟩).elim
        · simp [isNot,ho,evNot]
      exact List.mem_toFinset.mpr (List.mem_flatMap.mpr
        ⟨g,List.mem_filter.mpr ⟨hC,hnot⟩,List.contains_iff_mem.mp hread⟩)
    have htle : low.card ≤ (notGates.flatMap portRD).toFinset.card :=
      Finset.card_le_card_of_injOn Fin.val hnof (fun _ _ _ _ => Fin.ext)
    have hN : (notGates.flatMap portRD).toFinset.card ≤ notGates.length :=
      (List.toFinset_card_le _).trans (not_cost C)
    omega

  have exists_sole_binary (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool) :
      (∀ v, (G.neighborSet v).ncard = 3) →
      (∀ x, f x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
      ∀ s, s + 1 < 2 * n → HasCircuitSize n f s →
      ∃ C : Circuit, IsMinimalCircuit n C ∧ circuitFun n C = f ∧ C.size ≤ s ∧
        ∃ (v : Fin n) (g : Gate),
          C.gates.filter (fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains v.val) =
            [g] ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) := by
    intro hdeg hspec s hsmall hsize
    classical
    obtain ⟨D,hD,hDs,heD⟩ := hsize
    have hex : ∃ k : ℕ, ∃ C : Circuit, FanInTwo C ∧ circuitFun n C = f ∧ C.size = k :=
      ⟨D.size,D,hD,funext heD,rfl⟩
    obtain ⟨C,hC,heC,hCs⟩ := Nat.find_spec hex
    have hm : IsMinimalCircuit n C :=
      ⟨hC,fun E hE he => hCs.symm ▸ Nat.find_min' hex ⟨E,hE,he.trans heC,rfl⟩⟩
    have hsmallC : C.size ≤ s := (hm.2 D hD ((funext heD).trans heC.symm)).trans hDs
    have hbudget : C.size + 1 < 2 * n := by omega
    exact ⟨C,hm,heC,hsmallC,inexpensive_reader G C hm (fun x => by rw [heC]; exact hspec x) hdeg hbudget⟩

  obtain ⟨C,hmin,he,hC,v,g,hread,hop⟩ := exists_sole_binary n G f hdeg hf s hsmall hs
  have hspec (x : Fin n → Bool) : circuitFun n C x = true ↔
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by rw [he]; exact hf x
  obtain ⟨D,hDmin,hDC,hsizeD,hsole⟩ := companion n G C hmin hspec hdeg hgirth v g hread hop
  have hspecD (x : Fin n → Bool) : circuitFun n D x = true ↔
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by rw [hDC]; exact hspec x
  have hDbudget : D.size + 1 < 2 * n := by omega
  obtain ⟨p,q,hpq,hna,t,ht,hT⟩ := residual n G D hn heven hcolor hdeg hgirth hspecD hDbudget hDmin hsole
  exact ⟨p,q,hpq,hna,t,by omega,by rw [hDC,he] at hT; exact hT⟩

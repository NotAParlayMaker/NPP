import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves

theorem PEqualNP.Outside.R_meta_1971_41
    (redirects : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (S : Finset (Fin n)) (C : Circuit) (u : Fin n),
      IsMinimalCircuit n C → circuitFun n C = graphFun G S →
      (∀ i ∉ S, (G.neighborSet i).ncard = 3) →
      (∀ i (p : G.Walk i i), p.IsCycle → 7 ≤ p.length) →
      (∀ i j, G.Adj i j → i ∉ S) →
      (∀ i ∉ S, let r := C.gates.filter (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i.val)
        r.length ≤ 3 ∧ (r.length = 3 → ∀ g ∈ r, g.op = GateOp.or)) →
      u ∉ S → (C.gates.filter (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains u.val)).length = 1 →
      ∃ v ∉ S, ∃ moves : List (ℕ × ℕ), moves.length = 4 ∧
        (∀ i : Fin moves.length, moves[i].1 + i.val < C.size) ∧
        ∀ x : Fin n → Bool, x v = false →
          circuitFun n (moves.foldl (fun D mp => eraseGate n D mp.1 mp.2) C) x =
          circuitFun n C x)
    (pinFalse : ∀ (n : ℕ) (C : Circuit) (v : Fin n), FanInTwo C →
      HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) C.size) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length ≤ (1 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  classical
  intro n G S f C deg girth off edge semantics basis computes minimal readers low
  have least : IsMinimalCircuit n C := by
    refine ⟨basis, fun D hD same => minimal D.size ⟨D, hD, le_rfl, ?_⟩⟩
    exact fun x => congrFun (same.trans computes) x
  have graphEq : circuitFun n C = graphFun G S := by
    rw [computes]
    funext x
    apply Bool.eq_iff_iff.mpr
    simpa [graphFun] using semantics x
  obtain ⟨u,hu,huReads⟩ := low
  have fold1971Essential
      {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
      {f : (Fin n → Bool) → Bool}
      (degree : ∀ v ∉ S, (G.neighborSet v).ncard = 3)
      (edgeOff : ∀ a b, G.Adj a b → a ∉ S)
      (spec : ∀ m, f m = true ↔
        (∃ a ∈ S, m a = true) ∨ ∃ a b, G.Adj a b ∧ m a = true ∧ m b = true) :
      ∀ v ∉ S, ∃ w, G.Adj v w ∧ w ∉ S ∧ v ≠ w ∧
        f (fun i => decide (i = w)) = false ∧
        f (fun i => decide (i = v ∨ i = w)) = true ∧
        f (Function.update (fun i => decide (i = w)) v true) = true ∧
        f (Function.update (fun i => decide (i = v ∨ i = w)) v false) = false := by
    classical
    intro v hv
    have ex : ∃ w, G.Adj v w := by
      by_contra! no
      have empty : G.neighborSet v = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun w hw => no w hw)
      have d := degree v hv
      rw [empty, Set.ncard_empty] at d
      omega
    obtain ⟨w, adj⟩ := ex
    have hne : v ≠ w := adj.ne
    have hw : w ∉ S := edgeOff w v adj.symm
    have single : f (fun i => decide (i = w)) = false := by
      apply Bool.eq_false_iff.mpr
      intro accepted
      rcases (spec _).mp accepted with ⟨a, ha, hm⟩ | ⟨a, b, hab, hma, hmb⟩
      · have e : a = w := of_decide_eq_true hm
        exact hw (e ▸ ha)
      · have ea : a = w := of_decide_eq_true hma
        have eb : b = w := of_decide_eq_true hmb
        exact hab.ne (ea.trans eb.symm)
    refine ⟨w, adj, hw, hne, single, ?_, ?_, ?_⟩
    · apply (spec _).mpr
      exact Or.inr ⟨v, w, adj, by simp, by simp⟩
    · apply (spec _).mpr
      exact Or.inr ⟨v, w, adj, by simp, by simp [Function.update, Ne.symm hne]⟩
    · have e : Function.update (fun i => decide (i = v ∨ i = w)) v false =
          (fun i => decide (i = w)) := by
        funext i
        by_cases h : i = v
        · subst i
          simp [hne]
        · simp [Function.update, h]
      rw [e]
      exact single
  have fold1971Reader
      {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
      {f : (Fin n → Bool) → Bool} {C : PEqualNP.CircuitLowerBounds.Circuit}
      (degree : ∀ v ∉ S, (G.neighborSet v).ncard = 3)
      (edgeOff : ∀ a b, G.Adj a b → a ∉ S)
      (spec : ∀ m, f m = true ↔
        (∃ a ∈ S, m a = true) ∨ ∃ a b, G.Adj a b ∧ m a = true ∧ m b = true)
      (fan : PEqualNP.MetaComplexity.FanInTwo C)
      (computes : PEqualNP.MetaComplexity.circuitFun n C = f)
      (v : Fin n) (hv : v ∉ S)
      (hlow : (C.gates.filter (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length ≤ 1) :
      (C.gates.filter (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length = 1 := by
    classical
    let eff (g : PEqualNP.CircuitLowerBounds.Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
    let used := C.gates.filter (fun g => (eff g).contains v.val)
    change used.length ≤ 1 at hlow
    change used.length = 1
    by_contra bad
    have zero : used = [] := List.length_eq_zero_iff.mp (by omega)
    have unused (g : PEqualNP.CircuitLowerBounds.Gate) (hg : g ∈ C.gates) : v.val ∉ eff g := by
      intro hm
      have inUsed : g ∈ used := List.mem_filter.mpr ⟨hg, by simpa using hm⟩
      rw [zero] at inUsed
      exact List.not_mem_nil inUsed
    let run (gs : List PEqualNP.CircuitLowerBounds.Gate) (L : List Bool) :=
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) L
    have trunc (g : PEqualNP.CircuitLowerBounds.Gate) (hg : g ∈ C.gates) (F : ℕ → Bool) :
        g.op.eval (g.inputs.map F) = g.op.eval ((eff g).map F) := by
      obtain ⟨ops, hi⟩ := fan g hg
      rcases ops with a | a | a
      · simp [eff, a, PEqualNP.CircuitLowerBounds.GateOp.eval, List.take_of_length_le hi]
      · simp [eff, a, PEqualNP.CircuitLowerBounds.GateOp.eval, List.take_of_length_le hi]
      · change g.op = PEqualNP.CircuitLowerBounds.GateOp.not at a
        cases inp : g.inputs with
        | nil => simp [eff, a, inp, PEqualNP.CircuitLowerBounds.GateOp.eval]
        | cons k rest => simp [eff, a, inp, PEqualNP.CircuitLowerBounds.GateOp.eval]
    have snoc (l : List Bool) (b : Bool) (j : ℕ) (hj : j ≠ l.length) :
        (l ++ [b]).getD j false = l.getD j false := by
      by_cases h : j < l.length
      · exact List.getD_append _ _ _ _ h
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    have preserve (gs : List PEqualNP.CircuitLowerBounds.Gate) (subset : ∀ g ∈ gs, g ∈ C.gates)
        (L R : List Bool) (len : L.length = R.length)
        (agree : ∀ j : ℕ, j ≠ v.val → L.getD j false = R.getD j false) :
        ∀ j : ℕ, j ≠ v.val → (run gs L).getD j false = (run gs R).getD j false := by
      induction gs generalizing L R with
      | nil => exact agree
      | cons g gs ih =>
        have hg := subset g (by simp)
        have same : (eff g).map (fun i => L.getD i false) = (eff g).map (fun i => R.getD i false) := by
          apply List.map_congr_left
          intro j hj
          apply agree
          exact fun e => unused g hg (e ▸ hj)
        have ge : g.op.eval (g.inputs.map fun i => L.getD i false) =
            g.op.eval (g.inputs.map fun i => R.getD i false) := by
          rw [trunc g hg (fun i => L.getD i false), trunc g hg (fun i => R.getD i false), same]
        apply ih (fun k hk => subset k (by simp [hk]))
          (L ++ [g.op.eval (g.inputs.map fun i => L.getD i false)])
          (R ++ [g.op.eval (g.inputs.map fun i => R.getD i false)]) (by simp [len])
        intro j hj
        by_cases pos : j = L.length
        · subst j
          have last (q : List Bool) (b : Bool) : (q ++ [b]).getD q.length false = b := by simp
          rw [last, len, last]
          exact ge
        · rw [snoc _ _ _ pos, snoc _ _ _ (by omega)]
          exact agree _ hj
    have primary (gs : List PEqualNP.CircuitLowerBounds.Gate) (L : List Bool) (hin : v.val < L.length) :
        (run gs L).getD v.val false = L.getD v.val false := by
      induction gs generalizing L with
      | nil => rfl
      | cons g gs ih =>
        change (run gs (L ++ [_])).getD v.val false = _
        rw [ih _ (by simp; omega)]
        exact List.getD_append _ _ _ _ hin
    have evalAt (x : Fin n → Bool) : C.eval (List.ofFn x) = f x := congrFun computes x
    have out : C.output ≠ v.val := by
      intro h
      let m : Fin n → Bool := fun i => decide (i = v)
      have hEval := evalAt m
      change (run C.gates (List.ofFn m)).getD C.output false = f m at hEval
      rw [h, primary _ _ (by simp)] at hEval
      have hm : f m = true := by simpa [m] using hEval.symm
      rcases (spec m).mp hm with ⟨a, ha, hma⟩ | ⟨a, b, hab, hma, hmb⟩
      · exact hv ((of_decide_eq_true hma : a = v) ▸ ha)
      · exact hab.ne ((of_decide_eq_true hma : a = v).trans (of_decide_eq_true hmb : b = v).symm)
    obtain ⟨w, _, _, _, hfalse, _, htrue, _⟩ := fold1971Essential degree edgeOff spec v hv
    let x : Fin n → Bool := fun i => decide (i = w)
    let y := Function.update x v true
    have same : ∀ j : ℕ, j ≠ v.val → (List.ofFn x).getD j false = (List.ofFn y).getD j false := by
      intro j hj
      by_cases hjn : j < n
      · have neq : (⟨j, hjn⟩ : Fin n) ≠ v := fun h => hj (congrArg Fin.val h)
        simp [hjn, y, Function.update, neq]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have e := preserve C.gates (fun _ h => h) (List.ofFn x) (List.ofFn y) (by simp) same C.output out
    change C.eval (List.ofFn x) = C.eval (List.ofFn y) at e
    rw [evalAt, evalAt] at e
    change f x = false at hfalse
    change f y = true at htrue
    rw [hfalse, htrue] at e
    contradiction
  have unique := fold1971Reader deg off semantics basis computes u hu huReads
  obtain ⟨v,hv,moves,hfour,hpositions,heval⟩ :=
    redirects n G S C u least graphEq deg girth off readers hu unique
  have eraseAll : ∀ (D : Circuit) (ms : List (ℕ × ℕ)), FanInTwo D →
      (∀ i : Fin ms.length, ms[i].1 + i.val < D.size) →
      let E := ms.foldl (fun B mp => eraseGate n B mp.1 mp.2) D
      FanInTwo E ∧ E.size + ms.length = D.size := by
    intro D ms
    induction ms generalizing D with
    | nil => exact fun h _ => ⟨h, by simp⟩
    | cons m ms ih =>
      intro hD valid
      have hm : m.1 < D.gates.length := by
        simpa [Circuit.size] using valid ⟨0, by simp⟩
      have fan : FanInTwo (eraseGate n D m.1 m.2) := by
        intro g hg
        simp only [eraseGate, hm, ↓reduceIte, List.mem_append, List.mem_map] at hg
        rcases hg with ht | ⟨a,ha,rfl⟩
        · exact hD g (List.mem_of_mem_take ht)
        · obtain ⟨hop,hlen⟩ := hD a (List.mem_of_mem_drop ha)
          exact ⟨hop, by simpa using hlen⟩
      have sz : (eraseGate n D m.1 m.2).size + 1 = D.size := by
        simp [eraseGate, hm, Circuit.size, Nat.min_eq_left (Nat.le_of_lt hm)]
        omega
      obtain ⟨hh,hs⟩ := ih (eraseGate n D m.1 m.2) fan (by
        intro i
        have hi := valid i.succ
        change ms[i.val].1 + (i.val + 1) < D.size at hi
        change ms[i.val].1 + i.val < _
        omega)
      exact ⟨hh, by simp only [List.foldl_cons, List.length_cons]; omega⟩
  obtain ⟨hE,hsize⟩ := eraseAll C moves basis hpositions
  let E := moves.foldl (fun D (mp : ℕ × ℕ) => eraseGate n D mp.1 mp.2) C
  change FanInTwo E at hE
  change E.size + moves.length = C.size at hsize
  refine ⟨v,hv,E.size,by omega,?_⟩
  have pin := pinFalse n E v hE
  have eq : (fun x : Fin n → Bool => circuitFun n E (Function.update x v false)) =
      (fun x => f (Function.update x v false)) := by
    funext x
    exact (heval _ (Function.update_self ..)).trans (congrFun computes _)
  rwa [eq] at pin

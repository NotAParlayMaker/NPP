import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4833_297
    (h0 : ∃ layers : ℕ → Set (Set (BitVec 32)), {w | w ∈ ([0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752] : List (BitVec 32))} ∈ layers 0 ∧
      (∀ i < 18, ∀ A ∈ layers i, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ [x &&& y, x ||| y],
        ∃ B ∈ layers (i+1), ∀ w ∈ insert z A, ∃ u ∈ B, ∀ r : Fin 32,
          w.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val → u.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val) ∧
      ∀ i ≤ 18, ∀ A ∈ layers i, (16383 : BitVec 32) ∉ A)
    (h1 : ∃ layers : ℕ → Set (Set (BitVec 32)), {w | w ∈ ([8372227, 0, 32849932, 714129456, 26198208, 101352196, 19074064, 340530208, 410001728, 562049537, 1040189578] : List (BitVec 32))} ∈ layers 0 ∧
      (∀ i < 18, ∀ A ∈ layers i, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ [x &&& y, x ||| y],
        ∃ B ∈ layers (i+1), ∀ w ∈ insert z A, ∃ u ∈ B, ∀ r : Fin 32,
          w.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val → u.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val) ∧
      ∀ i ≤ 18, ∀ A ∈ layers i, (16383 : BitVec 32) ∉ A)
    (h2 : ∃ layers : ℕ → Set (Set (BitVec 32)), {w | w ∈ ([8372227, 1292189708, 0, 1418772528, 42631364, 202359552, 52628496, 676074528, 812654920, 1132474881, 2080376962] : List (BitVec 32))} ∈ layers 0 ∧
      (∀ i < 18, ∀ A ∈ layers i, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ [x &&& y, x ||| y],
        ∃ B ∈ layers (i+1), ∀ w ∈ insert z A, ∃ u ∈ B, ∀ r : Fin 32,
          w.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val → u.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val) ∧
      ∀ i ≤ 18, ∀ A ∈ layers i, (16383 : BitVec 32) ∉ A)
    (h3 : ∃ layers : ℕ → Set (Set (BitVec 32)), {w | w ∈ ([16760835, 353714188, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 318779905, 469764258] : List (BitVec 32))} ∈ layers 0 ∧
      (∀ i < 18, ∀ A ∈ layers i, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ [x &&& y, x ||| y],
        ∃ B ∈ layers (i+1), ∀ w ∈ insert z A, ∃ u ∈ B, ∀ r : Fin 32,
          w.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val → u.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val) ∧
      ∀ i ≤ 18, ∀ A ∈ layers i, (16383 : BitVec 32) ∉ A) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (19 : ℕ) ≤ x3.size := by
  intro G v C hv hAO hfun
  by_contra! small
  have hlen : C.gates.length ≤ 18 := by change C.gates.length < 19 at small; omega
  let encode (g : Gate) : (Bool × Fin 30 × Fin 30) :=
    (@decide (g.op = GateOp.and) (Classical.propDecidable _), Fin.ofNat 30 (g.inputs.getD 0 0), Fin.ofNat 30 (g.inputs.getD 1 0))
  let step := fun (w : List (BitVec 32)) (g : (Bool × Fin 30 × Fin 30)) => w ++ [if g.1 then (w.getD g.2.1.val 0) &&& (w.getD g.2.2.val 0) else (w.getD g.2.1.val 0) ||| (w.getD g.2.2.val 0)]
  let bases : Fin 4 → List (BitVec 32) := ![[0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752], [8372227, 0, 32849932, 714129456, 26198208, 101352196, 19074064, 340530208, 410001728, 562049537, 1040189578], [8372227, 1292189708, 0, 1418772528, 42631364, 202359552, 52628496, 676074528, 812654920, 1132474881, 2080376962], [16760835, 353714188, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 318779905, 469764258]]
  let k : Fin 4 := ⟨v.val, hv⟩
  let xs := bases k
  let ops := C.gates.map encode
  let bank := ops.foldl step xs
  have legal (g : Gate) (hg : g ∈ C.gates) :
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a < 30 ∧ b < 30 := by
    obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hg
    have atg : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hj]
      exact hgj
    have hback := hAO.2.1 j hj
    rw [atg] at hback
    refine ⟨hAO.1 g hg, ?_⟩
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 g hg)
    rw [hab] at hback
    have ha := hback a (by simp)
    have hb := hback b (by simp)
    exact ⟨a,b,hab,by omega,by omega⟩
  have mapped (w : List (BitVec 32)) (j r : ℕ) :
      (w.getD j 0).getLsbD r = (w.map (fun z => z.getLsbD r)).getD j false := by
    by_cases h : j < w.length
    · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
      simp
  let boolStep (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have band (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by
    cases a <;> cases b <;> rfl
  have bor (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by
    cases a <;> cases b <;> rfl
  have hne : GateOp.or ≠ GateOp.and := by intro h; cases h
  have simG (gs : List Gate) (ok : ∀ g ∈ gs, g ∈ C.gates) (w : List (BitVec 32)) (r : ℕ) :
      (((gs.map encode).foldl step w).map fun z => z.getLsbD r) =
        gs.foldl boolStep (w.map fun z => z.getLsbD r) := by
    induction gs generalizing w with
    | nil => rfl
    | cons g tail ih =>
      obtain ⟨hop,a,b,hab,ha,hb⟩ := legal g (ok g (by simp))
      simp only [List.map_cons, List.foldl_cons]
      rw [ih (fun _ h => ok _ (by simp [h]))]
      congr 1
      rcases hop with hop | hop <;>
        simp [step, encode, boolStep, hop, hab, band, bor, hne,
          Fin.ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] <;>
        cases w[a]? <;> cases w[b]? <;> simp
  let point (r : ℕ) (i : Fin 11) := (xs.getD i.val 0).getLsbD r
  have table : ∀ (j : Fin 4) (r : Fin 32),
      let p := fun i : Fin 11 => ((bases j).getD i.val 0).getLsbD r.val
      p ⟨j.val, Nat.lt_trans j.isLt (by decide : 4 < 11)⟩ = false ∧
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ p = (16383 : BitVec 32).getLsbD r.val := by
    dsimp only [G, bases]
    decide +kernel
  have width : xs.length = 11 := by
    have hw : ∀ j : Fin 4, (bases j).length = 11 := by decide +kernel
    exact hw k
  have simOut (r : Fin 32) :
      (bank.getD C.output 0).getLsbD r.val = (16383 : BitVec 32).getLsbD r.val := by
    have hp := table k r
    have hc := hfun (point r.val) hp.1
    have baseEq : (xs.map fun z => z.getLsbD r.val) = List.ofFn (point r.val) := by
      apply List.ext_getElem
      · simp [width]
      · intro j h1 h2
        simp only [List.getElem_map, List.getElem_ofFn]
        unfold point
        rw [List.getD_eq_getElem _ _ (by simpa using h1 : j < xs.length)]
    have hs := simG C.gates (fun _ t => t) xs r.val
    rw [baseEq] at hs
    rw [mapped]
    change (List.map _ ((C.gates.map encode).foldl step xs)).getD _ _ = _
    rw [hs]
    exact hc.trans hp.2
  have hit : bank.getD C.output 0 = (16383 : BitVec 32) :=
    BitVec.eq_of_getLsbD_eq fun r hr => simOut ⟨r,hr⟩
  have hout : C.output < bank.length := by
    by_contra! large
    rw [List.getD_eq_default _ _ large] at hit
    exact (by decide : (0 : BitVec 32) ≠ 16383) hit
  have hm : (16383 : BitVec 32) ∈ bank := by
    rw [← hit, List.getD_eq_getElem _ _ hout]
    exact List.getElem_mem ..
  have count : ops.length ≤ 18 := by simpa [ops] using hlen
  let good (a b : BitVec 32) := ∀ r : Fin 32, b.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val →
      a.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val
  let combine (gate : Bool) (a b : BitVec 32) := if gate then a &&& b else a ||| b
  have truth : ∀ (t a b x y : Bool), (x = t → a = t) → (y = t → b = t) →
      ((x && y) = t → (a && b) = t) ∧ ((x || y) = t → (a || b) = t) := by decide
  have preserves (c : Bool) (a b x y : BitVec 32) (ha : good a x) (hb : good b y) :
      good (combine c a b) (combine c x y) := by
    intro r
    have h := truth _ _ _ _ _ (ha r) (hb r)
    cases c
    · exact (by simpa only [combine, Bool.false_eq_true, ite_false, BitVec.getLsbD_or] using h.2)
    · exact (by simpa only [combine, ite_true, BitVec.getLsbD_and] using h.1)
  have disallow (s : List (BitVec 32)) (zero : 0 ∈ s)
      (certificate : ∃ layers : ℕ → Set (Set (BitVec 32)), {w | w ∈ (s : List (BitVec 32))} ∈ layers 0 ∧
      (∀ i < 18, ∀ A ∈ layers i, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ [x &&& y, x ||| y],
        ∃ B ∈ layers (i+1), ∀ w ∈ insert z A, ∃ u ∈ B, ∀ r : Fin 32,
          w.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val → u.getLsbD r.val = (16383 : BitVec 32).getLsbD r.val) ∧
      ∀ i ≤ 18, ∀ A ∈ layers i, (16383 : BitVec 32) ∉ A) : (16383 : BitVec 32) ∉ ops.foldl step s := by
    obtain ⟨layers, start, trans, safe⟩ := certificate
    have walk (seq : List (Bool × Fin 30 × Fin 30)) (i : ℕ) (w : List (BitVec 32))
        (A : Set (BitVec 32)) (hA : A ∈ layers i) (hz : 0 ∈ w)
        (cover : ∀ p ∈ w, ∃ u ∈ A, good u p) (limit : i + seq.length ≤ 18) :
        (16383 : BitVec 32) ∉ seq.foldl step w := by
      induction seq generalizing i w A with
      | nil =>
        intro hm
        obtain ⟨u, hu, gu⟩ := cover 16383 hm
        have eq : u = 16383 := BitVec.eq_of_getLsbD_eq fun r hr => gu ⟨r, hr⟩ rfl
        exact safe i (by simpa using limit) A hA (eq ▸ hu)
      | cons op tail ih =>
        have lookup (j : ℕ) : w.getD j 0 ∈ w := by
          by_cases hj : j < w.length
          · rw [List.getD_eq_getElem _ _ hj]
            exact List.getElem_mem ..
          · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
            exact hz
        obtain ⟨a, ha, ax⟩ := cover _ (lookup op.2.1.val)
        obtain ⟨b, hb, by'⟩ := cover _ (lookup op.2.2.val)
        have mem : combine op.1 a b ∈ [a &&& b, a ||| b] := by
          cases h : op.1 <;> simp [combine, h]
        have bound : i + (tail.length + 1) ≤ 18 := limit
        obtain ⟨B, hB, next⟩ := trans i (by omega) A hA a ha b hb _ mem
        apply ih (i+1) (step w op) B hB (List.mem_append_left _ hz) _ (by omega)
        intro p hp
        change p ∈ w ++ [combine op.1 (w.getD op.2.1.val 0) (w.getD op.2.2.val 0)] at hp
        rcases List.mem_append.mp hp with old | fresh
        · obtain ⟨u, hu, gu⟩ := cover p old
          obtain ⟨q, hq, gq⟩ := next u (Set.mem_insert_of_mem _ hu)
          exact ⟨q,hq,fun r h => gq r (gu r h)⟩
        · obtain rfl := List.mem_singleton.mp fresh
          obtain ⟨q, hq, gq⟩ := next _ (Set.mem_insert _ _)
          exact ⟨q,hq,fun r h => gq r (preserves op.1 a b _ _ ax by' r h)⟩
    exact walk ops 0 s _ start zero (fun p hp => ⟨p,hp,fun _ h => h⟩) (by simpa using count)
  have nohit : ∀ j : Fin 4, (16383 : BitVec 32) ∉ ops.foldl step (bases j) := by
    intro j
    fin_cases j
    · exact disallow _ (by decide) h0
    · exact disallow _ (by decide) h1
    · exact disallow _ (by decide) h2
    · exact disallow _ (by decide) h3
  exact nohit k hm

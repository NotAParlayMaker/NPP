import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A two-digit code gives the endpoints of a pair, with an implicit leading zero.
-- The reflection exchanges vertices 0 and 2, 3 and 5, and 4 and 7.
-- Wire 24 is beyond all eleven inputs and all thirteen gate outputs.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1930_217
    (pairs :
      let f := fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ e ∈ ([1,3,4,5,6,7,8,13,14,16,18,34,35,36,37,38,46,47,48,68] : List ℕ), ∀ C : Circuit,
        FanInTwo C → C.size ≤ 13 → C.output ≤ 24 →
        (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2,
          x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))]) ≠ f x)
    (triples :
      let f := fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ v ∈ ([1,3,4,6,8] : List ℕ), ∀ C : Circuit,
        FanInTwo C → C.size ≤ 13 → C.output ≤ 24 →
        (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2,
          (x 0 && x 2) && x (Fin.ofNat 9 v)]) ≠ f x) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let f := fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let pairCodes : List ℕ := [1,3,4,5,6,7,8,13,14,16,18,34,35,36,37,38,46,47,48,68]
  let thirdVertices : List ℕ := [1,3,4,6,8]
  let codes := pairCodes ++ thirdVertices.map (100 + ·)
  let perm (flip : Bool) (v : Fin 9) : Fin 9 :=
    if flip then (![2,1,0,5,7,3,6,4,8] : Fin 9 → Fin 9) v else v
  let row (flip : Bool) (x : Fin 9 → Bool) := fun i => x (perm flip i)
  let edges := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) ||
    (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
    (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  have graph : ∀ flip x, edges (row flip x) = f x := by decide +kernel
  have firstFixed (flip : Bool) (x : Fin 9 → Bool) :
      (row flip x 0 && row flip x 2) = (x 0 && x 2) := by
    cases flip
    · rfl
    · exact Bool.and_comm ..
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 2]
  let atom (p : Fin 12) (x : Fin 9 → Bool) :=
    if p.val = 11 then true else (seed x).getD p.val false
  let bonus (c : ℕ) (x : Fin 9 → Bool) :=
    if c < 100 then x (Fin.ofNat 9 (c / 10)) && x (Fin.ofNat 9 (c % 10))
    else (x 0 && x 2) && x (Fin.ofNat 9 (c - 100))
  let start (c : ℕ) (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 2, bonus c x]
  -- A set records the variables in a conjunction. The empty set gives true.
  -- A missing set represents the false value of an out-of-range wire.
  let prod (flip : Bool) (p : Fin 12) : Option (Finset (Fin 9)) :=
    if p.val < 9 then some {perm flip (Fin.ofNat 9 p.val)}
    else if p.val = 9 then some {perm flip 0, perm flip 2}
    else if p.val = 10 then none else some ∅
  let join (a b : Option (Finset (Fin 9))) := a.bind (fun u => b.map (fun v => u ∪ v))
  let available (c : ℕ) (d : Fin 13) : Option (Finset (Fin 9)) :=
    if d.val < 9 then some {Fin.ofNat 9 d.val}
    else if d.val = 9 then some {0,2}
    else if d.val = 10 then some (if c < 100 then {Fin.ofNat 9 (c / 10), Fin.ofNat 9 (c % 10)}
      else {0,2,Fin.ofNat 9 (c - 100)})
    else if d.val = 11 then none else some ∅
  have catalogue : ∀ p q : Fin 12, ∃ flip : Bool, ∃ c ∈ codes, ∃ d : Fin 13,
      join (prod flip p) (prod flip q) = available c d := by decide +kernel
  let value (x : Fin 9 → Bool) (a : Option (Finset (Fin 9))) :=
    a.elim false (fun t => decide (∀ i ∈ t, x i = true))
  have joinValue (x) (a b) : value x (join a b) = (value x a && value x b) := by
    cases a <;> cases b <;> simp [value, join, or_imp, forall_and]
  have atomValue : ∀ flip p x, value x (prod flip p) = atom p (row flip x) := by
    intro flip p x
    fin_cases p <;> simp [value, prod, atom, row, seed, List.getD_eq_getElem?_getD] <;> rfl
  let address (d : Fin 13) : Option ℕ :=
    if d.val = 12 then none else if d.val = 11 then some 24 else some d.val
  let read (w : List Bool) (a : Option ℕ) := a.elim true (fun i => w.getD i false)
  have slotValue (c : ℕ) (d : Fin 13) (x) :
      value x (available c d) = read (start c x) (address d) := by
    fin_cases d <;> simp [value, available, read, address, start, List.getD_eq_getElem?_getD,
      bonus, Bool.and_assoc] <;> first | rfl | split <;> simp
  intro pins arity C fan small
  let boundPin (i : ℕ) : Fin 12 := ⟨min i 10, by omega⟩
  have pinRead (i : ℕ) (x) : atom (boundPin i) x = (seed x).getD i false := by
    have hn : (seed x).length = 10 := by simp [seed]
    have hn11 : min i 10 ≠ 11 := by omega
    simp only [atom, boundPin, hn11, ite_false]
    by_cases hi : i ≤ 10
    · rw [Nat.min_eq_left hi]
    · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by omega)]
  have encode : ∃ p q : Fin 12, ∀ x, GateOp.and.eval
      (pins.map fun i => (seed x).getD i false) = (atom p x && atom q x) := by
    rcases pins with _ | ⟨a, _ | ⟨b, _ | ⟨v, vs⟩⟩⟩
    · exact ⟨11,11,fun _ => rfl⟩
    · refine ⟨boundPin a,11,fun x => ?_⟩
      rw [pinRead]
      rfl
    · refine ⟨boundPin a,boundPin b,fun x => ?_⟩
      rw [pinRead, pinRead]
      change (_ && (_ && true)) = _
      simp
    · simp at arity
  obtain ⟨p, q, encode⟩ := encode
  obtain ⟨flip, c, hc, d, shape⟩ := catalogue p q
  have aliasValue (x) : (atom p (row flip x) && atom q (row flip x)) =
      read (start c x) (address d) := by
    rw [← atomValue, ← atomValue, ← joinValue, shape, slotValue]
  classical
  let old (x : Fin 9 → Bool) := seed (row flip x) ++ [atom p (row flip x) && atom q (row flip x)]
  let addr (i : ℕ) := if i < 9 then some (perm flip (Fin.ofNat 9 i)).val
    else if i = 10 then address d else some (min i 24)
  have oldLen (x) : (old x).length = 11 := by simp [old, seed]
  have newLen (x) : (start c x).length = 11 := by simp [start]
  have addrLow (i : ℕ) (hi : i < 11) (j : ℕ) (h : addr i = some j) : j < 11 ∨ j = 24 := by
    by_cases raw : i < 9
    · simp [addr, raw] at h
      have bound := (perm flip (Fin.ofNat 9 i)).isLt
      omega
    by_cases ten : i = 10
    · rw [show addr i = address d by simp [addr, ten]] at h
      fin_cases d <;> simp [address] at h <;> omega
    · simp [addr, raw, ten] at h
      omega
  have addrHigh (i : ℕ) (hi : 11 ≤ i) : addr i = some (min i 24) := by
    simp [addr, show ¬i < 9 by omega, show i ≠ 10 by omega]
  have addrBound (i j : ℕ) (h : addr i = some j) : j ≤ 24 := by
    by_cases hi : i < 11
    · rcases addrLow i hi j h with a | a <;> omega
    · rw [addrHigh i (by omega), Option.some.injEq] at h
      omega
  have rawRead (x : Fin 9 → Bool) (extra : List Bool) (v : Fin 9) :
      (List.ofFn x ++ extra).getD v.val false = x v := by
    rw [List.getD_append _ _ _ _ (by simp),
      List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have atNine (x : Fin 9 → Bool) (u v : Bool) :
      (List.ofFn x ++ [u,v]).getD 9 false = u := by
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
    rfl
  have atTen (x : Fin 9 → Bool) (u v : Bool) :
      (List.ofFn x ++ [u,v]).getD 10 false = v := by
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
    rfl
  have baseRead (x) (i : ℕ) (hi : i < 11) : (old x).getD i false = read (start c x) (addr i) := by
    by_cases raw : i < 9
    · let v : Fin 9 := ⟨i,raw⟩
      have vi : Fin.ofNat 9 i = v := Fin.ext (Nat.mod_eq_of_lt raw)
      have before := rawRead (row flip x) [row flip x 0 && row flip x 2,
        atom p (row flip x) && atom q (row flip x)] v
      have after := rawRead x [x 0 && x 2, bonus c x] (perm flip v)
      simpa only [old, seed, addr, raw, ite_true, vi, read, Option.elim_some, start,
        List.append_assoc, List.singleton_append, row] using before.trans after.symm
    · rcases (show i = 9 ∨ i = 10 by omega) with rfl | rfl
      · rw [show addr 9 = some 9 from rfl]
        simp only [old, seed, read, Option.elim_some, start, List.append_assoc,
          List.singleton_append, atNine, firstFixed]
      · rw [show addr 10 = address d from rfl]
        simpa only [old, seed, List.append_assoc, List.singleton_append, atTen] using aliasValue x
  have agree (x) (t : List Bool) (sz : 11 + t.length ≤ 24) (i : ℕ) :
      (old x ++ t).getD i false = read (start c x ++ t) (addr i) := by
    by_cases hi : i < 11
    · rw [List.getD_append _ _ _ _ (by rwa [oldLen]), baseRead x i hi]
      cases h : addr i with
      | none => rfl
      | some j =>
        change (start c x).getD j false = (start c x ++ t).getD j false
        rcases addrLow i hi j h with hj | rfl
        · exact (List.getD_append _ _ _ _ (by rwa [newLen])).symm
        · rw [List.getD_eq_default _ _ (by rw [newLen]; omega),
            List.getD_eq_default _ _ (by rw [List.length_append, newLen]; omega)]
    · rw [addrHigh i (by omega)]
      change _ = (start c x ++ t).getD (min i 24) false
      by_cases hi24 : i ≤ 24
      · rw [Nat.min_eq_left hi24, List.getD_append_right _ _ _ _ (by rw [oldLen]; omega),
          List.getD_append_right _ _ _ _ (by rw [newLen]; omega), oldLen, newLen]
      · rw [Nat.min_eq_right (by omega),
          List.getD_eq_default _ _ (by rw [List.length_append, oldLen]; omega),
          List.getD_eq_default _ _ (by rw [List.length_append, newLen]; omega)]
  let legal (g : Gate) :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  let val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
  let step (w : List Bool) (g : Gate) := w ++ [val g w]
  -- In the rewritten circuit, a missing address supplies true. Drop it from
  -- AND, propagate it through OR, and negate it only when NOT reads it first.
  let lower (op : GateOp) (ps : List (Option ℕ)) : Gate :=
    if op = .or ∧ none ∈ ps then ⟨.and, []⟩
    else if op = .not ∧ ps.head? = some none then ⟨.or, []⟩
    else ⟨op, ps.filterMap id⟩
  let mapped (g : Gate) := lower g.op (g.inputs.map addr)
  have ea (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have eo (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have en (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have goodGate (g : Gate) (hg : legal g) :
      legal (mapped g) ∧ ∀ j ∈ (mapped g).inputs, j ≤ 24 := by
    have plen : (g.inputs.map addr).length ≤ 2 := by simpa using hg.2
    dsimp only [mapped, lower]
    split
    · simp [legal]
    split
    · simp [legal]
    refine ⟨⟨hg.1, (List.length_filterMap_le _ _).trans plen⟩, ?_⟩
    intro j hj
    obtain ⟨v,hv,eq⟩ := List.mem_filterMap.mp hj
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
    exact addrBound i j eq
  have gateValue (op : GateOp) (ps : List (Option ℕ)) (hs : ps.length ≤ 2)
      (hop : op = .and ∨ op = .or ∨ op = .not) (w : List Bool) :
      val (lower op ps) w = op.eval (ps.map (read w)) := by
    rcases ps with _ | ⟨u,_ | ⟨v,_ | ⟨z,zs⟩⟩⟩
    · rcases hop with rfl | rfl | rfl <;> simp [lower, val, ea, eo, en]
    · rcases hop with rfl | rfl | rfl <;> cases u <;> simp [lower, val, read, ea, eo, en]
    · rcases hop with rfl | rfl | rfl <;> cases u <;> cases v <;> simp [lower, val, read, ea, eo, en]
    · simp at hs
  have simulate (gs : List Gate) (ok : ∀ g ∈ gs, legal g) (x) (t : List Bool)
      (sz : 11 + t.length + gs.length ≤ 24) :
      ∃ u, gs.foldl step (old x ++ t) = old x ++ u ∧
        (gs.map mapped).foldl step (start c x ++ t) = start c x ++ u ∧ 11 + u.length ≤ 24 := by
    induction gs generalizing t with
    | nil => exact ⟨t,rfl,rfl,by simpa using sz⟩
    | cons g gs ih =>
      simp only [List.length_cons] at sz
      have hg := ok g (by simp)
      let bit := val g (old x ++ t)
      have moved : val (mapped g) (start c x ++ t) = bit := by
        have hop := hg.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rw [show mapped g = lower g.op (g.inputs.map addr) by rfl,
          gateValue _ _ (by simpa using hg.2) hop, List.map_map]
        exact congrArg g.op.eval (List.map_congr_left fun i _ => (agree x t (by omega) i).symm)
      have left : step (old x ++ t) g = old x ++ (t ++ [bit]) := List.append_assoc ..
      have right : step (start c x ++ t) (mapped g) = start c x ++ (t ++ [bit]) := by
        simp only [step, moved, List.append_assoc]
      simp only [List.map_cons, List.foldl_cons, left, right]
      exact ih (fun v hv => ok v (List.mem_cons_of_mem _ hv)) (t ++ [bit]) (by
        simp only [List.length_append, List.length_singleton]; omega)
  by_contra! computes
  have original (x) : C.eval (old x) = f x := by
    have h : C.eval (seed (row flip x) ++ [GateOp.and.eval (pins.map fun i =>
      (seed (row flip x)).getD i false)]) = edges (row flip x) :=
      Classical.not_not.mp (computes (row flip x))
    rw [encode] at h
    exact h.trans (graph flip x)
  let gs := C.gates.map mapped
  have lengthC : C.gates.length ≤ 13 := small
  have mappedRead (x) : f x = read ((Circuit.mk gs 0).wires (start c x)) (addr C.output) := by
    obtain ⟨u, oldRun, newRun, cap⟩ := simulate C.gates fan x [] (by simp; omega)
    simp only [List.append_nil] at oldRun newRun
    rw [← original]
    change (C.gates.foldl step (old x)).getD C.output false =
      read ((C.gates.map mapped).foldl step (start c x)) (addr C.output)
    rw [oldRun, newRun, agree x u cap]
  cases hout : addr C.output with
  | none =>
    have h := mappedRead (fun _ => false)
    rw [hout] at h
    exact Bool.false_ne_true h
  | some o =>
    let D : Circuit := ⟨gs,o⟩
    have dok : FanInTwo D := by
      intro g hg
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
      exact (goodGate v (fan v hv)).1
    have pinsD : ∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 24 := by
      intro g hg
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
      exact (goodGate v (fan v hv)).2
    have dsize : D.size ≤ 13 := by
      change (C.gates.map mapped).length ≤ 13
      simpa only [List.length_map] using lengthC
    have outputBound : D.output ≤ 24 := addrBound _ _ hout
    have computesD (x) : D.eval (start c x) = f x := by
      have h := mappedRead x
      rw [hout] at h
      exact h.symm
    rcases List.mem_append.mp hc with hp | ht
    · have below : c < 100 := by
        have allSmall : ∀ e ∈ pairCodes, e < 100 := by decide
        exact allSmall c hp
      obtain ⟨x,hx⟩ := pairs c hp D dok dsize outputBound pinsD
      exact hx (by simpa only [start, bonus, ite_eq_left below] using computesD x)
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
      obtain ⟨x,hx⟩ := triples v hv D dok dsize outputBound pinsD
      have high : ¬ 100 + v < 100 := by omega
      have index : 100 + v - 100 = v := by omega
      exact hx (by simpa only [start, bonus, ite_eq_right high, index] using computesD x)

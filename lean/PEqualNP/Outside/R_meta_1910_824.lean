import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_1910_824
    (short : ∀ D : Circuit, FanInTwo D → (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6]) = ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))) → (let r := fun (i v : ℕ) => ∃ g : Gate, D.gates[i]? = some g ∧ (g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs); ∃ i j : ℕ, i < j ∧ r i 4 ∧ r j 6 ∧ (∀ k, r k 4 → k = i) ∧ (∀ k, r k 6 → k = j)) → 14 ≤ D.size)
    (exactSize : ∀ D : Circuit, D.size = 14 → FanInTwo D → (let r := fun (i v : ℕ) => ∃ g : Gate, D.gates[i]? = some g ∧ (g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs); ∃ i j : ℕ, i < j ∧ r i 4 ∧ r j 6 ∧ (∀ k, r k 4 → k = i) ∧ (∀ k, r k 6 → k = j)) → ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6]) ≠ ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →       (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →         (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)],             ∃! x7 : Fin (List.drop (1 : ℕ) x1.gates).length,               have x8 : PEqualNP.CircuitLowerBounds.Gate := (List.drop (1 : ℕ) x1.gates).get x7;               x8.inputs[(0 : ℕ)]? = Option.some x5 ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x8.inputs) →           (16 : ℕ) ≤ x1.size := by
  have orders : ∀ D : Circuit, FanInTwo D → (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6]) = ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))) →
      ((let r := fun (i v : ℕ) => ∃ g : Gate, D.gates[i]? = some g ∧ (g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs); ∃ i j : ℕ, i < j ∧ r i 4 ∧ r j 6 ∧ (∀ k, r k 4 → k = i) ∧ (∀ k, r k 6 → k = j)) ∨ (let r := fun (i v : ℕ) => ∃ g : Gate, D.gates[i]? = some g ∧ (g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs); ∃ i j : ℕ, i < j ∧ r i 6 ∧ r j 4 ∧ (∀ k, r k 6 → k = i) ∧ (∀ k, r k 4 → k = j))) → 15 ≤ D.size := by
    let flip : Fin 9 → Fin 9 := ![8,3,2,1,6,5,4,7,0]

    let wire (i : Nat) : Nat := if h : i < 9 then (flip ⟨i,h⟩).val else i

    have twice (i : Nat) : wire (wire i) = i := by
      by_cases h : i < 9
      · interval_cases i <;> decide
      · simp [wire,h]

    have fixWire {i : Nat} (h : 9 ≤ i) : wire i = i := by simp [wire, Nat.not_lt.mpr h]

    have below {i n : Nat} (h : i < n) (hn : 9 ≤ n) : wire i < n := by
      by_cases lo : i < 9
      · simp only [wire,dite_eq_left lo]
        exact lt_of_lt_of_le (flip ⟨i,lo⟩).isLt hn
      · simpa only [wire,dite_eq_right lo] using h

    let renameGate (g : Gate) : Gate := ⟨g.op, g.inputs.map wire⟩
    let rename (C : Circuit) : Circuit := ⟨C.gates.map renameGate, wire C.output⟩

    let reads (v : Nat) (g : Gate) : Prop :=
      g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs

    have reads_flip (v : Nat) (g : Gate) : reads v (renameGate g) ↔ reads (wire v) g := by
      have hw (u : Nat) : wire u = v ↔ u = wire v := by
        constructor
        · intro h; rw [← h,twice]
        · rintro rfl; exact twice v
      cases g with
      | mk op inputs =>
        cases inputs with
        | nil => simp [reads,renameGate]
        | cons u rest =>
          simp only [reads,renameGate,List.map_cons,List.getElem?_cons_zero,Option.some.injEq,
            List.mem_cons,List.mem_map]
          simp only [hw, eq_comm (a := v) (b := wire u)]
          constructor
          · rintro (h | ⟨h,h' | ⟨z,hz,eq⟩⟩)
            · exact Or.inl h
            · exact Or.inr ⟨h,Or.inl h'.symm⟩
            · exact Or.inr ⟨h,Or.inr (eq ▸ hz)⟩
          · rintro (h | ⟨h,h' | hz⟩)
            · exact Or.inl h
            · exact Or.inr ⟨h,Or.inl h'.symm⟩
            · exact Or.inr ⟨h,Or.inr ⟨_,hz,rfl⟩⟩

    let edge (x : Fin 9 → Bool) : Bool :=
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5

    have edge_flip : ∀ x : Fin 9 → Bool, edge (x ∘ flip) = edge x := by decide +kernel

    let start (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]

    let Rel (u v : List Bool) : Prop := ∀ i, u.getD i false = v.getD (wire i) false

    have start_rel (x : Fin 9 → Bool) : Rel (start (x ∘ flip)) (start x) := by
      intro i
      by_cases h : i < 10
      · interval_cases i <;> simp [start, wire, flip, List.ofFn_succ, Function.comp_def, Bool.or_comm]
      · rw [fixWire (by omega), List.getD_eq_default _ _ (by simp [start]; omega),
          List.getD_eq_default _ _ (by simp [start]; omega)]

    let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]

    have run_rel (gs : List Gate) (u v : List Bool) (ll : u.length = v.length) (hn : 9 ≤ u.length)
        (hr : Rel u v) : Rel (gs.foldl step u) ((gs.map renameGate).foldl step v) := by
      induction gs generalizing u v with
      | nil => exact hr
      | cons g t ih =>
        apply ih (step u g) (step v (renameGate g)) (by simp [step,ll]) (by simp [step]; omega)
        intro i
        by_cases hi : i < u.length
        · have hi' : wire i < v.length := ll ▸ below hi hn
          simpa only [step,List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ hi'] using hr i
        · have val : g.op.eval (g.inputs.map fun i => u.getD i false) =
              (renameGate g).op.eval ((renameGate g).inputs.map fun i => v.getD i false) := by
            simp only [renameGate,List.map_map,Function.comp_def]
            exact congrArg g.op.eval (List.map_congr_left (fun j _ => hr j))
          rw [fixWire (by omega)]
          simp only [step,List.getD_append_right _ _ _ _ (show u.length ≤ i by omega),
            List.getD_append_right _ _ _ _ (show v.length ≤ i by omega),ll,val]

    have eval_flip (C : Circuit) (x : Fin 9 → Bool) :
        (rename C).eval (start x) = C.eval (start (x ∘ flip)) := by
      exact (run_rel C.gates _ _ (by simp [start]) (by simp [start]) (start_rel x) C.output).symm

    have fan_flip {C : Circuit} (h : FanInTwo C) : FanInTwo (rename C) := by
      intro g hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
      simpa [renameGate] using h q hq

    let atGate (t : List Gate) (i v : Nat) : Prop := ∃ g, t[i]? = some g ∧ reads v g

    have at_flip (t : List Gate) (i v : Nat) :
        atGate (t.map renameGate) i v ↔ atGate t i (wire v) := by
      cases h : t[i]? <;> simp [atGate,List.getElem?_map,h,reads_flip]

    let ordered (t : List Gate) (v w : Nat) : Prop := ∃ i j : Nat,
      i < j ∧ atGate t i v ∧ atGate t j w ∧
        (∀ k, atGate t k v → k = i) ∧ (∀ k, atGate t k w → k = j)

    have order_flip (t : List Gate) (v w : Nat) :
        ordered (t.map renameGate) v w ↔ ordered t (wire v) (wire w) := by
      simp only [ordered,at_flip]

    let boundFor (v w : Nat) := ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (start x) = edge x) → ordered D.gates v w → 15 ≤ D.size

    have reverse_order (h : boundFor 4 6) : boundFor 6 4 := by
      intro D hf he ho
      have good (x : Fin 9 → Bool) : (rename D).eval (start x) = edge x :=
        (eval_flip D x).trans ((he _).trans (edge_flip x))
      have horder : ordered (rename D).gates 4 6 := (order_flip D.gates 4 6).mpr ho
      have floor := h (rename D) (fan_flip hf) good horder
      change 15 ≤ (D.gates.map renameGate).length at floor
      change 15 ≤ D.gates.length
      simpa only [List.length_map] using floor

    let pack := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))
    have same : ∀ x, pack x = edge x := by decide +kernel
    have forward : boundFor 4 6 := by
      intro D hf he ho
      have hp (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 4 || x 6]) = pack x :=
        (he x).trans (same x).symm
      have lo := short D hf hp ho
      by_contra! h
      have eq : D.size = 14 := by omega
      obtain ⟨x,hx⟩ := exactSize D eq hf ho
      exact hx (hp x)
    intro D hf hp cases
    have he (x : Fin 9 → Bool) : D.eval (start x) = edge x := (hp x).trans (same x)
    rcases cases with h | h
    · exact forward D hf he h
    · exact reverse_order forward D hf he h
  intro C hf first computes uniqueRead
  obtain ⟨gates, out⟩ := C
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserve (t : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
      (t.foldl step w).getD j false = w.getD j false := by
    induction t generalizing w with
    | nil => rfl
    | cons g t ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hj
  cases gates with
  | nil =>
    have h := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
    rw [List.getD_eq_default _ _ (by simp)] at h
    contradiction
  | cons g t =>
    let D := Circuit.mk t out
    let start (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
    have headVal (x : Fin 9 → Bool) : step (List.ofFn x) g = start x := by
      have h := first x
      change (t.foldl step (step (List.ofFn x) g)).getD 9 false = _ at h
      rw [preserve _ _ _ (by simp [step])] at h
      have idx : (List.ofFn x).length = 9 := by simp
      change (_ ++ [_]).getD 9 false = _ at h
      rw [List.getD_append_right _ _ _ _ (Nat.le_of_eq idx), idx] at h
      change List.ofFn x ++ [_] = List.ofFn x ++ [_]
      exact congrArg (fun b => List.ofFn x ++ [b]) (by simpa using h)
    have evalEq (x : Fin 9 → Bool) :
        (Circuit.mk (g :: t) out).eval (List.ofFn x) = D.eval (start x) := by
      change (t.foldl step (step (List.ofFn x) g)).getD out false = _
      rw [headVal]
      rfl
    have basis : FanInTwo D := fun q hq => hf q (List.mem_cons_of_mem _ hq)
    have evalF (x : Fin 9 → Bool) :
        D.eval (start x) = ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9))) := by
      rw [← evalEq]
      have h := congrFun computes x
      refine h.trans ?_
      simp [List.any_cons, Bool.or_assoc, Fin.ofNat]
    let rd (v : Nat) (q : Gate) := q.inputs[0]? = some v ∨ q.op ≠ GateOp.not ∧ v ∈ q.inputs
    obtain ⟨a, ha, ua⟩ := uniqueRead 4 (by simp)
    obtain ⟨b, hb, ub⟩ := uniqueRead 6 (by simp)
    change rd 4 (t.get a) at ha
    change rd 6 (t.get b) at hb
    change ∀ i : Fin t.length, rd 4 (t.get i) → i = a at ua
    change ∀ i : Fin t.length, rd 6 (t.get i) → i = b at ub
    have distinct : a ≠ b := by
      intro same
      have paired (q : Gate) (hq : q ∈ t) : rd 4 q ↔ rd 6 q := by
        obtain ⟨i, eq⟩ := List.mem_iff_get.mp hq
        subst q
        constructor
        · intro h
          simpa only [ua i h, same] using hb
        · intro h
          simpa only [ub i h, ← same] using ha
      let X : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4)
      let Y : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 6)
      let sw (i : Nat) := if i = 4 then 6 else if i = 6 then 4 else i
      have gateEq (q : Gate) (hq : q ∈ t) (u v : List Bool)
          (rel : ∀ i, u.getD i false = v.getD (sw i) false) :
          q.op.eval (q.inputs.map fun i => u.getD i false) =
          q.op.eval (q.inputs.map fun i => v.getD i false) := by
        have pair := paired q hq
        obtain ⟨hop, len⟩ := basis q hq
        change q.op = .and ∨ q.op = .or ∨ q.op = .not at hop
        obtain ⟨op, ins⟩ := q
        cases ins with
        | nil => rfl
        | cons i rest =>
          cases rest with
          | nil =>
            have hi : i ≠ 4 ∧ i ≠ 6 := by
              simp [rd] at pair
              grind
            have e := rel i
            simp only [sw, ite_eq_right hi.1, ite_eq_right hi.2] at e
            exact congrArg (fun bit => op.eval [bit]) e
          | cons j rest =>
            cases rest with
            | cons k r => simp at len
            | nil =>
              simp only at hop
              have unchanged (a : Nat) (h4 : a ≠ 4) (h6 : a ≠ 6) :
                  u.getD a false = v.getD a false := by simpa only [sw, ite_eq_right h4, ite_eq_right h6] using rel a
              have four : u.getD 4 false = v.getD 6 false := rel 4
              have six : u.getD 6 false = v.getD 4 false := rel 6
              rcases hop with h | h | h <;> subst op
              · change (u.getD i false && (u.getD j false && true)) = (v.getD i false && (v.getD j false && true))
                simp only [Bool.and_true, Bool.or_false]
                simp [rd] at pair
                have shape : (i = 4 ∧ j = 6) ∨ (i = 6 ∧ j = 4) ∨ (i ≠ 4 ∧ i ≠ 6 ∧ j ≠ 4 ∧ j ≠ 6) := by grind
                rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨i4,i6,j4,j6⟩
                · rw [four,six,Bool.and_comm (v.getD 6 false)]
                · rw [four,six,Bool.and_comm (v.getD 6 false)]
                · rw [unchanged i i4 i6, unchanged j j4 j6]
              · change (u.getD i false || (u.getD j false || false)) = (v.getD i false || (v.getD j false || false))
                simp only [Bool.and_true, Bool.or_false]
                simp [rd] at pair
                have shape : (i = 4 ∧ j = 6) ∨ (i = 6 ∧ j = 4) ∨ (i ≠ 4 ∧ i ≠ 6 ∧ j ≠ 4 ∧ j ≠ 6) := by grind
                rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨i4,i6,j4,j6⟩
                · rw [four,six,Bool.or_comm (v.getD 6 false)]
                · rw [four,six,Bool.or_comm (v.getD 6 false)]
                · rw [unchanged i i4 i6, unchanged j j4 j6]
              · simp [rd] at pair
                have hi : i ≠ 4 ∧ i ≠ 6 := by grind
                exact congrArg Bool.not (unchanged i hi.1 hi.2)
      have lift (l : List Gate) (sub : ∀ q ∈ l, q ∈ t) (u v : List Bool)
          (len : u.length = v.length) (base : 6 < u.length)
          (rel : ∀ i, u.getD i false = v.getD (sw i) false) :
          ∀ i, (l.foldl step u).getD i false = (l.foldl step v).getD (sw i) false := by
        induction l generalizing u v with
        | nil => exact rel
        | cons q qs ih =>
          apply ih (fun r hr => sub r (List.mem_cons_of_mem _ hr)) (step u q) (step v q)
              (by simp [step,len]) (by simp [step]; omega)
          intro i
          by_cases lo : i < u.length
          · have lo' : sw i < v.length := by
              dsimp [sw]
              split
              · omega
              · split <;> omega
            simpa only [step, List.getD_append _ _ _ _ lo, List.getD_append _ _ _ _ lo'] using rel i
          · have fix : sw i = i := by simp [sw, show i ≠ 4 by omega, show i ≠ 6 by omega]
            rw [fix]
            simp only [step, List.getD_append_right _ _ _ _ (show u.length ≤ i by omega),
              List.getD_append_right _ _ _ _ (show v.length ≤ i by omega),
              gateEq q (sub q (by simp)) u v rel, len]
      have startRel : ∀ i, (start X).getD i false = (start Y).getD (sw i) false := by
        intro i
        by_cases small : i < 10
        · interval_cases i <;> decide
        · have fix : sw i = i := by simp [sw, show i ≠ 4 by omega, show i ≠ 6 by omega]
          rw [fix, List.getD_eq_default _ _ (by simp [start]; omega),
            List.getD_eq_default _ _ (by simp [start]; omega)]
      have fix : sw out = out := by
        let z : Fin 9 → Bool := fun i => decide (i = 4 ∨ i = 6)
        have e := congrFun computes z
        change (List.foldl step (List.ofFn z) (g :: t)).getD out false = false at e
        by_cases h4 : out = 4
        · rw [h4, preserve _ _ _ (by simp)] at e
          contradiction
        by_cases h6 : out = 6
        · rw [h6, preserve _ _ _ (by simp)] at e
          contradiction
        simp [sw,h4,h6]
      have eq := lift t (fun _ h => h) (start X) (start Y) (by simp [start]) (by simp [start]) startRel out
      rw [fix] at eq
      change D.eval (start X) = D.eval (start Y) at eq
      rw [evalF, evalF] at eq
      exact (by decide : ¬ (([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun e => X (Fin.ofNat 9 (e / 9)) && X (Fin.ofNat 9 (e % 9))) =
        ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun e => Y (Fin.ofNat 9 (e / 9)) && Y (Fin.ofNat 9 (e % 9))))) eq
    have liftOrder (a b : Fin t.length) (v w : Nat) (hab : a < b)
        (ha : rd v (t.get a)) (hb : rd w (t.get b))
        (ua : ∀ k : Fin t.length, rd v (t.get k) → k = a)
        (ub : ∀ k : Fin t.length, rd w (t.get k) → k = b) :
        (let r := fun (i v : ℕ) => ∃ g : Gate, D.gates[i]? = some g ∧ (g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs); ∃ i j : ℕ, i < j ∧ r i v ∧ r j w ∧ (∀ k, r k v → k = i) ∧ (∀ k, r k w → k = j)) := by
      dsimp only
      have present (c : Fin t.length) (z : Nat) (h : rd z (t.get c)) :
          ∃ g : Gate, D.gates[c.val]? = some g ∧ rd z g :=
        ⟨t.get c, List.getElem?_eq_getElem c.isLt,h⟩
      have uniq (z : Nat) (c : Fin t.length) (u : ∀ k : Fin t.length, rd z (t.get k) → k = c)
          (k : Nat) (h : ∃ g : Gate, D.gates[k]? = some g ∧ rd z g) : k = c.val := by
        obtain ⟨g,hg,hr⟩ := h
        change t[k]? = some g at hg
        have hk : k < t.length := by
          by_contra! n
          rw [List.getElem?_eq_none n] at hg
          contradiction
        have eg : t.get ⟨k,hk⟩ = g := by simpa [List.getElem?_eq_getElem hk] using hg
        exact congrArg Fin.val (u ⟨k,hk⟩ (eg ▸ hr))
      exact ⟨a.val,b.val,hab,present a v ha,present b w hb,uniq v a ua,uniq w b ub⟩
    have bound : 15 ≤ t.length := by
      rcases lt_or_gt_of_ne distinct with left | right
      · exact orders D basis evalF (Or.inl (liftOrder a b 4 6 left ha hb ua ub))
      · exact orders D basis evalF (Or.inr (liftOrder b a 6 4 right hb ha ub ua))
    change 16 ≤ (g :: t).length
    simpa using bound

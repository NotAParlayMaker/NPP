import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3500000 in
theorem PEqualNP.Outside.R_meta_3057_417
    (binary : let edge := fun x : Fin 9 → Bool => ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ D : Circuit, FanInTwo D → (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = edge x) →
        13 ≤ D.gates.countP (fun g => g.op.eval [true]))
    (andCase : let edge := fun x : Fin 9 → Bool => ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ (C : Circuit) (p : Fin 11) (i j : ℕ), Monotone2 C → C.size = 12 →
      11 ≤ i → i < j → j = 22 →
      (∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [!x 0]
        let V := (C.wires (w ++ [!(w.getD p.val false)])).getD
        (V i false && V j false) = edge x) → False)
    (orCase : let edge := fun x : Fin 9 → Bool => ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ (C : Circuit) (p : Fin 11) (i j : ℕ), Monotone2 C → C.size = 12 →
      11 ≤ i → i < j → j = 22 →
      (∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [!x 0]
        let V := (C.wires (w ++ [!(w.getD p.val false)])).getD
        (V i false || V j false) = edge x) → False) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (512 : ℕ)),             have x7 : Fin (9 : ℕ) → Bool := fun (x7 : Fin (9 : ℕ)) => Decidable.decide (↑x6 / (2 : ℕ) ^ (↑x7 % (9 : ℕ)) % (2 : ℕ) = (1 : ℕ));             have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];             x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x9.1 && x7 x9.2 := by
  let edge (x : Fin 9 → Bool) := ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let w (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  let decode (m : Fin 512) (i : Fin 9) := decide (m.val / 2 ^ (i.val % 9) % 2 = 1)
  intro pins pinSize C fan size
  by_contra! agrees
  have encode (x : Fin 9 → Bool) : ∃ m : Fin 512, decode m = x := by
    let pack (bits : List (Fin 9)) : ℕ := bits.foldr (fun i rest => 2 ^ i.val ||| rest) 0
    have bound (bits : List (Fin 9)) : pack bits < 512 := by
      induction bits with
      | nil => decide
      | cons i rest ih =>
        have hi : 2 ^ i.val < 2 ^ 9 := Nat.pow_lt_pow_right (by decide) i.isLt
        exact Nat.or_lt_two_pow hi ih
    have bit (bits : List (Fin 9)) (i : Fin 9) :
        (pack bits).testBit i.val = decide (i ∈ bits) := by
      induction bits with
      | nil => simp [pack]
      | cons j js ih =>
        change (2 ^ j.val ||| pack js).testBit i.val = _
        rw [Nat.testBit_or, Nat.testBit_two_pow, ih]
        by_cases same : i = j
        · subst j
          simp
        · have ne : j.val ≠ i.val := fun h => same (Fin.ext h.symm)
          simp [same, ne]
    let bits := (List.finRange 9).filter x
    refine ⟨⟨pack bits, bound bits⟩, funext (fun i => ?_)⟩
    change decide (pack bits / 2 ^ (i.val % 9) % 2 = 1) = x i
    rw [Nat.mod_eq_of_lt i.isLt, ← Nat.testBit_eq_decide_div_mod_eq, bit]
    simp [bits]
  let p : Fin 11 := ⟨min (pins.headD 10) 10, by omega⟩
  let base (x : Fin 9 → Bool) := w x ++ [!((w x).getD p.val false)]
  have wLen (x : Fin 9 → Bool) : (w x).length = 10 := by simp [w]
  have baseLen (x : Fin 9 → Bool) : (base x).length = 11 := by simp [base, wLen]
  have normalized (x : Fin 9 → Bool) :
      GateOp.not.eval (pins.map fun i => (w x).getD i false) = !((w x).getD p.val false) := by
    cases pins with
    | nil =>
      change true = !(w x).getD 10 false
      rw [List.getD_eq_default _ _ (by rw [wLen])]
      rfl
    | cons h t =>
      change (!( (w x).getD h false)) = !( (w x).getD (min h 10) false)
      by_cases hi : h ≤ 10
      · rw [Nat.min_eq_left hi]
      · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by rw [wLen]; omega),
          List.getD_eq_default _ _ (by rw [wLen])]
  have computes (x : Fin 9 → Bool) : C.eval (base x) = edge x := by
    obtain ⟨m, hm⟩ := encode x
    have eq : C.eval (w (decode m) ++ [GateOp.not.eval (pins.map fun i => (w (decode m)).getD i false)]) =
        edge (decode m) := not_not.mp (agrees m)
    rw [hm, normalized] at eq
    exact eq
  let B (P : Circuit) : Circuit := ⟨⟨.not,[0]⟩ :: ⟨.not,pins⟩ :: P.gates, P.output⟩
  have first (x : Fin 9 → Bool) :
      GateOp.not.eval [(List.ofFn x).getD 0 false] = !x 0 := by
    have h : (List.ofFn x).getD 0 false = x 0 := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      rfl
    rw [h]
    rfl
  have count (P : Circuit) (hf : FanInTwo P) (hc : ∀ x, P.eval (base x) = edge x) :
      13 ≤ P.gates.countP (fun g => g.op.eval [true]) := by
    have fullFan : FanInTwo (B P) := by
      intro g hg
      change g ∈ ⟨.not,[0]⟩ :: ⟨.not,pins⟩ :: P.gates at hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · simp
      · exact ⟨by simp, pinSize⟩
      · exact hf _ hg
    have full (x : Fin 9 → Bool) : (B P).eval (List.ofFn x) = edge x := by
      let u := List.ofFn x ++ [GateOp.not.eval [(List.ofFn x).getD 0 false]]
      change P.eval (u ++ [GateOp.not.eval (pins.map fun i => u.getD i false)]) = edge x
      have eq : u = w x := by dsimp only [u,w]; rw [first]
      rw [eq, normalized]
      exact hc x
    exact binary (B P) fullFan full
  have noShort (P : Circuit) (hf : FanInTwo P) (h : P.gates.length < 13)
      (hc : ∀ x, P.eval (base x) = edge x) : False := by
    have lower := count P hf hc
    have upper := List.countP_le_length (l := P.gates) (p := fun g => g.op.eval [true])
    omega
  have limit : C.gates.length ≤ 13 := size
  have countC := count C fan computes
  have upper := List.countP_le_length (l := C.gates) (p := fun g => g.op.eval [true])
  have exactSize : C.gates.length = 13 := by omega
  have mono : Monotone2 C := by
    intro g hg
    have all : C.gates.countP (fun g => g.op.eval [true]) = C.gates.length := by omega
    have keeps : g.op.eval [true] = true := List.countP_eq_length.mp all g hg
    obtain ⟨kind, len⟩ := fan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at kind ⊢
    rcases kind with ho | ho | ho
    · exact ⟨Or.inl ho,len⟩
    · exact ⟨Or.inr ho,len⟩
    · rw [ho] at keeps
      exact Bool.noConfusion keeps
  have zero : edge (fun _ => false) = false := rfl
  have unit : edge (fun _ => true) = true := rfl
  have nonconstant (q : Bool) : ¬ ∀ x, q = edge x := by
    intro h
    have z := h (fun _ => false)
    have t := h (fun _ => true)
    rw [zero] at z
    rw [unit] at t
    cases q <;> contradiction
  let witness (y : Bool) (i : Fin 10) (b : Bool) :=
    decode ⟨(if y then [6, 3, 12, 3, 3, 6, 3, 11, 3, 17, 3, 33, 3, 66, 3, 131, 3, 259, 3, 6] else [0, 1, 0, 2, 0, 4, 0, 8, 0, 16, 0, 32, 0, 64, 0, 128, 0, 256, 1, 0] : List ℕ).getD (2*i.val+b.toNat) 0, by
      have small : ∀ (y : Bool) (i : Fin 10) (b : Bool),
        (if y then [6, 3, 12, 3, 3, 6, 3, 11, 3, 17, 3, 33, 3, 66, 3, 131, 3, 259, 3, 6] else [0, 1, 0, 2, 0, 4, 0, 8, 0, 16, 0, 32, 0, 64, 0, 128, 0, 256, 1, 0] : List ℕ).getD (2*i.val+b.toNat) 0 < 512 := by decide
      exact small y i b⟩
  have contrast : ∀ (y : Bool) (i : Fin 10) (b : Bool),
      edge (witness y i b) = y ∧ (w (witness y i b)).getD i.val false = b := by decide +kernel
  let step (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
  have length (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step, Nat.add_left_comm, Nat.add_comm]
  have retain (gs : List Gate) (xs : List Bool) (i : ℕ) (h : i < xs.length) :
      (gs.foldl step xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ h
  obtain ⟨gs,g,hgs⟩ : ∃ gs g, C.gates = gs ++ [g] := by
    rcases C.gates.eq_nil_or_concat' with empty | form
    · rw [empty] at exactSize
      contradiction
    · exact form
  let P (o : ℕ) : Circuit := ⟨gs,o⟩
  let V (x : Fin 9 → Bool) := gs.foldl step (base x)
  have n : gs.length = 12 := by
    rw [hgs, List.length_append, List.length_singleton] at exactSize
    omega
  have pFan (o : ℕ) : FanInTwo (P o) := fun k hk => fan k (hgs ▸ List.mem_append_left [g] hk)
  have pMono (o : ℕ) : Monotone2 (P o) := fun k hk => mono k (hgs ▸ List.mem_append_left [g] hk)
  have lenV (x : Fin 9 → Bool) : (V x).length = 23 := by rw [length, baseLen, n]
  have extended (x : Fin 9 → Bool) : (step (V x) g).getD C.output false = edge x := by
    have h := computes x
    change (C.gates.foldl step (base x)).getD C.output false = edge x at h
    rw [hgs, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    exact h
  have output : C.output = 23 := by
    by_contra ne
    by_cases h : C.output < 23
    · apply noShort (P C.output) (pFan _) (by change gs.length < 13; omega)
      intro x
      have eq := extended x
      change ((V x) ++ [_]).getD C.output false = _ at eq
      rw [List.getD_append _ _ _ _ (by rwa [lenV])] at eq
      exact eq
    · apply nonconstant false
      intro x
      have eq := extended x
      rwa [List.getD_eq_default _ _ (by simp [step,lenV]; omega)] at eq
  have eval (x : Fin 9 → Bool) :
      g.op.eval (g.inputs.map fun i => (V x).getD i false) = edge x := by
    have eq := extended x
    rw [output, ← lenV x] at eq
    change ((V x) ++ [_]).getD (V x).length false = _ at eq
    rwa [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self] at eq
  have descend (i : ℕ) (hc : ∀ x, (V x).getD i false = edge x) : False :=
    noShort (P i) (pFan _) (by change gs.length < 13; omega) hc
  have actualWire (i : ℕ) (bit : Bool)
      (needs : ∀ x, edge x = bit → (V x).getD i false = bit)
      (contract : (∀ x, (V x).getD i false = bit) → False) : 11 ≤ i ∧ i < 23 := by
    by_contra outside
    have low (k : Fin 10) (x : Fin 9 → Bool) : (V x).getD k.val false = (w x).getD k.val false := by
      change (gs.foldl step (base x)).getD k.val false = _
      rw [retain gs (base x) _ (by rw [baseLen]; omega)]
      exact List.getD_append _ _ _ _ (by rw [wLen]; exact k.isLt)
    by_cases small : i < 10
    · let k : Fin 10 := ⟨i,small⟩
      have con := contrast bit k (!bit)
      have hs := needs _ con.1
      rw [show i = k.val from rfl, low, con.2] at hs
      cases bit <;> contradiction
    by_cases ten : i = 10
    · have at10 (x : Fin 9 → Bool) : (V x).getD i false = !((w x).getD p.val false) := by
        rw [ten]
        change (gs.foldl step (base x)).getD 10 false = _
        rw [retain gs (base x) _ (by rw [baseLen]; omega)]
        change ((w x) ++ [_]).getD 10 false = _
        rw [List.getD_append_right _ _ _ _ (by rw [wLen]), wLen]
        rfl
      by_cases pin : p.val < 10
      · let k : Fin 10 := ⟨p.val,pin⟩
        have eq := contrast bit k bit
        have hs := needs _ eq.1
        rw [at10, show p.val = k.val from rfl, eq.2] at hs
        cases bit <;> contradiction
      · have fixed (x : Fin 9 → Bool) : (V x).getD i false = true := by
          rw [at10, List.getD_eq_default _ _ (by rw [wLen]; omega)]
          rfl
        have eq := contrast bit 0 false
        have mark : true = bit := (fixed _).symm.trans (needs _ eq.1)
        exact contract (fun x => (fixed x).trans mark)
    · have fixed (x : Fin 9 → Bool) : (V x).getD i false = false :=
        List.getD_eq_default _ _ (by rw [lenV]; omega)
      have eq := contrast bit 0 false
      have mark : false = bit := (fixed _).symm.trans (needs _ eq.1)
      exact contract (fun x => (fixed x).trans mark)
  obtain ⟨mode, arity⟩ := mono g (by rw [hgs]; simp)
  have mode' : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using mode
  cases pinsG : g.inputs with
  | nil =>
    apply nonconstant (g.op.eval [])
    intro x
    simpa only [pinsG, List.map_nil] using eval x
  | cons a rest =>
    cases rest with
    | nil =>
      apply descend a
      intro x
      have h := eval x
      rcases mode' with op | op
      · rw [pinsG, op] at h
        change ((V x).getD a false && true) = edge x at h
        rwa [Bool.and_true] at h
      · rw [pinsG, op] at h
        change ((V x).getD a false || false) = edge x at h
        rwa [Bool.or_false] at h
    | cons b rest =>
      have restEmpty : rest = [] := by
        rw [pinsG, List.length_cons, List.length_cons] at arity
        exact List.eq_nil_of_length_eq_zero (by omega)
      have gateInputs : g.inputs = [a,b] := by rw [pinsG,restEmpty]
      have reject (t : Bool) (op : g.op = if t then GateOp.and else GateOp.or) : False := by
        let combine (u v : Bool) := if t then u && v else u || v
        have eq (x : Fin 9 → Bool) : combine ((V x).getD a false) ((V x).getD b false) = edge x := by
          have h := eval x
          cases t
          · have orOp : g.op = GateOp.or := op
            rw [gateInputs, orOp] at h
            change ((V x).getD a false || ((V x).getD b false || false)) = edge x at h
            rwa [Bool.or_false] at h
          · have andOp : g.op = GateOp.and := op
            rw [gateInputs, andOp] at h
            change ((V x).getD a false && ((V x).getD b false && true)) = edge x at h
            rwa [Bool.and_true] at h
        have force : ∀ (t u v : Bool), (if t then u && v else u || v) = t → u = t ∧ v = t := by decide
        have neutralL (v : Bool) : combine t v = v := by cases t <;> cases v <;> rfl
        have neutralR (v : Bool) : combine v t = v := by cases t <;> cases v <;> rfl
        have same (v : Bool) : combine v v = v := by cases t <;> cases v <;> rfl
        have commute (u v : Bool) : combine u v = combine v u := by cases t <;> cases u <;> cases v <;> rfl
        have aLive := actualWire a t
          (fun x hx => (force t _ _ ((eq x).trans hx)).1)
          (fun redundant => descend b fun x => by simpa only [redundant x, neutralL] using eq x)
        have bLive := actualWire b t
          (fun x hx => (force t _ _ ((eq x).trans hx)).2)
          (fun redundant => descend a fun x => by simpa only [redundant x, neutralR] using eq x)
        have distinct : a ≠ b := by
          intro sameWire
          exact descend a (fun x => by simpa only [← sameWire, same] using eq x)
        have usesLatest : a = 22 ∨ b = 22 := by
          by_contra! skip
          have nonempty : gs ≠ [] := by intro empty; simp [empty] at n
          let pre := gs.dropLast
          let last := gs.getLast nonempty
          have split : pre ++ [last] = gs := List.dropLast_append_getLast nonempty
          have preLen : pre.length = 11 := by
            have h := congrArg List.length split
            simp only [List.length_append, List.length_singleton, n] at h
            omega
          let D : Circuit := ⟨pre ++ [g], 22⟩
          have shorter : D.gates.length < 13 := by simp [D,preLen]
          have fanD : FanInTwo D := by
            intro k hk
            apply fan k
            rw [hgs, ← split, List.mem_append, List.mem_append]
            rcases List.mem_append.mp hk with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
          apply noShort D fanD shorter
          intro x
          let T := pre.foldl step (base x)
          have tLen : T.length = 22 := (length pre _).trans (by rw [baseLen,preLen])
          have keeps (i : ℕ) (iLt : i < 22) : (V x).getD i false = T.getD i false := by
            change (gs.foldl step (base x)).getD i false = _
            rw [← split, List.foldl_append]
            exact retain [last] T i (by rwa [tLen])
          change ((pre ++ [g]).foldl step (base x)).getD 22 false = _
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← tLen]
          change (T ++ [_]).getD T.length false = _
          rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
          change g.op.eval (g.inputs.map fun i => T.getD i false) = edge x
          have h := eval x
          rw [gateInputs, List.map_cons, List.map_cons, List.map_nil] at h ⊢
          rw [← keeps a (by omega), ← keeps b (by omega)]
          exact h
        have terminal (i j : ℕ) (low : 11 ≤ i) (order : i < j) (last : j = 22)
            (he : ∀ x, combine ((V x).getD i false) ((V x).getD j false) = edge x) : False := by
          cases t
          · exact orCase (P 0) p i j (pMono _) n low order last he
          · exact andCase (P 0) p i j (pMono _) n low order last he
        rcases usesLatest with latest | latest
        · exact terminal b a bLive.1 (by omega) latest (fun x => (commute _ _).trans (eq x))
        · exact terminal a b aLive.1 (by omega) latest eq
      rcases mode' with op | op
      · exact reject true op
      · exact reject false op

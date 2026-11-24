import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_3917_3
    (hFar : ∀ (C : BinaryCircuit) (phase : Bool) (hpos : 0 < C.size),
      (∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
      (∀ j : Fin C.size, (C.gates.get j).left < (C.gates.get j).right ∧
        (C.gates.get j).right < 10 + j.val) →
      C.output = 10 + C.size - 1 →
      (C.gates.get ⟨0, hpos⟩).right = 9 →
      2 ≤ (C.gates.get ⟨0, hpos⟩).left →
      (∀ x : Fin 9 → Bool,
        (C.eval (List.ofFn x ++ [x 0 || x 1]) != phase) =
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List Nat).any
            (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) →
      14 ≤ C.size)
    (hNear : ∀ (C : BinaryCircuit) (phase : Bool) (hpos : 0 < C.size),
      (∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
      (∀ j : Fin C.size, (C.gates.get j).left < (C.gates.get j).right ∧
        (C.gates.get j).right < 10 + j.val) →
      C.output = 10 + C.size - 1 →
      (C.gates.get ⟨0, hpos⟩).right = 9 →
      (C.gates.get ⟨0, hpos⟩).left ≤ 1 →
      (∃ a b : Bool, (C.gates.get ⟨0, hpos⟩).op = fun x y => (x == a) && (y == b) ∧
        a = false ∧ b = true) →
      (∀ x : Fin 9 → Bool,
        (C.eval (List.ofFn x ++ [x 0 || x 1]) != phase) =
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List Nat).any
            (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) →
      14 ≤ C.size) :
    have x1 : PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x1 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ x2 ∈ x1.gates, ∃ (x4 : Bool) (x5 : Bool), x2.op = fun (x6 x7 : Bool) => x6 == x4 && x7 == x5; have x2 : ℕ → PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x2 : ℕ) (x3 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ (x4 : Fin x3.size), (x3.gates.get x4).left < (x3.gates.get x4).right ∧ (x3.gates.get x4).right < x2 + ↑x4; have x3 : (Fin (9 : ℕ) → Bool) → Bool := fun (x3 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x4 : ℕ) => x3 (Fin.ofNat (9 : ℕ) (x4 / (10 : ℕ))) && x3 (Fin.ofNat (9 : ℕ) (x4 % (10 : ℕ))); ∀ (x4 : PEqualNP.MetaComplexity.BinaryCircuit) (x5 : Bool) (x6 : (0 : ℕ) < x4.size), x1 x4 → x2 (10 : ℕ) x4 → x4.output = (10 : ℕ) + x4.size - (1 : ℕ) → (x4.gates.get (⟨(0 : ℕ), x6⟩ : Fin x4.gates.length)).right = (9 : ℕ) → (∀ (x11 : Fin (9 : ℕ) → Bool), (x4.eval (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ))]) != x5) = x3 x11) → (14 : ℕ) ≤ x4.size := by
  dsimp only
  intro C phase pos sg ordered last first sem
  have size_rfl (B : BinaryCircuit) : B.size = B.gates.length := rfl
  have eval_rfl (B : BinaryCircuit) (x : List Bool) :
      B.eval x = (B.wires x).getD B.output false := rfl
  let edge (x : Fin 9 → Bool) : Bool :=
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List Nat).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have sem_edge (x : Fin 9 → Bool) :
      (C.eval (List.ofFn x ++ [x 0 || x 1]) != phase) = edge x := by
    simpa [edge] using sem x
  have notConst : ∀ (b ph : Bool), ¬ ∀ x : Fin 9 → Bool, (b != ph) = edge x := by
    decide +kernel
  have notIn : ∀ (i : Fin 10) (fl ph : Bool),
      ¬ ∀ x : Fin 9 → Bool,
        (((if h : i.val < 9 then x ⟨i.val, h⟩ else x 0 || x 1) != fl) != ph) = edge x := by
    decide +kernel
  have idTT0 : ∀ x : Fin 9 → Bool, ((x 0 == true) && ((x 0 || x 1) == true)) = x 0 := by
    decide +kernel
  have idTT1 : ∀ x : Fin 9 → Bool, ((x 1 == true) && ((x 0 || x 1) == true)) = x 1 := by
    decide +kernel
  have idFF0 : ∀ x : Fin 9 → Bool,
      ((x 0 == false) && ((x 0 || x 1) == false)) = !(x 0 || x 1) := by
    decide +kernel
  have idFF1 : ∀ x : Fin 9 → Bool,
      ((x 1 == false) && ((x 0 || x 1) == false)) = !(x 0 || x 1) := by
    decide +kernel
  have idTF0 : ∀ x : Fin 9 → Bool, ((x 0 == true) && ((x 0 || x 1) == false)) = false := by
    decide +kernel
  have idTF1 : ∀ x : Fin 9 → Bool, ((x 1 == true) && ((x 0 || x 1) == false)) = false := by
    decide +kernel
  let M := Bool × ℕ × Bool
  let mval (w : List Bool) (m : M) : Bool :=
    if m.1 = true then m.2.2 else w.getD m.2.1 false != m.2.2
  let after (m : M) (α : Bool) : M :=
    if m.1 = true then (true, 0, m.2.2 == α) else (false, m.2.1, m.2.2 == α)
  let pack (L R : M) : Option (ℕ × ℕ × Bool × Bool) × M :=
    if L.1 = true then
      if L.2.2 = false then (none, (true, 0, false)) else (none, R)
    else if R.1 = true then
      if R.2.2 = false then (none, (true, 0, false)) else (none, L)
    else if L.2.1 = R.2.1 then
      if L.2.2 = R.2.2 then (none, L) else (none, (true, 0, false))
    else if L.2.1 < R.2.1 then
      (some (L.2.1, R.2.1, !L.2.2, !R.2.2), (false, 0, false))
    else
      (some (R.2.1, L.2.1, !R.2.2, !L.2.2), (false, 0, false))
  let pol (op : Bool → Bool → Bool) : Bool × Bool :=
    (op true true || op true false, op true true || op false true)
  let resolve (means : List M) (r : ℕ) : M :=
    if r < 10 then (false, r, false) else means.getD (r - 10) (true, 0, false)
  let wires (gs : List BinaryGate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w
  let bump (i : ℕ) : ℕ := if i < 10 then i else i + 1
  let bumpG (g : BinaryGate) : BinaryGate := ⟨g.op, bump g.left, bump g.right⟩
  let Sg (g : BinaryGate) : Prop := ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)
  have bne_true (a : Bool) : (a != true) = !a := by cases a <;> rfl
  have bne_false (a : Bool) : (a != false) = a := by cases a <;> rfl
  have after_spec (w : List Bool) (m : M) (α : Bool) :
      mval w (after m α) = (mval w m == α) := by
    rcases m with ⟨c, idx, f⟩
    cases c <;> cases f <;> cases α <;> cases w.getD idx false <;> simp [mval, after]
  have pack_none (w : List Bool) (L R : M) (h : (pack L R).1 = none) :
      mval w (pack L R).2 = (mval w L && mval w R) := by
    rcases L with ⟨Lc, Li, Lf⟩
    rcases R with ⟨Rc, Ri, Rf⟩
    cases Lc
    · cases Rc
      · cases Lf <;> cases Rf <;>
          (by_cases heq : Li = Ri
           · subst heq
             cases hbit : w.getD Li false <;> dsimp [pack, mval] <;>
               rw [if_pos (rfl : Li = Li), hbit] <;> rfl
           · by_cases hlt : Li < Ri
             · dsimp [pack] at h
               rw [if_neg heq, if_pos hlt] at h
               injection h
             · dsimp [pack] at h
               rw [if_neg heq, if_neg hlt] at h
               injection h)
      · cases Rf <;> cases Lf <;> cases hbit : w.getD Li false <;>
          dsimp [pack, mval] <;> rw [hbit] <;> rfl
    · cases Lf
      · dsimp [pack, mval]
        rfl
      · cases Rc
        · cases Rf <;> cases hbit : w.getD Ri false <;> dsimp [pack, mval] <;> rw [hbit] <;> rfl
        · cases Rf <;> dsimp [pack, mval] <;> rfl
  have pack_some (w : List Bool) (L R : M) (lo hi : ℕ) (p q : Bool)
      (h : (pack L R).1 = some (lo, hi, p, q)) :
      lo < hi ∧ (((w.getD lo false == p) && (w.getD hi false == q)) =
        (mval w L && mval w R)) := by
    rcases L with ⟨Lc, Li, Lf⟩
    rcases R with ⟨Rc, Ri, Rf⟩
    cases Lc
    · cases Rc
      · by_cases heq : Li = Ri
        · subst heq
          cases Lf <;> cases Rf <;>
            (dsimp [pack] at h; rw [if_pos (rfl : Li = Li)] at h; injection h)
        · by_cases hlt : Li < Ri
          · dsimp [pack] at h
            rw [if_neg heq, if_pos hlt] at h
            injection h with h
            injection h with hlo hrest
            injection hrest with hhi hpq
            injection hpq with hp hq
            subst hlo hhi hp hq
            refine ⟨hlt, ?_⟩
            cases Lf <;> cases Rf <;> cases hL : w.getD Li false <;> cases hR : w.getD Ri false <;>
              dsimp [mval] <;> rw [hL, hR] <;> rfl
          · have hgt : Ri < Li := by omega
            dsimp [pack] at h
            rw [if_neg heq, if_neg hlt] at h
            injection h with h
            injection h with hlo hrest
            injection hrest with hhi hpq
            injection hpq with hp hq
            subst hlo hhi hp hq
            refine ⟨hgt, ?_⟩
            cases Lf <;> cases Rf <;> cases hL : w.getD Ri false <;> cases hR : w.getD Li false <;>
              dsimp [mval] <;> rw [hL, hR] <;> rfl
      · cases Rf <;> (dsimp [pack] at h; injection h)
    · cases Lf <;> (dsimp [pack] at h; injection h)
  have pol_eq (α β : Bool) (op : Bool → Bool → Bool)
      (hop : op = fun x y => (x == α) && (y == β)) : pol op = (α, β) := by
    cases α <;> cases β <;> simp [pol, hop]
  have wires_nil (w : List Bool) : wires [] w = w := by simp [wires]
  have wires_cons (g : BinaryGate) (gs : List BinaryGate) (w : List Bool) :
      wires (g :: gs) w =
        wires gs (w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) := by
    simp [wires, List.foldl_cons]
  have wires_len (gs : List BinaryGate) (w : List Bool) :
      (wires gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [wires]
    | cons g gs ih =>
      rw [wires_cons, ih]
      simp
      omega
  have wires_pref (gs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (wires gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => simp [wires]
    | cons g gs ih =>
      rw [wires_cons]
      have hi' : i < (w ++ [g.op (w.getD g.left false) (w.getD g.right false)]).length := by
        simp
        omega
      rw [ih _ hi', List.getD_append _ _ _ _ hi]
  have rel_ext (w v : List Bool) (bit : Bool)
      (hlen : w.length + 1 = v.length) (h10 : 10 ≤ w.length)
      (hag : ∀ i, v.getD (bump i) false = w.getD i false) :
      ∀ i, (v ++ [bit]).getD (bump i) false = (w ++ [bit]).getD i false := by
    intro i
    by_cases hi : i < w.length
    · by_cases h9 : i < 10
      · have hb : bump i = i := by simp [bump, h9]
        have hagi : v.getD i false = w.getD i false := by simpa [hb] using hag i
        rw [hb, List.getD_append v [bit] false i (by omega),
          List.getD_append w [bit] false i hi]
        exact hagi
      · have hb : bump i = i + 1 := by simp [bump, h9]
        have hv : i + 1 < v.length := by omega
        have hagi : v.getD (i + 1) false = w.getD i false := by simpa [hb] using hag i
        rw [hb, List.getD_append v [bit] false (i + 1) hv,
          List.getD_append w [bit] false i hi]
        exact hagi
    · have hge : w.length ≤ i := Nat.le_of_not_gt hi
      have h9 : ¬ i < 10 := by omega
      have hb : bump i = i + 1 := by simp [bump, h9]
      rw [hb, List.getD_append_right w [bit] false i hge]
      have hv : v.length ≤ i + 1 := by omega
      rw [List.getD_append_right v [bit] false (i + 1) hv]
      have hsub : i + 1 - v.length = i - w.length := by omega
      rw [hsub]
  have bump_run (gs : List BinaryGate) :
      ∀ w v : List Bool, w.length + 1 = v.length → 10 ≤ w.length →
        (∀ i, v.getD (bump i) false = w.getD i false) →
        ∀ i, (wires (gs.map bumpG) v).getD (bump i) false = (wires gs w).getD i false := by
    induction gs with
    | nil =>
      intro w v _ _ hag i
      simpa [wires] using hag i
    | cons g gs ih =>
      intro w v hlen h10 hag i
      have bit :
          g.op (v.getD (bump g.left) false) (v.getD (bump g.right) false) =
            g.op (w.getD g.left false) (w.getD g.right false) := by
        rw [hag g.left, hag g.right]
      have hstep := wires_cons (bumpG g) (gs.map bumpG) v
      rw [show (bumpG g :: gs.map bumpG) = (g :: gs).map bumpG by simp [bumpG]] at hstep
      rw [hstep]
      have hstep' := wires_cons g gs w
      rw [hstep']
      apply ih
      · simp [hlen]
      · simp
        omega
      · intro j
        rw [bit]
        exact rel_ext w v _ hlen h10 hag j
  have wires_append (a b : List BinaryGate) (w : List Bool) :
      wires (a ++ b) w = wires b (wires a w) := by
    induction a generalizing w with
    | nil => simp [wires]
    | cons g gs ih =>
      rw [List.cons_append, wires_cons, wires_cons, ih]
  have getD_last (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    rw [List.getD_append_right w [b] false w.length (Nat.le_refl _)]
    simp
  have bxor (a f p : Bool) : ((a != f) != p) = (a != (f != p)) := by
    cases a <;> cases f <;> cases p <;> rfl
  have bump_lt (a b : ℕ) (h : a < b) : bump a < bump b := by
    by_cases ha : a < 10 <;> by_cases hb : b < 10
    · simp [bump, ha, hb, h]
    · simp [bump, ha, hb]
      omega
    · omega
    · simp [bump, ha, hb]
      omega
  have bump_bound (r j : ℕ) (h : r < 10 + j) : bump r < 11 + j := by
    by_cases hr : r < 10
    · simp [bump, hr]
      omega
    · simp [bump, hr]
      omega
  rcases C with ⟨gates, out⟩
  cases gates with
  | nil => exact (Nat.not_lt_zero _ pos).elim
  | cons g0 rest =>
    let full : BinaryCircuit := ⟨g0 :: rest, out⟩
    have bright : g0.right = 9 := by
      simpa [full, List.get_eq_getElem, List.getElem_cons_zero] using first
    have hord0 : g0.left < g0.right ∧ g0.right < 10 := by
      have h := ordered ⟨0, pos⟩
      dsimp at h
      exact h
    have aLt : g0.left < 9 := by
      have := hord0.1
      rwa [bright] at this
    obtain ⟨p0, q0, hop0⟩ := sg g0 (by simp [full])
    have sg_rest : ∀ t ∈ rest, Sg t := fun t ht => sg t (by simp [full, ht])
    have ord_rest : ∀ j : Fin rest.length,
        (rest.get j).left < (rest.get j).right ∧ (rest.get j).right < 11 + j.val := by
      intro j
      have hj : j.val + 1 < (g0 :: rest).length := by simp
      have h := ordered ⟨j.val + 1, hj⟩
      have h1 := h.1
      have h2 := h.2
      change (rest.get j).left < (rest.get j).right at h1
      change (rest.get j).right < 10 + (j.val + 1) at h2
      exact ⟨h1, by omega⟩
    let base (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 1]
    have base_len (x : Fin 9 → Bool) : (base x).length = 10 := by simp [base]
    have base_lt (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
        (base x).getD i false = x ⟨i, hi⟩ := by
      have hlen : i < (List.ofFn x).length := by simpa using hi
      rw [show base x = List.ofFn x ++ [x 0 || x 1] from rfl,
        List.getD_append _ _ _ _ hlen, List.getD_eq_getElem _ _ hlen, List.getElem_ofFn]
    have base_9 (x : Fin 9 → Bool) : (base x).getD 9 false = (x 0 || x 1) := by
      rw [show base x = List.ofFn x ++ [x 0 || x 1] from rfl,
        List.getD_append_right _ _ _ _ (by simp)]
      simp
    have edge_sem (x : Fin 9 → Bool) :
        (full.eval (base x) != phase) = edge x := sem_edge x
    by_cases hfar : 2 ≤ g0.left
    · apply hFar full phase pos
      · simpa [full] using sg
      · simpa [full] using ordered
      · simpa [full] using last
      · simpa [full] using first
      · simpa [full] using hfar
      · intro x
        simpa [edge, base] using sem_edge x
    · have hle : g0.left ≤ 1 := by omega
      have h01 : g0.left = 0 ∨ g0.left = 1 := by omega
      have elim (initM : M) (hidx : initM.1 = true ∨ initM.2.1 < 10)
          (hval : ∀ x : Fin 9 → Bool,
            mval (base x) initM =
              g0.op ((base x).getD g0.left false) ((base x).getD g0.right false)) :
          14 ≤ full.size := by
        let gval (x : Fin 9 → Bool) : Bool :=
          g0.op ((base x).getD g0.left false) ((base x).getD g0.right false)
        let step (st : List BinaryGate × List M) (g : BinaryGate) : List BinaryGate × List M :=
          let acc := st.1
          let means := st.2
          let ab := pol g.op
          let res := pack (after (resolve means g.left) ab.1) (after (resolve means g.right) ab.2)
          if res.1.isSome = true then
            let spec := res.1.getD (0, 0, false, false)
            (acc ++ [⟨fun x y => (x == spec.2.2.1) && (y == spec.2.2.2), spec.1, spec.2.1⟩],
             means ++ [(false, 10 + acc.length, false)])
          else
            (acc, means ++ [res.2])
        have mval_stable (w : List Bool) (b : Bool) (m : M)
            (hk : m.1 = true ∨ m.2.1 < w.length) :
            mval (w ++ [b]) m = mval w m := by
          rcases m with ⟨c, i, f⟩
          cases c
          · rcases hk with hk | hk
            · simp at hk
            · simp only [mval]
              rw [List.getD_append w [b] false i hk]
          · simp [mval]
        have after_idx (m : M) (α : Bool) (n : ℕ) (h : m.1 = true ∨ m.2.1 < n) :
            (after m α).1 = true ∨ (after m α).2.1 < n := by
          rcases m with ⟨c, i, f⟩
          cases c
          · rcases h with h | h
            · simp [after] at h
            · right
              simpa [after] using h
          · left
            simp [after]
        have resolve_idx (means : List M) (n : ℕ) (h10 : 10 ≤ n)
            (hmem : ∀ m ∈ means, m.1 = true ∨ m.2.1 < n) (r : ℕ) :
            (resolve means r).1 = true ∨ (resolve means r).2.1 < n := by
          by_cases hr : r < 10
          · right
            have : r < n := by omega
            simpa [resolve, hr] using this
          · by_cases hm : r - 10 < means.length
            · have hget : means.get ⟨r - 10, hm⟩ ∈ means := List.get_mem _ _
              have hv := hmem _ hget
              simpa [resolve, hr, List.getD, List.get, List.getElem?_eq_getElem hm] using hv
            · left
              simp [resolve, hr, List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hm)]
        have pack_none_idx (L R : M) (n : ℕ)
            (hL : L.1 = true ∨ L.2.1 < n) (hR : R.1 = true ∨ R.2.1 < n)
            (h : (pack L R).1 = none) :
            (pack L R).2.1 = true ∨ (pack L R).2.2.1 < n := by
          rcases L with ⟨Lc, Li, Lf⟩
          rcases R with ⟨Rc, Ri, Rf⟩
          cases Lc
          · cases Rc
            · by_cases heq : Li = Ri
              · subst heq
                cases Lf <;> cases Rf
                · rcases hL with hL | hL
                  · simp at hL
                  · right
                    simpa [pack] using hL
                · left
                  simp [pack]
                · left
                  simp [pack]
                · rcases hL with hL | hL
                  · simp at hL
                  · right
                    simpa [pack] using hL
              · by_cases hlt : Li < Ri
                · simp [pack, heq, hlt] at h
                · simp [pack, heq, hlt] at h
            · cases Rf
              · left
                simp [pack]
              · rcases hL with hL | hL
                · simp at hL
                · right
                  simpa [pack] using hL
          · cases Lf
            · left
              simp [pack]
            · rcases hR with hR | hR
              · left
                dsimp [pack]
                exact hR
              · right
                dsimp [pack]
                exact hR
        have pack_lit (L R : M) (lo hi : ℕ) (p q : Bool)
            (h : (pack L R).1 = some (lo, hi, p, q)) :
            L.1 = false ∧ R.1 = false ∧
              (L.2.1 = lo ∧ R.2.1 = hi ∨ R.2.1 = lo ∧ L.2.1 = hi) := by
          rcases L with ⟨Lc, Li, Lf⟩
          rcases R with ⟨Rc, Ri, Rf⟩
          cases Lc
          · cases Rc
            · by_cases heq : Li = Ri
              · subst heq
                cases Lf <;> cases Rf <;> (simp only [pack] at h; injection h)
              · by_cases hlt : Li < Ri
                · have hred : pack (false, Li, Lf) (false, Ri, Rf) =
                      (some (Li, Ri, !Lf, !Rf), (false, 0, false)) := by
                    simp [pack, heq, hlt]
                  rw [hred] at h
                  injection h with h
                  injection h with hlo hrest
                  injection hrest with hhi hrest2
                  subst hlo hhi
                  exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
                · have hgt : Ri < Li := by omega
                  have hred : pack (false, Li, Lf) (false, Ri, Rf) =
                      (some (Ri, Li, !Rf, !Lf), (false, 0, false)) := by
                    simp [pack, heq, hlt]
                  rw [hred] at h
                  injection h with h
                  injection h with hlo hrest
                  injection hrest with hhi hrest2
                  subst hlo hhi
                  exact ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
            · cases Rf <;> simp [pack] at h
          · cases Lf <;> simp [pack] at h
        have step_ok (pre : List BinaryGate) (g : BinaryGate) (acc : List BinaryGate)
            (means : List M) (hsg : Sg g)
            (hord : g.left < g.right ∧ g.right < 11 + pre.length)
            (hlen : means.length = pre.length + 1) (hleA : acc.length ≤ pre.length)
            (hgood : (∀ t ∈ acc, Sg t) ∧ ∀ j : Fin acc.length,
              (acc.get j).left < (acc.get j).right ∧ (acc.get j).right < 10 + j.val)
            (hidxA : ∀ m ∈ means, m.1 = true ∨ m.2.1 < 10 + acc.length)
            (hagree : ∀ x : Fin 9 → Bool, ∀ r : ℕ, r < 10 + means.length →
              mval (wires acc (base x)) (resolve means r) =
                (wires pre (base x ++ [gval x])).getD r false) :
            (step (acc, means) g).1.length ≤ (pre ++ [g]).length ∧
            ((∀ t ∈ (step (acc, means) g).1, Sg t) ∧ ∀ j : Fin (step (acc, means) g).1.length,
              ((step (acc, means) g).1.get j).left < ((step (acc, means) g).1.get j).right ∧
                ((step (acc, means) g).1.get j).right < 10 + j.val) ∧
            (step (acc, means) g).2.length = (pre ++ [g]).length + 1 ∧
            (∀ m ∈ (step (acc, means) g).2, m.1 = true ∨ m.2.1 < 10 + (step (acc, means) g).1.length) ∧
            ∀ x : Fin 9 → Bool, ∀ r : ℕ, r < 10 + (step (acc, means) g).2.length →
              mval (wires (step (acc, means) g).1 (base x)) (resolve (step (acc, means) g).2 r) =
                (wires (pre ++ [g]) (base x ++ [gval x])).getD r false := by
          rcases hsg with ⟨α, β, hop⟩
          have hp : pol g.op = (α, β) := pol_eq α β g.op hop
          let Lm : M := after (resolve means g.left) α
          let Rm : M := after (resolve means g.right) β
          let res : Option (ℕ × ℕ × Bool × Bool) × M := pack Lm Rm
          have hl : g.left < 10 + means.length := by
            have h1 := hord.1
            have h2 := hord.2
            omega
          have hrgt : g.right < 10 + means.length := by
            have h2 := hord.2
            omega
          have old_len (x : Fin 9 → Bool) :
              (wires pre (base x ++ [gval x])).length = 10 + means.length := by
            rw [wires_len]
            simp [base_len, List.length_append, List.length_singleton, hlen]
            omega
          have hL (x : Fin 9 → Bool) :
              mval (wires acc (base x)) Lm =
                ((wires pre (base x ++ [gval x])).getD g.left false == α) := by
            rw [show Lm = after (resolve means g.left) α from rfl, after_spec,
              hagree x g.left hl]
          have hR (x : Fin 9 → Bool) :
              mval (wires acc (base x)) Rm =
                ((wires pre (base x ++ [gval x])).getD g.right false == β) := by
            rw [show Rm = after (resolve means g.right) β from rfl, after_spec,
              hagree x g.right hrgt]
          have hnew (x : Fin 9 → Bool) :
              (wires (pre ++ [g]) (base x ++ [gval x])).getD (10 + means.length) false =
                (mval (wires acc (base x)) Lm && mval (wires acc (base x)) Rm) := by
            rw [wires_append, wires_cons, wires_nil]
            have hw := old_len x
            rw [← hw, getD_last, hop]
            dsimp
            rw [← hL x, ← hR x]
          have resolve_old (m : M) (r : ℕ) (hr : r < 10 + means.length) :
              resolve (means ++ [m]) r = resolve means r := by
            by_cases h10 : r < 10
            · simp [resolve, h10]
            · have hr' : r - 10 < means.length := by omega
              simp only [resolve, h10, if_neg h10]
              rw [List.getD_append _ _ _ _ hr']
          have resolve_last (m : M) :
              resolve (means ++ [m]) (10 + means.length) = m := by
            have h10 : ¬ 10 + means.length < 10 := by omega
            simp only [resolve, h10, if_neg h10]
            have hsub : 10 + means.length - 10 = means.length := by omega
            rw [hsub, List.getD_append_right _ _ _ _ (Nat.le_refl _)]
            simp
          have hLi : Lm.1 = true ∨ Lm.2.1 < 10 + acc.length :=
            after_idx (resolve means g.left) α (10 + acc.length)
              (resolve_idx means (10 + acc.length) (by omega) hidxA g.left)
          have hRi : Rm.1 = true ∨ Rm.2.1 < 10 + acc.length :=
            after_idx (resolve means g.right) β (10 + acc.length)
              (resolve_idx means (10 + acc.length) (by omega) hidxA g.right)
          by_cases hs : res.1.isSome = true
          · obtain ⟨⟨lo, hi, p, q⟩, hspec⟩ :
                ∃ spec : ℕ × ℕ × Bool × Bool, res.1 = some spec := by
              cases hres : res.1 with
              | none => simp [hres, Option.isSome] at hs
              | some spec => exact ⟨spec, rfl⟩
            have hlohi : lo < hi := (pack_some [] Lm Rm lo hi p q hspec).1
            have hbits (w : List Bool) :
                ((w.getD lo false == p) && (w.getD hi false == q)) =
                  (mval w Lm && mval w Rm) :=
              (pack_some w Lm Rm lo hi p q hspec).2
            have hhi : hi < 10 + acc.length := by
              rcases pack_lit Lm Rm lo hi p q hspec with ⟨hLf, hRf, hOr⟩
              rcases hLi with hLc | hLi
              · simp [hLc] at hLf
              · rcases hRi with hRc | hRi
                · simp [hRc] at hRf
                · rcases hOr with ⟨-, hhi⟩ | ⟨-, hhi⟩
                  · simpa [hhi] using hRi
                  · simpa [hhi] using hLi
            let ng : BinaryGate := ⟨fun x y => (x == p) && (y == q), lo, hi⟩
            have hst : step (acc, means) g =
                (acc ++ [ng], means ++ [(false, 10 + acc.length, false)]) := by
              dsimp only [step]
              rw [hp]
              dsimp
              rw [show pack (after (resolve means g.left) α) (after (resolve means g.right) β) = res
                from rfl, hspec]
              simp [Option.isSome, Option.getD_some, ng]
            rw [hst]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · simp
              omega
            · constructor
              · intro t ht
                simp at ht
                rcases ht with ht | rfl
                · exact hgood.1 t ht
                · exact ⟨p, q, rfl⟩
              · intro j
                by_cases hj : j.val < acc.length
                · have hg : (acc ++ [ng]).get j = acc.get ⟨j.val, hj⟩ := by
                    simp [List.get_eq_getElem, List.getElem_append_left hj]
                  rw [hg]
                  exact hgood.2 ⟨j.val, hj⟩
                · have hj' : j.val = acc.length := by
                    have := j.isLt
                    simp at this
                    omega
                  have hg : (acc ++ [ng]).get j = ng := by
                    have hleJ : acc.length ≤ j.val := by omega
                    simp [List.get_eq_getElem, List.getElem_append_right hleJ, hj', ng]
                  simp [hg, ng, hlohi, hhi, hj']
            · simp [hlen]
            · intro m hm
              simp at hm
              rcases hm with hm | rfl
              · rcases hidxA m hm with hc | hk
                · left
                  exact hc
                · right
                  have hlen1 : 10 + acc.length < 10 + (acc ++ [ng]).length := by simp
                  exact Nat.lt_trans hk hlen1
              · right
                simp
            · intro x r hr
              have happ : wires (acc ++ [ng]) (base x) =
                  wires acc (base x) ++ [ng.op ((wires acc (base x)).getD ng.left false)
                    ((wires acc (base x)).getD ng.right false)] := by
                rw [wires_append, wires_cons, wires_nil]
              by_cases hr0 : r < 10 + means.length
              · have hro := resolve_old (false, 10 + acc.length, false) r hr0
                have hresm : (resolve means r).1 = true ∨
                    (resolve means r).2.1 < (wires acc (base x)).length := by
                  rw [wires_len, base_len]
                  exact resolve_idx means (10 + acc.length) (by omega) hidxA r
                rw [happ, hro, mval_stable _ _ _ hresm, hagree x r hr0, wires_append,
                  wires_cons, wires_nil,
                  List.getD_append _ _ _ _ (by rw [old_len]; exact hr0)]
              · have hr1 : r = 10 + means.length := by
                  simp at hr
                  omega
                subst hr1
                have hro := resolve_last (false, 10 + acc.length, false)
                rw [happ, hro]
                have hwlen : (wires acc (base x)).length = 10 + acc.length := by
                  rw [wires_len, base_len]
                have hbit : ((wires acc (base x) ++ [ng.op ((wires acc (base x)).getD ng.left false)
                    ((wires acc (base x)).getD ng.right false)]).getD (10 + acc.length) false) =
                    ng.op ((wires acc (base x)).getD ng.left false)
                      ((wires acc (base x)).getD ng.right false) := by
                  rw [← hwlen]
                  exact getD_last _ _
                simp only [mval, hbit, bne_false]
                dsimp [ng]
                rw [hbits (wires acc (base x))]
                exact (hnew x).symm
          · have hnone : res.1 = none := by
              cases hres : res.1 with
              | none => rfl
              | some spec => simp [hres, Option.isSome] at hs
            have hst : step (acc, means) g = (acc, means ++ [res.2]) := by
              dsimp only [step]
              rw [hp]
              dsimp
              rw [show pack (after (resolve means g.left) α) (after (resolve means g.right) β) = res
                from rfl, hnone]
              simp [Option.isSome]
            rw [hst]
            have hnewidx := pack_none_idx Lm Rm (10 + acc.length) hLi hRi hnone
            refine ⟨?_, hgood, ?_, ?_, ?_⟩
            · simp
              omega
            · simp [hlen]
            · intro m hm
              simp at hm
              rcases hm with hm | rfl
              · exact hidxA m hm
              · exact hnewidx
            · intro x r hr
              by_cases hr0 : r < 10 + means.length
              · rw [resolve_old res.2 r hr0, hagree x r hr0, wires_append, wires_cons, wires_nil,
                  List.getD_append _ _ _ _ (by rw [old_len]; exact hr0)]
              · have hr1 : r = 10 + means.length := by
                  simp at hr
                  omega
                subst hr1
                rw [resolve_last res.2, pack_none (wires acc (base x)) Lm Rm hnone, hnew x]
        have fold : ∀ (pre suf : List BinaryGate) (acc : List BinaryGate) (means : List M),
            (∀ t ∈ suf, Sg t) →
            (∀ j : Fin suf.length, (suf.get j).left < (suf.get j).right ∧
              (suf.get j).right < 11 + pre.length + j.val) →
            means.length = pre.length + 1 →
            acc.length ≤ pre.length →
            ((∀ t ∈ acc, Sg t) ∧ ∀ j : Fin acc.length,
              (acc.get j).left < (acc.get j).right ∧ (acc.get j).right < 10 + j.val) →
            (∀ m ∈ means, m.1 = true ∨ m.2.1 < 10 + acc.length) →
            (∀ x : Fin 9 → Bool, ∀ r : ℕ, r < 10 + means.length →
              mval (wires acc (base x)) (resolve means r) =
                (wires pre (base x ++ [gval x])).getD r false) →
            (suf.foldl step (acc, means)).1.length ≤ (pre ++ suf).length ∧
            ((∀ t ∈ (suf.foldl step (acc, means)).1, Sg t) ∧
              ∀ j : Fin (suf.foldl step (acc, means)).1.length,
                ((suf.foldl step (acc, means)).1.get j).left <
                  ((suf.foldl step (acc, means)).1.get j).right ∧
                ((suf.foldl step (acc, means)).1.get j).right < 10 + j.val) ∧
            (suf.foldl step (acc, means)).2.length = (pre ++ suf).length + 1 ∧
            (∀ m ∈ (suf.foldl step (acc, means)).2,
              m.1 = true ∨ m.2.1 < 10 + (suf.foldl step (acc, means)).1.length) ∧
            ∀ x : Fin 9 → Bool, ∀ r : ℕ, r < 10 + (suf.foldl step (acc, means)).2.length →
              mval (wires (suf.foldl step (acc, means)).1 (base x))
                (resolve (suf.foldl step (acc, means)).2 r) =
                (wires (pre ++ suf) (base x ++ [gval x])).getD r false := by
          intro pre suf acc means
          induction suf generalizing pre acc means with
          | nil =>
            intro _ _ hlen hleA hgood hidxA hagree
            simp only [List.foldl_nil, List.append_nil]
            exact ⟨hleA, hgood, hlen, hidxA, hagree⟩
          | cons g suf ih =>
            intro hsgS hordS hlen hleA hgood hidxA hagree
            have hsgg : Sg g := hsgS g (by simp)
            have hordg : g.left < g.right ∧ g.right < 11 + pre.length := by
              have h := hordS ⟨0, by simp⟩
              simpa [List.get_eq_getElem, List.getElem_cons_zero] using h
            rcases step_ok pre g acc means hsgg hordg hlen hleA hgood hidxA hagree with
              ⟨hle1, hgood1, hlen1, hidx1, hagree1⟩
            simp only [List.foldl_cons]
            have happS : pre ++ (g :: suf) = (pre ++ [g]) ++ suf := by simp
            have heta : step (acc, means) g =
                ((step (acc, means) g).1, (step (acc, means) g).2) := by
              cases step (acc, means) g
              rfl
            rw [happS, heta]
            apply ih (pre ++ [g]) (step (acc, means) g).1 (step (acc, means) g).2
            · intro t ht
              exact hsgS t (List.mem_cons_of_mem _ ht)
            · intro j
              have hj : j.val + 1 < (g :: suf).length := by simp
              have h := hordS ⟨j.val + 1, hj⟩
              have hg : (g :: suf).get ⟨j.val + 1, hj⟩ = suf.get j := by
                simp [List.get_eq_getElem, List.getElem_cons_succ]
              refine ⟨?_, ?_⟩
              · simpa [hg] using h.1
              · have h2 := h.2
                simp only [hg, List.length_append, List.length_singleton] at h2 ⊢
                omega
            · exact hlen1
            · exact hle1
            · exact hgood1
            · exact hidx1
            · exact hagree1
        have agree0 : ∀ x : Fin 9 → Bool, ∀ r : ℕ, r < 11 →
            mval (base x) (resolve [initM] r) =
              ((base x) ++ [gval x]).getD r false := by
          intro x r hr
          by_cases h10 : r < 10
          · have hget : ((base x) ++ [gval x]).getD r false = (base x).getD r false :=
              List.getD_append (base x) [gval x] false r (by rw [base_len]; exact h10)
            have hres : resolve [initM] r = (false, r, false) := by simp [resolve, h10]
            have hm : mval (base x) (false, r, false) = (base x).getD r false := by
              simp [mval, bne_false]
            rw [hres, hm]
            exact hget.symm
          · have hr10 : r = 10 := by omega
            subst hr10
            have hres : resolve [initM] 10 = initM := by
              simp [resolve]
            rw [hres, hval x]
            have hlast : ((base x) ++ [gval x]).getD 10 false = gval x := by
              have hlen10 : (base x).length = 10 := base_len x
              rw [← hlen10]
              exact getD_last _ _
            exact hlast
        have hordZ : ∀ j : Fin rest.length,
            (rest.get j).left < (rest.get j).right ∧
              (rest.get j).right < 11 + ([] : List BinaryGate).length + j.val := by
          intro j
          rcases ord_rest j with ⟨h1, h2⟩
          exact ⟨h1, by simpa using h2⟩
        have good0 : (∀ t ∈ ([] : List BinaryGate), Sg t) ∧
            ∀ j : Fin ([] : List BinaryGate).length,
              (([] : List BinaryGate).get j).left < (([] : List BinaryGate).get j).right ∧
                (([] : List BinaryGate).get j).right < 10 + j.val :=
          ⟨fun t ht => by simp at ht, fun j => (Nat.not_lt_zero _ j.isLt).elim⟩
        have idx0 : ∀ m ∈ [initM], m.1 = true ∨ m.2.1 < 10 := by
          intro m hm
          simp at hm
          subst hm
          exact hidx
        rcases fold [] rest [] [initM] sg_rest hordZ rfl (Nat.zero_le _) good0 idx0
            (by
              intro x r hr
              simpa [wires_nil] using agree0 x r (by simpa using hr)) with
          ⟨hleF, hgoodF, hlenF, hidxF, hagreeF⟩
        let stF := rest.foldl step ([], [initM])
        have hout : out = 10 + rest.length := by
          have h := last
          simp [size_rfl] at h
          omega
        have heval (x : Fin 9 → Bool) :
            full.eval (base x) =
              (wires rest (base x ++ [gval x])).getD (10 + rest.length) false := by
          have hrfl : BinaryCircuit.wires full (base x) = wires (g0 :: rest) (base x) := rfl
          rw [eval_rfl, hrfl, wires_cons]
          have : g0.op ((base x).getD g0.left false) ((base x).getD g0.right false) = gval x := rfl
          have houtf : full.output = 10 + rest.length := by simpa [full] using hout
          rw [this, houtf]
        have hlenS : stF.2.length = rest.length + 1 := by
          simpa [stF, List.append_nil] using hlenF
        have hleS : stF.1.length ≤ rest.length := by
          simpa [stF, List.append_nil] using hleF
        have hagreeS (x : Fin 9 → Bool) (r : ℕ) (hr : r < 10 + stF.2.length) :
            mval (wires stF.1 (base x)) (resolve stF.2 r) =
              (wires rest (base x ++ [gval x])).getD r false := by
          simpa [stF, List.append_nil] using hagreeF x r hr
        have hrOut : 10 + rest.length < 10 + stF.2.length := by
          rw [hlenS]
          omega
        let mOut : M := resolve stF.2 (10 + rest.length)
        have hsem (x : Fin 9 → Bool) :
            (mval (wires stF.1 (base x)) mOut != phase) = edge x := by
          rw [show mval (wires stF.1 (base x)) mOut =
              (wires rest (base x ++ [gval x])).getD (10 + rest.length) false from
            hagreeS x _ hrOut, ← heval x]
          exact edge_sem x
        have hmOut : mOut.1 = true ∨ mOut.2.1 < 10 + stF.1.length := by
          have h10 : ¬ 10 + rest.length < 10 := by omega
          have hlt : rest.length < stF.2.length := by
            rw [hlenS]
            omega
          have hmem : mOut ∈ stF.2 := by
            simp only [mOut, resolve, h10, ite_false]
            have hsub : 10 + rest.length - 10 = rest.length := by omega
            rw [hsub]
            have hget : stF.2.getD rest.length (true, 0, false) = stF.2.get ⟨rest.length, hlt⟩ := by
              simp [List.getD, List.get, List.getElem?_eq_getElem hlt]
            rw [hget]
            exact List.get_mem _ _
          have hidxS : ∀ m ∈ stF.2, m.1 = true ∨ m.2.1 < 10 + stF.1.length := by
            simpa [stF, List.append_nil] using hidxF
          exact hidxS mOut hmem
        rcases mOut with ⟨c, k, fl⟩
        cases c
        · have hk : k < 10 + stF.1.length := by
            rcases hmOut with hc | hk
            · simp at hc
            · exact hk
          by_cases hk10 : k < 10
          · have hlit (x : Fin 9 → Bool) :
                (((if h : k < 9 then x ⟨k, h⟩ else x 0 || x 1) != fl) != phase) = edge x := by
              have hget : (wires stF.1 (base x)).getD k false =
                  (if h : k < 9 then x ⟨k, h⟩ else x 0 || x 1) := by
                rw [wires_pref _ _ _ (by rw [base_len]; omega)]
                by_cases h9 : k < 9
                · rw [base_lt x k h9]
                  simp [h9]
                · have hk9 : k = 9 := by omega
                  rw [hk9, base_9]
                  simp [hk9]
              have hs := hsem x
              simp only [mval] at hs
              rw [hget] at hs
              exact hs
            exact (notIn ⟨k, hk10⟩ fl phase hlit).elim
          · have hkge : 10 ≤ k := Nat.le_of_not_gt hk10
            let nGates : ℕ := k - 10 + 1
            have hn : nGates ≤ stF.1.length := by omega
            have hn1 : 0 < nGates := by omega
            let trimmed := stF.1.take nGates
            have htn : trimmed.length = nGates := by
              simp [trimmed, List.length_take, Nat.min_eq_left hn]
            have hklt : k < 10 + nGates := by omega
            have take_mem : ∀ (l : List BinaryGate) (n : ℕ) (t : BinaryGate),
                t ∈ l.take n → t ∈ l := by
              intro l
              induction l with
              | nil => intro n t ht; simp at ht
              | cons a l ih =>
                intro n t ht
                cases n with
                | zero => simp at ht
                | succ n =>
                  simp at ht
                  rcases ht with rfl | ht
                  · exact List.mem_cons.mpr (Or.inl rfl)
                  · exact List.mem_cons_of_mem a (ih n t ht)
            rcases hgoodF with ⟨hsgF, hordF⟩
            have hsgT : ∀ t ∈ trimmed, Sg t := fun t ht =>
              hsgF t (take_mem _ _ _ (by simpa [trimmed] using ht))
            have hordT : ∀ j : Fin trimmed.length,
                (trimmed.get j).left < (trimmed.get j).right ∧
                  (trimmed.get j).right < 10 + j.val := by
              intro j
              have hjl : j.val < nGates := by
                have := j.isLt
                simp [htn] at this
                exact this
              have hj : j.val < stF.1.length := by omega
              have hg : trimmed.get j = stF.1.get ⟨j.val, hj⟩ := by
                simp [trimmed, List.get_eq_getElem, List.getElem_take]
              have hordS : ∀ j : Fin stF.1.length,
                  (stF.1.get j).left < (stF.1.get j).right ∧ (stF.1.get j).right < 10 + j.val := by
                simpa [stF, List.append_nil] using hordF
              rw [hg]
              exact hordS ⟨j.val, hj⟩
            let dummy : BinaryGate := ⟨fun x y => (x == true) && (y == true), 2, 9⟩
            let D : BinaryCircuit := ⟨dummy :: trimmed.map bumpG, bump k⟩
            have hposD : 0 < D.size := by
              simp [D, size_rfl, htn]
            have h14 : 14 ≤ D.size := by
              apply hFar D (fl != phase) hposD
              · intro g hg
                simp [D, List.mem_map] at hg
                rcases hg with rfl | ⟨t, ht, rfl⟩
                · exact ⟨true, true, rfl⟩
                · exact hsgT t ht
              · intro j
                by_cases hj : j.val = 0
                · have hje : j = ⟨0, hposD⟩ := Fin.ext (by simp [hj])
                  have hget : D.gates.get j = dummy := by
                    rw [hje]
                    have hsz : D.size = (dummy :: trimmed.map bumpG).length := by
                      simp [D, size_rfl]
                    cases hsz
                    exact List.get_cons_zero
                  simp only [hget, dummy, hj]
                  decide
                · let i : ℕ := j.val - 1
                  have hjs : j.val = i + 1 := by omega
                  have hi : i < trimmed.length := by
                    have hlt : j.val < nGates + 1 := by
                      simpa [D, size_rfl, htn] using j.isLt
                    omega
                  have hltD : i + 1 < D.size := by
                    rw [← hjs]
                    exact j.isLt
                  have hje : j = ⟨i + 1, hltD⟩ := Fin.ext (by simp [hjs])
                  have hg : D.gates.get j = bumpG (trimmed.get ⟨i, hi⟩) := by
                    rw [hje]
                    have hsz : D.size = (dummy :: trimmed.map bumpG).length := by
                      simp [D, size_rfl]
                    cases hsz
                    change (dummy :: trimmed.map bumpG).get ⟨i + 1, hltD⟩ =
                      bumpG (trimmed.get ⟨i, hi⟩)
                    have htail : (dummy :: trimmed.map bumpG).get ⟨i + 1, hltD⟩ =
                        (trimmed.map bumpG).get ⟨i, Nat.lt_of_succ_lt_succ hltD⟩ :=
                      List.get_cons_succ
                    rw [htail, List.get_eq_getElem, List.get_eq_getElem]
                    simp [Fin.val_mk, List.getElem_map]
                  have htg := hordT ⟨i, hi⟩
                  refine ⟨?_, ?_⟩
                  · simpa [hg, bumpG] using bump_lt _ _ htg.1
                  · have hb := bump_bound (trimmed.get ⟨i, hi⟩).right i htg.2
                    have heq : 11 + i = 10 + (i + 1) := by
                      calc
                        11 + i = (10 + 1) + i := rfl
                        _ = 10 + (1 + i) := Nat.add_assoc 10 1 i
                        _ = 10 + (i + 1) := by rw [Nat.add_comm 1 i]
                    simp only [hg, bumpG, hjs]
                    rw [← heq]
                    exact hb
              · have hb : bump k = k + 1 := by simp [bump, hk10]
                simp [D, size_rfl, htn, hb]
                omega
              · simp [D, dummy, List.get_eq_getElem, List.getElem_cons_zero]
              · simp [D, dummy, List.get_eq_getElem, List.getElem_cons_zero]
              · intro x
                have hsplit : wires stF.1 (base x) =
                    wires (stF.1.drop nGates) (wires trimmed (base x)) := by
                  conv_lhs =>
                    rw [show stF.1 = trimmed ++ List.drop nGates stF.1 by
                      simp [trimmed, List.take_append_drop]]
                  rw [wires_append]
                have hpref : (wires trimmed (base x)).getD k false =
                    (wires stF.1 (base x)).getD k false := by
                  rw [hsplit]
                  exact (wires_pref (stF.1.drop nGates) (wires trimmed (base x)) k
                    (by rw [wires_len, base_len, htn]; omega)).symm
                let bit := dummy.op ((base x).getD dummy.left false)
                  ((base x).getD dummy.right false)
                have init_rel (i : ℕ) :
                    ((base x) ++ [bit]).getD (bump i) false = (base x).getD i false := by
                  by_cases hi : i < 10
                  · have hb : bump i = i := by simp [bump, hi]
                    rw [hb, List.getD_append _ _ _ _ (by rw [base_len]; exact hi)]
                  · have hb : bump i = i + 1 := by simp [bump, hi]
                    have hdef (l : List Bool) (j : ℕ) (hj : l.length ≤ j) :
                        l.getD j false = false := by
                      simp [List.getD, List.getElem?_eq_none hj]
                    rw [hb, hdef (base x) i (by rw [base_len]; omega)]
                    apply hdef
                    simp [base_len, List.length_append]
                    omega
                have hrun := bump_run trimmed (base x) ((base x) ++ [bit])
                  (by simp [base_len]) (by simp [base_len]) init_rel
                have hDe : D.eval (base x) = (wires trimmed (base x)).getD k false := by
                  have hrfl : BinaryCircuit.wires D (base x) = wires D.gates (base x) := rfl
                  rw [eval_rfl, hrfl]
                  simp only [D]
                  rw [wires_cons]
                  have hb : bump k = k + 1 := by simp [bump, hk10]
                  have hbit : dummy.op ((base x).getD dummy.left false)
                      ((base x).getD dummy.right false) = bit := rfl
                  rw [hbit]
                  have := hrun k
                  simpa [hb] using this
                have hsem' : (((wires stF.1 (base x)).getD k false != fl) != phase) = edge x := by
                  simpa [mval] using hsem x
                rw [hDe, hpref, ← bxor]
                exact hsem'
            have hleD : D.size ≤ full.size := by
              simp [D, size_rfl, full, htn]
              omega
            exact Nat.le_trans h14 hleD
        · have hconst (x : Fin 9 → Bool) : (fl != phase) = edge x := by
            simpa [mval] using hsem x
          exact (notConst fl phase hconst).elim
      cases p0 <;> cases q0
      · let initM : M := (false, 9, true)
        have hidx : initM.1 = true ∨ initM.2.1 < 10 := by simp [initM]
        have hval (x : Fin 9 → Bool) :
            mval (base x) initM =
              g0.op ((base x).getD g0.left false) ((base x).getD g0.right false) := by
          rcases h01 with h0 | h1
          · simp only [mval, initM]
            rw [hop0, bright, h0, base_lt x 0 (by decide), base_9, bne_true, ← idFF0]
            rfl
          · simp only [mval, initM]
            rw [hop0, bright, h1, base_lt x 1 (by decide), base_9, bne_true, ← idFF1]
            rfl
        exact elim initM hidx hval
      · apply hNear full phase pos
        · simpa [full] using sg
        · simpa [full] using ordered
        · simpa [full] using last
        · simpa [full] using first
        · simpa [full] using hle
        · exact ⟨false, true, by simpa [full, List.get_eq_getElem, List.getElem_cons_zero, hop0]⟩
        · intro x
          simpa [edge, base] using sem_edge x
      · let initM : M := (true, 0, false)
        have hidx : initM.1 = true ∨ initM.2.1 < 10 := by simp [initM]
        have hval (x : Fin 9 → Bool) :
            mval (base x) initM =
              g0.op ((base x).getD g0.left false) ((base x).getD g0.right false) := by
          rcases h01 with h0 | h1
          · simp only [mval, initM]
            rw [hop0, bright, h0, base_lt x 0 (by decide), base_9]
            dsimp
            rw [idTF0]
          · simp only [mval, initM]
            rw [hop0, bright, h1, base_lt x 1 (by decide), base_9]
            dsimp
            rw [idTF1]
        exact elim initM hidx hval
      · let initM : M := (false, g0.left, false)
        have hidx : initM.1 = true ∨ initM.2.1 < 10 := by
          right
          simpa [initM] using Nat.lt_trans aLt (by decide : (9 : ℕ) < 10)
        have hval (x : Fin 9 → Bool) :
            mval (base x) initM =
              g0.op ((base x).getD g0.left false) ((base x).getD g0.right false) := by
          rcases h01 with h0 | h1
          · simp only [mval, initM]
            rw [hop0, bright, h0, base_lt x 0 (by decide), base_9, bne_false]
            dsimp
            rw [idTT0]
          · simp only [mval, initM]
            rw [hop0, bright, h1, base_lt x 1 (by decide), base_9, bne_false]
            dsimp
            rw [idTT1]
        exact elim initM hidx hval

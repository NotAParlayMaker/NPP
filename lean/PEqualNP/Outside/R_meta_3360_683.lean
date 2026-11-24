import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Count paths to the observed wires after cutting the incoming reads of wire 9.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3360_683
    (without : ∀ (C : Circuit), FanInTwo C → C.size = 8 →
      (∀ g ∈ C.gates, g.op ≠ GateOp.not) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      let path (u v : ℕ) := Relation.ReflTransGen
        (fun a b : ℕ => 10 ≤ b ∧ b < 17 ∧ a < b ∧ a ∈ (gateAt C (b-9)).inputs) u v
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let pins (j : ℕ) := (gateAt C (j-9)).inputs
      ∀ S ⊆ Finset.range 17, S.card = 6 →
        9 ∉ S →
        (∀ i < 9, ∃ w ∈ S, path i w) →
        let live (j : ℕ) := 10 ≤ j ∧ j < 17 ∧ ∃ w ∈ S, path j w
        (∃ J : Finset ℕ, 4 ≤ J.card ∧ ∀ j ∈ J, live j) →
        (¬ ∃ a b j : ℕ, a < b ∧ b < 9 ∧ live j ∧ a ∉ S ∧ b ∉ S ∧
          (pins j = [a,b] ∨ pins j = [b,a]) ∧
          ∀ k, live k → (a ∈ pins k ∨ b ∈ pins k) → k = j) →
        ∃ p n : Fin 9 → Bool, f p ≠ f n ∧ ∀ w ∈ S,
          (C.wires (List.ofFn p)).getD w false = (C.wires (List.ofFn n)).getD w false)
    (withSeed : ∀ (C : Circuit), FanInTwo C → C.size = 8 →
      (∀ g ∈ C.gates, g.op ≠ GateOp.not) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      let path (u v : ℕ) := Relation.ReflTransGen
        (fun a b : ℕ => 10 ≤ b ∧ b < 17 ∧ a < b ∧ a ∈ (gateAt C (b-9)).inputs) u v
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let pins (j : ℕ) := (gateAt C (j-9)).inputs
      ∀ S ⊆ Finset.range 17, S.card = 6 →
        9 ∈ S → ¬ (0 ∈ S ∧ 2 ∈ S) →
        (∀ i < 9, ∃ w ∈ S, path i w) →
        let live (j : ℕ) := 10 ≤ j ∧ j < 17 ∧ ∃ w ∈ S, path j w
        (∃ J : Finset ℕ, 5 ≤ J.card ∧ ∀ j ∈ J, live j) →
        (¬ ∃ a b j : ℕ, a < b ∧ b < 9 ∧ live j ∧ a ∉ S ∧ b ∉ S ∧
          (pins j = [a,b] ∨ pins j = [b,a]) ∧
          ∀ k, live k → (a ∈ pins k ∨ b ∈ pins k) → k = j) →
        ∃ p n : Fin 9 → Bool, f p ≠ f n ∧ ∀ w ∈ S,
          (C.wires (List.ofFn p)).getD w false = (C.wires (List.ofFn n)).getD w false) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (8 : ℕ) → (∀ x5 ∈ x2.gates, x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x6 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = (x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)))) → ∀ x7 ⊆ Finset.range (17 : ℕ), x7.card ≤ (6 : ℕ) → ∃ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ) → Bool), x1 x10 ≠ x1 x11 ∧ ∀ x12 ∈ x7, (x2.wires (List.ofFn x10)).getD x12 Bool.false = (x2.wires (List.ofFn x11)).getD x12 Bool.false := by
  classical
  let row (r : Fin 512) (i : Fin 9) : Bool := r.val.testBit i.val

  let target (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))

  let pos : Fin 9 → Fin 512 := ![21,3,133,24,17,33,66,132,264]
  let neg : Fin 9 → Fin 512 := ![20,1,129,16,1,1,2,4,8]

  have rows (i : Fin 9) : ∃ p n : Fin 512,
      target (row p) ≠ target (row n) ∧
      (∀ j : Fin 9, j ≠ i → row p j = row n j) ∧
      (row p 0 || row p 2) = (row n 0 || row n 2) := by
    refine ⟨pos i, neg i, ?_⟩
    fin_cases i <;> decide +kernel

  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨.or,[]⟩ = C.gates[j]
    exact List.getD_eq_getElem _ _ hj

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  let path (C : Circuit) (x y : ℕ) : Prop :=
    Relation.ReflTransGen
      (fun u v : ℕ => 10 ≤ v ∧ v < 17 ∧ u < v ∧ u ∈ (gateAt C (v-9)).inputs) x y

  let observe (C : Circuit) (x : Fin 9 → Bool) (w : ℕ) : Bool :=
    val C (List.ofFn x) w

  let collision (C : Circuit) (S : Finset ℕ) : Prop :=
    ∃ p n : Fin 9 → Bool, target p ≠ target n ∧
      ∀ w ∈ S, observe C p w = observe C n w

  have reads_raw (C : Circuit) (x : Fin 9 → Bool) {w : ℕ} (hw : w < 9) :
      observe C x w = x ⟨w,hw⟩ := by
    have len : (List.ofFn x).length = 9 := List.length_ofFn
    have h : w < (List.ofFn x).length := by rw [len]; exact hw
    change val C (List.ofFn x) w = _
    rw [val_input len hw,List.getD_eq_getElem _ _ h,List.getElem_ofFn]

  have missing (C : Circuit) (size : C.size = 8)
      (seed : ∀ x : Fin 9 → Bool, observe C x 9 = (x 0 || x 2))
      (S : Finset ℕ) (bounded : S ⊆ Finset.range 17)
      (absent : ¬ ∀ i < 9, ∃ w ∈ S, path C i w) : collision C S := by
    classical
    push Not at absent
    obtain ⟨i,hi,absent⟩ := absent
    let j : Fin 9 := ⟨i,hi⟩
    obtain ⟨p,n,diff,oneBit,seedSame⟩ := rows j
    let p' := row p
    let n' := row n
    have agree (w : ℕ) (valid : w < 17) (no : ¬ path C i w) :
        observe C p' w = observe C n' w := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        by_cases raw : w < 9
        · rw [reads_raw C p' raw,reads_raw C n' raw]
          have ne : (⟨w,raw⟩ : Fin 9) ≠ j := by
            intro eq
            have same : w = i := congrArg Fin.val eq
            subst w
            exact no Relation.ReflTransGen.refl
          exact oneBit _ ne
        · by_cases s : w = 9
          · subst w
            rw [seed,seed]
            exact seedSame
          let k := w-9
          have off : 9+k = w := by dsimp [k]; omega
          have gvalid : k < C.gates.length := by
            change C.gates.length = 8 at size
            dsimp [k]
            omega
          have eqp := val_gate (n := 9) (C := C) (x := List.ofFn p') List.length_ofFn gvalid
          have eqn := val_gate (n := 9) (C := C) (x := List.ofFn n') List.length_ofFn gvalid
          rw [off] at eqp eqn
          change val C (List.ofFn p') w = val C (List.ofFn n') w
          rw [eqp,eqn]
          congr 1
          apply List.map_congr_left
          intro u hu
          by_cases lo : u < w
          · rw [ite_eq_left lo,ite_eq_left lo]
            exact ih u lo (by omega) (fun h => no (h.tail ⟨by omega,valid,lo,hu⟩))
          · rw [ite_eq_right lo,ite_eq_right lo]
    exact ⟨p',n',diff,fun w hw => agree w (Finset.mem_range.mp (bounded hw)) (absent w hw)⟩

  have canonical (C : Circuit)
      (seed : ∀ x : Fin 9 → Bool, observe C x 9 = (x 0 || x 2))
      (without : ∀ B : Finset ℕ, B ⊆ Finset.range 17 → B.card = 6 → 9 ∉ B → collision C B)
      (withSeed : ∀ B : Finset ℕ, B ⊆ Finset.range 17 → B.card = 6 → 9 ∈ B →
        ¬ (0 ∈ B ∧ 2 ∈ B) → collision C B)
      (S : Finset ℕ) (bounded : S ⊆ Finset.range 17) (size : S.card ≤ 6) : collision C S := by
    classical
    have capacity : 6 ≤ (Finset.range 17).card := by decide
    obtain ⟨B,subB,rangeB,eqB⟩ := Finset.exists_subsuperset_card_eq bounded size capacity
    have restrict (h : collision C B) : collision C S := by
      obtain ⟨p,n,d,obs⟩ := h
      exact ⟨p,n,d,fun w hw => obs w (subB hw)⟩
    by_cases sel : 9 ∈ B
    · by_cases pair : 0 ∈ B ∧ 2 ∈ B
      · have within : B.erase 9 ⊆ (Finset.range 17).erase 9 := by
          intro w hw
          obtain ⟨ne,here⟩ := Finset.mem_erase.mp hw
          exact Finset.mem_erase.mpr ⟨ne,rangeB here⟩
        have budget : (B.erase 9).card ≤ 6 :=
          (Finset.card_le_card (Finset.erase_subset 9 B)).trans_eq eqB
        have cap : 6 ≤ ((Finset.range 17).erase 9).card := by decide
        obtain ⟨U,subU,rangeU,eqU⟩ := Finset.exists_subsuperset_card_eq within budget cap
        have no : 9 ∉ U := fun h => (Finset.mem_erase.mp (rangeU h)).1 rfl
        obtain ⟨p,n,d,obs⟩ := without U
          (rangeU.trans (Finset.erase_subset 9 _)) eqU no
        apply restrict
        refine ⟨p,n,d,?_⟩
        intro w hw
        by_cases sel9 : w = 9
        · subst w
          have h0 := obs 0 (subU (Finset.mem_erase.mpr ⟨by decide,pair.1⟩))
          have h2 := obs 2 (subU (Finset.mem_erase.mpr ⟨by decide,pair.2⟩))
          rw [reads_raw C p (show 0<9 by decide),reads_raw C n (show 0<9 by decide)] at h0
          rw [reads_raw C p (show 2<9 by decide),reads_raw C n (show 2<9 by decide)] at h2
          rw [seed,seed]
          change (p ⟨0,by decide⟩ || p ⟨2,by decide⟩) = (n ⟨0,by decide⟩ || n ⟨2,by decide⟩)
          rw [h0,h2]
        · exact obs w (subU (Finset.mem_erase.mpr ⟨sel9,hw⟩))
      · exact restrict (withSeed B rangeB eqB sel pair)
    · exact restrict (without B rangeB eqB sel)

  let combine (conj a b : Bool) : Bool := if conj then a && b else a || b
  let packed (conj : Bool) (u v : Fin 9) : ℕ :=
    (if conj then
      [0,2054,4620,2060,4120,10261,1090,2180,4360,
       0,0,515,515,515,515,515,515,515,
       0,0,0,8216,529,545,1090,4621,4360,
       0,0,0,0,529,545,1090,2060,2060,
       0,0,0,0,0,529,529,529,529,
       0,0,0,0,0,0,545,545,545,
       0,0,0,0,0,0,0,1090,1090,
       0,0,0,0,0,0,0,0,2180,
       0,0,0,0,0,0,0,0,0]
     else
      [0,515,4621,2573,529,545,43093,2693,4873,
       0,0,2054,4619,5146,18470,1090,17570,5386,
       0,0,0,2060,2581,2597,37453,2180,18724,
       0,0,0,0,4120,4649,5194,20648,4360,
       0,0,0,0,0,20536,9298,10388,24880,
       0,0,0,0,0,0,17506,16544,16672,
       0,0,0,0,0,0,0,35012,33088,
       0,0,0,0,0,0,0,0,70024,
       0,0,0,0,0,0,0,0,0]).getD (u.val * 9 + v.val) 0

  have pairRows (u v : Fin 9) (lt : u < v) (conj : Bool) :
      ∃ p n : Fin 512, target (row p) ≠ target (row n) ∧
        (∀ i : Fin 9, i ≠ u → i ≠ v → row p i = row n i) ∧
        (row p 0 || row p 2) = (row n 0 || row n 2) ∧
        combine conj (row p u) (row p v) = combine conj (row n u) (row n v) := by
    refine ⟨Fin.ofNat 512 (packed conj u v % 512), Fin.ofNat 512 (packed conj u v / 512), ?_⟩
    revert lt
    dsimp only [target, row, packed, combine]
    fin_cases u <;> fin_cases v <;> cases conj <;> decide +kernel

  have isolated (C : Circuit) (size : C.size = 8) (fan : FanInTwo C)
      (noNot : ∀ g ∈ C.gates, g.op ≠ GateOp.not)
      (seed : ∀ x : Fin 9 → Bool, observe C x 9 = (x 0 || x 2))
      (S : Finset ℕ) (bound : S ⊆ Finset.range 17) (j : ℕ) (jlo : 10 ≤ j) (jhi : j < 17)
      (u v : Fin 9) (uv : u < v)
      (pins : (gateAt C (j-9)).inputs = [u.val, v.val] ∨
        (gateAt C (j-9)).inputs = [v.val, u.val])
      (un : u.val ∉ S) (vn : v.val ∉ S)
      (unique : ∀ k, 10 ≤ k → k < 17 → (∃ w ∈ S, path C k w) →
        (u.val ∈ (gateAt C (k-9)).inputs ∨ v.val ∈ (gateAt C (k-9)).inputs) → k = j) :
      collision C S := by
    have len : C.gates.length = 8 := size
    have gvalid : j - 9 < C.gates.length := by omega
    have gm := gateAt_mem gvalid
    have hop : (gateAt C (j-9)).op = .and ∨ (gateAt C (j-9)).op = .or := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, noNot _ gm] using (fan _ gm).1
    obtain ⟨conj, hmode⟩ : ∃ conj : Bool,
        (gateAt C (j-9)).op = if conj then GateOp.and else GateOp.or := by
      rcases hop with h | h
      · exact ⟨true,h⟩
      · exact ⟨false,h⟩
    obtain ⟨p,n,diff,outside,seedSame,gateSame⟩ := pairRows u v uv conj
    have evalPair (a b : Bool) : (gateAt C (j-9)).op.eval [a,b] = combine conj a b := by
      rw [hmode]
      cases conj
      · change (a || (b || false)) = _
        simp [combine]
      · change (a && (b && true)) = _
        simp [combine]
    have comm (a b : Bool) : combine conj a b = combine conj b a := by
      cases conj <;> simp [combine, Bool.and_comm, Bool.or_comm]
    have gate (x : Fin 9 → Bool) : observe C x j = combine conj (x u) (x v) := by
      have eq := val_gate (n := 9) (C := C) (x := List.ofFn x) List.length_ofFn gvalid
      rw [show 9 + (j-9) = j by omega] at eq
      have ru : val C (List.ofFn x) u.val = x u := reads_raw C x u.isLt
      have rv : val C (List.ofFn x) v.val = x v := reads_raw C x v.isLt
      have ju : u.val < j := by omega
      have jv : v.val < j := by omega
      change val C (List.ofFn x) j = _
      rw [eq]
      rcases pins with hp | hp
      · simp only [hp, List.map_cons, List.map_nil, ite_eq_left ju, ite_eq_left jv, ru, rv, evalPair]
      · simp only [hp, List.map_cons, List.map_nil, ite_eq_left ju, ite_eq_left jv, ru, rv, evalPair, comm _ (x u)]
    have agree (w : ℕ) (valid : w < 17) (live : ∃ s ∈ S, path C w s)
        (wu : w ≠ u.val) (wv : w ≠ v.val) : observe C (row p) w = observe C (row n) w := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        by_cases raw : w < 9
        · rw [reads_raw C (row p) raw, reads_raw C (row n) raw]
          exact outside _ (fun h => wu (congrArg Fin.val h)) (fun h => wv (congrArg Fin.val h))
        by_cases sq : w = 9
        · subst w
          rw [seed,seed]
          exact seedSame
        by_cases wj : w = j
        · subst w
          rw [gate,gate]
          exact gateSame
        have inGates : w - 9 < C.gates.length := by omega
        have hp := val_gate (n := 9) (C := C) (x := List.ofFn (row p)) List.length_ofFn inGates
        have hn := val_gate (n := 9) (C := C) (x := List.ofFn (row n)) List.length_ofFn inGates
        have hw : 9 + (w-9) = w := by omega
        rw [hw] at hp hn
        change val C (List.ofFn (row p)) w = val C (List.ofFn (row n)) w
        rw [hp,hn]
        congr 1
        apply List.map_congr_left
        intro k hk
        by_cases lo : k < w
        · rw [ite_eq_left lo,ite_eq_left lo]
          have klive : ∃ s ∈ S, path C k s := by
            obtain ⟨s, hs, hpath⟩ := live
            exact ⟨s, hs, hpath.head ⟨by omega,valid,lo,hk⟩⟩
          exact ih k lo (by omega) klive
            (fun h => wj (unique w (by omega) valid live (Or.inl (h ▸ hk))))
            (fun h => wj (unique w (by omega) valid live (Or.inr (h ▸ hk))))
        · rw [ite_eq_right lo,ite_eq_right lo]
    exact ⟨row p, row n, diff, fun w hw => agree w (Finset.mem_range.mp (bound hw))
      ⟨w, hw, Relation.ReflTransGen.refl⟩ (fun h => un (h ▸ hw)) (fun h => vn (h ▸ hw))⟩

  let live (C : Circuit) (S : Finset ℕ) (j : ℕ) : Prop :=
    10 ≤ j ∧ j < 17 ∧ ∃ w ∈ S, path C j w
  let pins (C : Circuit) (j : ℕ) := (gateAt C (j-9)).inputs
  let obstruction (C : Circuit) (S : Finset ℕ) : Prop :=
    ∃ a b j : ℕ, a < b ∧ b < 9 ∧ live C S j ∧ a ∉ S ∧ b ∉ S ∧
      (pins C j = [a,b] ∨ pins C j = [b,a]) ∧
      ∀ k, live C S k → (a ∈ pins C k ∨ b ∈ pins C k) → k = j
  have obstructed (C : Circuit) (size : C.size = 8) (fan : FanInTwo C)
      (noNot : ∀ g ∈ C.gates, g.op ≠ GateOp.not)
      (seed : ∀ x : Fin 9 → Bool, observe C x 9 = (x 0 || x 2))
      (S : Finset ℕ) (bound : S ⊆ Finset.range 17) (h : obstruction C S) : collision C S := by
    obtain ⟨a,b,j,hab,hb,⟨jlo,jhi,_⟩,an,bn,pair,sole⟩ := h
    exact isolated C size fan noNot seed S bound j jlo jhi ⟨a,hab.trans hb⟩ ⟨b,hb⟩ hab
      pair an bn (fun k klo khi klive => sole k ⟨klo,khi,klive⟩)

  have budget (C : Circuit) (size : C.size = 8) (fan : FanInTwo C)
      (noNot : ∀ g ∈ C.gates, g.op ≠ GateOp.not)
      (seed : ∀ x : Fin 9 → Bool, observe C x 9 = (x 0 || x 2))
      (S : Finset ℕ) (bounded : S ⊆ Finset.range 17) (width : S.card = 6)
      (cover : ∀ i < 9, ∃ w ∈ S, path C i w) :
      collision C S ∨ ∃ J : Finset ℕ,
        (∀ j ∈ J, 10 ≤ j ∧ j < 17 ∧ ∃ w ∈ S, path C j w) ∧
        10 + (if 9 ∈ S then 1 else 0) ≤ S.card + J.card := by
    classical
    let A := (Finset.range 17).filter (fun i => ∃ w ∈ S, path C i w)
    let J := A.filter fun j => 10 ≤ j
    let base := if 9 ∈ S then Finset.range 10 else Finset.range 9
    have baseSize : base.card = 9 + (if 9 ∈ S then 1 else 0) := by
      by_cases sel : 9 ∈ S <;> simp [base,sel]
    have inA {i : ℕ} (hi : i < 17) (h : ∃ w ∈ S, path C i w) : i ∈ A :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,h⟩
    have reachable {j : ℕ} (hj : j ∈ J) : 10 ≤ j ∧ j < 17 ∧ ∃ w ∈ S, path C j w := by
      obtain ⟨ha,hj⟩ := Finset.mem_filter.mp hj
      obtain ⟨hr,h⟩ := Finset.mem_filter.mp ha
      exact ⟨hj,Finset.mem_range.mp hr,h⟩
    have base_condition {v : ℕ} (hv : v ∈ base) : v < 9 ∨ v = 9 ∧ 9 ∈ S := by
      unfold base at hv
      by_cases seed : 9 ∈ S
      · rw [ite_eq_left seed] at hv
        have h := Finset.mem_range.mp hv
        by_cases small : v < 9
        · exact Or.inl small
        · exact Or.inr ⟨by omega,seed⟩
      · rw [ite_eq_right seed] at hv
        exact Or.inl (Finset.mem_range.mp hv)
    have disjoint : Disjoint base J := by
      apply Finset.disjoint_left.mpr
      intro v hb hj
      have lo := (reachable hj).1
      rcases base_condition hb with h | ⟨h,_⟩ <;> omega
    have lo : base ∪ J ⊆ A := by
      intro v h
      rcases Finset.mem_union.mp h with h | h
      · rcases base_condition h with h | ⟨rfl,sel⟩
        · exact inA (by omega) (cover v h)
        · exact inA (by decide) ⟨9,sel,Relation.ReflTransGen.refl⟩
      · exact (Finset.mem_filter.mp h).1
    let pins (j : ℕ) := (gateAt C (j-9)).inputs
    let eff (j : ℕ) := (pins j).filter fun i => decide (i < j)
    let tokens := S.toList ++ J.toList.flatMap eff
    have effective {k i : ℕ} : i ∈ eff k ↔ i ∈ pins k ∧ i < k := by
      simp only [eff, List.mem_filter, decide_eq_true_eq]
    have cap {j : ℕ} (hj : j ∈ J) : (pins j).length ≤ 2 := by
      obtain ⟨late,jlt,_⟩ := reachable hj
      have gvalid : j-9 < C.gates.length := by
        change C.gates.length = 8 at size
        omega
      exact (fan _ (gateAt_mem gvalid)).2
    have capEff {j : ℕ} (hj : j ∈ J) : (eff j).length ≤ 2 := by
      exact (List.length_filter_le _ _).trans (cap hj)
    have coverTokens : A ⊆ tokens.toFinset := by
      intro v hv
      obtain ⟨w,hw,p⟩ := (Finset.mem_filter.mp hv).2
      simp only [tokens, List.mem_toFinset, List.mem_append, List.mem_flatMap, Finset.mem_toList]
      rcases p.cases_head with rfl | ⟨j,⟨late,jlt,lt,reads⟩,rest⟩
      · exact Or.inl hw
      · have hj : j ∈ J := Finset.mem_filter.mpr ⟨inA jlt ⟨w,hw,rest⟩,late⟩
        exact Or.inr ⟨j, hj, effective.mpr ⟨reads,lt⟩⟩
    have count (l : List ℕ) (hl : ∀ j ∈ l, (eff j).length ≤ 2) :
        (l.flatMap eff).length ≤ 2*l.length ∧
        ((l.flatMap eff).length = 2*l.length → ∀ j ∈ l, (eff j).length = 2) := by
      induction l with
      | nil => simp
      | cons j l ih =>
        have bj := hl j (by simp)
        obtain ⟨b, hx⟩ := ih (fun k h => hl k (List.mem_cons_of_mem j h))
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        refine ⟨by omega, ?_⟩
        intro he k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · omega
        · exact hx (by omega) k hk
    have countJ := count J.toList (fun j hj => capEff (Finset.mem_toList.mp hj))
    have lenTokens : tokens.length = S.card + (J.toList.flatMap eff).length := by simp [tokens]
    have lower := Finset.card_le_card lo
    rw [Finset.card_union_of_disjoint disjoint,baseSize] at lower
    have cardA := Finset.card_le_card coverTokens
    have cardTokens := List.toFinset_card_le tokens
    have lenA : (J.toList.flatMap eff).length ≤ 2*J.card := by simpa using countJ.1
    by_cases spare : 10 + (if 9 ∈ S then 1 else 0) ≤ S.card + J.card
    · exact Or.inr ⟨J,fun _ hj => reachable hj,spare⟩
    left
    have eqA : base ∪ J = A := Finset.eq_of_subset_of_card_le lo (by
      rw [Finset.card_union_of_disjoint disjoint, baseSize]
      omega)
    have eqTokens : A = tokens.toFinset := Finset.eq_of_subset_of_card_le coverTokens (by omega)
    have cardEq : tokens.toFinset.card = tokens.length := by omega
    have nt : tokens.Nodup := by
      exact (Multiset.toFinset_card_eq_card_iff_nodup (m := (tokens : Multiset ℕ))).mp cardEq
    have nd := List.nodup_append'.mp nt
    have disj := List.disjoint_left.mp nd.2.2
    have finalCap : (J.toList.flatMap eff).length = 2*J.toList.length := by
      rw [Finset.length_toList]
      omega
    have uniqueIn (l : List ℕ) (h : (l.flatMap eff).Nodup) :
        ∀ j k i : ℕ, j ∈ l → k ∈ l → i ∈ eff j → i ∈ eff k → j = k := by
      induction l with
      | nil => simp
      | cons a l ih =>
        rw [List.flatMap_cons, List.nodup_append'] at h
        intro j k i hj hk hij hik
        rcases List.mem_cons.mp hj with eqj | hjt
        · subst j
          rcases List.mem_cons.mp hk with eqk | hkt
          · exact eqk.symm
          · exact (List.disjoint_left.mp h.2.2 hij (List.mem_flatMap.mpr ⟨k,hkt,hik⟩)).elim
        · rcases List.mem_cons.mp hk with eqk | hkt
          · subst k
            exact (List.disjoint_left.mp h.2.2 hik (List.mem_flatMap.mpr ⟨j,hjt,hij⟩)).elim
          · exact ih h.2.1 j k i hjt hkt hij hik
    have jNonempty : J.Nonempty := Finset.card_pos.mp (by omega)
    let j := J.min' jNonempty
    have hj : j ∈ J := Finset.min'_mem J jNonempty
    obtain ⟨jlo,jhi,_⟩ := reachable hj
    have jList : j ∈ J.toList := Finset.mem_toList.mpr hj
    have lenj : (eff j).length = 2 := countJ.2 finalCap j jList
    have ndj : (eff j).Nodup := (List.nodup_flatMap.mp nd.2.1).1 j jList
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp lenj
    have ane : a ≠ b := by simpa [hab] using ndj
    have full : pins j = [a,b] := by
      have pct := cap hj
      have hs : (eff j).Sublist (pins j) := List.filter_sublist
      exact (hs.eq_of_length_le (by omega)).symm.trans hab
    have excluded {i : ℕ} (h : i ∈ eff j) : i ∉ S := by
      intro hs
      exact disj (Finset.mem_toList.mpr hs) (List.mem_flatMap.mpr ⟨j,jList,h⟩)
    have raw {i : ℕ} (h : i ∈ eff j) : i < 9 := by
      have hi : i ∈ A := by
        rw [eqTokens]
        exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨j,jList,h⟩))
      rw [← eqA] at hi
      rcases Finset.mem_union.mp hi with hi | hi
      · rcases base_condition hi with hi | ⟨rfl,hs⟩
        · exact hi
        · exact (excluded h hs).elim
      · have le : j ≤ i := Finset.min'_le J i hi
        exact (Nat.not_lt_of_ge le (effective.mp h).2).elim
    have am : a ∈ eff j := by simp [hab]
    have bm : b ∈ eff j := by simp [hab]
    let u : Fin 9 := ⟨a,raw am⟩
    let v : Fin 9 := ⟨b,raw bm⟩
    have sole (k : ℕ) (klo : 10 ≤ k) (khi : k < 17) (klive : ∃ w ∈ S, path C k w)
        (hread : a ∈ pins k ∨ b ∈ pins k) : k = j := by
      have km : k ∈ J.toList := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨inA khi klive,klo⟩)
      rcases hread with ha | hb
      · exact uniqueIn J.toList nd.2.1 k j a km jList (effective.mpr ⟨ha,by have := u.isLt; exact (raw am).trans_le (by omega)⟩) am
      · exact uniqueIn J.toList nd.2.1 k j b km jList (effective.mpr ⟨hb,by have := v.isLt; exact (raw bm).trans_le (by omega)⟩) bm
    rcases lt_or_gt_of_ne ane with h | h
    · exact isolated C size fan noNot seed S bounded j jlo jhi u v h
        (Or.inl full) (excluded am) (excluded bm) sole
    · exact isolated C size fan noNot seed S bounded j jlo jhi v u h
        (Or.inr full) (excluded bm) (excluded am) (fun k lo hi live reads => sole k lo hi live reads.symm)


  dsimp only
  intro C fan size noNot first selected bounded width
  have seed : ∀ x : Fin 9 → Bool, observe C x 9 = (x 0 || x 2) := first
  have off (S : Finset ℕ) (bound : S ⊆ Finset.range 17) (sz : S.card = 6) (no : 9 ∉ S) :
      collision C S := by
    by_cases bad : obstruction C S
    · exact obstructed C size fan noNot seed S bound bad
    by_cases coverage : ∀ i < 9, ∃ w ∈ S, path C i w
    · rcases budget C size fan noNot seed S bound sz coverage with h | ⟨J,live,cnt⟩
      · exact h
      · rw [ite_eq_right no,sz] at cnt
        exact without C fan size noNot first S bound sz no coverage ⟨J,by omega,live⟩ bad
    · exact missing C size seed S bound coverage
  have on_ (S : Finset ℕ) (bound : S ⊆ Finset.range 17) (sz : S.card = 6) (yes : 9 ∈ S)
      (essential : ¬ (0 ∈ S ∧ 2 ∈ S)) : collision C S := by
    by_cases bad : obstruction C S
    · exact obstructed C size fan noNot seed S bound bad
    by_cases coverage : ∀ i < 9, ∃ w ∈ S, path C i w
    · rcases budget C size fan noNot seed S bound sz coverage with h | ⟨J,live,cnt⟩
      · exact h
      · rw [ite_eq_left yes,sz] at cnt
        exact withSeed C fan size noNot first S bound sz yes essential coverage ⟨J,by omega,live⟩ bad
    · exact missing C size seed S bound coverage
  exact canonical C seed off on_ selected bounded width

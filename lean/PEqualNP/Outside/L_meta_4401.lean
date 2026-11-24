import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4401

def f (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def maskEval (m : ℕ) (x : Fin 9 → Bool) : Bool :=
  (List.finRange 9).any fun i => m.testBit ↑i && x i

def w0 (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 4 || x 6]

def args (m : ℕ) (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 4 || x 6, maskEval m x]

def targets : List ℕ :=
  [3, 5, 9, 17, 33, 65, 129, 257, 20, 36, 132, 144, 81, 84, 208]

lemma getD_append_left {α : Type} (l r : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge_length {α : Type} (l : List α) (d : α) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_snoc_ne {α : Type} (l : List α) (a d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [a]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_append_left l [a] d i hlt
  · rw [getD_ge_length _ _ _ (by simp; omega), getD_ge_length _ _ _ (by omega)]

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma getD_wiresFrom_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    unfold wiresFrom
    rw [List.foldl_cons]
    change (wiresFrom gs _).getD i false = _
    rw [ih _ i (by simp; omega), getD_append_left _ _ _ _ hi]

def mapGate (φ : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map φ⟩

def mapCircuit (φ : ℕ → ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mapGate φ), φ C.output⟩

lemma fanInTwo_mapCircuit (φ : ℕ → ℕ) (C : Circuit) (hC : FanInTwo C) :
    FanInTwo (mapCircuit φ C) := by
  intro g hg
  simp only [mapCircuit, List.mem_map] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  simpa [mapGate] using hC h hh

lemma size_mapCircuit (φ : ℕ → ℕ) (C : Circuit) :
    (mapCircuit φ C).size = C.size := by
  simp [mapCircuit, Circuit.size]

lemma wiresFrom_mapGate (φ : ℕ → ℕ) (gs : List Gate) :
    ∀ (uB uC : List Bool),
      uB.length = uC.length →
      (∀ L, uC.length ≤ L → L < uC.length + gs.length → ∀ w, (φ w = L ↔ w = L)) →
      (∀ w, uB.getD (φ w) false = uC.getD w false) →
      ∀ w, (wiresFrom (gs.map (mapGate φ)) uB).getD (φ w) false = (wiresFrom gs uC).getD w false := by
  induction gs with
  | nil =>
    intro uB uC _ _ hsim w
    exact hsim w
  | cons g gs ih =>
    intro uB uC hlen hfix hsim w
    have hmap : (mapGate φ g).inputs.map (fun i => uB.getD i false) =
        g.inputs.map (fun i => uC.getD i false) := by
      simp only [mapGate, List.map_map, Function.comp_def, hsim]
    let val := g.op.eval (g.inputs.map fun i => uC.getD i false)
    have stepB : wiresFrom ((g :: gs).map (mapGate φ)) uB =
        wiresFrom (gs.map (mapGate φ)) (uB ++ [val]) := by
      simp only [List.map_cons, wiresFrom, List.foldl_cons, hmap]
      rfl
    have stepC : wiresFrom (g :: gs) uC = wiresFrom gs (uC ++ [val]) := rfl
    rw [stepB, stepC]
    apply ih (uB ++ [val]) (uC ++ [val])
    · simp [hlen]
    · intro L hL1 hL2 u
      simp only [List.length_append, List.length_singleton] at hL1 hL2
      exact hfix L (by omega) (by simp; omega) u
    · intro u
      have hiff := hfix uC.length (Nat.le_refl _) (by simp) u
      by_cases hu : u = uC.length
      · have hφu : φ u = uB.length := by rw [hlen]; exact hiff.mpr hu
        rw [hφu, hu, getD_snoc_eq, getD_snoc_eq]
      · have hφu : φ u ≠ uB.length := by rw [hlen]; exact mt hiff.mp hu
        rw [getD_snoc_ne _ _ _ _ hφu, getD_snoc_ne _ _ _ _ hu]
        exact hsim u

lemma eval_mapCircuit (φ : ℕ → ℕ) (C : Circuit) (uB uC : List Bool)
    (hlen : uB.length = uC.length)
    (hfix : ∀ L, uC.length ≤ L → L < uC.length + C.gates.length → ∀ w, (φ w = L ↔ w = L))
    (hsim : ∀ w, uB.getD (φ w) false = uC.getD w false) :
    (mapCircuit φ C).eval uB = C.eval uC := by
  simp only [Circuit.eval, Circuit.wires, mapCircuit]
  exact wiresFrom_mapGate φ C.gates uB uC hlen hfix hsim C.output

def clamp (i : ℕ) : Fin 11 :=
  if h : i < 10 then ⟨i, by omega⟩ else ⟨10, by omega⟩

lemma getD_clamp (l : List Bool) (hl : l.length = 10) (i : ℕ) :
    l.getD (clamp i).val false = l.getD i false := by
  unfold clamp
  split
  · rfl
  · rw [getD_ge_length _ _ _ (by simp [hl]), getD_ge_length _ _ _ (by omega)]

def pairOfInputs : List ℕ → Fin 11 × Fin 11
  | [] => (⟨10, by omega⟩, ⟨10, by omega⟩)
  | [u] => (clamp u, ⟨10, by omega⟩)
  | u :: v :: _ => (clamp u, clamp v)

lemma or_eval_pairOfInputs (l : List Bool) (hl : l.length = 10) (ins : List ℕ) (hins : ins.length ≤ 2) :
    GateOp.or.eval (ins.map fun i => l.getD i false) =
      (l.getD (pairOfInputs ins).1.val false || l.getD (pairOfInputs ins).2.val false) := by
  have h10 : l.getD 10 false = false := getD_ge_length l false 10 (by omega)
  match ins, hins with
  | [], _ =>
    simp only [GateOp.eval, pairOfInputs, List.map_nil, List.any_nil, Bool.or_false, h10]
  | [u], _ =>
    simp only [GateOp.eval, pairOfInputs, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, id_eq, Bool.or_false, getD_clamp l hl, h10]
  | [u, v], _ =>
    simp only [GateOp.eval, pairOfInputs, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, id_eq, Bool.or_false, getD_clamp l hl]
  | _ :: _ :: _ :: _, hins => simp at hins

def wireMask (a : Fin 11) : ℕ :=
  if a.val < 9 then 1 <<< a.val else if a.val = 9 then 80 else 0

def rawMask (a b : Fin 11) : ℕ :=
  wireMask a ||| wireMask b

lemma any_or {α : Type} (l : List α) (p q : α → Bool) :
    l.any (fun a => p a || q a) = (l.any p || l.any q) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, ih]
    cases p a <;> cases q a <;> cases l.any p <;> cases l.any q <;> rfl

lemma maskEval_or (m1 m2 : ℕ) (x : Fin 9 → Bool) :
    maskEval (m1 ||| m2) x = (maskEval m1 x || maskEval m2 x) := by
  unfold maskEval
  rw [← any_or]
  congr 1
  ext i
  rw [Nat.testBit_or]
  cases m1.testBit ↑i <;> cases m2.testBit ↑i <;> cases x i <;> rfl

lemma w0_getD_lt9 (x : Fin 9 → Bool) (k : ℕ) (hk : k < 9) :
    (w0 x).getD k false = x ⟨k, hk⟩ := by
  unfold w0
  rw [getD_append_left _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hk]

lemma w0_getD_9 (x : Fin 9 → Bool) :
    (w0 x).getD 9 false = (x 4 || x 6) := by
  unfold w0
  have hlen : (List.ofFn x).length = 9 := by simp
  have h := getD_snoc_eq (List.ofFn x) (x 4 || x 6) false
  rwa [hlen] at h

lemma w0_getD_ge10 (x : Fin 9 → Bool) (k : ℕ) (hk : 10 ≤ k) :
    (w0 x).getD k false = false := by
  apply getD_ge_length
  simp [w0]
  omega

lemma w0_getD_eq_maskEval_fn :
    ∀ a : Fin 11, (fun x : Fin 9 → Bool => (w0 x).getD a.val false) = maskEval (wireMask a) := by
  decide +kernel

lemma w0_getD_eq_maskEval (a : Fin 11) (x : Fin 9 → Bool) :
    (w0 x).getD a.val false = maskEval (wireMask a) x :=
  congrFun (w0_getD_eq_maskEval_fn a) x

lemma w0_or_eq_rawMask (a b : Fin 11) (x : Fin 9 → Bool) :
    ((w0 x).getD a.val false || (w0 x).getD b.val false) = maskEval (rawMask a b) x := by
  rw [rawMask, maskEval_or, w0_getD_eq_maskEval, w0_getD_eq_maskEval]

lemma args_eq_w0_snoc (m : ℕ) (x : Fin 9 → Bool) :
    args m x = w0 x ++ [maskEval m x] := by
  simp [args, w0]

lemma args_getD_lt10 (m : ℕ) (x : Fin 9 → Bool) (w : ℕ) (hw : w < 10) :
    (args m x).getD w false = (w0 x).getD w false := by
  rw [args_eq_w0_snoc]
  exact getD_append_left (w0 x) [maskEval m x] false w (by simp [w0]; omega)

lemma args_getD_lt9 (m : ℕ) (x : Fin 9 → Bool) (w : ℕ) (hw : w < 9) :
    (args m x).getD w false = x ⟨w, hw⟩ := by
  rw [args_getD_lt10 m x w (by omega), w0_getD_lt9 x w hw]

lemma args_getD_9 (m : ℕ) (x : Fin 9 → Bool) :
    (args m x).getD 9 false = (x 4 || x 6) := by
  rw [args_getD_lt10 m x 9 (by omega), w0_getD_9 x]

lemma args_getD_10 (m : ℕ) (x : Fin 9 → Bool) :
    (args m x).getD 10 false = maskEval m x := by
  rw [args_eq_w0_snoc]
  have hlen : (w0 x).length = 10 := by simp [w0]
  have h := getD_snoc_eq (w0 x) (maskEval m x) false
  rwa [hlen] at h

lemma args_getD_ge11 (m : ℕ) (x : Fin 9 → Bool) (w : ℕ) (hw : 11 ≤ w) :
    (args m x).getD w false = false := by
  exact getD_ge_length (args m x) false w (by simp [args]; omega)

lemma args_getD_ne10 (m1 m2 : ℕ) (x : Fin 9 → Bool) (w : ℕ) (hw : w ≠ 10) :
    (args m1 x).getD w false = (args m2 x).getD w false := by
  rw [args_eq_w0_snoc, args_eq_w0_snoc]
  have hlen : (w0 x).length = 10 := by simp [w0]
  rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]

def repWire (c : Fin 11) : ℕ :=
  if c.val < 10 then c.val else 99

lemma args_getD_repWire (m : ℕ) (x : Fin 9 → Bool) (c : Fin 11) :
    (args m x).getD (repWire c) false = maskEval (wireMask c) x := by
  rw [← w0_getD_eq_maskEval c x]
  unfold repWire
  by_cases hc : c.val < 10
  · simp only [hc, ↓reduceIte]
    exact args_getD_lt10 m x c.val hc
  · simp only [hc, ↓reduceIte]
    rw [args_getD_ge11 m x 99 (by omega), w0_getD_ge10 x c.val (by omega)]

def perm (r : Fin 4) (i : Fin 9) : Fin 9 :=
  match r.val, i.val with
  | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 5 | 1, 3 => 8 | 1, 4 => 6
  | 1, 5 => 2 | 1, 6 => 4 | 1, 7 => 7 | 1, 8 => 3
  | 2, 0 => 3 | 2, 1 => 8 | 2, 2 => 5 | 2, 3 => 0 | 2, 4 => 4
  | 2, 5 => 2 | 2, 6 => 6 | 2, 7 => 7 | 2, 8 => 1
  | 3, 0 => 8 | 3, 1 => 3 | 3, 2 => 2 | 3, 3 => 1 | 3, 4 => 6
  | 3, 5 => 5 | 3, 6 => 4 | 3, 7 => 7 | 3, 8 => 0
  | _, _ => i

lemma perm_or46 (r : Fin 4) (x : Fin 9 → Bool) :
    (x (perm r 4) || x (perm r 6)) = (x 4 || x 6) := by
  obtain ⟨rv, hrv⟩ := r
  have hrc : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 := by omega
  rcases hrc with rfl | rfl | rfl | rfl
  · rfl
  · exact Bool.or_comm (x 6) (x 4)
  · rfl
  · exact Bool.or_comm (x 6) (x 4)

lemma f_perm_eq : ∀ r : Fin 4, (fun x : Fin 9 → Bool => f (fun i => x (perm r i))) = f := by
  decide +kernel

lemma f_perm (r : Fin 4) (x : Fin 9 → Bool) :
    f (fun i => x (perm r i)) = f x :=
  congrFun (f_perm_eq r) x

def packBits (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : ℕ :=
  (if b0 then 1 else 0) |||
  (if b1 then 2 else 0) |||
  (if b2 then 4 else 0) |||
  (if b3 then 8 else 0) |||
  (if b4 then 16 else 0) |||
  (if b5 then 32 else 0) |||
  (if b6 then 64 else 0) |||
  (if b7 then 128 else 0) |||
  (if b8 then 256 else 0)

lemma packBits_testBit :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      (packBits b0 b1 b2 b3 b4 b5 b6 b7 b8).testBit 0 = b0 ∧
      (packBits b0 b1 b2 b3 b4 b5 b6 b7 b8).testBit 1 = b1 ∧
      (packBits b0 b1 b2 b3 b4 b5 b6 b7 b8).testBit 2 = b2 ∧
      (packBits b0 b1 b2 b3 b4 b5 b6 b7 b8).testBit 3 = b3 ∧
      (packBits b0 b1 b2 b3 b4 b5 b6 b7 b8).testBit 4 = b4 ∧
      (packBits b0 b1 b2 b3 b4 b5 b6 b7 b8).testBit 5 = b5 ∧
      (packBits b0 b1 b2 b3 b4 b5 b6 b7 b8).testBit 6 = b6 ∧
      (packBits b0 b1 b2 b3 b4 b5 b6 b7 b8).testBit 7 = b7 ∧
      (packBits b0 b1 b2 b3 b4 b5 b6 b7 b8).testBit 8 = b8 := by
  decide +kernel

def permMask (r : Fin 4) (M : ℕ) : ℕ :=
  packBits
    (M.testBit (perm r 0).val) (M.testBit (perm r 1).val) (M.testBit (perm r 2).val)
    (M.testBit (perm r 3).val) (M.testBit (perm r 4).val) (M.testBit (perm r 5).val)
    (M.testBit (perm r 6).val) (M.testBit (perm r 7).val) (M.testBit (perm r 8).val)

lemma finRange9_eq :
    List.finRange 9 = [(0 : Fin 9), 1, 2, 3, 4, 5, 6, 7, 8] := by
  decide

lemma maskEval_expand (m : ℕ) (x : Fin 9 → Bool) :
    maskEval m x =
      ((m.testBit 0 && x 0) || ((m.testBit 1 && x 1) ||
       ((m.testBit 2 && x 2) || ((m.testBit 3 && x 3) ||
       ((m.testBit 4 && x 4) || ((m.testBit 5 && x 5) ||
       ((m.testBit 6 && x 6) || ((m.testBit 7 && x 7) ||
       (m.testBit 8 && x 8))))))))) := by
  unfold maskEval
  rw [finRange9_eq]
  simp

lemma maskEval_permMask (r : Fin 4) (M : ℕ) (x : Fin 9 → Bool) :
    maskEval (permMask r M) x = maskEval M (fun i => x (perm r i)) := by
  rw [maskEval_expand, maskEval_expand]
  have hp := packBits_testBit
    (M.testBit (perm r 0).val) (M.testBit (perm r 1).val) (M.testBit (perm r 2).val)
    (M.testBit (perm r 3).val) (M.testBit (perm r 4).val) (M.testBit (perm r 5).val)
    (M.testBit (perm r 6).val) (M.testBit (perm r 7).val) (M.testBit (perm r 8).val)
  unfold permMask
  rw [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
    hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2]
  obtain ⟨rv, hrv⟩ := r
  have hrc : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 := by omega
  rcases hrc with rfl | rfl | rfl | rfl
  · rfl
  · change ((M.testBit 1 && x 0) || ((M.testBit 0 && x 1) || ((M.testBit 5 && x 2) ||
        ((M.testBit 8 && x 3) || ((M.testBit 6 && x 4) || ((M.testBit 2 && x 5) ||
        ((M.testBit 4 && x 6) || ((M.testBit 7 && x 7) || (M.testBit 3 && x 8))))))))) =
      ((M.testBit 0 && x 1) || ((M.testBit 1 && x 0) || ((M.testBit 2 && x 5) ||
        ((M.testBit 3 && x 8) || ((M.testBit 4 && x 6) || ((M.testBit 5 && x 2) ||
        ((M.testBit 6 && x 4) || ((M.testBit 7 && x 7) || (M.testBit 8 && x 3)))))))))
    ac_rfl
  · change ((M.testBit 3 && x 0) || ((M.testBit 8 && x 1) || ((M.testBit 5 && x 2) ||
        ((M.testBit 0 && x 3) || ((M.testBit 4 && x 4) || ((M.testBit 2 && x 5) ||
        ((M.testBit 6 && x 6) || ((M.testBit 7 && x 7) || (M.testBit 1 && x 8))))))))) =
      ((M.testBit 0 && x 3) || ((M.testBit 1 && x 8) || ((M.testBit 2 && x 5) ||
        ((M.testBit 3 && x 0) || ((M.testBit 4 && x 4) || ((M.testBit 5 && x 2) ||
        ((M.testBit 6 && x 6) || ((M.testBit 7 && x 7) || (M.testBit 8 && x 1)))))))))
    ac_rfl
  · change ((M.testBit 8 && x 0) || ((M.testBit 3 && x 1) || ((M.testBit 2 && x 2) ||
        ((M.testBit 1 && x 3) || ((M.testBit 6 && x 4) || ((M.testBit 5 && x 5) ||
        ((M.testBit 4 && x 6) || ((M.testBit 7 && x 7) || (M.testBit 0 && x 8))))))))) =
      ((M.testBit 0 && x 8) || ((M.testBit 1 && x 3) || ((M.testBit 2 && x 2) ||
        ((M.testBit 3 && x 1) || ((M.testBit 4 && x 6) || ((M.testBit 5 && x 5) ||
        ((M.testBit 6 && x 4) || ((M.testBit 7 && x 7) || (M.testBit 8 && x 0)))))))))
    ac_rfl

def remapSymm (r : Fin 4) (w : ℕ) : ℕ :=
  if h : w < 9 then (perm r ⟨w, h⟩).val else w

lemma classify_rawMask : ∀ a b : Fin 11,
    (∃ c : Fin 11, rawMask a b = wireMask c) ∨
    (∃ r : Fin 4, permMask r (rawMask a b) ∈ targets) := by
  decide

lemma main :
    ∀ (C : Circuit) (g : Gate),
      FanInTwo C → C.size ≤ 15 →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
      circuitFun 9 C = f →
      C.gates[1]? = some g →
      g.op = GateOp.or →
      ∃ m ∈ targets, ∃ B : Circuit, FanInTwo B ∧ B.size ≤ 13 ∧ ∀ x : Fin 9 → Bool, B.eval (args m x) = f x := by
  intro C g hf hsz h9 heval hg1 hop
  obtain ⟨gs, out⟩ := C
  match gs, hf, hsz, h9, heval, hg1 with
  | [], _, _, _, _, hg1 => simp at hg1
  | [_], _, _, _, _, hg1 => simp at hg1
  | g0 :: g1 :: rest, hf, hsz, h9, heval, hg1 =>
    have hg_eq : g1 = g := by simpa using hg1
    subst g1
    have hrest_len : rest.length ≤ 13 := by
      simp only [Circuit.size, List.length_cons] at hsz
      omega
    have hg_in : g.inputs.length ≤ 2 := (hf g (by simp)).2
    let C_rest : Circuit := ⟨rest, out⟩
    have hCrest_fan : FanInTwo C_rest :=
      fun h hh => hf h (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hh))
    have hCrest_sz : C_rest.size ≤ 13 := hrest_len
    let a := (pairOfInputs g.inputs).1
    let b := (pairOfInputs g.inputs).2
    have hCrest_eval : ∀ y : Fin 9 → Bool, C_rest.eval (args (rawMask a b) y) = f y := by
      intro y
      have hy_fun : (Circuit.mk (g0 :: g :: rest) out).eval (List.ofFn y) = f y :=
        congrFun heval y
      have hw9 := h9 y
      simp only [Circuit.wires, List.foldl_cons] at hw9
      change (wiresFrom (g :: rest) _).getD 9 false = _ at hw9
      rw [getD_wiresFrom_lt _ _ 9 (by simp)] at hw9
      have hlen_y : (List.ofFn y).length = 9 := by simp
      have hb0 : g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false) = (y 4 || y 6) := by
        have hsnoc := getD_snoc_eq (List.ofFn y)
          (g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false)) false
        rw [hlen_y] at hsnoc
        exact hsnoc.symm.trans hw9
      have hw0_len : (w0 y).length = 10 := by simp [w0]
      have hb1 : g.op.eval (g.inputs.map fun i => (w0 y).getD i false) =
          maskEval (rawMask a b) y := by
        rw [hop, or_eval_pairOfInputs (w0 y) hw0_len g.inputs hg_in]
        exact w0_or_eq_rawMask a b y
      rw [← hy_fun]
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, C_rest]
      change (wiresFrom rest (args (rawMask a b) y)).getD out false =
        (wiresFrom rest ((List.ofFn y ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false)]) ++
          [g.op.eval (g.inputs.map fun i =>
            (List.ofFn y ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false)]).getD i false)])).getD out false
      rw [hb0]
      change (wiresFrom rest (args (rawMask a b) y)).getD out false =
        (wiresFrom rest (w0 y ++ [g.op.eval (g.inputs.map fun i => (w0 y).getD i false)])).getD out false
      rw [hb1, ← args_eq_w0_snoc]
    rcases classify_rawMask a b with ⟨c, hc⟩ | ⟨r, hr⟩
    · refine ⟨3, by simp [targets],
        mapCircuit (fun w => if w = 10 then repWire c else w) C_rest,
        fanInTwo_mapCircuit _ C_rest hCrest_fan,
        by rw [size_mapCircuit]; exact hCrest_sz, ?_⟩
      intro x
      rw [← hCrest_eval x, hc]
      apply eval_mapCircuit _ C_rest (args 3 x) (args (wireMask c) x)
      · simp [args]
      · intro L hL1 hL2 w
        have hlenC : (args (wireMask c) x).length = 11 := by simp [args]
        have hL_bounds : 11 ≤ L ∧ L < 24 := by
          simp only [C_rest, hlenC] at hL1 hL2
          omega
        have hrep_ne : repWire c ≠ L := by
          unfold repWire
          by_cases hlt : c.val < 10
          · simp only [hlt, ↓reduceIte]; omega
          · simp only [hlt, ↓reduceIte]; omega
        by_cases hw10 : w = 10
        · simp only [hw10, ↓reduceIte]
          exact ⟨fun h => absurd h hrep_ne, fun h => by omega⟩
        · simp only [hw10, ↓reduceIte]
      · intro w
        by_cases hw10 : w = 10
        · subst hw10
          simp only [↓reduceIte]
          rw [args_getD_repWire, args_getD_10]
        · simp only [hw10, ↓reduceIte]
          exact args_getD_ne10 3 (wireMask c) x w hw10
    · refine ⟨permMask r (rawMask a b), hr,
        mapCircuit (remapSymm r) C_rest,
        fanInTwo_mapCircuit _ C_rest hCrest_fan,
        by rw [size_mapCircuit]; exact hCrest_sz, ?_⟩
      intro x
      let y : Fin 9 → Bool := fun i => x (perm r i)
      rw [← f_perm r x, ← hCrest_eval y]
      apply eval_mapCircuit _ C_rest (args (permMask r (rawMask a b)) x) (args (rawMask a b) y)
      · simp [args]
      · intro L hL1 _ w
        have hlenC : (args (rawMask a b) y).length = 11 := by simp [args]
        unfold remapSymm
        by_cases hw9 : w < 9
        · simp only [hw9, ↓reduceDIte]
          have hp9 : (perm r ⟨w, hw9⟩).val < 9 := (perm r ⟨w, hw9⟩).isLt
          omega
        · simp only [hw9, ↓reduceDIte]
      · intro w
        unfold remapSymm
        by_cases hw9 : w < 9
        · simp only [hw9, ↓reduceDIte]
          have hp9 : (perm r ⟨w, hw9⟩).val < 9 := (perm r ⟨w, hw9⟩).isLt
          rw [args_getD_lt9 _ x _ hp9, args_getD_lt9 _ y w hw9]
        · simp only [hw9, ↓reduceDIte]
          by_cases hw_eq9 : w = 9
          · subst hw_eq9
            rw [args_getD_9, args_getD_9]
            exact (perm_or46 r x).symm
          · by_cases hw_eq10 : w = 10
            · subst hw_eq10
              rw [args_getD_10, args_getD_10]
              exact maskEval_permMask r (rawMask a b) x
            · rw [args_getD_ge11 _ _ w (by omega), args_getD_ge11 _ _ w (by omega)]

end PEqualNP.Outside.L_meta_4401

theorem PEqualNP.Outside.L_meta_4401 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : ℕ → (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : ℕ) (x3 : Fin (9 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)), (List.finRange (9 : ℕ)).any fun (x4 : Fin (9 : ℕ)) => x2.testBit ↑x4 && x3 x4]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : PEqualNP.CircuitLowerBounds.Gate), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (15 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), (x3.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = (x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 → x3.gates[(1 : ℕ)]? = Option.some x4 → x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∃ x11 ∈ [(3 : ℕ), (5 : ℕ), (9 : ℕ), (17 : ℕ), (33 : ℕ), (65 : ℕ), (129 : ℕ), (257 : ℕ), (20 : ℕ), (36 : ℕ), (132 : ℕ), (144 : ℕ), (81 : ℕ), (84 : ℕ), (208 : ℕ)], ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size ≤ (13 : ℕ) ∧ ∀ (x13 : Fin (9 : ℕ) → Bool), x12.eval (x2 x11 x13) = x1 x13 := by
  exact PEqualNP.Outside.L_meta_4401.main

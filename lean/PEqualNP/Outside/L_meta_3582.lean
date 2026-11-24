import PEqualNP.Defs

namespace PEqualNP.Outside.Lmeta3582

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def target : (Fin 9 → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))

private def inputs (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 || x 2]

private def reads (g : Gate) (v : Nat) : Bool :=
  (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v

private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def advance (w : List Bool) (g : Gate) : List Bool :=
  w ++ [value g w]

private theorem appendExcept {a b : List Bool} {s t : Bool} {v : Nat}
    (hlen : a.length = b.length)
    (same : ∀ i, i ≠ v → a.getD i false = b.getD i false) (ht : s = t) :
    ∀ i, i ≠ v → (a ++ [s]).getD i false = (b ++ [t]).getD i false := by
  intro i hi
  by_cases endAt : i = a.length
  · subst i
    simpa [← hlen] using ht
  · by_cases hlt : i < a.length
    · have hlt' : i < b.length := by omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt']
      exact same i hi
    · have hA : (a ++ [s]).length ≤ i := by simp; omega
      have hB : (b ++ [t]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ hA, List.getD_eq_default _ _ hB]

private theorem prefixPreserved (gs : List Gate) (w : List Bool) (i : Nat)
    (h : i < w.length) : (gs.foldl advance w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl advance (advance w g)).getD i false = w.getD i false
    rw [ih (advance w g) (by simp [advance]; omega)]
    exact List.getD_append _ _ _ _ h

private theorem rawGet (x : Fin 9 → Bool) (i : Fin 9) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
    List.getElem_ofFn]

private theorem rawExcept (x y : Fin 9 → Bool) (v : Fin 9)
    (h : ∀ i, i ≠ v → x i = y i) :
    ∀ i : Nat, i ≠ v.val →
      (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  intro i hi
  by_cases inRange : i < 9
  · let k : Fin 9 := ⟨i, inRange⟩
    change (List.ofFn x).getD k.val false = (List.ofFn y).getD k.val false
    rw [rawGet, rawGet]
    exact h k (fun e => hi (congrArg Fin.val e))
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt inRange),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt inRange)]

private theorem valueNoRead (g : Gate) (a b : List Bool) (v : Nat)
    (hOps : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hArity : g.inputs.length ≤ 2) (hNo : reads g v = false)
    (h : ∀ i, i ≠ v → a.getD i false = b.getD i false) :
    value g a = value g b := by
  rcases hOps with hop | hop | hop
  · have hv : v ∉ g.inputs := by
      simpa [reads, hop, GateOp.eval, List.take_of_length_le hArity] using hNo
    have hm : (g.inputs.map fun i => a.getD i false) =
        (g.inputs.map fun i => b.getD i false) :=
      List.map_congr_left (fun i hi => h i (fun e => hv (e ▸ hi)))
    rw [value, value, hm]
  · have hv : v ∉ g.inputs := by
      simpa [reads, hop, GateOp.eval, List.take_of_length_le hArity] using hNo
    have hm : (g.inputs.map fun i => a.getD i false) =
        (g.inputs.map fun i => b.getD i false) :=
      List.map_congr_left (fun i hi => h i (fun e => hv (e ▸ hi)))
    rw [value, value, hm]
  · cases hin : g.inputs with
    | nil => simp [value, hop, hin, GateOp.eval]
    | cons i is =>
      have hne : v ≠ i := by simpa [reads, hop, hin, GateOp.eval] using hNo
      have he := h i hne.symm
      simp only [List.getD_eq_getElem?_getD] at he
      simp [value, hop, hin, GateOp.eval, he]

private theorem valueAbsorb (g : Gate) (a b : List Bool) (v u : Nat) (isOr : Bool)
    (hop : g.op = (bif isOr then .or else .and))
    (hin : g.inputs = [v, u] ∨ g.inputs = [u, v])
    (ha : a.getD u false = isOr) (hb : b.getD u false = isOr) :
    value g a = value g b := by
  simp only [List.getD_eq_getElem?_getD] at ha hb
  cases isOr <;> rcases hin with h | h <;>
    simp [value, hop, h, GateOp.eval, ha, hb]

private theorem foldExcept
    (gs : List Gate) (a b : List Bool) (v u : Nat) (absorber : Bool)
    (hlen : a.length = b.length) (hu : u < a.length)
    (ha : a.getD u false = absorber) (hb : b.getD u false = absorber)
    (same : ∀ i, i ≠ v → a.getD i false = b.getD i false)
    (step : ∀ g ∈ gs, ∀ A B : List Bool,
      (∀ i, i ≠ v → A.getD i false = B.getD i false) →
      A.getD u false = absorber → B.getD u false = absorber →
      value g A = value g B) :
    ∀ i, i ≠ v → (gs.foldl advance a).getD i false = (gs.foldl advance b).getD i false := by
  induction gs generalizing a b with
  | nil => exact same
  | cons g gs ih =>
    have hv := step g (by simp) a b same ha hb
    have hu' : u < b.length := by omega
    change ∀ i, i ≠ v →
      (gs.foldl advance (advance a g)).getD i false =
      (gs.foldl advance (advance b g)).getD i false
    apply ih (advance a g) (advance b g)
    · simp [advance, hlen]
    · simp [advance]; omega
    · exact (List.getD_append _ _ _ _ hu).trans ha
    · exact (List.getD_append _ _ _ _ hu').trans hb
    · exact appendExcept hlen same hv
    · intro g' hg'
      exact step g' (List.mem_cons_of_mem _ hg')

private theorem oneReader (C : Circuit) (v : Nat) (g : Gate)
    (hg : g ∈ C.gates) (hr : reads g v = true)
    (small : (C.gates.filter (fun h => reads h v)).length < 2) :
    C.gates.filter (fun h => reads h v) = [g] := by
  have hm : g ∈ C.gates.filter (fun h => reads h v) := List.mem_filter.mpr ⟨hg, hr⟩
  generalize he : C.gates.filter (fun h => reads h v) = gs at hm small ⊢
  cases gs with
  | nil => simp at hm
  | cons h gs =>
    have hz : gs.length = 0 := by simp only [List.length_cons] at small; omega
    have hnil := List.length_eq_zero_iff.mp hz
    subst gs
    have hg' : g = h := by simpa using hm
    subst h
    rfl

private def masks (isOr : Bool) : List (List Nat) :=
  bif isOr then
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [1, 0, 4, 9, 20, 36, 64, 129, 257, 1],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [5, 18, 4, 0, 16, 36, 68, 144, 256, 4],
     [1, 10, 5, 8, 0, 40, 65, 129, 257, 1],
     [1, 130, 5, 9, 144, 0, 65, 128, 256, 1],
     [257, 2, 260, 10, 18, 34, 0, 130, 256, 257],
     [5, 34, 4, 40, 20, 32, 68, 0, 260, 4],
     [9, 10, 36, 8, 48, 32, 64, 136, 0, 9]]
  else
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [4, 0, 1, 1, 1, 1, 1, 1, 1, 64],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [4, 4, 16, 0, 4, 4, 4, 4, 4, 16],
     [8, 1, 1, 1, 0, 1, 1, 1, 1, 8],
     [128, 1, 1, 1, 1, 0, 1, 1, 1, 128],
     [2, 256, 2, 2, 2, 2, 0, 2, 2, 2],
     [4, 4, 32, 4, 4, 4, 4, 0, 4, 32],
     [8, 8, 8, 32, 8, 8, 8, 8, 0, 8]]

private def row (isOr : Bool) (v : Fin 9) (u : Fin 10) (b : Bool)
    (i : Fin 9) : Bool :=
  if i = v then b else (((masks isOr).getD v.val []).getD u.val 0).testBit i.val

set_option maxHeartbeats 1000000 in
private theorem rowsGood (isOr : Bool) :
    ∀ (v : Fin 9) (u : Fin 10), v ≠ 0 → v ≠ 2 → v.castSucc ≠ u →
    target (row isOr v u false) = false ∧ target (row isOr v u true) = true ∧
    (inputs (row isOr v u false)).getD u.val false = isOr ∧
    (inputs (row isOr v u true)).getD u.val false = isOr := by
  cases isOr <;> decide +kernel

private theorem singletonFalse : ∀ v : Fin 9, target (fun j => decide (j = v)) = false := by
  decide +kernel

theorem twice (C : Circuit) (hFan : FanInTwo C)
    (computes : ∀ x, C.eval (inputs x) = target x)
    (v : Fin 9) (u : Fin 10) (h0 : v ≠ 0) (h2 : v ≠ 2) (hvu : v.castSucc ≠ u)
    (g : Gate) (hg : g ∈ C.gates) (hop : g.op = .and ∨ g.op = .or)
    (hin : g.inputs = [v.val, u.val] ∨ g.inputs = [u.val, v.val]) :
    2 ≤ (C.gates.filter (fun h => reads h v.val)).length := by
  have hout : C.output ≠ v.val := by
    intro hout
    let x : Fin 9 → Bool := fun j => decide (j = v)
    have hRange : v.val < (inputs x).length := by
      have := v.isLt
      simp [inputs]; omega
    have hv : (inputs x).getD v.val false = true := by
      unfold inputs
      rw [List.getD_append _ _ _ _ (by simp), rawGet]
      simp [x]
    have hEval : C.eval (inputs x) = true := by
      change (C.gates.foldl advance (inputs x)).getD C.output false = true
      rw [hout, prefixPreserved _ _ _ hRange]
      exact hv
    rw [computes x, singletonFalse v] at hEval
    contradiction
  by_contra hCount
  have hCount' : (C.gates.filter (fun h => reads h v.val)).length < 2 := by omega
  have hRead : reads g v.val = true := by
    rcases hop with ho | ho <;> rcases hin with hi | hi <;>
      simp [reads, ho, hi, GateOp.eval]
  have hSingle := oneReader C v.val g hg hRead hCount'
  let isOr : Bool := match g.op with
    | .or => true
    | _ => false
  have gOp : g.op = (bif isOr then .or else .and) := by
    rcases hop with hr | hr <;> simp [isOr, hr]
  let x := row isOr v u false
  let y := row isOr v u true
  obtain ⟨hX, hY, ha, hb⟩ := rowsGood isOr v u h0 h2 hvu
  have hRaw : ∀ i : Fin 9, i ≠ v → x i = y i := by
    intro i hi
    simp [x, y, row, hi]
  have hPrep : (x 0 || x 2) = (y 0 || y 2) := by
    rw [hRaw 0 h0.symm, hRaw 2 h2.symm]
  have hInput : ∀ i, i ≠ v.val → (inputs x).getD i false = (inputs y).getD i false :=
    appendExcept (by simp) (rawExcept x y v hRaw) hPrep
  have hStep : ∀ h ∈ C.gates, ∀ A B : List Bool,
      (∀ i, i ≠ v.val → A.getD i false = B.getD i false) →
      A.getD u.val false = isOr → B.getD u.val false = isOr →
      value h A = value h B := by
    intro h hh A B agree ha' hb'
    cases hr : reads h v.val
    case false =>
      have hOp : h.op = .and ∨ h.op = .or ∨ h.op = .not := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hFan h hh).1
      exact valueNoRead h A B v.val hOp (hFan h hh).2 hr agree
    case true =>
      have hm : h ∈ C.gates.filter (fun h => reads h v.val) :=
        List.mem_filter.mpr ⟨hh, hr⟩
      have hG : h = g := by simpa [hSingle] using hm
      subst h
      exact valueAbsorb g A B v.val u.val isOr gOp hin ha' hb'
  have hu : u.val < (inputs x).length := by simp [inputs]
  have hEq := foldExcept C.gates (inputs x) (inputs y) v.val u.val isOr
    (by simp [inputs]) hu ha hb hInput hStep C.output hout
  change C.eval (inputs x) = C.eval (inputs y) at hEq
  rw [computes x, computes y, hX, hY] at hEq
  contradiction

end PEqualNP.Outside.Lmeta3582

theorem PEqualNP.Outside.L_meta_3582 :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = x1 x4) → ∀ (x5 : Fin (9 : ℕ)) (x6 : Fin (10 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) → x5 ≠ (2 : Fin (9 : ℕ)) → x5.castSucc ≠ x6 → ∀ x10 ∈ x2.gates, x10.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10.inputs = [↑x5, ↑x6] ∨ x10.inputs = [↑x6, ↑x5] → (2 : ℕ) ≤ (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x5) x2.gates).length := by
  exact PEqualNP.Outside.Lmeta3582.twice


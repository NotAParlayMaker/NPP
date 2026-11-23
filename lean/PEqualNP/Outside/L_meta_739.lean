import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_739

open PEqualNP.CircuitLowerBounds

def scan {α : Type} (op : GateOp → List α → α) (d : α) (gs : List Gate) (a : List α) :=
  gs.foldl (fun w g => w ++ [op g.op (g.inputs.map (fun i => w.getD i d))]) a

def stepValue {α : Type} (op : GateOp → List α → α) (d : α) (a : List α) (g : Gate) :=
  op g.op (g.inputs.map (fun i => a.getD i d))

theorem scan_cons {α : Type} (op : GateOp → List α → α) (d : α) (g : Gate)
    (gs : List Gate) (a : List α) :
    scan op d (g :: gs) a = scan op d gs (a ++ [stepValue op d a g]) := rfl

theorem scan_append {α : Type} (op : GateOp → List α → α) (d : α) (gs hs : List Gate)
    (a : List α) : scan op d (gs ++ hs) a = scan op d hs (scan op d gs a) := by
  simp [scan, List.foldl_append]

theorem scan_length {α : Type} (op : GateOp → List α → α) (d : α)
    (gs : List Gate) (a : List α) : (scan op d gs a).length = a.length + gs.length := by
  induction gs generalizing a with
  | nil => simp [scan]
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

theorem read_below {α : Type} (a b : List α) (d : α) (i : ℕ) (hi : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem read_above {α : Type} (a : List α) (d : α) (i : ℕ) (hi : a.length ≤ i) :
    a.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

theorem read_snoc_self {α : Type} (a : List α) (b d : α) :
    (a ++ [b]).getD a.length d = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

theorem scan_prefix {α : Type} (op : GateOp → List α → α) (d : α)
    (gs : List Gate) (a : List α) (i : ℕ) (hi : i < a.length) :
    (scan op d gs a).getD i d = a.getD i d := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega), read_below _ _ _ _ hi]

theorem scan_gate {α : Type} (op : GateOp → List α → α) (d : α) (gs : List Gate)
    (a : List α) (j : ℕ) (hj : j < gs.length) :
    (scan op d gs a).getD (a.length + j) d =
      op gs[j].op (gs[j].inputs.map fun i =>
        if i < a.length + j then (scan op d gs a).getD i d else d) := by
  let w := scan op d (gs.take j) a
  have hw : w.length = a.length + j := by
    simp [w, scan_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hgs : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hf : scan op d gs a = scan op d (gs[j] :: gs.drop (j + 1)) w := by
    conv_lhs => rw [hgs]
    rw [scan_append]
  have hp : ∀ i < a.length + j, (scan op d gs a).getD i d = w.getD i d := by
    intro i hi
    rw [hf]
    exact scan_prefix op d _ w _ (by omega)
  calc
    (scan op d gs a).getD (a.length + j) d = stepValue op d w gs[j] := by
      rw [hf, scan_cons, ← hw, scan_prefix op d _ _ _ (by simp), read_snoc_self]
    _ = _ := by
      unfold stepValue
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < a.length + j
      · rw [ite_eq_left hi, hp i hi]
      · rw [ite_eq_right hi, read_above w d i (by omega)]

def degOp (op : GateOp) (values : List ℕ) : ℕ :=
  @ite ℕ (op = GateOp.and) (lineDegreeGateOpDecEq op GateOp.and) values.sum
    (values.foldr max 0)

def initialDegrees (n : ℕ) (marked : Finset ℕ) : List ℕ :=
  (List.range n).map fun i => if i ∈ marked then 1 else 0

theorem degrees_scan (C : Circuit) (n : ℕ) (marked : Finset ℕ) :
    C.lineDegrees n marked = scan degOp 0 C.gates (initialDegrees n marked) := rfl

theorem wires_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan GateOp.eval false C.gates x := rfl

def Reads (n : ℕ) (C : Circuit) (a b : ℕ) :=
  a < b ∧ ∃ j : Fin C.gates.length, b = n + j.val ∧ a ∈ (C.gates.get j).inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) :=
  Relation.ReflTransGen (Reads n C) i C.output

theorem live_of_read {n : ℕ} {C : Circuit} {a b : ℕ}
    (h : Reads n C a b) (hb : Live n C b) : Live n C a :=
  Relation.ReflTransGen.head h hb

def shift (d i : ℕ) := if i < d then i else i - 1

def renumber (d : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift d)⟩

def removeGate (n j : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (renumber (n + j)), shift (n + j) C.output⟩

-- Deleting an unreferenced wire shifts each later index by one.
theorem scan_delete_tail {α : Type} (op : GateOp → List α → α) (d : α)
    (gone : ℕ) (post : List Gate) (large small : List α)
    (hLen : small.length + 1 = large.length) (hGone : gone < large.length)
    (hMatch : ∀ i, i ≠ gone → small.getD (shift gone i) d = large.getD i d)
    (hPost : ∀ g ∈ post, gone ∉ g.inputs) :
    ∀ i, i ≠ gone →
      (scan op d (post.map (renumber gone)) small).getD (shift gone i) d =
        (scan op d post large).getD i d := by
  induction post generalizing large small with
  | nil => simpa [scan] using hMatch
  | cons g post ih =>
    have hs : stepValue op d small (renumber gone g) = stepValue op d large g := by
      unfold stepValue renumber
      simp only [List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro i him
      apply hMatch
      intro he
      exact hPost g (by simp) (he ▸ him)
    simp only [List.map_cons, scan_cons, hs]
    refine ih _ _ (by simp; omega) (by simp; omega) ?_
      (fun g' hg' => hPost g' (by simp [hg']))
    intro i hi
    have hShift : shift gone i = (if i < gone then i else i - 1) := rfl
    rcases lt_trichotomy i large.length with hil | hie | hig
    · have hsm : shift gone i < small.length := by split at hShift <;> omega
      rw [read_below _ _ _ _ hsm, read_below _ _ _ _ hil, hMatch i hi]
    · have hsm : shift gone i = small.length := by split at hShift <;> omega
      rw [hsm, hie, read_snoc_self, read_snoc_self]
    · have hsm : small.length + 1 ≤ shift gone i := by split at hShift <;> omega
      rw [read_above _ _ _ (by simp; omega), read_above _ _ _ (by simp; omega)]

theorem remove_preserves {α : Type} (op : GateOp → List α → α) (d : α)
    (C : Circuit) (x : List α) (n j : ℕ) (hx : x.length = n) (hj : j < C.gates.length)
    (ho : C.output ≠ n + j)
    (hr : ∀ g ∈ C.gates.drop (j + 1), n + j ∉ g.inputs) :
    (scan op d (removeGate n j C).gates x).getD (removeGate n j C).output d =
      (scan op d C.gates x).getD C.output d := by
  let w := scan op d (C.gates.take j) x
  let v := stepValue op d w C.gates[j]
  have hw : w.length = n + j := by
    simp [w, scan_length, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hf : scan op d C.gates x = scan op d (C.gates.drop (j + 1)) (w ++ [v]) := by
    conv_lhs =>
      rw [← List.take_append_drop j C.gates, List.drop_eq_getElem_cons hj, scan_append, scan_cons]
  rw [hf]
  change (scan op d (C.gates.take j ++ _) x).getD (shift (n + j) C.output) d = _
  rw [scan_append]
  apply scan_delete_tail op d (n + j) _ (w ++ [v]) w (by simp) (by simp [hw]) ?_ hr _ ho
  intro i hi
  rcases lt_or_gt_of_ne hi with hil | hig
  · rw [shift, ite_eq_left hil, read_below _ _ _ _ (by omega)]
  · rw [shift, ite_eq_right (by omega), read_above w d _ (by omega),
      read_above (w ++ [v]) d _ (by simp; omega)]

theorem remove_mono (n j : ℕ) (C : Circuit)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    IsMonotoneCircuit (removeGate n j C) ∧
      ∀ g ∈ (removeGate n j C).gates, g.inputs.length ≤ 2 := by
  have h : ∀ g ∈ (removeGate n j C).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact ⟨hm g (List.mem_of_mem_take hg), hf g (List.mem_of_mem_take hg)⟩
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have hmem := List.mem_of_mem_drop hg'
      exact ⟨hm g' hmem, by simpa [renumber] using hf g' hmem⟩
  exact ⟨fun g hg => (h g hg).1, fun g hg => (h g hg).2⟩

-- A least circuit with the same evaluations and degree bound has no unused gate.
theorem reduce_to_live (n : ℕ) (C : Circuit) (hm : IsMonotoneCircuit C)
    (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (M : Finset ℕ)
    (hd : HasLineDegree n M C 1) :
    ∃ D : Circuit, D.size ≤ C.size ∧ IsMonotoneCircuit D ∧
      (∀ g ∈ D.gates, g.inputs.length ≤ 2) ∧ HasLineDegree n M D 1 ∧
      (∀ x : List Bool, x.length = n → D.eval x = C.eval x) ∧
      ∀ j : Fin D.gates.length, Live n D (n + j.val) := by
  classical
  let ok (s : ℕ) := ∃ D : Circuit, D.size = s ∧ IsMonotoneCircuit D ∧
    (∀ g ∈ D.gates, g.inputs.length ≤ 2) ∧ HasLineDegree n M D 1 ∧
    ∀ x : List Bool, x.length = n → D.eval x = C.eval x
  have hex : ∃ s, ok s := ⟨C.size, C, rfl, hm, hf, hd, fun _ _ => rfl⟩
  obtain ⟨D, hsz, hD, hF, hDeg, he⟩ := Nat.find_spec hex
  refine ⟨D, hsz.trans_le (Nat.find_min' hex ⟨C, rfl, hm, hf, hd, fun _ _ => rfl⟩),
    hD, hF, hDeg, he, ?_⟩
  intro j
  by_contra hbad
  let bad := (Finset.range D.gates.length).filter (fun i => ¬ Live n D (n + i))
  have hmem : j.val ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, hbad⟩
  let r := bad.max' ⟨j.val, hmem⟩
  have hmax : r ∈ bad := Finset.max'_mem bad _
  have hr : r < D.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hmax).1
  have hdead : ¬ Live n D (n + r) := (Finset.mem_filter.mp hmax).2
  have ho : D.output ≠ n + r := by
    intro h
    exact hdead (h ▸ Relation.ReflTransGen.refl)
  have hpost : ∀ g ∈ D.gates.drop (r + 1), n + r ∉ g.inputs := by
    intro g hg hread
    obtain ⟨k, hk, hgk⟩ := List.mem_iff_getElem.mp hg
    have hlt : r + 1 + k < D.gates.length := by
      simp only [List.length_drop] at hk
      omega
    have hkG : D.gates[r + 1 + k] = g := by
      simpa using hgk
    have hLive : Live n D (n + (r + 1 + k)) := by
      by_contra h
      have hm' : r + 1 + k ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, h⟩
      have hle : r + 1 + k ≤ r := Finset.le_max' bad _ hm'
      omega
    apply hdead (live_of_read ?_ hLive)
    refine ⟨by omega, ⟨⟨r + 1 + k, hlt⟩, rfl, ?_⟩⟩
    change n + r ∈ (D.gates[r + 1 + k]).inputs
    rwa [hkG]
  let E := removeGate n r D
  obtain ⟨hEM, hEF⟩ := remove_mono n r D hD hF
  have hED : HasLineDegree n M E 1 := by
    unfold HasLineDegree Circuit.lineDeg at hDeg ⊢
    rw [degrees_scan, remove_preserves degOp 0 D (initialDegrees n M) n r
      (by simp [initialDegrees]) hr ho hpost, ← degrees_scan]
    exact hDeg
  have hEE : ∀ x : List Bool, x.length = n → E.eval x = C.eval x := by
    intro x hx
    rw [← he x hx]
    simp only [Circuit.eval, wires_scan]
    exact remove_preserves GateOp.eval false D x n r hx hr ho hpost
  have hEsz : E.size < D.size := by
    simp only [E, removeGate, Circuit.size, List.length_append, List.length_map,
      List.length_take, List.length_drop]
    omega
  have hmin := Nat.find_min' hex (show ok E.size from ⟨E, rfl, hEM, hEF, hED, hEE⟩)
  omega

theorem eval_agrees_on_live {n : ℕ} (C : Circuit) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (ha : ∀ i < n, Live n C i → x.getD i false = y.getD i false) :
    C.eval x = C.eval y := by
  have hh : ∀ i, Live n C i → (C.wires x).getD i false = (C.wires y).getD i false := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hLive
      by_cases hi : i < n
      · simp only [wires_scan]
        rw [scan_prefix _ _ _ _ _ (by omega), scan_prefix _ _ _ _ _ (by omega)]
        exact ha i hi hLive
      · by_cases hg : i < n + C.gates.length
        · let j := i - n
          have hj : j < C.gates.length := by omega
          have hij : n + j = i := by omega
          have hxf := scan_gate GateOp.eval false C.gates x j hj
          have hyf := scan_gate GateOp.eval false C.gates y j hj
          rw [hx, hij] at hxf
          rw [hy, hij] at hyf
          rw [wires_scan, wires_scan, hxf, hyf]
          congr 1
          apply List.map_congr_left
          intro k hk
          by_cases hk' : k < i
          · simp only [ite_eq_left hk']
            apply ih k hk'
            exact live_of_read ⟨hk', ⟨⟨j, hj⟩, hij.symm, hk⟩⟩ hLive
          · simp [hk']
        · simp only [wires_scan]
          rw [read_above _ _ _ (by rw [scan_length, hx]; omega),
              read_above _ _ _ (by rw [scan_length, hy]; omega)]
  exact hh _ Relation.ReflTransGen.refl

def BoolLe (x y : List Bool) : Prop :=
  ∀ i, x.getD i false = true → y.getD i false = true

theorem mono_step {w w' : List Bool} (h : BoolLe w w') (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    stepValue GateOp.eval false w g = true → stepValue GateOp.eval false w' g = true := by
  rcases hg with e | e
  · simp only [stepValue, e, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hb i hi => h i (hb i hi)
  · simp only [stepValue, e, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hb⟩
    exact ⟨i, hi, h i hb⟩

theorem mono_scan (gs : List Gate) (hM : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hLen : x.length = y.length) (h : BoolLe x y) :
    BoolLe (scan GateOp.eval false gs x) (scan GateOp.eval false gs y) := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    simp only [scan_cons]
    apply ih (fun h' hh' => hM h' (by simp [hh'])) _ _ (by simpa using hLen)
    intro i
    rcases lt_trichotomy i x.length with hil | hie | hig
    · rw [read_below _ _ _ _ hil, read_below _ _ _ _ (by omega)]
      exact h i
    · rw [hie, read_snoc_self, hLen, read_snoc_self]
      exact mono_step h g (hM g (by simp))
    · rw [read_above _ _ _ (by simp; omega), read_above _ _ _ (by simp; omega)]
      simp

theorem mono_circuit {C : Circuit} (hM : IsMonotoneCircuit C) {x y : List Bool}
    (hLen : x.length = y.length) (h : BoolLe x y) : BoolLe (C.wires x) (C.wires y) :=
  mono_scan C.gates hM x y hLen h

def binaryGate (fallback : ℕ) (g : Gate) (base : ℕ → Bool) : Gate :=
  ⟨g.op, match g.inputs with
    | [] => [fallback, fallback]
    | [a] => [a, a]
    | a :: b :: _ => if @decide (g.op = GateOp.and) (lineDegreeGateOpDecEq g.op GateOp.and) then
        if base a then [b, b] else if base b then [a, a] else [a, b]
      else [a, b]⟩

theorem binaryGate_size (fallback : ℕ) (g : Gate) (base : ℕ → Bool) :
    (binaryGate fallback g base).inputs.length = 2 := by
  rcases g with ⟨op, ins⟩
  cases ins with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      simp only [binaryGate]
      repeat' first | rfl | split

theorem binaryGate_eval (f : ℕ) (g : Gate) (b u v : ℕ → Bool)
    (hM : g.op = GateOp.and ∨ g.op = GateOp.or) (hF : g.inputs.length ≤ 2)
    (hTrue : ∀ i, b i = true → u i = true)
    (hFalse : ∀ i, b i = false → v i = u i)
    (h0 : g.op.eval (g.inputs.map b) = false) (hf : v f = false) :
    (binaryGate f g b).op.eval ((binaryGate f g b).inputs.map v) = g.op.eval (g.inputs.map u) := by
  rcases g with ⟨op, ins⟩
  rcases hM with rfl | rfl <;> cases ins with
  | nil => simp_all [binaryGate, GateOp.eval]
  | cons a ins =>
    cases ins with
    | nil =>
      have hb : b a = false := by simpa [GateOp.eval] using h0
      simp [binaryGate, GateOp.eval, hFalse a hb]
    | cons j ins =>
      cases ins with
      | cons z zs => simp at hF
      | nil =>
        cases ha : b a <;> cases hj : b j <;>
          simp_all [binaryGate, GateOp.eval]

def binaryCircuit (n : ℕ) (C : Circuit) (z : List Bool) : Circuit :=
  ⟨List.ofFn (fun j : Fin C.gates.length =>
    binaryGate (n + C.gates.length) (C.gates.get j) (fun i =>
      if i < n + j.val then (C.wires z).getD i false else false)), C.output⟩

-- Fold constant-true wires and duplicate unary inputs to preserve every wire that is false at zero.
theorem binary_wires (n : ℕ) (C : Circuit) (hM : IsMonotoneCircuit C)
    (hF : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (x z : List Bool) (hx : x.length = n)
    (hz : z.length = n) (hzx : BoolLe z x) :
    ∀ i, (C.wires z).getD i false = false →
      ((binaryCircuit n C z).wires x).getD i false = (C.wires x).getD i false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h0
    let D := binaryCircuit n C z
    have hLen : D.gates.length = C.gates.length := by simp [D, binaryCircuit]
    have hmon := mono_circuit hM (hx ▸ hz) hzx
    by_cases hi : i < n
    · simp only [wires_scan]
      rw [scan_prefix _ _ _ _ _ (by omega), scan_prefix _ _ _ _ _ (by omega)]
    · by_cases hg : i < n + C.gates.length
      · let j := i - n
        have hj : j < C.gates.length := by omega
        have hj' : j < D.gates.length := by omega
        have hij : n + j = i := by omega
        let g := C.gates[j]
        have hm := hM g (List.getElem_mem hj)
        have hf := hF g (List.getElem_mem hj)
        let b := fun k => if k < i then (C.wires z).getD k false else false
        let u := fun k => if k < i then (C.wires x).getD k false else false
        let v := fun k => if k < i then (D.wires x).getD k false else false
        have hb : g.op.eval (g.inputs.map b) = false := by
          have hsz := scan_gate GateOp.eval false C.gates z j hj
          rw [hz, hij] at hsz
          rw [wires_scan] at h0
          exact hsz.symm.trans h0
        have htrue : ∀ k, b k = true → u k = true := by
          intro k hk
          by_cases hki : k < i
          · exact by simpa [u, hki] using hmon k (by simpa [b, hki] using hk)
          · simp [b, hki] at hk
        have hfalse : ∀ k, b k = false → v k = u k := by
          intro k hk
          by_cases hki : k < i
          · simpa [u, v, hki] using ih k hki (by simpa [b, hki] using hk)
          · simp [u, v, hki]
        have hfallback : v (n + C.gates.length) = false :=
          ite_eq_right (show ¬ n + C.gates.length < i by omega)
        have hG : D.gates[j]'hj' = binaryGate (n + C.gates.length) g b := by
          simp [D, binaryCircuit, g, b, hij]
        have hdx := scan_gate GateOp.eval false D.gates x j hj'
        have hcx := scan_gate GateOp.eval false C.gates x j hj
        rw [hx, hij, hG, ← wires_scan ⟨D.gates, D.output⟩] at hdx
        rw [hx, hij, ← wires_scan C] at hcx
        exact hdx.trans ((binaryGate_eval (n + C.gates.length) g b u v hm hf htrue hfalse hb hfallback).trans hcx.symm)
      · simp only [wires_scan]
        rw [read_above _ _ _ (by rw [scan_length, hx, hLen]; omega),
            read_above _ _ _ (by rw [scan_length, hx]; omega)]

def oneHot {n : ℕ} (i : Fin n) (j : Fin n) : Bool := decide (j = i)

theorem oneHot_card {n : ℕ} (i : Fin n) :
    (Finset.univ.filter (fun j : Fin n => oneHot i j = true)).card = 1 := by
  have h : Finset.univ.filter (fun j : Fin n => oneHot i j = true) = {i} := by
    ext j
    simp [oneHot]
  simp [h]

theorem zeros_card (n : ℕ) :
    (Finset.univ.filter (fun _ : Fin n => (false : Bool) = true)).card = 0 := by simp

theorem zero_getD (n i : ℕ) :
    (List.ofFn (fun _ : Fin n => (false : Bool))).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> rfl

theorem ofFn_read {n : ℕ} (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi]
  rfl

theorem zero_lines_le {P L : ℕ} (x : Fin P → Bool) (y : Fin L → Bool) :
    BoolLe (List.ofFn x ++ List.ofFn (fun _ : Fin L => false)) (List.ofFn x ++ List.ofFn y) := by
  intro i hi
  by_cases h : i < (List.ofFn x).length
  · rwa [read_below _ _ _ _ h, ← read_below _ (List.ofFn (fun _ : Fin L => false)) _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega), zero_getD] at hi
    contradiction

-- If the one-line test changes the value, the corresponding input reaches the output.
theorem every_line_live {P L : ℕ} (C : Circuit) (w : Fin L) (x : Fin P → Bool)
    (hne : C.eval (List.ofFn x ++ List.ofFn (oneHot w)) ≠
      C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false))) :
    Live (P + L) C (P + w.val) := by
  by_contra h
  apply hne
  apply eval_agrees_on_live (n := P + L) C _ _ (by simp) (by simp)
  intro i hi hLive
  by_cases hP : i < (List.ofFn x).length
  · rw [read_below _ _ _ _ hP, read_below _ _ _ _ hP]
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), zero_getD]
    simp only [List.length_ofFn]
    have hlt : i - P < L := by simp only [List.length_ofFn] at hP; omega
    rw [ofFn_read _ hlt]
    have hne' : (⟨i - P, hlt⟩ : Fin L) ≠ w := by
      intro he
      have hv := congrArg Fin.val he
      change i - P = w.val at hv
      simp only [List.length_ofFn] at hP
      exact h ((show i = P + w.val by omega) ▸ hLive)
    simp [oneHot, hne']

theorem binary_good (n : ℕ) (D : Circuit) (z : List Bool) :
    ∀ g ∈ (binaryCircuit n D z).gates, g.inputs.length = 2 := by
  intro g hg
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  exact binaryGate_size _ _ _

theorem binary_mono (n : ℕ) (D : Circuit) (z : List Bool) (hM : IsMonotoneCircuit D) :
    IsMonotoneCircuit (binaryCircuit n D z) := by
  intro g hg
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  change (D.gates.get j).op = GateOp.and ∨ (D.gates.get j).op = GateOp.or
  exact hM _ (List.get_mem _ _)

theorem zero_for_fn (n : ℕ) (x : Fin n → Bool) :
    BoolLe (List.ofFn (fun _ : Fin n => false)) (List.ofFn x) := by
  intro i hi
  rw [zero_getD] at hi
  contradiction

end PEqualNP.Outside.L_meta_739

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_739

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.L_meta_739 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true)))) → ∀ (P2 L2 k2 q2 : ℕ) (S2 : Fin L2 → Finset (Fin P2)) (C2 : PEqualNP.CircuitLowerBounds.Circuit), 1 ≤ k2 → 2 ≤ q2 → (∀ w2 : Fin L2, (S2 w2).card = q2) → (∀ w3 w4 : Fin L2, w3 ≠ w4 → (S2 w3 ∩ S2 w4).card ≤ 1) → (∀ (w5 : Fin L2) (p2 : Fin P2), p2 ∈ S2 w5 → ∃ u2 : Fin L2, p2 ∉ S2 u2) → PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C2 → (∀ g2 ∈ C2.gates, g2.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P2 + L2) (Finset.Ico P2 (P2 + L2)) C2 1 → (∀ (x2 : Fin P2 → Bool) (y2 : Fin L2 → Bool), (Finset.univ.filter (fun u3 : Fin L2 => y2 u3 = true)).card = 1 → (Finset.univ.filter (fun p3 : Fin P2 => x2 p3 = true)).card ≤ k2 → C2.eval (List.ofFn x2 ++ List.ofFn y2) = decide (∃ w6 : Fin L2, y2 w6 = true ∧ ∃ p4 ∈ S2 w6, x2 p4 = true)) → ∀ c2 : ℕ, c2 ≤ k2 → c2 + 1 ≤ q2 → L2 * c2 + L2 ≤ C2.size + 1 := by
  classical
  intro hCharge hSplit P L k q S C hk hq hcard hinter hAvoid hC hFan hDegree hSpec c hck hcq
  obtain ⟨A, hsize, hAM, hAF, hAD, hEval, hLive⟩ :=
    reduce_to_live (P + L) C hC hFan (Finset.Ico P (P + L)) hDegree
  let zL : Fin L → Bool := fun _ => false
  let zP : Fin P → Bool := fun _ => false
  have hEq (x : Fin P → Bool) (y : Fin L → Bool) :
      A.eval (List.ofFn x ++ List.ofFn y) = C.eval (List.ofFn x ++ List.ofFn y) :=
    hEval _ (by simp)
  have placed (x : Fin P → Bool) (w : Fin L)
      (hs : (Finset.univ.filter (fun p => x p = true)).card ≤ k) :
      A.eval (List.ofFn x ++ List.ofFn (oneHot w)) =
        decide (∃ p ∈ S w, x p = true) := by
    rw [hEq, hSpec x (oneHot w) (oneHot_card w) hs]
    congr 1
    simp [oneHot]
  have base_false (x : Fin P → Bool) (u : Fin L)
      (hs : (Finset.univ.filter (fun p => x p = true)).card ≤ k)
      (hOff : ∀ p ∈ S u, x p = false) :
      A.eval (List.ofFn x ++ List.ofFn zL) = false := by
    have hu : ¬ ∃ p ∈ S u, x p = true := by
      rintro ⟨p, hp, he⟩
      simp [hOff p hp] at he
    have hfu : A.eval (List.ofFn x ++ List.ofFn (oneHot u)) = false := by
      simp [placed x u hs, hu]
    have hmono := mono_circuit hAM (by simp : (List.ofFn x ++ List.ofFn zL).length =
        (List.ofFn x ++ List.ofFn (oneHot u)).length) (zero_lines_le x (oneHot u))
    cases h0 : A.eval (List.ofFn x ++ List.ofFn zL) with
    | false => rfl
    | true =>
      have ht : A.eval (List.ofFn x ++ List.ofFn (oneHot u)) = true := hmono A.output h0
      simp [hfu] at ht
  have base_single (w : Fin L) (p : Fin P) :
      A.eval (List.ofFn (oneHot p) ++ List.ofFn zL) = false := by
    obtain ⟨u, hu⟩ : ∃ u : Fin L, p ∉ S u := by
      by_cases hp : p ∈ S w
      · exact hAvoid w p hp
      · exact ⟨w, hp⟩
    apply base_false _ u (by rw [oneHot_card]; exact hk)
    intro s hs
    have hn : s ≠ p := fun e => hu (e ▸ hs)
    simp [oneHot, hn]
  have hAll (w : Fin L) : Live (P + L) A (P + w.val) := by
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (S w).card from
      lt_of_lt_of_le (by decide) (hcard w ▸ hq))
    apply every_line_live A w (oneHot p)
    rw [base_single w p, placed _ w (by rw [oneHot_card]; exact hk)]
    have hP : ∃ a ∈ S w, oneHot p a = true := ⟨p, hp, by simp [oneHot]⟩
    simp [hP]
  obtain ⟨D, T, o, hDM, hDF, hPaid, hRep⟩ := hSplit P L A Finset.univ hAM hAF hAD hLive
    (fun w => ⟨fun _ => hAll w, fun _ => Finset.mem_univ w⟩)
  have factor (x : Fin P → Bool) (w : Fin L)
      (hs : (Finset.univ.filter (fun p => x p = true)).card ≤ k)
      (hb : A.eval (List.ofFn x ++ List.ofFn zL) = false) :
      (w ∈ T ∨ (D.wires (List.ofFn x)).getD (o w) false = true) ↔
        ∃ p ∈ S w, x p = true := by
    have e := hRep x (oneHot w)
    rw [placed x w hs] at e
    change _ = (A.eval (List.ofFn x ++ List.ofFn zL) || _) at e
    exact (by simpa [hb, oneHot] using congrArg (fun b : Bool => b = true) e.symm)
  have hZero (w : Fin L) :
      w ∉ T ∧ (D.wires (List.ofFn zP)).getD (o w) false = false := by
    have hs : (Finset.univ.filter (fun p : Fin P => zP p = true)).card ≤ k := by simp [zP]
    have hf := factor zP w hs (base_false zP w hs (fun _ _ => rfl))
    have hn : ¬ (w ∈ T ∨ (D.wires (List.ofFn zP)).getD (o w) false = true) := by
      simpa [zP] using hf
    simpa only [not_or, Bool.not_eq_true] using hn
  let B := binaryCircuit P D (List.ofFn zP)
  have hB (w : Fin L) (x : Fin P → Bool) :
      (B.wires (List.ofFn x)).getD (o w) false =
        (D.wires (List.ofFn x)).getD (o w) false :=
    binary_wires P D hDM hDF _ _ (by simp) (by simp) (zero_for_fn P x) _ (hZero w).2
  have hGates : ∀ g ∈ B.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨binary_mono P D _ hDM g hg, binary_good P D _ g hg⟩
  have hS (w : Fin L) : 2 ≤ (S w).card := hcard w ▸ hq
  have hSingle (w : Fin L) (p : Fin P) :
      (B.wires (List.ofFn (oneHot p))).getD (o w) false = true ↔ p ∈ S w := by
    rw [hB]
    simpa [oneHot, (hZero w).1] using factor (oneHot p) w
      (by rw [oneHot_card]; exact hk) (base_single w p)
  have hOff (w : Fin L) (x : Fin P → Bool)
      (hs : (Finset.univ.filter (fun p : Fin P => x p = true)).card ≤ k)
      (hn : ∀ p ∈ S w, x p = false) :
      (B.wires (List.ofFn x)).getD (o w) false = false := by
    rw [hB]
    have hf := factor x w hs (base_false x w hs hn)
    cases h : (D.wires (List.ofFn x)).getD (o w) false with
    | false => rfl
    | true =>
      obtain ⟨p, hp, ht⟩ := hf.mp (Or.inr h)
      simp [hn p hp] at ht
  have hCharge' := hCharge P L k S B o (fun _ => c) hinter hS hGates
    hSingle hOff (fun _ => hck) (fun w => hcard w ▸ hcq)
  have hBsize : B.size = D.size := by simp [B, binaryCircuit, Circuit.size]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hCharge'
  rw [hBsize] at hCharge'
  simp only [Finset.card_univ, Fintype.card_fin] at hPaid
  have hcount : L * c ≤ D.size := by simpa [Nat.mul_comm] using hCharge'
  exact (Nat.add_le_add_right hcount L).trans (hPaid.trans (Nat.add_le_add_right hsize 1))

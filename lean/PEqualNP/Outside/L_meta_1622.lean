import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1622_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val {N : ℕ} (gates : List Gate) (w : ℕ) (x : Fin N → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < N + k ∧ val gates i x = true := by
  by_cases hi : i < N + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (N + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < N + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (N + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < N + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (hw : w < N) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simp; exact hw)]
  exact List.getElem_ofFn _

theorem val_big {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : N + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono {N : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) :
    val gs w x = true → val gs w y = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < N
    · simpa only [val_input gs _ w hw] using hxy ⟨w, hw⟩
    by_cases hg : w < N + gs.length
    · have hi : w - N < gs.length := by omega
      have he : N + (w - N) = w := by omega
      rcases (legal gs[w - N] (List.getElem_mem hi)).1 with ha | ho
      · intro h
        have hs := (val_and gs x (w - N) hi ha).mp (by simpa only [he] using h)
        rw [← he]
        apply (val_and gs y (w - N) hi ha).mpr
        intro r hr
        obtain ⟨hlt, hit⟩ := hs r hr
        exact ⟨hlt, ih r (by omega) hit⟩
      · intro h
        obtain ⟨r, hr, hlt, hit⟩ := (val_or gs x (w - N) hi ho).mp (by simpa only [he] using h)
        rw [← he]
        exact (val_or gs y (w - N) hi ho).mpr ⟨r, hr, hlt, ih r (by omega) hit⟩
    · simp [val_big gs x w (by omega)]

def ldFold (gs : List Gate) (d : List ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) d

theorem ldFold_snoc (gs : List Gate) (g : Gate) (d : List ℕ) :
    ldFold (gs ++ [g]) d = ldFold gs d ++ [g.lineDegree (ldFold gs d)] := by
  simp [ldFold, List.foldl_append]

theorem ldFold_len (gs : List Gate) : ∀ d : List ℕ, (ldFold gs d).length = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp [ldFold]
  | cons g gs ih =>
    intro d
    have := ih (d ++ [g.lineDegree d])
    simp only [ldFold, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem ldFold_keep (gs : List Gate) : ∀ (d : List ℕ) (i : ℕ), i < d.length →
    (ldFold gs d).getD i 0 = d.getD i 0 := by
  induction gs with
  | nil => intro d i _; rfl
  | cons g gs ih =>
    intro d i hi
    have := ih (d ++ [g.lineDegree d]) i (by simp; omega)
    simp only [ldFold, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem ldFold_prefix (pre post : List Gate) (d : List ℕ) (i : ℕ)
    (hi : i < d.length + pre.length) :
    (ldFold (pre ++ post) d).getD i 0 = (ldFold pre d).getD i 0 := by
  have : ldFold (pre ++ post) d = ldFold post (ldFold pre d) := by simp [ldFold, List.foldl_append]
  rw [this]
  exact ldFold_keep post _ i (by rw [ldFold_len]; exact hi)

theorem ld_take (gs : List Gate) (d : List ℕ) (k i : ℕ) (hi : i < d.length + k) (hk : k ≤ gs.length) :
    (ldFold gs d).getD i 0 = (ldFold (gs.take k) d).getD i 0 := by
  conv_lhs => rw [← List.take_append_drop k gs]
  exact ldFold_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

def deg (n m : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0

theorem deg_input_left (n m : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    deg n m C w = 0 := by
  unfold deg Circuit.lineDegrees
  change (ldFold C.gates ((List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0)).getD w 0 = 0
  rw [ldFold_keep _ _ w (by simp; omega)]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp [Finset.mem_Ico]
  omega

theorem deg_input_right (n m : ℕ) (C : Circuit) (w : ℕ) (h1 : n ≤ w) (h2 : w < n + m) :
    deg n m C w = 1 := by
  unfold deg Circuit.lineDegrees
  change (ldFold C.gates ((List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0)).getD w 0 = 1
  rw [ldFold_keep _ _ w (by simp; omega)]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp [Finset.mem_Ico, h1, h2]

theorem deg_gate_eq (n m : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hback : ∀ i ∈ C.gates[k].inputs, i < n + m + k) :
    deg n m C (n + m + k) =
      @ite ℕ (C.gates[k].op = GateOp.and) (lineDegreeGateOpDecEq _ _)
        ((C.gates[k].inputs.map fun i => deg n m C i).sum)
        ((C.gates[k].inputs.map fun i => deg n m C i).foldr max 0) := by
  let d0 := (List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0
  have hd0 : d0.length = n + m := by simp [d0]
  have hstep : (ldFold C.gates d0).getD (n + m + k) 0 =
      C.gates[k].lineDegree (ldFold (C.gates.take k) d0) := by
    rw [ld_take C.gates d0 (k + 1) (n + m + k) (by omega) hk, List.take_succ_eq_append_getElem hk, ldFold_snoc]
    have hlen : (ldFold (C.gates.take k) d0).length = n + m + k := by
      rw [ldFold_len, hd0, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    rw [← hlen]
    simp [List.getD_eq_getElem?_getD]
  have hmap : C.gates[k].inputs.map (fun i => (ldFold (C.gates.take k) d0).getD i 0) =
      C.gates[k].inputs.map (fun i => deg n m C i) := by
    apply List.map_congr_left
    intro i hi
    have hilt := hback i hi
    exact (ld_take C.gates d0 k i (by omega) (Nat.le_of_lt hk)).symm
  change (ldFold C.gates d0).getD (n + m + k) 0 = _
  rw [hstep]
  unfold Gate.lineDegree
  rw [hmap]

theorem foldr_max_eq_zero (l : List ℕ) : l.foldr max 0 = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons, Nat.max_eq_zero_iff, ih, List.mem_cons, forall_eq_or_imp]

theorem deg_zero_inputs (n m : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hback : ∀ i ∈ C.gates[k].inputs, i < n + m + k)
    (hdz : deg n m C (n + m + k) = 0) :
    ∀ i ∈ C.gates[k].inputs, deg n m C i = 0 := by
  rw [deg_gate_eq n m C k hk hback] at hdz
  split_ifs at hdz
  · intro i hi
    exact List.sum_eq_zero_iff.mp hdz (deg n m C i) (List.mem_map_of_mem hi)
  · intro i hi
    exact (foldr_max_eq_zero _).mp hdz (deg n m C i) (List.mem_map_of_mem hi)

theorem fin_append_left {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (hw : w < n) :
    Fin.append x y ⟨w, by omega⟩ = x ⟨w, hw⟩ := by
  have heq : (⟨w, by omega⟩ : Fin (n + m)) = Fin.castAdd m ⟨w, hw⟩ := rfl
  rw [heq, Fin.append_left]

theorem fin_append_right {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ)
    (h1 : n ≤ w) (h2 : w < n + m) :
    Fin.append x y ⟨w, h2⟩ = y ⟨w - n, by omega⟩ := by
  have heq : (⟨w, h2⟩ : Fin (n + m)) = Fin.natAdd n ⟨w - n, by omega⟩ := by
    apply Fin.ext; simp [Fin.val_natAdd]; omega
  rw [heq, Fin.append_right]

theorem deg_zero_indep (n m : ℕ) (C : Circuit)
    (hmono : Monotone2 C) (hback : ReadsBack (n + m) C)
    (x : Fin n → Bool) (y : Fin m → Bool) :
    ∀ w < n + m + C.gates.length, deg n m C w = 0 →
      val C.gates w (Fin.append x y) = val C.gates w (Fin.append x (fun _ : Fin m => false)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hdz
    by_cases hwn : w < n
    · rw [val_input C.gates _ w (by omega), val_input C.gates _ w (by omega)]
      rw [fin_append_left x y w hwn, fin_append_left x (fun _ => false) w hwn]
    by_cases hwm : w < n + m
    · have h1 := deg_input_right n m C w (by omega) hwm
      omega
    · have hk : w - (n + m) < C.gates.length := by omega
      have hweq : n + m + (w - (n + m)) = w := by omega
      have hbk : ∀ i ∈ C.gates[w - (n + m)].inputs, i < n + m + (w - (n + m)) := by
        intro i hi
        have hb := hback (w - (n + m)) hk i
        unfold gateAt at hb
        rw [List.getD_eq_getElem _ _ hk] at hb
        exact hb hi
      have hdzk : deg n m C (n + m + (w - (n + m))) = 0 := by simpa only [hweq] using hdz
      have hdz_in := deg_zero_inputs n m C (w - (n + m)) hk hbk hdzk
      have hop : C.gates[w - (n + m)].op = GateOp.and ∨ C.gates[w - (n + m)].op = GateOp.or := by
        have := (hmono C.gates[w - (n + m)] (List.getElem_mem hk)).1
        simpa using this
      rw [← hweq]
      apply Bool.eq_iff_iff.mpr
      rcases hop with hand | hor
      · rw [val_and C.gates _ (w - (n + m)) hk hand, val_and C.gates _ (w - (n + m)) hk hand]
        constructor
        · intro h i hi
          obtain ⟨hlt, hv⟩ := h i hi
          exact ⟨hlt, by rw [← ih i (by omega) (by omega) (hdz_in i hi)]; exact hv⟩
        · intro h i hi
          obtain ⟨hlt, hv⟩ := h i hi
          exact ⟨hlt, by rw [ih i (by omega) (by omega) (hdz_in i hi)]; exact hv⟩
      · rw [val_or C.gates _ (w - (n + m)) hk hor, val_or C.gates _ (w - (n + m)) hk hor]
        constructor
        · rintro ⟨i, hi, hlt, hv⟩
          exact ⟨i, hi, hlt, by rw [← ih i (by omega) (by omega) (hdz_in i hi)]; exact hv⟩
        · rintro ⟨i, hi, hlt, hv⟩
          exact ⟨i, hi, hlt, by rw [ih i (by omega) (by omega) (hdz_in i hi)]; exact hv⟩

def fwdMap (n m : ℕ) (u : ℕ) : ℕ :=
  if u < n then u else if u < n + m then n else u - m + 2

def fwdGates (n m : ℕ) (C : Circuit) : List Gate :=
  [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++
    C.gates.map fun g => ⟨g.op, g.inputs.map (fwdMap n m)⟩

theorem fwdGates_len (n m : ℕ) (C : Circuit) : (fwdGates n m C).length = 2 + C.gates.length := by
  simp [fwdGates]; omega

theorem fwdGates_mono (n m : ℕ) (C : Circuit) (hmono : Monotone2 C) :
    Monotone2 ⟨fwdGates n m C, 0⟩ := by
  intro g hg
  simp only [fwdGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hg
  rcases hg with (rfl | rfl) | ⟨g0, hg0, rfl⟩
  · exact ⟨Or.inr rfl, by simp⟩
  · exact ⟨Or.inl rfl, by simp⟩
  · obtain ⟨hop, hlen⟩ := hmono g0 hg0
    exact ⟨hop, by simpa using hlen⟩

theorem fwdGates_readsBack (n m : ℕ) (C : Circuit) (hback : ReadsBack (n + m) C) :
    ReadsBack n ⟨fwdGates n m C, 0⟩ := by
  intro j hj i hi
  unfold gateAt at hi
  rw [List.getD_eq_getElem _ _ hj] at hi
  match j with
  | 0 => simp [fwdGates] at hi
  | 1 => simp [fwdGates] at hi
  | k + 2 =>
    have hk : k < C.gates.length := by simp [fwdGates] at hj; omega
    have hget : (fwdGates n m C)[k + 2] = ⟨C.gates[k].op, C.gates[k].inputs.map (fwdMap n m)⟩ := by
      simp [fwdGates]
    rw [hget] at hi
    simp only [List.mem_map] at hi
    obtain ⟨u, hu, rfl⟩ := hi
    have hub : u < n + m + k := by
      have hb := hback k hk u
      unfold gateAt at hb
      rw [List.getD_eq_getElem _ _ hk] at hb
      exact hb hu
    unfold fwdMap
    split_ifs <;> omega

theorem fwdGates_eval (n m : ℕ) (C : Circuit) (hmono : Monotone2 C) (hback : ReadsBack (n + m) C)
    (x : Fin n → Bool) :
    val (fwdGates n m C) n x = false ∧
    val (fwdGates n m C) (n + 1) x = true ∧
    ∀ w < n + m + C.gates.length,
      val (fwdGates n m C) (fwdMap n m w) x = val C.gates w (Fin.append x (fun _ : Fin m => false)) := by
  have hfalse : val (fwdGates n m C) n x = false := by
    have h0 : 0 < (fwdGates n m C).length := by simp [fwdGates]
    have hop : (fwdGates n m C)[0].op = GateOp.or := rfl
    apply Bool.eq_false_iff.mpr
    intro h
    have := (val_or (fwdGates n m C) x 0 h0 hop).mp (by simpa using h)
    rcases this with ⟨_, hi, _⟩
    simp [fwdGates] at hi
  have htrue : val (fwdGates n m C) (n + 1) x = true := by
    have h1 : 1 < (fwdGates n m C).length := by simp [fwdGates]
    have hop : (fwdGates n m C)[1].op = GateOp.and := rfl
    apply (val_and (fwdGates n m C) x 1 h1 hop).mpr
    intro i hi
    simp [fwdGates] at hi
  refine ⟨hfalse, htrue, ?_⟩
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hfm : fwdMap n m w = w := by simp [fwdMap, hwn]
      rw [hfm, val_input (fwdGates n m C) x w hwn, val_input C.gates _ w (by omega)]
      exact (fin_append_left x (fun _ => false) w hwn).symm
    by_cases hwm : w < n + m
    · have hfm : fwdMap n m w = n := by simp [fwdMap, hwn, hwm]
      rw [hfm, hfalse, val_input C.gates _ w hwm, fin_append_right x (fun _ => false) w (by omega) hwm]
    · have hk : w - (n + m) < C.gates.length := by omega
      have hweq : n + m + (w - (n + m)) = w := by omega
      have hfm : fwdMap n m w = n + (w - (n + m) + 2) := by
        unfold fwdMap; rw [ite_eq_right hwn, ite_eq_right hwm]; omega
      have hfk : w - (n + m) + 2 < (fwdGates n m C).length := by rw [fwdGates_len]; omega
      have hget : (fwdGates n m C)[w - (n + m) + 2] = ⟨C.gates[w - (n + m)].op, C.gates[w - (n + m)].inputs.map (fwdMap n m)⟩ := by
        simp [fwdGates]
      have hbk : ∀ i ∈ C.gates[w - (n + m)].inputs, i < n + m + (w - (n + m)) := by
        intro i hi
        have hb := hback (w - (n + m)) hk i
        unfold gateAt at hb
        rw [List.getD_eq_getElem _ _ hk] at hb
        exact hb hi
      have hbf : ∀ i ∈ C.gates[w - (n + m)].inputs, fwdMap n m i < n + (w - (n + m) + 2) := by
        intro i hi
        have := hbk i hi
        unfold fwdMap; split_ifs <;> omega
      have hop : C.gates[w - (n + m)].op = GateOp.and ∨ C.gates[w - (n + m)].op = GateOp.or := by
        simpa using (hmono C.gates[w - (n + m)] (List.getElem_mem hk)).1
      rw [hfm]
      conv_rhs => rw [← hweq]
      apply Bool.eq_iff_iff.mpr
      rcases hop with hand | hor
      · have hand' : (fwdGates n m C)[w - (n + m) + 2].op = GateOp.and := by rw [hget]; exact hand
        rw [val_and (fwdGates n m C) x (w - (n + m) + 2) hfk hand', val_and C.gates _ (w - (n + m)) hk hand, hget]
        constructor
        · intro h i hi
          have h1 := h (fwdMap n m i) (List.mem_map_of_mem hi)
          have hlt := hbk i hi
          exact ⟨hlt, by rw [← ih i (by omega) (by omega)]; exact h1.2⟩
        · intro h j hj
          simp only [List.mem_map] at hj
          obtain ⟨i, hi, rfl⟩ := hj
          have h1 := h i hi
          exact ⟨hbf i hi, by rw [ih i (by omega) (by omega)]; exact h1.2⟩
      · have hor' : (fwdGates n m C)[w - (n + m) + 2].op = GateOp.or := by rw [hget]; exact hor
        rw [val_or (fwdGates n m C) x (w - (n + m) + 2) hfk hor', val_or C.gates _ (w - (n + m)) hk hor, hget]
        constructor
        · rintro ⟨j, hj, _, hvj⟩
          simp only [List.mem_map] at hj
          obtain ⟨i, hi, rfl⟩ := hj
          have hlt := hbk i hi
          exact ⟨i, hi, hlt, by rw [← ih i (by omega) (by omega)]; exact hvj⟩
        · rintro ⟨i, hi, hlt, hvi⟩
          exact ⟨fwdMap n m i, List.mem_map_of_mem hi, hbf i hi, by rw [ih i (by omega) (by omega)]; exact hvi⟩

def optVal {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : Option ℕ → Bool
  | none => false
  | some u => val gs u x

def orOpt (n : ℕ) (gs : List Gate) : Option ℕ → Option ℕ → List Gate × Option ℕ
  | none, b => (gs, b)
  | a, none => (gs, a)
  | some u, some v => (gs ++ [⟨GateOp.or, [u, v]⟩], some (n + gs.length))

def andWireOpt (n : ℕ) (gs : List Gate) : Option ℕ → ℕ → List Gate × Option ℕ
  | none, _ => (gs, none)
  | some u, c => (gs ++ [⟨GateOp.and, [u, c]⟩], some (n + gs.length))

theorem append_gate_ok (n : ℕ) (gs : List Gate) (g : Gate)
    (hmono : Monotone2 ⟨gs, 0⟩) (hback : ReadsBack n ⟨gs, 0⟩)
    (hg_mono : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hg_back : ∀ i ∈ g.inputs, i < n + gs.length) :
    Monotone2 ⟨gs ++ [g], 0⟩ ∧ ReadsBack n ⟨gs ++ [g], 0⟩ := by
  constructor
  · intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hmono z hz
    · exact ⟨by simpa using hg_mono.1, hg_mono.2⟩
  · intro j hj i hi
    unfold gateAt at hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g])[j] = gs[j] := List.getElem_append_left hlt
      rw [hget] at hi
      have hb := hback j hlt i
      unfold gateAt at hb
      rw [List.getD_eq_getElem _ _ hlt] at hb
      exact hb hi
    · have hjeq : j = gs.length := by simp at hj; omega
      subst hjeq
      have hget : (gs ++ [g])[gs.length] = g := by simp
      rw [hget] at hi
      exact hg_back i hi

theorem orOpt_spec (n : ℕ) (gs : List Gate) (a b : Option ℕ)
    (hmono : Monotone2 ⟨gs, 0⟩) (hback : ReadsBack n ⟨gs, 0⟩)
    (ha : ∀ u, a = some u → u < n + gs.length)
    (hb : ∀ v, b = some v → v < n + gs.length) :
    let res := orOpt n gs a b
    (∃ extra, res.1 = gs ++ extra ∧ extra.length ≤ 1) ∧
    Monotone2 ⟨res.1, 0⟩ ∧ ReadsBack n ⟨res.1, 0⟩ ∧
    (∀ u, res.2 = some u → u < n + res.1.length) ∧
    (∀ x : Fin n → Bool, optVal res.1 x res.2 = (optVal gs x a || optVal gs x b)) := by
  cases a with
  | none =>
    refine ⟨⟨[], by simp [orOpt]⟩, hmono, hback, hb, ?_⟩
    intro x; simp [orOpt, optVal]
  | some u =>
    cases b with
    | none =>
      refine ⟨⟨[], by simp [orOpt]⟩, hmono, hback, ha, ?_⟩
      intro x; simp [orOpt, optVal]
    | some v =>
      have hu : u < n + gs.length := ha u rfl
      have hv : v < n + gs.length := hb v rfl
      let gnew : Gate := ⟨GateOp.or, [u, v]⟩
      have hok := append_gate_ok n gs gnew hmono hback ⟨Or.inr rfl, by simp [gnew]⟩
        (fun i hi => by simp [gnew] at hi; rcases hi with rfl | rfl <;> assumption)
      refine ⟨⟨[gnew], rfl, by simp⟩, hok.1, hok.2, ?_, ?_⟩
      · intro w hw
        simp only [orOpt, Option.some.injEq] at hw
        subst hw; simp [orOpt]
      · intro x
        simp only [orOpt, optVal]
        have hk : gs.length < (gs ++ [gnew]).length := by simp
        have hget : (gs ++ [gnew])[gs.length] = gnew := by simp
        apply Bool.eq_iff_iff.mpr
        rw [val_or (gs ++ [gnew]) x gs.length hk (by rw [hget]), hget]
        have hpu : val (gs ++ [gnew]) u x = val gs u x :=
          wf_prefix gs [gnew] (List.ofFn x) u (by simpa using hu)
        have hpv : val (gs ++ [gnew]) v x = val gs v x :=
          wf_prefix gs [gnew] (List.ofFn x) v (by simpa using hv)
        simp only [gnew, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true]
        constructor
        · rintro ⟨i, rfl | rfl, _, hvi⟩
          · exact Or.inl (hpu ▸ hvi)
          · exact Or.inr (hpv ▸ hvi)
        · rintro (h | h)
          · exact ⟨u, Or.inl rfl, hu, hpu.symm ▸ h⟩
          · exact ⟨v, Or.inr rfl, hv, hpv.symm ▸ h⟩

theorem andWireOpt_spec (n : ℕ) (gs : List Gate) (a : Option ℕ) (c : ℕ)
    (hmono : Monotone2 ⟨gs, 0⟩) (hback : ReadsBack n ⟨gs, 0⟩)
    (ha : ∀ u, a = some u → u < n + gs.length) (hc : c < n + gs.length) :
    let res := andWireOpt n gs a c
    (∃ extra, res.1 = gs ++ extra ∧ extra.length ≤ 1) ∧
    Monotone2 ⟨res.1, 0⟩ ∧ ReadsBack n ⟨res.1, 0⟩ ∧
    (∀ u, res.2 = some u → u < n + res.1.length) ∧
    (∀ x : Fin n → Bool, optVal res.1 x res.2 = (optVal gs x a && val gs c x)) := by
  cases a with
  | none =>
    refine ⟨⟨[], by simp [andWireOpt]⟩, hmono, hback, fun _ h => by simp [andWireOpt] at h, ?_⟩
    intro x; simp [andWireOpt, optVal]
  | some u =>
    have hu : u < n + gs.length := ha u rfl
    let gnew : Gate := ⟨GateOp.and, [u, c]⟩
    have hok := append_gate_ok n gs gnew hmono hback ⟨Or.inl rfl, by simp [gnew]⟩
      (fun i hi => by simp [gnew] at hi; rcases hi with rfl | rfl <;> assumption)
    refine ⟨⟨[gnew], rfl, by simp⟩, hok.1, hok.2, ?_, ?_⟩
    · intro w hw
      simp only [andWireOpt, Option.some.injEq] at hw
      subst hw; simp [andWireOpt]
    · intro x
      simp only [andWireOpt, optVal]
      have hk : gs.length < (gs ++ [gnew]).length := by simp
      have hget : (gs ++ [gnew])[gs.length] = gnew := by simp
      apply Bool.eq_iff_iff.mpr
      rw [val_and (gs ++ [gnew]) x gs.length hk (by rw [hget]), hget]
      have hpu : val (gs ++ [gnew]) u x = val gs u x :=
        wf_prefix gs [gnew] (List.ofFn x) u (by simpa using hu)
      have hpc : val (gs ++ [gnew]) c x = val gs c x :=
        wf_prefix gs [gnew] (List.ofFn x) c (by simpa using hc)
      simp only [gnew, List.mem_cons, List.not_mem_nil, or_false, Bool.and_eq_true]
      constructor
      · intro h
        exact ⟨hpu ▸ (h u (Or.inl rfl)).2, hpc ▸ (h c (Or.inr rfl)).2⟩
      · rintro ⟨h1, h2⟩ i (rfl | rfl)
        · exact ⟨hu, hpu.symm ▸ h1⟩
        · exact ⟨hc, hpc.symm ▸ h2⟩

theorem final_thm : ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧ ∀ (x : Fin n → Bool) (j : Fin m), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || (D.wires (List.ofFn x)).getD (o j) false) := by
  classical
  intro n m C hmono hback hnoCross
  by_cases hm0 : m = 0
  · subst hm0
    exact ⟨⟨[], 0⟩, Fin.elim0, fun _ h => by simp at h, fun _ h => by simp at h, by simp [Circuit.size], fun _ j => Fin.elim0 j⟩
  by_cases hoob : n + m + C.gates.length ≤ C.output
  · refine ⟨⟨[], 0⟩, fun _ => n, fun _ h => by simp at h, fun _ h => by simp at h, by simp [Circuit.size], ?_⟩
    intro x j
    change val C.gates C.output _ = (val C.gates C.output _ || val [] n x)
    rw [val_big C.gates _ C.output hoob, val_big C.gates _ C.output hoob, val_big [] x n (by simp)]
    rfl
  by_cases hdz : deg n m C C.output = 0
  · refine ⟨⟨[], 0⟩, fun _ => n, fun _ h => by simp at h, fun _ h => by simp at h, by simp [Circuit.size], ?_⟩
    intro x j
    change val C.gates C.output _ = (val C.gates C.output _ || val [] n x)
    rw [deg_zero_indep n m C hmono hback x (fun l => decide (l = j)) C.output (by omega) hdz,
      val_big [] x n (by simp), Bool.or_false]
  by_cases hlin : C.output < n + m
  · have hge : n ≤ C.output := by
      by_contra hlt
      exact hdz (deg_input_left n m C C.output (by omega))
    let l0 : Fin m := ⟨C.output - n, by omega⟩
    let D0 : Circuit := ⟨[⟨GateOp.and, []⟩], 0⟩
    refine ⟨D0, fun j => if j = l0 then n else n + 1, ?_, ?_, ?_, ?_⟩
    · intro g hg; simp [D0] at hg; subst hg; exact ⟨Or.inl rfl, by simp⟩
    · intro j hj i hi
      unfold gateAt at hi; rw [List.getD_eq_getElem _ _ hj] at hi
      have hj0 : j = 0 := by simp [D0] at hj; omega
      subst hj0; simp [D0] at hi
    · simp only [D0, Circuit.size, List.length_singleton]; omega
    · intro x j
      change val C.gates C.output _ = (val C.gates C.output _ || val D0.gates (if j = l0 then n else n + 1) x)
      rw [val_input C.gates _ C.output hlin, val_input C.gates _ C.output hlin,
        fin_append_right x _ C.output hge hlin, fin_append_right x _ C.output hge hlin]
      have htrueD : val D0.gates n x = true := by
        have h0 : 0 < D0.gates.length := by simp [D0]
        exact (val_and D0.gates x 0 h0 rfl).mpr (by simp [D0])
      have hfalseD : val D0.gates (n + 1) x = false := val_big D0.gates x (n + 1) (by simp [D0])
      by_cases hjl : j = l0
      · rw [ite_eq_left hjl, htrueD]
        have : (⟨C.output - n, by omega⟩ : Fin m) = j := hjl.symm
        simp [this]
      · rw [ite_eq_right hjl, hfalseD]
        have : (⟨C.output - n, by omega⟩ : Fin m) ≠ j := fun h => hjl h.symm
        simp [this]
  have houtG : C.output - (n + m) < C.gates.length := by omega
  have houtEq : n + m + (C.output - (n + m)) = C.output := by omega
  let Tfin : Finset ℕ := (Finset.range C.gates.length).filter fun j => 0 < deg n m C (n + m + j)
  have hTset : ({j : ℕ | j < C.gates.length ∧ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} : Set ℕ) = (Tfin : Set ℕ) := by
    ext j; simp [Tfin, deg]
  have hTcard : Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} = Tfin.card := by
    rw [hTset, Set.ncard_coe_finset]
  have hTpos : 1 ≤ Tfin.card := by
    apply Finset.card_pos.mpr
    refine ⟨C.output - (n + m), Finset.mem_filter.mpr ⟨Finset.mem_range.mpr houtG, ?_⟩⟩
    rw [houtEq]; omega
  have hlegC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg; obtain ⟨hop, hlen⟩ := hmono g hg; exact ⟨by simpa using hop, hlen⟩
  have hback_step : ∀ k (hk : k ≤ C.gates.length), ∃ gs : List Gate, ∃ adj : ℕ → Option ℕ,
      (∃ extra, gs = fwdGates n m C ++ extra) ∧
      Monotone2 ⟨gs, 0⟩ ∧ ReadsBack n ⟨gs, 0⟩ ∧
      gs.length ≤ 2 + C.gates.length + 2 * (Tfin.filter fun i => C.gates.length - k ≤ i).card ∧
      (∀ w u, adj w = some u → u < n + gs.length) ∧
      (∀ (x : Fin n → Bool) (j : Fin m),
        let x0 := Fin.append x (fun _ : Fin m => false)
        let xj := Fin.append x (fun l => decide (l = j))
        (∀ w < n + m + (C.gates.length - k), val C.gates w x0 = true → optVal gs x (adj w) = true → val C.gates C.output x0 = true) ∧
        (∀ w < n + m + (C.gates.length - k), val C.gates w xj = true → optVal gs x (adj w) = true → val C.gates C.output xj = true) ∧
        (val C.gates C.output xj = true → val C.gates C.output x0 = true ∨
          ∃ w < n + m + (C.gates.length - k), 0 < deg n m C w ∧ val C.gates w xj = true ∧ optVal gs x (adj w) = true)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fwdGates n m C, fun w => if w = C.output then some (n + 1) else none,
        ⟨[], by simp⟩, fwdGates_mono n m C hmono, fwdGates_readsBack n m C hback,
        by rw [fwdGates_len]; omega, ?_, ?_⟩
      · intro w u hu
        dsimp only at hu
        by_cases hwo : w = C.output
        · rw [ite_eq_left hwo, Option.some.injEq] at hu; subst hu; rw [fwdGates_len]; omega
        · rw [ite_eq_right hwo] at hu; simp at hu
      · intro x j
        dsimp only
        have htrue := (fwdGates_eval n m C hmono hback x).2.1
        refine ⟨?_, ?_, ?_⟩
        · intro w _ hv ha
          by_cases hwo : w = C.output
          · subst hwo; exact hv
          · rw [ite_eq_right hwo] at ha; simp [optVal] at ha
        · intro w _ hv ha
          by_cases hwo : w = C.output
          · subst hwo; exact hv
          · rw [ite_eq_right hwo] at ha; simp [optVal] at ha
        · intro hv
          refine Or.inr ⟨C.output, by omega, by omega, hv, ?_⟩
          rw [ite_eq_left rfl]
          exact htrue
    | succ k ih =>
      intro hk
      obtain ⟨gs, adj, ⟨extra0, hgs_ext⟩, hmono_gs, hback_gs, hlen_gs, hvalid_adj, hsem⟩ := ih (by omega)
      let p : ℕ := C.gates.length - (k + 1)
      have hp_lt : p < C.gates.length := by omega
      have hp_succ : C.gates.length - k = p + 1 := by omega
      have hback_p : ∀ i ∈ C.gates[p].inputs, i < n + m + p := by
        intro i hi
        have hb := hback p hp_lt i
        unfold gateAt at hb
        rw [List.getD_eq_getElem _ _ hp_lt] at hb
        exact hb hi
      have hfilt_sub : ∀ hnot : p ∉ Tfin,
          (Tfin.filter fun i => p + 1 ≤ i).card ≤ (Tfin.filter fun i => p ≤ i).card := by
        intro _
        exact Finset.card_le_card fun i hi => by
          rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, by omega⟩
      have hfilt_inc : ∀ hmem : p ∈ Tfin,
          (Tfin.filter fun i => p + 1 ≤ i).card + 1 = (Tfin.filter fun i => p ≤ i).card := by
        intro hmem
        have heq : (Tfin.filter fun i => p ≤ i) = insert p (Tfin.filter fun i => p + 1 ≤ i) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hi, hge⟩
            by_cases hip : i = p
            · exact Or.inl hip
            · exact Or.inr ⟨hi, by omega⟩
          · rintro (rfl | ⟨hi, hge⟩)
            · exact ⟨hmem, le_rfl⟩
            · exact ⟨hi, by omega⟩
        rw [heq, Finset.card_insert_of_notMem (by simp)]
      by_cases hdp : deg n m C (n + m + p) = 0
      · have hpnot : p ∉ Tfin := by simp [Tfin, hdp]
        refine ⟨gs, adj, ⟨extra0, hgs_ext⟩, hmono_gs, hback_gs, ?_, hvalid_adj, ?_⟩
        · have := hfilt_sub hpnot
          rw [hp_succ] at hlen_gs
          change gs.length ≤ 2 + C.gates.length + 2 * (Tfin.filter fun i => p ≤ i).card
          omega
        · intro x j
          obtain ⟨hs0, hsj, hcomp⟩ := hsem x j
          rw [hp_succ] at hs0 hsj hcomp
          refine ⟨fun w hw => hs0 w (by omega), fun w hw => hsj w (by omega), ?_⟩
          intro hv
          rcases hcomp hv with h0 | ⟨w, hw, hdw, hvw, haw⟩
          · exact Or.inl h0
          · have hne : w ≠ n + m + p := fun h => by subst h; omega
            exact Or.inr ⟨w, by omega, hdw, hvw, haw⟩
      · have hpT : p ∈ Tfin := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp_lt, by omega⟩
        have hinc := hfilt_inc hpT
        have add1 : ∀ (gs1 : List Gate) (adj1 : ℕ → Option ℕ) (w1 : ℕ) (r1 : Option ℕ),
            Monotone2 ⟨gs1, 0⟩ → ReadsBack n ⟨gs1, 0⟩ →
            (∀ w u, adj1 w = some u → u < n + gs1.length) →
            (∀ u, r1 = some u → u < n + gs1.length) →
            ∃ gs2 : List Gate, ∃ adj2 : ℕ → Option ℕ,
              (∃ ex, gs2 = gs1 ++ ex ∧ ex.length ≤ 1) ∧
              Monotone2 ⟨gs2, 0⟩ ∧ ReadsBack n ⟨gs2, 0⟩ ∧
              (∀ w u, adj2 w = some u → u < n + gs2.length) ∧
              (∀ (x : Fin n → Bool) (w : ℕ),
                optVal gs2 x (adj2 w) = if w = w1 then (optVal gs1 x (adj1 w1) || optVal gs1 x r1) else optVal gs1 x (adj1 w)) := by
          intro gs1 adj1 w1 r1 hm1 hb1 hv1 hr1
          let res := orOpt n gs1 (adj1 w1) r1
          obtain ⟨⟨ex, hex, hexlen⟩, hm2, hb2, hv2, hval2⟩ := orOpt_spec n gs1 (adj1 w1) r1 hm1 hb1 (hv1 w1) hr1
          refine ⟨res.1, fun w => if w = w1 then res.2 else adj1 w, ⟨ex, hex, hexlen⟩, hm2, hb2, ?_, ?_⟩
          · intro w u hu
            dsimp only at hu
            by_cases hww : w = w1
            · rw [ite_eq_left hww] at hu; exact hv2 u hu
            · rw [ite_eq_right hww] at hu
              have := hv1 w u hu; rw [hex, List.length_append]; omega
          · intro x w
            dsimp only
            by_cases hww : w = w1
            · rw [ite_eq_left hww, ite_eq_left hww]; exact hval2 x
            · rw [ite_eq_right hww, ite_eq_right hww]
              cases h : adj1 w with
              | none => rfl
              | some u =>
                simp only [optVal]
                rw [hex]
                exact wf_prefix gs1 ex (List.ofFn x) u (by simpa using hv1 w u h)
        have hgs_fwd_val : ∀ (x : Fin n → Bool) (w : ℕ), w < n + m + C.gates.length →
            val gs (fwdMap n m w) x = val C.gates w (Fin.append x (fun _ : Fin m => false)) := by
          intro x w hw
          have hfm_lt : fwdMap n m w < n + (fwdGates n m C).length := by
            rw [fwdGates_len]; unfold fwdMap; split_ifs <;> omega
          rw [hgs_ext]
          have hpr := wf_prefix (fwdGates n m C) extra0 (List.ofFn x) (fwdMap n m w) (by simpa using hfm_lt)
          exact hpr.trans ((fwdGates_eval n m C hmono hback x).2.2 w hw)
        have hlen_p := (hlegC C.gates[p] (List.getElem_mem hp_lt)).2
        have hstep_done : ∃ gs' : List Gate, ∃ adj' : ℕ → Option ℕ,
            (∃ ex, gs' = gs ++ ex ∧ ex.length ≤ 2) ∧
            Monotone2 ⟨gs', 0⟩ ∧ ReadsBack n ⟨gs', 0⟩ ∧
            (∀ w u, adj' w = some u → u < n + gs'.length) ∧
            (∀ (x : Fin n → Bool) (j : Fin m),
              let x0 := Fin.append x (fun _ : Fin m => false)
              let xj := Fin.append x (fun l => decide (l = j))
              (∀ w < n + m + p, val C.gates w x0 = true → optVal gs' x (adj' w) = true → val C.gates C.output x0 = true) ∧
              (∀ w < n + m + p, val C.gates w xj = true → optVal gs' x (adj' w) = true → val C.gates C.output xj = true) ∧
              (val C.gates C.output xj = true → val C.gates C.output x0 = true ∨
                ∃ w < n + m + p, 0 < deg n m C w ∧ val C.gates w xj = true ∧ optVal gs' x (adj' w) = true)) := by
          rcases (hlegC C.gates[p] (List.getElem_mem hp_lt)).1 with hop_and | hop_or
          · match hin : C.gates[p].inputs with
            | [] =>
              have := deg_gate_eq n m C p hp_lt hback_p
              split_ifs at this
              rw [hin] at this; simp at this; exact absurd this hdp
            | [a] =>
              have halt : a < n + m + p := hback_p a (by rw [hin]; simp)
              obtain ⟨gs1, adj1, ⟨ex1, hex1, hex1len⟩, hm1, hb1, hv1, hval1⟩ :=
                add1 gs adj a (adj (n + m + p)) hmono_gs hback_gs hvalid_adj (hvalid_adj (n + m + p))
              refine ⟨gs1, adj1, ⟨ex1, hex1, by omega⟩, hm1, hb1, hv1, ?_⟩
              intro x j
              obtain ⟨hs0, hsj, hcomp⟩ := hsem x j
              rw [hp_succ] at hs0 hsj hcomp
              have hval_p : ∀ z : Fin (n + m) → Bool, val C.gates (n + m + p) z = true ↔ val C.gates a z = true := by
                intro z
                rw [val_and C.gates z p hp_lt hop_and, hin]
                simp [halt]
              refine ⟨?_, ?_, ?_⟩
              · intro w hw hvw haw
                rw [hval1 x w] at haw
                by_cases hwa : w = a
                · subst w; rw [ite_eq_left rfl, Bool.or_eq_true] at haw
                  rcases haw with h1 | h2
                  · exact hs0 a (by omega) hvw h1
                  · exact hs0 (n + m + p) (by omega) ((hval_p _).mpr hvw) h2
                · rw [ite_eq_right hwa] at haw; exact hs0 w (by omega) hvw haw
              · intro w hw hvw haw
                rw [hval1 x w] at haw
                by_cases hwa : w = a
                · subst w; rw [ite_eq_left rfl, Bool.or_eq_true] at haw
                  rcases haw with h1 | h2
                  · exact hsj a (by omega) hvw h1
                  · exact hsj (n + m + p) (by omega) ((hval_p _).mpr hvw) h2
                · rw [ite_eq_right hwa] at haw; exact hsj w (by omega) hvw haw
              · intro hv
                rcases hcomp hv with h0 | ⟨w, hw, hdw, hvw, haw⟩
                · exact Or.inl h0
                · by_cases hwp : w = n + m + p
                  · subst hwp
                    have hva : val C.gates a (Fin.append x (fun l => decide (l = j))) = true := (hval_p _).mp hvw
                    by_cases hda : deg n m C a = 0
                    · have hva0 : val C.gates a (Fin.append x (fun _ : Fin m => false)) = true := by
                        rw [← deg_zero_indep n m C hmono hback x (fun l => decide (l = j)) a (by omega) hda]; exact hva
                      exact Or.inl (hs0 (n + m + p) (by omega) ((hval_p _).mpr hva0) haw)
                    · refine Or.inr ⟨a, halt, by omega, hva, ?_⟩
                      rw [hval1 x a, ite_eq_left rfl, haw, Bool.or_true]
                  · refine Or.inr ⟨w, by omega, hdw, hvw, ?_⟩
                    rw [hval1 x w]
                    by_cases hwa : w = a
                    · rw [ite_eq_left hwa, ← hwa, haw, Bool.true_or]
                    · rw [ite_eq_right hwa]; exact haw
            | [a, b] =>
              have halt : a < n + m + p := hback_p a (by rw [hin]; simp)
              have hblt : b < n + m + p := hback_p b (by rw [hin]; simp)
              have hnc : deg n m C a = 0 ∨ deg n m C b = 0 := by
                have hc := hnoCross p hp_lt
                unfold gateAt at hc
                rw [List.getD_eq_getElem _ _ hp_lt, hin] at hc
                obtain ⟨i, hi, hdi⟩ := hc hop_and rfl
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl
                · exact Or.inl hdi
                · exact Or.inr hdi
              have handle_and : ∀ (c d : ℕ), c < n + m + p → d < n + m + p → deg n m C c = 0 →
                  (∀ z : Fin (n + m) → Bool, val C.gates (n + m + p) z = true ↔ val C.gates c z = true ∧ val C.gates d z = true) →
                  ∃ gs' : List Gate, ∃ adj' : ℕ → Option ℕ,
                    (∃ ex, gs' = gs ++ ex ∧ ex.length ≤ 2) ∧
                    Monotone2 ⟨gs', 0⟩ ∧ ReadsBack n ⟨gs', 0⟩ ∧
                    (∀ w u, adj' w = some u → u < n + gs'.length) ∧
                    (∀ (x : Fin n → Bool) (j : Fin m),
                      let x0 := Fin.append x (fun _ : Fin m => false)
                      let xj := Fin.append x (fun l => decide (l = j))
                      (∀ w < n + m + p, val C.gates w x0 = true → optVal gs' x (adj' w) = true → val C.gates C.output x0 = true) ∧
                      (∀ w < n + m + p, val C.gates w xj = true → optVal gs' x (adj' w) = true → val C.gates C.output xj = true) ∧
                      (val C.gates C.output xj = true → val C.gates C.output x0 = true ∨
                        ∃ w < n + m + p, 0 < deg n m C w ∧ val C.gates w xj = true ∧ optVal gs' x (adj' w) = true)) := by
                intro c d hclt hdlt hdc hval_cd
                have hfc_lt : fwdMap n m c < n + gs.length := by
                  rw [hgs_ext, List.length_append, fwdGates_len]
                  unfold fwdMap; split_ifs <;> omega
                let r1 := andWireOpt n gs (adj (n + m + p)) (fwdMap n m c)
                obtain ⟨⟨ex1, hex1, hex1len⟩, hm1, hb1, hv1, hval1⟩ :=
                  andWireOpt_spec n gs (adj (n + m + p)) (fwdMap n m c) hmono_gs hback_gs (hvalid_adj (n + m + p)) hfc_lt
                have hv_adj1 : ∀ w u, adj w = some u → u < n + r1.1.length := by
                  intro w u hu; have := hvalid_adj w u hu; rw [hex1, List.length_append]; omega
                obtain ⟨gs2, adj2, ⟨ex2, hex2, hex2len⟩, hm2, hb2, hv2, hval2⟩ :=
                  add1 r1.1 adj d r1.2 hm1 hb1 hv_adj1 hv1
                refine ⟨gs2, adj2, ⟨ex1 ++ ex2, by rw [hex2, hex1, List.append_assoc], by simp; omega⟩, hm2, hb2, hv2, ?_⟩
                intro x j
                obtain ⟨hs0, hsj, hcomp⟩ := hsem x j
                rw [hp_succ] at hs0 hsj hcomp
                have hopt_keep : ∀ w, optVal r1.1 x (adj w) = optVal gs x (adj w) := by
                  intro w
                  cases h : adj w with
                  | none => rfl
                  | some u =>
                    simp only [optVal]; rw [hex1]
                    exact wf_prefix gs ex1 (List.ofFn x) u (by simpa using hvalid_adj w u h)
                have hvc0 : val gs (fwdMap n m c) x = val C.gates c (Fin.append x (fun _ => false)) :=
                  hgs_fwd_val x c (by omega)
                have hvcj : val C.gates c (Fin.append x (fun l => decide (l = j))) = val C.gates c (Fin.append x (fun _ => false)) :=
                  deg_zero_indep n m C hmono hback x (fun l => decide (l = j)) c (by omega) hdc
                refine ⟨?_, ?_, ?_⟩
                · intro w hw hvw haw
                  rw [hval2 x w] at haw
                  by_cases hwd : w = d
                  · subst w; rw [ite_eq_left rfl, hopt_keep d, hval1 x, hvc0, Bool.or_eq_true, Bool.and_eq_true] at haw
                    rcases haw with h1 | ⟨h2, h3⟩
                    · exact hs0 d (by omega) hvw h1
                    · exact hs0 (n + m + p) (by omega) ((hval_cd _).mpr ⟨h3, hvw⟩) h2
                  · rw [ite_eq_right hwd, hopt_keep w] at haw; exact hs0 w (by omega) hvw haw
                · intro w hw hvw haw
                  rw [hval2 x w] at haw
                  by_cases hwd : w = d
                  · subst w; rw [ite_eq_left rfl, hopt_keep d, hval1 x, hvc0, Bool.or_eq_true, Bool.and_eq_true] at haw
                    rcases haw with h1 | ⟨h2, h3⟩
                    · exact hsj d (by omega) hvw h1
                    · exact hsj (n + m + p) (by omega) ((hval_cd _).mpr ⟨hvcj.symm ▸ h3, hvw⟩) h2
                  · rw [ite_eq_right hwd, hopt_keep w] at haw; exact hsj w (by omega) hvw haw
                · intro hv
                  rcases hcomp hv with h0 | ⟨w, hw, hdw, hvw, haw⟩
                  · exact Or.inl h0
                  · by_cases hwp : w = n + m + p
                    · subst hwp
                      obtain ⟨hvc, hvd⟩ := (hval_cd _).mp hvw
                      have hvc0_tr : val C.gates c (Fin.append x (fun _ : Fin m => false)) = true := hvcj.symm.trans hvc
                      by_cases hdd : deg n m C d = 0
                      · have hvd0 : val C.gates d (Fin.append x (fun _ : Fin m => false)) = true := by
                          rw [← deg_zero_indep n m C hmono hback x (fun l => decide (l = j)) d (by omega) hdd]; exact hvd
                        exact Or.inl (hs0 (n + m + p) (by omega) ((hval_cd _).mpr ⟨hvc0_tr, hvd0⟩) haw)
                      · refine Or.inr ⟨d, hdlt, by omega, hvd, ?_⟩
                        rw [hval2 x d, ite_eq_left rfl, hval1 x, hvc0, haw, hvc0_tr]
                        simp
                    · refine Or.inr ⟨w, by omega, hdw, hvw, ?_⟩
                      rw [hval2 x w]
                      by_cases hwd : w = d
                      · rw [ite_eq_left hwd, ← hwd, hopt_keep w, haw, Bool.true_or]
                      · rw [ite_eq_right hwd, hopt_keep w]; exact haw
              rcases hnc with hda | hdb
              · exact handle_and a b halt hblt hda fun z => by
                  rw [val_and C.gates z p hp_lt hop_and, hin]; simp [halt, hblt]
              · exact handle_and b a hblt halt hdb fun z => by
                  rw [val_and C.gates z p hp_lt hop_and, hin]; simp [halt, hblt, and_comm]
            | _ :: _ :: _ :: _ => rw [hin] at hlen_p; simp at hlen_p
          · match hin : C.gates[p].inputs with
            | [] =>
              have := deg_gate_eq n m C p hp_lt hback_p
              split_ifs at this with h
              · exact GateOp.noConfusion (hop_or.symm.trans h)
              · rw [hin] at this; simp at this; exact absurd this hdp
            | [a] =>
              have halt : a < n + m + p := hback_p a (by rw [hin]; simp)
              obtain ⟨gs1, adj1, ⟨ex1, hex1, hex1len⟩, hm1, hb1, hv1, hval1⟩ :=
                add1 gs adj a (adj (n + m + p)) hmono_gs hback_gs hvalid_adj (hvalid_adj (n + m + p))
              refine ⟨gs1, adj1, ⟨ex1, hex1, by omega⟩, hm1, hb1, hv1, ?_⟩
              intro x j
              obtain ⟨hs0, hsj, hcomp⟩ := hsem x j
              rw [hp_succ] at hs0 hsj hcomp
              have hval_p : ∀ z : Fin (n + m) → Bool, val C.gates (n + m + p) z = true ↔ val C.gates a z = true := by
                intro z; rw [val_or C.gates z p hp_lt hop_or, hin]; simp [halt]
              refine ⟨?_, ?_, ?_⟩
              · intro w hw hvw haw
                rw [hval1 x w] at haw
                by_cases hwa : w = a
                · subst w; rw [ite_eq_left rfl, Bool.or_eq_true] at haw
                  rcases haw with h1 | h2
                  · exact hs0 a (by omega) hvw h1
                  · exact hs0 (n + m + p) (by omega) ((hval_p _).mpr hvw) h2
                · rw [ite_eq_right hwa] at haw; exact hs0 w (by omega) hvw haw
              · intro w hw hvw haw
                rw [hval1 x w] at haw
                by_cases hwa : w = a
                · subst w; rw [ite_eq_left rfl, Bool.or_eq_true] at haw
                  rcases haw with h1 | h2
                  · exact hsj a (by omega) hvw h1
                  · exact hsj (n + m + p) (by omega) ((hval_p _).mpr hvw) h2
                · rw [ite_eq_right hwa] at haw; exact hsj w (by omega) hvw haw
              · intro hv
                rcases hcomp hv with h0 | ⟨w, hw, hdw, hvw, haw⟩
                · exact Or.inl h0
                · by_cases hwp : w = n + m + p
                  · subst hwp
                    have hva : val C.gates a (Fin.append x (fun l => decide (l = j))) = true := (hval_p _).mp hvw
                    by_cases hda : deg n m C a = 0
                    · have hva0 : val C.gates a (Fin.append x (fun _ : Fin m => false)) = true := by
                        rw [← deg_zero_indep n m C hmono hback x (fun l => decide (l = j)) a (by omega) hda]; exact hva
                      exact Or.inl (hs0 (n + m + p) (by omega) ((hval_p _).mpr hva0) haw)
                    · refine Or.inr ⟨a, halt, by omega, hva, ?_⟩
                      rw [hval1 x a, ite_eq_left rfl, haw, Bool.or_true]
                  · refine Or.inr ⟨w, by omega, hdw, hvw, ?_⟩
                    rw [hval1 x w]
                    by_cases hwa : w = a
                    · rw [ite_eq_left hwa, ← hwa, haw, Bool.true_or]
                    · rw [ite_eq_right hwa]; exact haw
            | [a, b] =>
              have halt : a < n + m + p := hback_p a (by rw [hin]; simp)
              have hblt : b < n + m + p := hback_p b (by rw [hin]; simp)
              let r := adj (n + m + p)
              obtain ⟨gs1, adj1, ⟨ex1, hex1, hex1len⟩, hm1, hb1, hv1, hval1⟩ :=
                add1 gs adj a r hmono_gs hback_gs hvalid_adj (hvalid_adj (n + m + p))
              have hr1 : ∀ u, r = some u → u < n + gs1.length := by
                intro u hu; have := hvalid_adj (n + m + p) u hu; rw [hex1, List.length_append]; omega
              obtain ⟨gs2, adj2, ⟨ex2, hex2, hex2len⟩, hm2, hb2, hv2, hval2⟩ :=
                add1 gs1 adj1 b r hm1 hb1 hv1 hr1
              refine ⟨gs2, adj2, ⟨ex1 ++ ex2, by rw [hex2, hex1, List.append_assoc], by simp; omega⟩, hm2, hb2, hv2, ?_⟩
              intro x j
              obtain ⟨hs0, hsj, hcomp⟩ := hsem x j
              rw [hp_succ] at hs0 hsj hcomp
              have hval_p : ∀ z : Fin (n + m) → Bool, val C.gates (n + m + p) z = true ↔ val C.gates a z = true ∨ val C.gates b z = true := by
                intro z; rw [val_or C.gates z p hp_lt hop_or, hin]; simp [halt, hblt]
              have hr_keep : optVal gs1 x r = optVal gs x r := by
                cases h : r with
                | none => rfl
                | some u =>
                  simp only [optVal]; rw [hex1]
                  exact wf_prefix gs ex1 (List.ofFn x) u (by simpa using hvalid_adj (n + m + p) u h)
              have hcomb : ∀ w, optVal gs2 x (adj2 w) = true ↔
                  optVal gs x (adj w) = true ∨ ((w = a ∨ w = b) ∧ optVal gs x r = true) := by
                intro w
                rw [hval2 x w]
                by_cases hwb : w = b
                · subst w; rw [ite_eq_left rfl, hval1 x b, hr_keep]
                  by_cases hba : b = a
                  · subst hba; rw [ite_eq_left rfl]; simp [Bool.or_eq_true]
                  · rw [ite_eq_right hba]; simp [Bool.or_eq_true]
                · rw [ite_eq_right hwb, hval1 x w]
                  by_cases hwa : w = a
                  · subst w; rw [ite_eq_left rfl]; simp [Bool.or_eq_true]
                  · rw [ite_eq_right hwa]; simp [hwa, hwb]
              refine ⟨?_, ?_, ?_⟩
              · intro w hw hvw haw
                rcases (hcomb w).mp haw with h1 | ⟨rfl | rfl, h2⟩
                · exact hs0 w (by omega) hvw h1
                · exact hs0 (n + m + p) (by omega) ((hval_p _).mpr (Or.inl hvw)) h2
                · exact hs0 (n + m + p) (by omega) ((hval_p _).mpr (Or.inr hvw)) h2
              · intro w hw hvw haw
                rcases (hcomb w).mp haw with h1 | ⟨rfl | rfl, h2⟩
                · exact hsj w (by omega) hvw h1
                · exact hsj (n + m + p) (by omega) ((hval_p _).mpr (Or.inl hvw)) h2
                · exact hsj (n + m + p) (by omega) ((hval_p _).mpr (Or.inr hvw)) h2
              · intro hv
                rcases hcomp hv with h0 | ⟨w, hw, hdw, hvw, haw⟩
                · exact Or.inl h0
                · by_cases hwp : w = n + m + p
                  · subst hwp
                    rcases (hval_p _).mp hvw with hva | hvb
                    · by_cases hda : deg n m C a = 0
                      · have hva0 : val C.gates a (Fin.append x (fun _ : Fin m => false)) = true := by
                          rw [← deg_zero_indep n m C hmono hback x (fun l => decide (l = j)) a (by omega) hda]; exact hva
                        exact Or.inl (hs0 (n + m + p) (by omega) ((hval_p _).mpr (Or.inl hva0)) haw)
                      · exact Or.inr ⟨a, halt, by omega, hva, (hcomb a).mpr (Or.inr ⟨Or.inl rfl, haw⟩)⟩
                    · by_cases hdb : deg n m C b = 0
                      · have hvb0 : val C.gates b (Fin.append x (fun _ : Fin m => false)) = true := by
                          rw [← deg_zero_indep n m C hmono hback x (fun l => decide (l = j)) b (by omega) hdb]; exact hvb
                        exact Or.inl (hs0 (n + m + p) (by omega) ((hval_p _).mpr (Or.inr hvb0)) haw)
                      · exact Or.inr ⟨b, hblt, by omega, hvb, (hcomb b).mpr (Or.inr ⟨Or.inr rfl, haw⟩)⟩
                  · exact Or.inr ⟨w, by omega, hdw, hvw, (hcomb w).mpr (Or.inl haw)⟩
            | _ :: _ :: _ :: _ => rw [hin] at hlen_p; simp at hlen_p
        obtain ⟨gs', adj', ⟨ex', hex', hex'len⟩, hm', hb', hv', hsem'⟩ := hstep_done
        refine ⟨gs', adj', ⟨extra0 ++ ex', by rw [hex', hgs_ext, List.append_assoc]⟩, hm', hb', ?_, hv', hsem'⟩
        rw [hex', List.length_append]
        rw [hp_succ] at hlen_gs
        change gs.length + ex'.length ≤ 2 + C.gates.length + 2 * (Tfin.filter fun i => p ≤ i).card
        omega
  obtain ⟨gs, adj, _, hmD, hbD, hlenD, _, hsemD⟩ := hback_step C.gates.length le_rfl
  let D : Circuit := ⟨gs, 0⟩
  let o : Fin m → ℕ := fun j => match adj (n + j.val) with | none => n + gs.length | some u => u
  have ho_val : ∀ (x : Fin n → Bool) (j : Fin m), val gs (o j) x = optVal gs x (adj (n + j.val)) := by
    intro x j
    dsimp only [o]
    cases adj (n + j.val) with
    | none => exact val_big gs x (n + gs.length) le_rfl
    | some u => rfl
  refine ⟨D, o, hmD, hbD, ?_, ?_⟩
  · have hfilt : (Tfin.filter fun i => C.gates.length - C.gates.length ≤ i) = Tfin := by
      ext i; simp
    rw [hfilt] at hlenD
    rw [hTcard]
    change gs.length ≤ C.gates.length + 3 * Tfin.card + m
    omega
  · intro x j
    obtain ⟨_, hsj, hcomp⟩ := hsemD x j
    rw [Nat.sub_self, add_zero] at hsj hcomp
    change val C.gates C.output (Fin.append x (fun l => decide (l = j))) =
      (val C.gates C.output (Fin.append x (fun _ => false)) || val gs (o j) x)
    rw [ho_val x j]
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true]
    constructor
    · intro hv
      rcases hcomp hv with h0 | ⟨w, hw, hdw, hvw, haw⟩
      · exact Or.inl h0
      · have hwn : n ≤ w := by
          by_contra hlt; have := deg_input_left n m C w (by omega); omega
        rw [val_input C.gates _ w hw, fin_append_right x _ w hwn hw, decide_eq_true_eq] at hvw
        have hweq : w = n + j.val := by have := congrArg Fin.val hvw; dsimp at this; omega
        subst hweq
        exact Or.inr haw
    · rintro (h0 | ho)
      · exact val_mono C.gates hlegC _ _ (fun v hv => by
          by_cases hvn : v.val < n
          · have hv' : v = ⟨v.val, v.isLt⟩ := rfl
            rw [hv', fin_append_left _ _ v.val hvn] at hv ⊢; exact hv
          · have hv' : v = ⟨v.val, v.isLt⟩ := rfl
            rw [hv', fin_append_right _ _ v.val (by omega) v.isLt] at hv; simp at hv) C.output h0
      · have hvnj : val C.gates (n + j.val) (Fin.append x (fun l => decide (l = j))) = true := by
          rw [val_input C.gates _ (n + j.val) (by omega), fin_append_right x _ (n + j.val) (by omega) (by omega)]
          simp
        exact hsj (n + j.val) (by omega) hvnj ho

end PEqualNP.Outside.L_meta_1622_aux

theorem PEqualNP.Outside.L_meta_1622 : ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧ ∀ (x : Fin n → Bool) (j : Fin m), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || (D.wires (List.ofFn x)).getD (o j) false) := by
  exact PEqualNP.Outside.L_meta_1622_aux.final_thm

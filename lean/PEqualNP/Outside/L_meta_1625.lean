import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1625_aux
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
    apply Fin.ext; simp; omega
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


theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem merge_card {n : ℕ} (A : Finset (Fin n)) (c : Fin n → Fin n) (x y : Fin n) :
    (A.image c).card ≤ (A.image fun p => if c p = y then x else c p).card + 1 := by
  classical
  have h1 : ((A.image c).erase y) ⊆ A.image fun p => if c p = y then x else c p := by
    intro v hv
    rw [Finset.mem_erase] at hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv.2
    exact Finset.mem_image.2 ⟨p, hp, by simp [hv.1]⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.pred_card_le_card_erase (s := A.image c) (a := y)
  omega

theorem two_list (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : l = [a, b] ∨ l = [b, a] := by
  match l, hl with
  | [], _ => simp at ha
  | [u], _ =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | [u, v], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hab

theorem main (n : ℕ) (M A : Finset (Fin n)) (tau : Fin n → Fin n → Bool)
    (gates : List Gate)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hAM : A ⊆ M) (htau : ∀ p ∈ A, ∀ v ∈ M, tau p v = true ↔ v = p)
    (I : Finset (Fin gates.length))
    (hI : ∀ g : Fin gates.length, ((gates.get g).op = GateOp.or ∧
        val gates (n + (g : ℕ)) (fun v : Fin n => decide (v ∉ M)) = false ∧
        ∃ p ∈ A, ∃ p' ∈ A, p ≠ p' ∧
          val gates (n + (g : ℕ)) (tau p) = true ∧ val gates (n + (g : ℕ)) (tau p') = true) → g ∈ I) :
    ∀ k, k ≤ gates.length → ∃ c : Fin n → Fin n,
      A.card ≤ (A.image c).card + (I.filter fun g => g.val < k).card ∧
      ∀ w < n + k, val gates w (fun v : Fin n => decide (v ∉ M)) = false →
        ∀ p ∈ A, ∀ p' ∈ A, val gates w (tau p) = true → val gates w (tau p') = true →
          c p = c p' := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨id, by simp, ?_⟩
    intro w hw hz p hp p' hp' h1 h2
    have hw' : w < n := by omega
    rw [val_input gates _ w hw'] at hz h1 h2
    have hM : (⟨w, hw'⟩ : Fin n) ∈ M := by simpa using hz
    have e1 := (htau p hp _ hM).1 h1
    have e2 := (htau p' hp' _ hM).1 h2
    exact e1.symm.trans e2
  | succ k ih =>
    intro hk
    have hk' : k < gates.length := hk
    obtain ⟨c, hcard, hc⟩ := ih (Nat.le_of_lt hk')
    have hmono : (I.filter fun g => g.val < k).card ≤ (I.filter fun g => g.val < k + 1).card :=
      Finset.card_le_card (fun g hg => by
        rw [Finset.mem_filter] at hg ⊢; exact ⟨hg.1, by omega⟩)
    have keep : (val gates (n + k) (fun v : Fin n => decide (v ∉ M)) = false →
        ∀ p ∈ A, ∀ p' ∈ A, val gates (n + k) (tau p) = true → val gates (n + k) (tau p') = true →
          c p = c p') →
        ∃ c : Fin n → Fin n,
          A.card ≤ (A.image c).card + (I.filter fun g => g.val < k + 1).card ∧
          ∀ w < n + (k + 1), val gates w (fun v : Fin n => decide (v ∉ M)) = false →
            ∀ p ∈ A, ∀ p' ∈ A, val gates w (tau p) = true → val gates w (tau p') = true →
              c p = c p' := by
      intro hnew
      refine ⟨c, by omega, ?_⟩
      intro w hw hz p hp p' hp' h1 h2
      by_cases hwk : w = n + k
      · subst hwk; exact hnew hz p hp p' hp' h1 h2
      · exact hc w (by omega) hz p hp p' hp' h1 h2
    have hlegk := hleg gates[k] (List.getElem_mem hk')
    rcases hlegk.1 with hop | hop
    · apply keep
      intro hz p hp p' hp' h1 h2
      have hz' : ¬ ∀ i ∈ gates[k].inputs, i < n + k ∧
          val gates i (fun v : Fin n => decide (v ∉ M)) = true := by
        intro h; rw [(val_and gates _ k hk' hop).2 h] at hz; exact absurd hz (by simp)
      push Not at hz'
      obtain ⟨i, hi, hiz⟩ := hz'
      have a1 := (val_and gates (tau p) k hk' hop).1 h1 i hi
      have a2 := (val_and gates (tau p') k hk' hop).1 h2 i hi
      have hzi : val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
        simpa using hiz a1.1
      exact hc i a1.1 hzi p hp p' hp' a1.2 a2.2
    · by_cases hkI : (⟨k, hk'⟩ : Fin gates.length) ∈ I
      · by_cases hsame : val gates (n + k) (fun v : Fin n => decide (v ∉ M)) = false →
            ∀ p ∈ A, ∀ p' ∈ A, val gates (n + k) (tau p) = true →
              val gates (n + k) (tau p') = true → c p = c p'
        · exact keep hsame
        · push Not at hsame
          obtain ⟨hz, a, ha, b, hb, hva, hvb, hne⟩ := hsame
          obtain ⟨ia, hia, hia1, hia2⟩ := (val_or gates (tau a) k hk' hop).1 hva
          obtain ⟨ib, hib, hib1, hib2⟩ := (val_or gates (tau b) k hk' hop).1 hvb
          have hzall : ∀ i ∈ gates[k].inputs, i < n + k →
              val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
            intro i hi hlt
            by_contra hcon
            have : val gates i (fun v : Fin n => decide (v ∉ M)) = true := by simpa using hcon
            rw [(val_or gates _ k hk' hop).2 ⟨i, hi, hlt, this⟩] at hz
            exact absurd hz (by simp)
          have hiab : ia ≠ ib := by
            intro h; subst h
            exact hne (hc ia hia1 (hzall ia hia hia1) a ha b hb hia2 hib2)
          have hcount : (I.filter fun g => g.val < k).card + 1 ≤
              (I.filter fun g => g.val < k + 1).card := by
            have hsub : insert (⟨k, hk'⟩ : Fin gates.length) (I.filter fun g => g.val < k) ⊆
                I.filter fun g => g.val < k + 1 := by
              intro g hg
              rw [Finset.mem_insert] at hg
              rcases hg with rfl | hg
              · exact Finset.mem_filter.2 ⟨hkI, by simp⟩
              · rw [Finset.mem_filter] at hg ⊢; exact ⟨hg.1, by omega⟩
            have := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem (by simp)] at this
            exact this
          refine ⟨fun p => if c p = c b then c a else c p, ?_, ?_⟩
          · have := merge_card A c (c a) (c b)
            omega
          · intro w hw hzw p hp p' hp' h1 h2
            by_cases hwk : w = n + k
            · subst hwk
              have col : ∀ q ∈ A, val gates (n + k) (tau q) = true → c q = c a ∨ c q = c b := by
                intro q hq hvq
                obtain ⟨iq, hiq, hiq1, hiq2⟩ := (val_or gates (tau q) k hk' hop).1 hvq
                rcases two_list _ hlegk.2 ia ib hia hib hiab with hl | hl
                · rw [hl] at hiq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hiq
                  rcases hiq with rfl | rfl
                  · exact Or.inl (hc _ hiq1 (hzall _ hia hiq1) q hq a ha hiq2 hia2)
                  · exact Or.inr (hc _ hiq1 (hzall _ hib hiq1) q hq b hb hiq2 hib2)
                · rw [hl] at hiq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hiq
                  rcases hiq with rfl | rfl
                  · exact Or.inr (hc _ hiq1 (hzall _ hib hiq1) q hq b hb hiq2 hib2)
                  · exact Or.inl (hc _ hiq1 (hzall _ hia hiq1) q hq a ha hiq2 hia2)
              have fin : ∀ q ∈ A, val gates (n + k) (tau q) = true →
                  (if c q = c b then c a else c q) = c a := by
                intro q hq hvq
                rcases col q hq hvq with h | h
                · rw [h]; split_ifs <;> rfl
                · rw [if_pos h]
              show (if c p = c b then c a else c p) = (if c p' = c b then c a else c p')
              rw [fin p hp h1, fin p' hp' h2]
            · have := hc w (by omega) hzw p hp p' hp' h1 h2
              show (if c p = c b then c a else c p) = (if c p' = c b then c a else c p')
              rw [this]
      · apply keep
        intro hz p hp p' hp' h1 h2
        obtain ⟨ia, hia, hia1, hia2⟩ := (val_or gates (tau p) k hk' hop).1 h1
        obtain ⟨ib, hib, hib1, hib2⟩ := (val_or gates (tau p') k hk' hop).1 h2
        have hzall : ∀ i ∈ gates[k].inputs, i < n + k →
            val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
          intro i hi hlt
          by_contra hcon
          have : val gates i (fun v : Fin n => decide (v ∉ M)) = true := by simpa using hcon
          rw [(val_or gates _ k hk' hop).2 ⟨i, hi, hlt, this⟩] at hz
          exact absurd hz (by simp)
        by_cases hiab : ia = ib
        · subst hiab
          exact hc ia hia1 (hzall ia hia hia1) p hp p' hp' hia2 hib2
        · by_contra hcne
          have hpp : p ≠ p' := fun h => hcne (by rw [h])
          apply hkI
          apply hI ⟨k, hk'⟩
          exact ⟨hop, hz, p, hp, p', hp', hpp, h1, h2⟩

lemma row_bound : ∀ (n : ℕ) (M A : Finset (Fin n)) (tau : Fin n → Fin n → Bool)
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    A ⊆ M →
    (∀ p ∈ A, ∀ v ∈ M, tau p v = true ↔ v = p) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false →
    (∀ p ∈ A, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (tau p)) = true) →
    ∀ I : Finset (Fin gates.length),
      (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false ∧
        ∃ p ∈ A, ∃ p' ∈ A, p ≠ p' ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (tau p)) = true ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (tau p')) = true) → g ∈ I) →
      A.card ≤ 1 + I.card := by
  classical
  intro n M A tau gates o hleg hAM htau hout htrue I hI
  obtain ⟨c, hcard, hc⟩ := main n M A tau gates hleg hAM htau I hI gates.length le_rfl
  have hJ : (I.filter fun g => g.val < gates.length).card ≤ I.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rcases A.eq_empty_or_nonempty with hA | ⟨p0, hp0⟩
  · subst hA; simp
  · have ho : o < n + gates.length := by
      by_contra hcon
      have := htrue p0 hp0
      rw [eval_eq] at this
      have h2 := val_big gates (tau p0) o (by omega)
      rw [val] at h2
      rw [h2] at this
      exact absurd this (by simp)
    have hconst : ∀ p ∈ A, c p = c p0 := fun p hp =>
      hc o ho hout p hp p0 hp0 (htrue p hp) (htrue p0 hp0)
    have himg : (A.image c).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      rw [hconst p hp, hconst q hq]
    omega

theorem val_prefix {N : ℕ} (pre post : List Gate) (w : ℕ) (z : Fin N → Bool)
    (hw : w < N + pre.length) : val (pre ++ post) w z = val pre w z :=
  wf_prefix pre post (List.ofFn z) w (by simpa using hw)

def degG (n m : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  deg n m ⟨gs, 0⟩ w

theorem degG_input_left (n m : ℕ) (gs : List Gate) (w : ℕ) (hw : w < n) :
    degG n m gs w = 0 := deg_input_left n m ⟨gs, 0⟩ w hw

theorem degG_input_right (n m : ℕ) (gs : List Gate) (w : ℕ) (h1 : n ≤ w) (h2 : w < n + m) :
    degG n m gs w = 1 := deg_input_right n m ⟨gs, 0⟩ w h1 h2

theorem degG_prefix (n m : ℕ) (pre post : List Gate) (w : ℕ) (hw : w < n + m + pre.length) :
    degG n m (pre ++ post) w = degG n m pre w := by
  unfold degG deg Circuit.lineDegrees
  change (ldFold (pre ++ post) ((List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0)).getD w 0 =
    (ldFold pre ((List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0)).getD w 0
  exact ldFold_prefix pre post _ w (by simp; omega)

theorem degG_append_zero (n m : ℕ) (gs : List Gate) (g : Gate)
    (hback_g : ∀ i ∈ g.inputs, i < n + m + gs.length)
    (hd_g : ∀ i ∈ g.inputs, degG n m gs i = 0) :
    degG n m (gs ++ [g]) (n + m + gs.length) = 0 := by
  have hk : gs.length < (gs ++ [g]).length := by simp
  have hget : (gs ++ [g])[gs.length] = g := by simp
  have hbk : ∀ i ∈ (gs ++ [g])[gs.length].inputs, i < n + m + gs.length := by
    rw [hget]; exact hback_g
  have heq := deg_gate_eq n m ⟨gs ++ [g], 0⟩ gs.length hk hbk
  change degG n m (gs ++ [g]) (n + m + gs.length) = _ at heq
  rw [heq, hget]
  have hzero : ∀ i ∈ g.inputs, deg n m ⟨gs ++ [g], 0⟩ i = 0 := by
    intro i hi
    change degG n m (gs ++ [g]) i = 0
    rw [degG_prefix n m gs [g] i (hback_g i hi)]
    exact hd_g i hi
  split_ifs
  · exact List.sum_eq_zero_iff.mpr (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact hzero i hi)
  · exact (foldr_max_eq_zero _).mpr (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact hzero i hi)

def NoCross (n m : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), gs[j].op = GateOp.and → gs[j].inputs.length = 2 →
    ∃ i ∈ gs[j].inputs, degG n m gs i = 0

theorem NoCross_snoc (n m : ℕ) (gs : List Gate) (g : Gate)
    (hnc : NoCross n m gs) (hback_gs : ReadsBack (n + m) ⟨gs, 0⟩)
    (hback_g : ∀ i ∈ g.inputs, i < n + m + gs.length)
    (hg_nc : g.op = GateOp.and → g.inputs.length = 2 → ∃ i ∈ g.inputs, degG n m gs i = 0) :
    NoCross n m (gs ++ [g]) := by
  intro j hj hop hlen
  by_cases hlt : j < gs.length
  · have hget : (gs ++ [g])[j] = gs[j] := List.getElem_append_left hlt
    rw [hget] at hop hlen ⊢
    obtain ⟨i, hi, hdi⟩ := hnc j hlt hop hlen
    have hilt : i < n + m + j := by
      have hb := hback_gs j hlt i
      unfold gateAt at hb
      rw [List.getD_eq_getElem _ _ hlt] at hb
      exact hb hi
    exact ⟨i, hi, by rw [degG_prefix n m gs [g] i (by omega)]; exact hdi⟩
  · have hjeq : j = gs.length := by simp at hj; omega
    subst hjeq
    have hget : (gs ++ [g])[gs.length] = g := by simp
    rw [hget] at hop hlen ⊢
    obtain ⟨i, hi, hdi⟩ := hg_nc hop hlen
    exact ⟨i, hi, by rw [degG_prefix n m gs [g] i (hback_g i hi)]; exact hdi⟩

def tCount (n m : ℕ) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter (fun q => 0 < degG n m gs (n + m + q))).card

theorem tCount_snoc_zero (n m : ℕ) (gs : List Gate) (g : Gate)
    (hdz : degG n m (gs ++ [g]) (n + m + gs.length) = 0) :
    tCount n m (gs ++ [g]) = tCount n m gs := by
  unfold tCount
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_range, List.length_append, List.length_singleton]
  constructor
  · rintro ⟨hq, hpos⟩
    by_cases hqeq : q = gs.length
    · subst hqeq; omega
    · have hqlt : q < gs.length := by omega
      rw [degG_prefix n m gs [g] (n + m + q) (by omega)] at hpos
      exact ⟨hqlt, hpos⟩
  · rintro ⟨hq, hpos⟩
    refine ⟨by omega, ?_⟩
    rw [degG_prefix n m gs [g] (n + m + q) (by omega)]
    exact hpos

theorem tCount_snoc_le (n m : ℕ) (gs : List Gate) (g : Gate) :
    tCount n m (gs ++ [g]) ≤ tCount n m gs + 1 := by
  unfold tCount
  have hsub : ((Finset.range (gs ++ [g]).length).filter (fun q => 0 < degG n m (gs ++ [g]) (n + m + q))) ⊆
      insert gs.length ((Finset.range gs.length).filter (fun q => 0 < degG n m gs (n + m + q))) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range, List.length_append, List.length_singleton] at hq
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    by_cases hqeq : q = gs.length
    · exact Or.inl hqeq
    · have hqlt : q < gs.length := by omega
      right
      refine ⟨hqlt, ?_⟩
      have hpos := hq.2
      rw [degG_prefix n m gs [g] (n + m + q) (by omega)] at hpos
      exact hpos
  have hle := Finset.card_le_card hsub
  have hins := Finset.card_insert_le gs.length ((Finset.range gs.length).filter (fun q => 0 < degG n m gs (n + m + q)))
  omega

theorem orOpt_deg_spec (n m : ℕ) (gs : List Gate) (a b : Option ℕ)
    (hmono : Monotone2 ⟨gs, 0⟩) (hback : ReadsBack (n + m) ⟨gs, 0⟩) (hnc : NoCross n m gs)
    (ha : ∀ u, a = some u → u < n + m + gs.length ∧ degG n m gs u = 0)
    (hb : ∀ v, b = some v → v < n + m + gs.length ∧ degG n m gs v = 0) :
    let res := orOpt (n + m) gs a b
    (∃ extra, res.1 = gs ++ extra ∧ extra.length ≤ 1) ∧
    Monotone2 ⟨res.1, 0⟩ ∧ ReadsBack (n + m) ⟨res.1, 0⟩ ∧ NoCross n m res.1 ∧
    tCount n m res.1 = tCount n m gs ∧
    (∀ u, res.2 = some u → u < n + m + res.1.length ∧ degG n m res.1 u = 0) ∧
    (∀ z : Fin (n + m) → Bool, optVal res.1 z res.2 = (optVal gs z a || optVal gs z b)) := by
  have hbase := orOpt_spec (n + m) gs a b hmono hback (fun u hu => (ha u hu).1) (fun v hv => (hb v hv).1)
  cases a with
  | none =>
    exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hnc, rfl, hb, hbase.2.2.2.2⟩
  | some u =>
    cases b with
    | none =>
      exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hnc, rfl, ha, hbase.2.2.2.2⟩
    | some v =>
      obtain ⟨hu, hdu⟩ := ha u rfl
      obtain ⟨hv, hdv⟩ := hb v rfl
      let gnew : Gate := ⟨GateOp.or, [u, v]⟩
      have hbg : ∀ i ∈ gnew.inputs, i < n + m + gs.length := by
        intro i hi; simp [gnew] at hi; rcases hi with rfl | rfl <;> assumption
      have hdg : ∀ i ∈ gnew.inputs, degG n m gs i = 0 := by
        intro i hi; simp [gnew] at hi; rcases hi with rfl | rfl <;> assumption
      have hdz : degG n m (gs ++ [gnew]) (n + m + gs.length) = 0 :=
        degG_append_zero n m gs gnew hbg hdg
      have hnc' : NoCross n m (gs ++ [gnew]) :=
        NoCross_snoc n m gs gnew hnc hback hbg (fun h => by simp [gnew] at h)
      have htc' : tCount n m (gs ++ [gnew]) = tCount n m gs :=
        tCount_snoc_zero n m gs gnew hdz
      refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, hnc', htc', ?_, hbase.2.2.2.2⟩
      intro w hw
      simp only [orOpt, Option.some.injEq] at hw
      subst hw
      exact ⟨by simp [orOpt], hdz⟩

theorem andWireOpt_deg_spec (n m : ℕ) (gs : List Gate) (a : Option ℕ) (c : ℕ)
    (hmono : Monotone2 ⟨gs, 0⟩) (hback : ReadsBack (n + m) ⟨gs, 0⟩) (hnc : NoCross n m gs)
    (ha : ∀ u, a = some u → u < n + m + gs.length ∧ degG n m gs u = 0)
    (hc : c < n + m + gs.length) (hdc : degG n m gs c = 0) :
    let res := andWireOpt (n + m) gs a c
    (∃ extra, res.1 = gs ++ extra ∧ extra.length ≤ 1) ∧
    Monotone2 ⟨res.1, 0⟩ ∧ ReadsBack (n + m) ⟨res.1, 0⟩ ∧ NoCross n m res.1 ∧
    tCount n m res.1 = tCount n m gs ∧
    (∀ u, res.2 = some u → u < n + m + res.1.length ∧ degG n m res.1 u = 0) ∧
    (∀ z : Fin (n + m) → Bool, optVal res.1 z res.2 = (optVal gs z a && val gs c z)) := by
  have hbase := andWireOpt_spec (n + m) gs a c hmono hback (fun u hu => (ha u hu).1) hc
  cases a with
  | none =>
    exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hnc, rfl, fun _ h => by simp [andWireOpt] at h, hbase.2.2.2.2⟩
  | some u =>
    obtain ⟨hu, hdu⟩ := ha u rfl
    let gnew : Gate := ⟨GateOp.and, [u, c]⟩
    have hbg : ∀ i ∈ gnew.inputs, i < n + m + gs.length := by
      intro i hi; simp [gnew] at hi; rcases hi with rfl | rfl <;> assumption
    have hdg : ∀ i ∈ gnew.inputs, degG n m gs i = 0 := by
      intro i hi; simp [gnew] at hi; rcases hi with rfl | rfl <;> assumption
    have hdz : degG n m (gs ++ [gnew]) (n + m + gs.length) = 0 :=
      degG_append_zero n m gs gnew hbg hdg
    have hnc' : NoCross n m (gs ++ [gnew]) :=
      NoCross_snoc n m gs gnew hnc hback hbg (fun _ _ => ⟨c, by simp [gnew], hdc⟩)
    have htc' : tCount n m (gs ++ [gnew]) = tCount n m gs :=
      tCount_snoc_zero n m gs gnew hdz
    refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, hnc', htc', ?_, hbase.2.2.2.2⟩
    intro w hw
    simp only [andWireOpt, Option.some.injEq] at hw
    subst hw
    exact ⟨by simp [andWireOpt], hdz⟩

theorem base_consts_eval (n m : ℕ) (gs rest : List Gate)
    (hpre : gs = [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ rest) :
    2 ≤ gs.length ∧
    degG n m gs (n + m) = 0 ∧
    degG n m gs (n + m + 1) = 0 ∧
    (∀ z : Fin (n + m) → Bool, val gs (n + m) z = false) ∧
    (∀ z : Fin (n + m) → Bool, val gs (n + m + 1) z = true) := by
  have hlen : 2 ≤ gs.length := by rw [hpre]; simp
  have hg0 : gs[0]'(by omega) = ⟨GateOp.or, []⟩ := by simp [hpre]
  have hg1 : gs[1]'(by omega) = ⟨GateOp.and, []⟩ := by simp [hpre]
  have hd0 : degG n m gs (n + m) = 0 := by
    have h := deg_gate_eq n m ⟨gs, 0⟩ 0 (by dsimp; omega) (by dsimp; rw [hg0]; simp)
    change degG n m gs (n + m + 0) = _ at h
    rw [add_zero] at h
    dsimp only at h
    rw [h, hg0]; simp
  have hd1 : degG n m gs (n + m + 1) = 0 := by
    have h := deg_gate_eq n m ⟨gs, 0⟩ 1 (by dsimp; omega) (by dsimp; rw [hg1]; simp)
    change degG n m gs (n + m + 1) = _ at h
    dsimp only at h
    rw [h, hg1]; simp
  refine ⟨hlen, hd0, hd1, ?_, ?_⟩
  · intro z
    apply Bool.eq_false_iff.mpr
    intro h
    have hv := (val_or gs z 0 (by omega) (by rw [hg0])).mp (by simpa using h)
    rcases hv with ⟨_, hi, _⟩
    rw [hg0] at hi; simp at hi
  · intro z
    apply (val_and gs z 1 (by omega) (by rw [hg1])).mpr
    intro i hi
    rw [hg1] at hi; simp at hi

theorem backPass (n m : ℕ) (gs0 rest0 : List Gate)
    (hpre0 : gs0 = [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ rest0)
    (hmono0 : Monotone2 ⟨gs0, 0⟩) (hback0 : ReadsBack (n + m) ⟨gs0, 0⟩) (hnc0 : NoCross n m gs0)
    (target : ℕ) (htarget : target < n + m + gs0.length) :
    ∃ (extra : List Gate) (adj : ℕ → Option ℕ),
      extra.length ≤ 2 * tCount n m gs0 ∧
      Monotone2 ⟨gs0 ++ extra, 0⟩ ∧
      ReadsBack (n + m) ⟨gs0 ++ extra, 0⟩ ∧
      NoCross n m (gs0 ++ extra) ∧
      tCount n m (gs0 ++ extra) = tCount n m gs0 ∧
      (∀ w u, adj w = some u → u < n + m + (gs0 ++ extra).length ∧ degG n m (gs0 ++ extra) u = 0) ∧
      (∀ (x : Fin n → Bool) (j : Fin m),
        val gs0 target (Fin.append x (fun l => decide (l = j))) =
          (val gs0 target (Fin.append x (fun _ : Fin m => false)) ||
            optVal (gs0 ++ extra) (Fin.append x (fun _ : Fin m => false)) (adj (n + j.val)))) := by
  classical
  obtain ⟨hlen0, hd_false0, hd_true0, hv_false0, hv_true0⟩ := base_consts_eval n m gs0 rest0 hpre0
  have hleg0 : ∀ g ∈ gs0, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg; obtain ⟨h1, h2⟩ := hmono0 g hg; exact ⟨by simpa using h1, h2⟩
  by_cases hdz : degG n m gs0 target = 0
  · refine ⟨[], fun _ => none, by simp, by simpa using hmono0, by simpa using hback0, by simpa using hnc0, by simp,
      fun _ _ h => by simp at h, ?_⟩
    intro x j
    simp only [List.append_nil, optVal, Bool.or_false]
    exact deg_zero_indep n m ⟨gs0, 0⟩ hmono0 hback0 x (fun l => decide (l = j)) target htarget hdz
  by_cases htin : target < n + m
  · have htn : n ≤ target := by
      by_contra hlt
      exact hdz (degG_input_left n m gs0 target (by omega))
    refine ⟨[], fun w => if w = target then some (n + m + 1) else none, by simp,
      by simpa using hmono0, by simpa using hback0, by simpa using hnc0, by simp, ?_, ?_⟩
    · intro w u hu
      dsimp only at hu
      split_ifs at hu
      injection hu with h
      subst h
      exact ⟨by simp; omega, by simpa using hd_true0⟩
    · intro x j
      simp only [List.append_nil]
      rw [val_input gs0 _ target htin, val_input gs0 _ target htin,
          fin_append_right x _ target htn htin, fin_append_right x _ target htn htin, Bool.false_or]
      by_cases hjt : n + j.val = target
      · rw [if_pos hjt]
        simp only [optVal, hv_true0]
        have hfin : (⟨target - n, by omega⟩ : Fin m) = j := by apply Fin.ext; dsimp; omega
        simp [hfin]
      · rw [if_neg hjt]
        simp only [optVal]
        have hfin : (⟨target - n, by omega⟩ : Fin m) ≠ j := by
          intro h; have := congrArg Fin.val h; dsimp at this; omega
        simp [hfin]
  have htG : target - (n + m) < gs0.length := by omega
  have htEq : n + m + (target - (n + m)) = target := by omega
  let Tfin : Finset ℕ := (Finset.range gs0.length).filter (fun q => 0 < degG n m gs0 (n + m + q))
  have hTcard : tCount n m gs0 = Tfin.card := rfl
  have hstep : ∀ k, k ≤ gs0.length →
      ∃ (extra : List Gate) (adj : ℕ → Option ℕ),
        extra.length ≤ 2 * (Tfin.filter fun i => gs0.length - k ≤ i).card ∧
        Monotone2 ⟨gs0 ++ extra, 0⟩ ∧
        ReadsBack (n + m) ⟨gs0 ++ extra, 0⟩ ∧
        NoCross n m (gs0 ++ extra) ∧
        tCount n m (gs0 ++ extra) = tCount n m gs0 ∧
        (∀ w u, adj w = some u → u < n + m + (gs0 ++ extra).length ∧ degG n m (gs0 ++ extra) u = 0) ∧
        (∀ (x : Fin n → Bool) (j : Fin m),
          let x0 := Fin.append x (fun _ : Fin m => false)
          let xj := Fin.append x (fun l => decide (l = j))
          (∀ w < n + m + (gs0.length - k), val gs0 w x0 = true → optVal (gs0 ++ extra) x0 (adj w) = true → val gs0 target x0 = true) ∧
          (∀ w < n + m + (gs0.length - k), val gs0 w xj = true → optVal (gs0 ++ extra) x0 (adj w) = true → val gs0 target xj = true) ∧
          (val gs0 target xj = true → val gs0 target x0 = true ∨
            ∃ w < n + m + (gs0.length - k), 0 < degG n m gs0 w ∧ val gs0 w xj = true ∧ optVal (gs0 ++ extra) x0 (adj w) = true)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if w = target then some (n + m + 1) else none, by simp,
        by simpa using hmono0, by simpa using hback0, by simpa using hnc0, by simp, ?_, ?_⟩
      · intro w u hu
        dsimp only at hu
        split_ifs at hu
        injection hu with h; subst h
        exact ⟨by simp; omega, by simpa using hd_true0⟩
      · intro x j
        simp only [List.append_nil, Nat.sub_zero]
        refine ⟨?_, ?_, ?_⟩
        · intro w _ hvw haw
          by_cases hwt : w = target
          · subst hwt; exact hvw
          · rw [if_neg hwt] at haw; simp [optVal] at haw
        · intro w _ hvw haw
          by_cases hwt : w = target
          · subst hwt; exact hvw
          · rw [if_neg hwt] at haw; simp [optVal] at haw
        · intro hv
          right
          refine ⟨target, htarget, by omega, hv, ?_⟩
          rw [if_pos rfl]; simp [optVal, hv_true0]
    | succ k ih =>
      intro hk
      obtain ⟨extra0, adj, hlen0_ex, hm0, hb0, hnc_cur, htc_cur, hv0, hsem⟩ := ih (by omega)
      let gs := gs0 ++ extra0
      have hv_gs : ∀ w u, adj w = some u → u < n + m + gs.length ∧ degG n m gs u = 0 := hv0
      let p : ℕ := gs0.length - (k + 1)
      have hp_lt : p < gs0.length := by omega
      have hp_succ : gs0.length - k = p + 1 := by omega
      have hback_p : ∀ i ∈ gs0[p].inputs, i < n + m + p := by
        intro i hi
        have hb := hback0 p hp_lt i
        unfold gateAt at hb
        rw [List.getD_eq_getElem _ _ hp_lt] at hb
        exact hb hi
      have hfilt_sub : (Tfin.filter fun i => p + 1 ≤ i).card ≤ (Tfin.filter fun i => p ≤ i).card :=
        Finset.card_le_card (fun i hi => by simp only [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, by omega⟩)
      have hfilt_inc : p ∈ Tfin → (Tfin.filter fun i => p + 1 ≤ i).card + 1 = (Tfin.filter fun i => p ≤ i).card := by
        intro hpT
        have hset : Tfin.filter (fun i => p ≤ i) = insert p (Tfin.filter fun i => p + 1 ≤ i) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_insert]; constructor
          · rintro ⟨hiT, hpi⟩
            by_cases h : i = p
            · exact Or.inl h
            · exact Or.inr ⟨hiT, by omega⟩
          · rintro (rfl | ⟨hiT, hpi⟩)
            · exact ⟨hpT, le_rfl⟩
            · exact ⟨hiT, by omega⟩
        rw [hset, Finset.card_insert_of_notMem (by simp)]
      by_cases hdp : degG n m gs0 (n + m + p) = 0
      · refine ⟨extra0, adj, ?_, hm0, hb0, hnc_cur, htc_cur, hv0, ?_⟩
        · rw [hp_succ] at hlen0_ex
          change extra0.length ≤ 2 * (Tfin.filter fun i => p ≤ i).card
          omega
        · intro x j
          obtain ⟨hs0, hsj, hcomp⟩ := hsem x j
          rw [hp_succ] at hs0 hsj hcomp
          refine ⟨fun w hw => hs0 w (by omega), fun w hw => hsj w (by omega), ?_⟩
          intro hv
          rcases hcomp hv with h0 | ⟨w, hw, hdw, hvw, haw⟩
          · exact Or.inl h0
          · have hne : w ≠ n + m + p := by intro h; subst h; omega
            exact Or.inr ⟨w, by omega, hdw, hvw, haw⟩
      · have hpT : p ∈ Tfin := by
          simp only [Tfin, Finset.mem_filter, Finset.mem_range]
          exact ⟨hp_lt, by omega⟩
        have hinc := hfilt_inc hpT
        have add1 : ∀ (gs1 : List Gate) (adj1 : ℕ → Option ℕ) (w1 : ℕ) (r1 : Option ℕ),
            Monotone2 ⟨gs1, 0⟩ → ReadsBack (n + m) ⟨gs1, 0⟩ → NoCross n m gs1 →
            (∀ w u, adj1 w = some u → u < n + m + gs1.length ∧ degG n m gs1 u = 0) →
            (∀ u, r1 = some u → u < n + m + gs1.length ∧ degG n m gs1 u = 0) →
            ∃ gs2 : List Gate, ∃ adj2 : ℕ → Option ℕ,
              (∃ ex, gs2 = gs1 ++ ex ∧ ex.length ≤ 1) ∧
              Monotone2 ⟨gs2, 0⟩ ∧ ReadsBack (n + m) ⟨gs2, 0⟩ ∧ NoCross n m gs2 ∧
              tCount n m gs2 = tCount n m gs1 ∧
              (∀ w u, adj2 w = some u → u < n + m + gs2.length ∧ degG n m gs2 u = 0) ∧
              (∀ (z : Fin (n + m) → Bool) (w : ℕ),
                optVal gs2 z (adj2 w) = if w = w1 then (optVal gs1 z (adj1 w1) || optVal gs1 z r1) else optVal gs1 z (adj1 w)) := by
          intro gs1 adj1 w1 r1 hm1 hb1 hnc1 hva1 hvr1
          let res := orOpt (n + m) gs1 (adj1 w1) r1
          obtain ⟨⟨ex, hex, hexlen⟩, hm2, hb2, hnc2, htc2, hv2, hval2⟩ :=
            orOpt_deg_spec n m gs1 (adj1 w1) r1 hm1 hb1 hnc1 (hva1 w1) hvr1
          refine ⟨res.1, fun w => if w = w1 then res.2 else adj1 w, ⟨ex, hex, hexlen⟩, hm2, hb2, hnc2, htc2, ?_, ?_⟩
          · intro w u hu
            dsimp only at hu
            by_cases hww : w = w1
            · rw [if_pos hww] at hu; exact hv2 u hu
            · rw [if_neg hww] at hu
              obtain ⟨hult, hdu⟩ := hva1 w u hu
              refine ⟨by rw [hex, List.length_append]; omega, ?_⟩
              rw [hex, degG_prefix n m gs1 ex u hult]; exact hdu
          · intro z w
            dsimp only
            by_cases hww : w = w1
            · subst w; rw [if_pos rfl, if_pos rfl]; exact hval2 z
            · rw [if_neg hww, if_neg hww]
              cases h : adj1 w with
              | none => rfl
              | some u =>
                simp only [optVal]; rw [hex]
                exact val_prefix gs1 ex u z (hva1 w u h).1
        have hlen_p : gs0[p].inputs.length ≤ 2 := (hleg0 gs0[p] (List.getElem_mem hp_lt)).2
        have hstep_done : ∃ gs' : List Gate, ∃ adj' : ℕ → Option ℕ,
            (∃ ex, gs' = gs ++ ex ∧ ex.length ≤ 2) ∧
            Monotone2 ⟨gs', 0⟩ ∧ ReadsBack (n + m) ⟨gs', 0⟩ ∧ NoCross n m gs' ∧
            tCount n m gs' = tCount n m gs ∧
            (∀ w u, adj' w = some u → u < n + m + gs'.length ∧ degG n m gs' u = 0) ∧
            (∀ (x : Fin n → Bool) (j : Fin m),
              let x0 := Fin.append x (fun _ : Fin m => false)
              let xj := Fin.append x (fun l => decide (l = j))
              (∀ w < n + m + p, val gs0 w x0 = true → optVal gs' x0 (adj' w) = true → val gs0 target x0 = true) ∧
              (∀ w < n + m + p, val gs0 w xj = true → optVal gs' x0 (adj' w) = true → val gs0 target xj = true) ∧
              (val gs0 target xj = true → val gs0 target x0 = true ∨
                ∃ w < n + m + p, 0 < degG n m gs0 w ∧ val gs0 w xj = true ∧ optVal gs' x0 (adj' w) = true)) := by
          rcases (hleg0 gs0[p] (List.getElem_mem hp_lt)).1 with hop_and | hop_or
          · match hin : gs0[p].inputs with
            | [] =>
              have hdg := deg_gate_eq n m ⟨gs0, 0⟩ p hp_lt hback_p
              change degG n m gs0 (n + m + p) = _ at hdg
              dsimp only at hdg
              rw [if_pos hop_and, hin] at hdg; simp at hdg; exact absurd hdg hdp
            | [a] =>
              have halt : a < n + m + p := hback_p a (by rw [hin]; simp)
              obtain ⟨gs1, adj1, ⟨ex1, hex1, hex1len⟩, hm1, hb1, hnc1, htc1, hv1, hval1⟩ :=
                add1 gs adj a (adj (n + m + p)) hm0 hb0 hnc_cur hv_gs (hv_gs (n + m + p))
              refine ⟨gs1, adj1, ⟨ex1, hex1, by omega⟩, hm1, hb1, hnc1, htc1, hv1, ?_⟩
              intro x j
              obtain ⟨hs0, hsj, hcomp⟩ := hsem x j
              rw [hp_succ] at hs0 hsj hcomp
              have hval_p : ∀ z : Fin (n + m) → Bool, val gs0 (n + m + p) z = true ↔ val gs0 a z = true := by
                intro z; rw [val_and gs0 z p hp_lt hop_and, hin]; simp [halt]
              refine ⟨?_, ?_, ?_⟩
              · intro w hw hvw haw
                rw [hval1 _ w] at haw
                by_cases hwa : w = a
                · subst w; rw [if_pos rfl, Bool.or_eq_true] at haw
                  rcases haw with h1 | h2
                  · exact hs0 a (by omega) hvw h1
                  · exact hs0 (n + m + p) (by omega) ((hval_p _).mpr hvw) h2
                · rw [if_neg hwa] at haw; exact hs0 w (by omega) hvw haw
              · intro w hw hvw haw
                rw [hval1 _ w] at haw
                by_cases hwa : w = a
                · subst w; rw [if_pos rfl, Bool.or_eq_true] at haw
                  rcases haw with h1 | h2
                  · exact hsj a (by omega) hvw h1
                  · exact hsj (n + m + p) (by omega) ((hval_p _).mpr hvw) h2
                · rw [if_neg hwa] at haw; exact hsj w (by omega) hvw haw
              · intro hv
                rcases hcomp hv with h0 | ⟨w, hw, hdw, hvw, haw⟩
                · exact Or.inl h0
                · by_cases hwp : w = n + m + p
                  · subst hwp
                    have hva : val gs0 a (Fin.append x (fun l => decide (l = j))) = true := (hval_p _).mp hvw
                    by_cases hda : degG n m gs0 a = 0
                    · have hva0 : val gs0 a (Fin.append x (fun _ : Fin m => false)) = true := by
                        rw [← deg_zero_indep n m ⟨gs0, 0⟩ hmono0 hback0 x (fun l => decide (l = j)) a (by dsimp; omega) hda]; exact hva
                      exact Or.inl (hs0 (n + m + p) (by omega) ((hval_p _).mpr hva0) haw)
                    · refine Or.inr ⟨a, halt, by omega, hva, ?_⟩
                      rw [hval1 _ a, if_pos rfl, haw, Bool.or_true]
                  · refine Or.inr ⟨w, by omega, hdw, hvw, ?_⟩
                    rw [hval1 _ w]
                    by_cases hwa : w = a
                    · rw [if_pos hwa, ← hwa, haw, Bool.true_or]
                    · rw [if_neg hwa]; exact haw
            | [a, b] =>
              have halt : a < n + m + p := hback_p a (by rw [hin]; simp)
              have hblt : b < n + m + p := hback_p b (by rw [hin]; simp)
              have hnc_ab : degG n m gs0 a = 0 ∨ degG n m gs0 b = 0 := by
                obtain ⟨i, hi, hdi⟩ := hnc0 p hp_lt hop_and (by rw [hin]; rfl)
                rw [hin] at hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl
                · exact Or.inl hdi
                · exact Or.inr hdi
              have handle_and : ∀ (c d : ℕ), c < n + m + p → d < n + m + p → degG n m gs0 c = 0 →
                  (∀ z : Fin (n + m) → Bool, val gs0 (n + m + p) z = true ↔ val gs0 c z = true ∧ val gs0 d z = true) →
                  ∃ gs' : List Gate, ∃ adj' : ℕ → Option ℕ,
                    (∃ ex, gs' = gs ++ ex ∧ ex.length ≤ 2) ∧
                    Monotone2 ⟨gs', 0⟩ ∧ ReadsBack (n + m) ⟨gs', 0⟩ ∧ NoCross n m gs' ∧
                    tCount n m gs' = tCount n m gs ∧
                    (∀ w u, adj' w = some u → u < n + m + gs'.length ∧ degG n m gs' u = 0) ∧
                    (∀ (x : Fin n → Bool) (j : Fin m),
                      let x0 := Fin.append x (fun _ : Fin m => false)
                      let xj := Fin.append x (fun l => decide (l = j))
                      (∀ w < n + m + p, val gs0 w x0 = true → optVal gs' x0 (adj' w) = true → val gs0 target x0 = true) ∧
                      (∀ w < n + m + p, val gs0 w xj = true → optVal gs' x0 (adj' w) = true → val gs0 target xj = true) ∧
                      (val gs0 target xj = true → val gs0 target x0 = true ∨
                        ∃ w < n + m + p, 0 < degG n m gs0 w ∧ val gs0 w xj = true ∧ optVal gs' x0 (adj' w) = true)) := by
                intro c d hclt hdlt hdc hval_cd
                have hc_gs : c < n + m + gs.length := by simp [gs]; omega
                have hdc_gs : degG n m gs c = 0 := by
                  simp only [gs]; rw [degG_prefix n m gs0 extra0 c (by omega)]; exact hdc
                let r1 := andWireOpt (n + m) gs (adj (n + m + p)) c
                obtain ⟨⟨ex1, hex1, hex1len⟩, hm1, hb1, hnc1, htc1, hv1, hval1⟩ :=
                  andWireOpt_deg_spec n m gs (adj (n + m + p)) c hm0 hb0 hnc_cur (hv_gs (n + m + p)) hc_gs hdc_gs
                have hv_adj1 : ∀ w u, adj w = some u → u < n + m + r1.1.length ∧ degG n m r1.1 u = 0 := by
                  intro w u hu
                  obtain ⟨hult, hdu⟩ := hv_gs w u hu
                  exact ⟨by rw [hex1, List.length_append]; omega, by rw [hex1, degG_prefix n m gs ex1 u hult]; exact hdu⟩
                obtain ⟨gs2, adj2, ⟨ex2, hex2, hex2len⟩, hm2, hb2, hnc2, htc2, hv2, hval2⟩ :=
                  add1 r1.1 adj d r1.2 hm1 hb1 hnc1 hv_adj1 hv1
                refine ⟨gs2, adj2, ⟨ex1 ++ ex2, by rw [hex2, hex1, List.append_assoc], by simp; omega⟩,
                  hm2, hb2, hnc2, htc2.trans htc1, hv2, ?_⟩
                intro x j
                obtain ⟨hs0, hsj, hcomp⟩ := hsem x j
                rw [hp_succ] at hs0 hsj hcomp
                have hopt_keep : ∀ w, optVal r1.1 (Fin.append x (fun _ : Fin m => false)) (adj w) =
                    optVal gs (Fin.append x (fun _ : Fin m => false)) (adj w) := by
                  intro w
                  cases h : adj w with
                  | none => rfl
                  | some u =>
                    simp only [optVal]; rw [hex1]
                    exact val_prefix gs ex1 u _ (hv_gs w u h).1
                have hvc0 : val gs c (Fin.append x (fun _ : Fin m => false)) =
                    val gs0 c (Fin.append x (fun _ : Fin m => false)) :=
                  val_prefix gs0 extra0 c _ (by omega)
                have hvcj : val gs0 c (Fin.append x (fun l => decide (l = j))) =
                    val gs0 c (Fin.append x (fun _ : Fin m => false)) :=
                  deg_zero_indep n m ⟨gs0, 0⟩ hmono0 hback0 x (fun l => decide (l = j)) c (by dsimp; omega) hdc
                refine ⟨?_, ?_, ?_⟩
                · intro w hw hvw haw
                  rw [hval2 _ w] at haw
                  by_cases hwd : w = d
                  · subst w; rw [if_pos rfl, hopt_keep d, hval1 _, hvc0, Bool.or_eq_true, Bool.and_eq_true] at haw
                    rcases haw with h1 | ⟨h2, h3⟩
                    · exact hs0 d (by omega) hvw h1
                    · exact hs0 (n + m + p) (by omega) ((hval_cd _).mpr ⟨h3, hvw⟩) h2
                  · rw [if_neg hwd, hopt_keep w] at haw; exact hs0 w (by omega) hvw haw
                · intro w hw hvw haw
                  rw [hval2 _ w] at haw
                  by_cases hwd : w = d
                  · subst w; rw [if_pos rfl, hopt_keep d, hval1 _, hvc0, Bool.or_eq_true, Bool.and_eq_true] at haw
                    rcases haw with h1 | ⟨h2, h3⟩
                    · exact hsj d (by omega) hvw h1
                    · exact hsj (n + m + p) (by omega) ((hval_cd _).mpr ⟨hvcj.symm ▸ h3, hvw⟩) h2
                  · rw [if_neg hwd, hopt_keep w] at haw; exact hsj w (by omega) hvw haw
                · intro hv
                  rcases hcomp hv with h0 | ⟨w, hw, hdw, hvw, haw⟩
                  · exact Or.inl h0
                  · by_cases hwp : w = n + m + p
                    · subst hwp
                      obtain ⟨hvc, hvd⟩ := (hval_cd _).mp hvw
                      have hvc0_tr : val gs0 c (Fin.append x (fun _ : Fin m => false)) = true := hvcj.symm.trans hvc
                      by_cases hdd : degG n m gs0 d = 0
                      · have hvd0 : val gs0 d (Fin.append x (fun _ : Fin m => false)) = true := by
                          rw [← deg_zero_indep n m ⟨gs0, 0⟩ hmono0 hback0 x (fun l => decide (l = j)) d (by dsimp; omega) hdd]; exact hvd
                        exact Or.inl (hs0 (n + m + p) (by omega) ((hval_cd _).mpr ⟨hvc0_tr, hvd0⟩) haw)
                      · refine Or.inr ⟨d, hdlt, by omega, hvd, ?_⟩
                        rw [hval2 _ d, if_pos rfl, hval1 _, hvc0, haw, hvc0_tr]; simp
                    · refine Or.inr ⟨w, by omega, hdw, hvw, ?_⟩
                      rw [hval2 _ w]
                      by_cases hwd : w = d
                      · subst w; rw [if_pos rfl, hopt_keep d, haw, Bool.true_or]
                      · rw [if_neg hwd, hopt_keep w]; exact haw
              rcases hnc_ab with hda | hdb
              · exact handle_and a b halt hblt hda (fun z => by
                  rw [val_and gs0 z p hp_lt hop_and, hin]; simp [halt, hblt])
              · exact handle_and b a hblt halt hdb (fun z => by
                  rw [val_and gs0 z p hp_lt hop_and, hin]; simp [halt, hblt, and_comm])
            | _ :: _ :: _ :: _ => rw [hin] at hlen_p; simp at hlen_p
          · match hin : gs0[p].inputs with
            | [] =>
              have hdg := deg_gate_eq n m ⟨gs0, 0⟩ p hp_lt hback_p
              change degG n m gs0 (n + m + p) = _ at hdg
              dsimp only at hdg
              have hne_and : gs0[p].op ≠ GateOp.and := by rw [hop_or]; intro h; cases h
              rw [if_neg hne_and, hin] at hdg; simp at hdg; exact absurd hdg hdp
            | [a] =>
              have halt : a < n + m + p := hback_p a (by rw [hin]; simp)
              obtain ⟨gs1, adj1, ⟨ex1, hex1, hex1len⟩, hm1, hb1, hnc1, htc1, hv1, hval1⟩ :=
                add1 gs adj a (adj (n + m + p)) hm0 hb0 hnc_cur hv_gs (hv_gs (n + m + p))
              refine ⟨gs1, adj1, ⟨ex1, hex1, by omega⟩, hm1, hb1, hnc1, htc1, hv1, ?_⟩
              intro x j
              obtain ⟨hs0, hsj, hcomp⟩ := hsem x j
              rw [hp_succ] at hs0 hsj hcomp
              have hval_p : ∀ z : Fin (n + m) → Bool, val gs0 (n + m + p) z = true ↔ val gs0 a z = true := by
                intro z; rw [val_or gs0 z p hp_lt hop_or, hin]; simp [halt]
              refine ⟨?_, ?_, ?_⟩
              · intro w hw hvw haw
                rw [hval1 _ w] at haw
                by_cases hwa : w = a
                · subst w; rw [if_pos rfl, Bool.or_eq_true] at haw
                  rcases haw with h1 | h2
                  · exact hs0 a (by omega) hvw h1
                  · exact hs0 (n + m + p) (by omega) ((hval_p _).mpr hvw) h2
                · rw [if_neg hwa] at haw; exact hs0 w (by omega) hvw haw
              · intro w hw hvw haw
                rw [hval1 _ w] at haw
                by_cases hwa : w = a
                · subst w; rw [if_pos rfl, Bool.or_eq_true] at haw
                  rcases haw with h1 | h2
                  · exact hsj a (by omega) hvw h1
                  · exact hsj (n + m + p) (by omega) ((hval_p _).mpr hvw) h2
                · rw [if_neg hwa] at haw; exact hsj w (by omega) hvw haw
              · intro hv
                rcases hcomp hv with h0 | ⟨w, hw, hdw, hvw, haw⟩
                · exact Or.inl h0
                · by_cases hwp : w = n + m + p
                  · subst hwp
                    have hva : val gs0 a (Fin.append x (fun l => decide (l = j))) = true := (hval_p _).mp hvw
                    by_cases hda : degG n m gs0 a = 0
                    · have hva0 : val gs0 a (Fin.append x (fun _ : Fin m => false)) = true := by
                        rw [← deg_zero_indep n m ⟨gs0, 0⟩ hmono0 hback0 x (fun l => decide (l = j)) a (by dsimp; omega) hda]; exact hva
                      exact Or.inl (hs0 (n + m + p) (by omega) ((hval_p _).mpr hva0) haw)
                    · refine Or.inr ⟨a, halt, by omega, hva, ?_⟩
                      rw [hval1 _ a, if_pos rfl, haw, Bool.or_true]
                  · refine Or.inr ⟨w, by omega, hdw, hvw, ?_⟩
                    rw [hval1 _ w]
                    by_cases hwa : w = a
                    · rw [if_pos hwa, ← hwa, haw, Bool.true_or]
                    · rw [if_neg hwa]; exact haw
            | [a, b] =>
              have halt : a < n + m + p := hback_p a (by rw [hin]; simp)
              have hblt : b < n + m + p := hback_p b (by rw [hin]; simp)
              let r := adj (n + m + p)
              obtain ⟨gs1, adj1, ⟨ex1, hex1, hex1len⟩, hm1, hb1, hnc1, htc1, hv1, hval1⟩ :=
                add1 gs adj a r hm0 hb0 hnc_cur hv_gs (hv_gs (n + m + p))
              have hr1 : ∀ u, r = some u → u < n + m + gs1.length ∧ degG n m gs1 u = 0 := by
                intro u hu
                obtain ⟨hult, hdu⟩ := hv_gs (n + m + p) u hu
                exact ⟨by rw [hex1, List.length_append]; omega, by rw [hex1, degG_prefix n m gs ex1 u hult]; exact hdu⟩
              obtain ⟨gs2, adj2, ⟨ex2, hex2, hex2len⟩, hm2, hb2, hnc2, htc2, hv2, hval2⟩ :=
                add1 gs1 adj1 b r hm1 hb1 hnc1 hv1 hr1
              refine ⟨gs2, adj2, ⟨ex1 ++ ex2, by rw [hex2, hex1, List.append_assoc], by simp; omega⟩,
                hm2, hb2, hnc2, htc2.trans htc1, hv2, ?_⟩
              intro x j
              obtain ⟨hs0, hsj, hcomp⟩ := hsem x j
              rw [hp_succ] at hs0 hsj hcomp
              have hval_p : ∀ z : Fin (n + m) → Bool, val gs0 (n + m + p) z = true ↔ val gs0 a z = true ∨ val gs0 b z = true := by
                intro z; rw [val_or gs0 z p hp_lt hop_or, hin]; simp [halt, hblt]
              have hr_keep : optVal gs1 (Fin.append x (fun _ : Fin m => false)) r =
                  optVal gs (Fin.append x (fun _ : Fin m => false)) r := by
                cases h : r with
                | none => rfl
                | some u =>
                  simp only [optVal]; rw [hex1]
                  exact val_prefix gs ex1 u _ (hv_gs (n + m + p) u h).1
              have hcomb : ∀ w, optVal gs2 (Fin.append x (fun _ : Fin m => false)) (adj2 w) = true ↔
                  optVal gs (Fin.append x (fun _ : Fin m => false)) (adj w) = true ∨
                  ((w = a ∨ w = b) ∧ optVal gs (Fin.append x (fun _ : Fin m => false)) r = true) := by
                intro w
                rw [hval2 _ w]
                by_cases hwb : w = b
                · subst w; rw [if_pos rfl, hval1 _ b, hr_keep]
                  by_cases hba : b = a
                  · subst hba; rw [if_pos rfl]; simp [Bool.or_eq_true]
                  · rw [if_neg hba]; simp [Bool.or_eq_true]
                · rw [if_neg hwb, hval1 _ w]
                  by_cases hwa : w = a
                  · subst w; rw [if_pos rfl]; simp [Bool.or_eq_true]
                  · rw [if_neg hwa]; simp [hwa, hwb]
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
                    · by_cases hda : degG n m gs0 a = 0
                      · have hva0 : val gs0 a (Fin.append x (fun _ : Fin m => false)) = true := by
                          rw [← deg_zero_indep n m ⟨gs0, 0⟩ hmono0 hback0 x (fun l => decide (l = j)) a (by dsimp; omega) hda]; exact hva
                        exact Or.inl (hs0 (n + m + p) (by omega) ((hval_p _).mpr (Or.inl hva0)) haw)
                      · exact Or.inr ⟨a, halt, by omega, hva, (hcomb a).mpr (Or.inr ⟨Or.inl rfl, haw⟩)⟩
                    · by_cases hdb : degG n m gs0 b = 0
                      · have hvb0 : val gs0 b (Fin.append x (fun _ : Fin m => false)) = true := by
                          rw [← deg_zero_indep n m ⟨gs0, 0⟩ hmono0 hback0 x (fun l => decide (l = j)) b (by dsimp; omega) hdb]; exact hvb
                        exact Or.inl (hs0 (n + m + p) (by omega) ((hval_p _).mpr (Or.inr hvb0)) haw)
                      · exact Or.inr ⟨b, hblt, by omega, hvb, (hcomb b).mpr (Or.inr ⟨Or.inr rfl, haw⟩)⟩
                  · exact Or.inr ⟨w, by omega, hdw, hvw, (hcomb w).mpr (Or.inl haw)⟩
            | _ :: _ :: _ :: _ => rw [hin] at hlen_p; simp at hlen_p
        obtain ⟨gs', adj', ⟨ex', hex', hex'len⟩, hm', hb', hnc', htc', hv', hsem'⟩ := hstep_done
        have hgs'_eq : gs' = gs0 ++ (extra0 ++ ex') := by rw [hex', List.append_assoc]
        rw [hgs'_eq] at hm' hb' hnc' htc' hv' hsem'
        refine ⟨extra0 ++ ex', adj', ?_, hm', hb', hnc', htc'.trans htc_cur, hv', hsem'⟩
        rw [List.length_append]
        rw [hp_succ] at hlen0_ex
        change extra0.length + ex'.length ≤ 2 * (Tfin.filter fun i => p ≤ i).card
        omega
  obtain ⟨extra, adj, hlen_ex, hmF, hbF, hncF, htcF, hvF, hsemF⟩ := hstep gs0.length le_rfl
  refine ⟨extra, adj, ?_, hmF, hbF, hncF, htcF, hvF, ?_⟩
  · have hfilt : Tfin.filter (fun i => gs0.length - gs0.length ≤ i) = Tfin := by ext i; simp
    rw [hfilt] at hlen_ex; exact hlen_ex
  · intro x j
    obtain ⟨_, hsj, hcomp⟩ := hsemF x j
    rw [Nat.sub_self, add_zero] at hsj hcomp
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true]
    constructor
    · intro hv
      rcases hcomp hv with h0 | ⟨w, hw, hdw, hvw, haw⟩
      · exact Or.inl h0
      · have hwn : n ≤ w := by
          by_contra hlt; have := degG_input_left n m gs0 w (by omega); omega
        rw [val_input gs0 _ w hw, fin_append_right x _ w hwn hw, decide_eq_true_eq] at hvw
        have hweq : w = n + j.val := by have := congrArg Fin.val hvw; dsimp at this; omega
        subst hweq
        exact Or.inr haw
    · rintro (h0 | ho)
      · exact val_mono gs0 hleg0 _ _ (fun v hv => by
          by_cases hvn : v.val < n
          · have hv' : v = ⟨v.val, v.isLt⟩ := rfl
            rw [hv', fin_append_left _ _ v.val hvn] at hv ⊢; exact hv
          · have hv' : v = ⟨v.val, v.isLt⟩ := rfl
            rw [hv', fin_append_right _ _ v.val (by omega) v.isLt] at hv; simp at hv) target h0
      · have hvnj : val gs0 (n + j.val) (Fin.append x (fun l => decide (l = j))) = true := by
          rw [val_input gs0 _ (n + j.val) (by omega), fin_append_right x _ (n + j.val) (by omega) (by omega)]
          simp
        exact hsj (n + j.val) (by omega) hvnj ho

theorem crossCombine (n m : ℕ) (E3 rest3 : List Gate)
    (hpre3 : E3 = [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ rest3)
    (hm3 : Monotone2 ⟨E3, 0⟩) (hb3 : ReadsBack (n + m) ⟨E3, 0⟩) (hnc3 : NoCross n m E3)
    (a0 b0 wBase : ℕ)
    (ha0 : a0 < n + m + E3.length) (hda0 : degG n m E3 a0 = 0)
    (hb0 : b0 < n + m + E3.length) (hdb0 : degG n m E3 b0 = 0)
    (hwB : wBase < n + m + E3.length) (hdwB : degG n m E3 wBase = 0)
    (adjA adjB : ℕ → Option ℕ)
    (hvA : ∀ w u, adjA w = some u → u < n + m + E3.length ∧ degG n m E3 u = 0)
    (hvB : ∀ w u, adjB w = some u → u < n + m + E3.length ∧ degG n m E3 u = 0) :
    ∀ r ≤ m, ∃ (ex : List Gate) (acc : ℕ),
      ex.length = 5 * r ∧
      Monotone2 ⟨E3 ++ ex, 0⟩ ∧
      ReadsBack (n + m) ⟨E3 ++ ex, 0⟩ ∧
      NoCross n m (E3 ++ ex) ∧
      tCount n m (E3 ++ ex) ≤ tCount n m E3 + 2 * r ∧
      acc < n + m + (E3 ++ ex).length ∧
      (∀ x : Fin n → Bool,
        let x0 := Fin.append x (fun _ : Fin m => false)
        val (E3 ++ ex) acc x0 = val E3 wBase x0 ∧
        ∀ j : Fin m,
          val (E3 ++ ex) acc (Fin.append x (fun l => decide (l = j))) =
            (val E3 wBase x0 ||
              if j.val < r then
                ((val E3 a0 x0 || optVal E3 x0 (adjA (n + j.val))) &&
                 (val E3 b0 x0 || optVal E3 x0 (adjB (n + j.val))))
              else false)) := by
  obtain ⟨hlen3, hd_false3, _, hv_false3, _⟩ := base_consts_eval n m E3 rest3 hpre3
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨[], wBase, by simp, by simpa using hm3, by simpa using hb3, by simpa using hnc3, by simp,
      by simpa using hwB, ?_⟩
    intro x
    refine ⟨by simp, fun j => ?_⟩
    simp only [List.append_nil, Nat.not_lt_zero, ite_false, Bool.or_false]
    exact deg_zero_indep n m ⟨E3, 0⟩ hm3 hb3 x (fun l => decide (l = j)) wBase hwB hdwB
  | succ r ih =>
    intro hrm
    obtain ⟨ex, acc, hexlen, hmr, hbr, hncr, htcr, hacc, hsemr⟩ := ih (by omega)
    let Er := E3 ++ ex
    have hEr_len : Er.length = E3.length + 5 * r := by simp [Er, hexlen]
    have htc_er : tCount n m Er ≤ tCount n m E3 + 2 * r := htcr
    have hacc_er : acc < n + m + Er.length := hacc
    let uA : ℕ := (adjA (n + r)).getD (n + m)
    let uB : ℕ := (adjB (n + r)).getD (n + m)
    have huA_lt : uA < n + m + E3.length := by
      dsimp only [uA]; cases h : adjA (n + r) with
      | none => simp; omega
      | some u => simp [(hvA (n + r) u h).1]
    have huA_deg : degG n m E3 uA = 0 := by
      dsimp only [uA]; cases h : adjA (n + r) with
      | none => simpa using hd_false3
      | some u => simpa using (hvA (n + r) u h).2
    have huA_val : ∀ z : Fin (n + m) → Bool, val E3 uA z = optVal E3 z (adjA (n + r)) := by
      intro z; dsimp only [uA]; cases h : adjA (n + r) with
      | none => simpa [optVal] using hv_false3 z
      | some u => rfl
    have huB_lt : uB < n + m + E3.length := by
      dsimp only [uB]; cases h : adjB (n + r) with
      | none => simp; omega
      | some u => simp [(hvB (n + r) u h).1]
    have huB_deg : degG n m E3 uB = 0 := by
      dsimp only [uB]; cases h : adjB (n + r) with
      | none => simpa using hd_false3
      | some u => simpa using (hvB (n + r) u h).2
    have huB_val : ∀ z : Fin (n + m) → Bool, val E3 uB z = optVal E3 z (adjB (n + r)) := by
      intro z; dsimp only [uB]; cases h : adjB (n + r) with
      | none => simpa [optVal] using hv_false3 z
      | some u => rfl
    let wAl := n + m + Er.length
    let g1 : Gate := ⟨GateOp.or, [a0, uA]⟩
    let E_1 := Er ++ [g1]
    have ha0_r : a0 < n + m + Er.length := by omega
    have huA_r : uA < n + m + Er.length := by omega
    have hda0_r : degG n m Er a0 = 0 := by rw [degG_prefix n m E3 ex a0 ha0]; exact hda0
    have hduA_r : degG n m Er uA = 0 := by rw [degG_prefix n m E3 ex uA huA_lt]; exact huA_deg
    have hg1_bk : ∀ i ∈ g1.inputs, i < n + m + Er.length := by
      intro i hi; simp [g1] at hi; rcases hi with rfl | rfl <;> assumption
    have hg1_dg : ∀ i ∈ g1.inputs, degG n m Er i = 0 := by
      intro i hi; simp [g1] at hi; rcases hi with rfl | rfl <;> assumption
    have hok1 := append_gate_ok (n + m) Er g1 hmr hbr ⟨Or.inr rfl, by simp [g1]⟩ hg1_bk
    have hnc1 : NoCross n m E_1 := NoCross_snoc n m Er g1 hncr hbr hg1_bk (fun h => by simp [g1] at h)
    have hdwAl : degG n m E_1 wAl = 0 := degG_append_zero n m Er g1 hg1_bk hg1_dg
    have htc1 : tCount n m E_1 = tCount n m Er := tCount_snoc_zero n m Er g1 hdwAl
    let wBl := n + m + E_1.length
    let g2 : Gate := ⟨GateOp.or, [b0, uB]⟩
    let E_2 := E_1 ++ [g2]
    have hb0_1 : b0 < n + m + E_1.length := by simp [E_1]; omega
    have huB_1 : uB < n + m + E_1.length := by simp [E_1]; omega
    have hdb0_1 : degG n m E_1 b0 = 0 := by
      have hpre1 : E_1 = E3 ++ (ex ++ [g1]) := by simp [E_1, Er, List.append_assoc]
      rw [hpre1, degG_prefix n m E3 (ex ++ [g1]) b0 hb0]; exact hdb0
    have hduB_1 : degG n m E_1 uB = 0 := by
      have hpre1 : E_1 = E3 ++ (ex ++ [g1]) := by simp [E_1, Er, List.append_assoc]
      rw [hpre1, degG_prefix n m E3 (ex ++ [g1]) uB huB_lt]; exact huB_deg
    have hg2_bk : ∀ i ∈ g2.inputs, i < n + m + E_1.length := by
      intro i hi; simp [g2] at hi; rcases hi with rfl | rfl <;> assumption
    have hg2_dg : ∀ i ∈ g2.inputs, degG n m E_1 i = 0 := by
      intro i hi; simp [g2] at hi; rcases hi with rfl | rfl <;> assumption
    have hok2 := append_gate_ok (n + m) E_1 g2 hok1.1 hok1.2 ⟨Or.inr rfl, by simp [g2]⟩ hg2_bk
    have hnc2 : NoCross n m E_2 := NoCross_snoc n m E_1 g2 hnc1 hok1.2 hg2_bk (fun h => by simp [g2] at h)
    have hdwBl : degG n m E_2 wBl = 0 := degG_append_zero n m E_1 g2 hg2_bk hg2_dg
    have htc2 : tCount n m E_2 = tCount n m E_1 := tCount_snoc_zero n m E_1 g2 hdwBl
    let wPr := n + m + E_2.length
    let g3 : Gate := ⟨GateOp.and, [wAl, wBl]⟩
    let E_3 := E_2 ++ [g3]
    have hwAl_2 : wAl < n + m + E_2.length := by simp [E_2, E_1, wAl]
    have hwBl_2 : wBl < n + m + E_2.length := by simp [E_2, wBl]
    have hdwAl_2 : degG n m E_2 wAl = 0 := by
      rw [degG_prefix n m E_1 [g2] wAl (by simp [E_1, wAl])]; exact hdwAl
    have hg3_bk : ∀ i ∈ g3.inputs, i < n + m + E_2.length := by
      intro i hi; simp [g3] at hi; rcases hi with rfl | rfl <;> assumption
    have hg3_dg : ∀ i ∈ g3.inputs, degG n m E_2 i = 0 := by
      intro i hi; simp [g3] at hi; rcases hi with rfl | rfl <;> assumption
    have hok3 := append_gate_ok (n + m) E_2 g3 hok2.1 hok2.2 ⟨Or.inl rfl, by simp [g3]⟩ hg3_bk
    have hnc3' : NoCross n m E_3 := NoCross_snoc n m E_2 g3 hnc2 hok2.2 hg3_bk (fun _ _ => ⟨wAl, by simp [g3], hdwAl_2⟩)
    have hdwPr : degG n m E_3 wPr = 0 := degG_append_zero n m E_2 g3 hg3_bk hg3_dg
    have htc3 : tCount n m E_3 = tCount n m E_2 := tCount_snoc_zero n m E_2 g3 hdwPr
    let wTm := n + m + E_3.length
    let g4 : Gate := ⟨GateOp.and, [wPr, n + r]⟩
    let E_4 := E_3 ++ [g4]
    have hwPr_3 : wPr < n + m + E_3.length := by simp [E_3, wPr]
    have hnr_3 : n + r < n + m + E_3.length := by omega
    have hg4_bk : ∀ i ∈ g4.inputs, i < n + m + E_3.length := by
      intro i hi; simp [g4] at hi; rcases hi with rfl | rfl <;> assumption
    have hok4 := append_gate_ok (n + m) E_3 g4 hok3.1 hok3.2 ⟨Or.inl rfl, by simp [g4]⟩ hg4_bk
    have hnc4 : NoCross n m E_4 := NoCross_snoc n m E_3 g4 hnc3' hok3.2 hg4_bk (fun _ _ => ⟨wPr, by simp [g4], hdwPr⟩)
    have htc4 : tCount n m E_4 ≤ tCount n m E_3 + 1 := tCount_snoc_le n m E_3 g4
    let wAc := n + m + E_4.length
    let g5 : Gate := ⟨GateOp.or, [acc, wTm]⟩
    let E_5 := E_4 ++ [g5]
    have hacc_4 : acc < n + m + E_4.length := by simp [E_4, E_3, E_2, E_1]; omega
    have hwTm_4 : wTm < n + m + E_4.length := by simp [E_4, wTm]
    have hg5_bk : ∀ i ∈ g5.inputs, i < n + m + E_4.length := by
      intro i hi; simp [g5] at hi; rcases hi with rfl | rfl <;> assumption
    have hok5 := append_gate_ok (n + m) E_4 g5 hok4.1 hok4.2 ⟨Or.inr rfl, by simp [g5]⟩ hg5_bk
    have hnc5 : NoCross n m E_5 := NoCross_snoc n m E_4 g5 hnc4 hok4.2 hg5_bk (fun h => by simp [g5] at h)
    have htc5 : tCount n m E_5 ≤ tCount n m E_4 + 1 := tCount_snoc_le n m E_4 g5
    have hE5_eq : E_5 = E3 ++ (ex ++ [g1, g2, g3, g4, g5]) := by
      simp [E_5, E_4, E_3, E_2, E_1, Er, List.append_assoc]
    have hE5_val_g1 : ∀ z : Fin (n + m) → Bool, val E_1 wAl z = (val E3 a0 z || val E3 uA z) := by
      intro z
      apply Bool.eq_iff_iff.mpr
      have hk : Er.length < E_1.length := by simp [E_1]
      have hget : E_1[Er.length] = g1 := by simp [E_1]
      rw [val_or E_1 z Er.length hk (by rw [hget]), hget]
      have hpa : val E_1 a0 z = val E3 a0 z := by
        have hp : E_1 = E3 ++ (ex ++ [g1]) := by simp [E_1, Er, List.append_assoc]
        rw [hp]; exact val_prefix E3 (ex ++ [g1]) a0 z ha0
      have hpu : val E_1 uA z = val E3 uA z := by
        have hp : E_1 = E3 ++ (ex ++ [g1]) := by simp [E_1, Er, List.append_assoc]
        rw [hp]; exact val_prefix E3 (ex ++ [g1]) uA z huA_lt
      simp only [g1, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true]
      constructor
      · rintro ⟨i, rfl | rfl, _, hvi⟩
        · exact Or.inl (hpa ▸ hvi)
        · exact Or.inr (hpu ▸ hvi)
      · rintro (h | h)
        · exact ⟨a0, Or.inl rfl, ha0_r, hpa.symm ▸ h⟩
        · exact ⟨uA, Or.inr rfl, huA_r, hpu.symm ▸ h⟩
    have hE5_val_g2 : ∀ z : Fin (n + m) → Bool, val E_2 wBl z = (val E3 b0 z || val E3 uB z) := by
      intro z
      apply Bool.eq_iff_iff.mpr
      have hk : E_1.length < E_2.length := by simp [E_2]
      have hget : E_2[E_1.length] = g2 := by simp [E_2]
      rw [val_or E_2 z E_1.length hk (by rw [hget]), hget]
      have hpb : val E_2 b0 z = val E3 b0 z := by
        have hp : E_2 = E3 ++ (ex ++ [g1, g2]) := by simp [E_2, E_1, Er, List.append_assoc]
        rw [hp]; exact val_prefix E3 (ex ++ [g1, g2]) b0 z hb0
      have hpu : val E_2 uB z = val E3 uB z := by
        have hp : E_2 = E3 ++ (ex ++ [g1, g2]) := by simp [E_2, E_1, Er, List.append_assoc]
        rw [hp]; exact val_prefix E3 (ex ++ [g1, g2]) uB z huB_lt
      simp only [g2, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true]
      constructor
      · rintro ⟨i, rfl | rfl, _, hvi⟩
        · exact Or.inl (hpb ▸ hvi)
        · exact Or.inr (hpu ▸ hvi)
      · rintro (h | h)
        · exact ⟨b0, Or.inl rfl, hb0_1, hpb.symm ▸ h⟩
        · exact ⟨uB, Or.inr rfl, huB_1, hpu.symm ▸ h⟩
    have hE5_val_g3 : ∀ z : Fin (n + m) → Bool, val E_3 wPr z = ((val E3 a0 z || val E3 uA z) && (val E3 b0 z || val E3 uB z)) := by
      intro z
      apply Bool.eq_iff_iff.mpr
      have hk : E_2.length < E_3.length := by simp [E_3]
      have hget : E_3[E_2.length] = g3 := by simp [E_3]
      rw [val_and E_3 z E_2.length hk (by rw [hget]), hget]
      have hp1 : val E_3 wAl z = val E_1 wAl z := by
        have hp : E_3 = E_1 ++ [g2, g3] := by simp [E_3, E_2, List.append_assoc]
        rw [hp]; exact val_prefix E_1 [g2, g3] wAl z (by simp [E_1, wAl])
      have hp2 : val E_3 wBl z = val E_2 wBl z :=
        val_prefix E_2 [g3] wBl z hwBl_2
      simp only [g3, List.mem_cons, List.not_mem_nil, or_false, Bool.and_eq_true]
      constructor
      · intro h
        exact ⟨hE5_val_g1 z ▸ hp1 ▸ (h wAl (Or.inl rfl)).2, hE5_val_g2 z ▸ hp2 ▸ (h wBl (Or.inr rfl)).2⟩
      · rintro ⟨h1, h2⟩ i (rfl | rfl)
        · exact ⟨hwAl_2, by rw [hp1, hE5_val_g1 z]; exact h1⟩
        · exact ⟨hwBl_2, by rw [hp2, hE5_val_g2 z]; exact h2⟩
    have hE5_val_g4 : ∀ z : Fin (n + m) → Bool, val E_4 wTm z = (val E_3 wPr z && z ⟨n + r, by omega⟩) := by
      intro z
      apply Bool.eq_iff_iff.mpr
      have hk : E_3.length < E_4.length := by simp [E_4]
      have hget : E_4[E_3.length] = g4 := by simp [E_4]
      rw [val_and E_4 z E_3.length hk (by rw [hget]), hget]
      have hp3 : val E_4 wPr z = val E_3 wPr z := val_prefix E_3 [g4] wPr z hwPr_3
      have hpnr : val E_4 (n + r) z = z ⟨n + r, by omega⟩ := val_input E_4 z (n + r) (by omega)
      simp only [g4, List.mem_cons, List.not_mem_nil, or_false, Bool.and_eq_true]
      constructor
      · intro h
        exact ⟨hp3 ▸ (h wPr (Or.inl rfl)).2, hpnr ▸ (h (n + r) (Or.inr rfl)).2⟩
      · rintro ⟨h1, h2⟩ i (rfl | rfl)
        · exact ⟨hwPr_3, hp3.symm ▸ h1⟩
        · exact ⟨hnr_3, hpnr.symm ▸ h2⟩
    have hE5_val_g5 : ∀ z : Fin (n + m) → Bool, val E_5 wAc z = (val Er acc z || val E_4 wTm z) := by
      intro z
      apply Bool.eq_iff_iff.mpr
      have hk : E_4.length < E_5.length := by simp [E_5]
      have hget : E_5[E_4.length] = g5 := by simp [E_5]
      rw [val_or E_5 z E_4.length hk (by rw [hget]), hget]
      have hpacc : val E_5 acc z = val Er acc z := by
        have hp : E_5 = Er ++ [g1, g2, g3, g4, g5] := by simp [E_5, E_4, E_3, E_2, E_1, List.append_assoc]
        rw [hp]; exact val_prefix Er [g1, g2, g3, g4, g5] acc z hacc_er
      have hptm : val E_5 wTm z = val E_4 wTm z := val_prefix E_4 [g5] wTm z hwTm_4
      simp only [g5, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true]
      constructor
      · rintro ⟨i, rfl | rfl, _, hvi⟩
        · exact Or.inl (hpacc ▸ hvi)
        · exact Or.inr (hptm ▸ hvi)
      · rintro (h | h)
        · exact ⟨acc, Or.inl rfl, hacc_4, hpacc.symm ▸ h⟩
        · exact ⟨wTm, Or.inr rfl, hwTm_4, hptm.symm ▸ h⟩
    refine ⟨ex ++ [g1, g2, g3, g4, g5], wAc, by simp [hexlen]; omega,
      hE5_eq ▸ hok5.1, hE5_eq ▸ hok5.2, hE5_eq ▸ hnc5, ?_, by rw [← hE5_eq]; simp [E_5, wAc], ?_⟩
    · rw [← hE5_eq]; omega
    · intro x
      rw [← hE5_eq]
      obtain ⟨hacc0, haccj⟩ := hsemr x
      refine ⟨?_, ?_⟩
      · rw [hE5_val_g5, hacc0, hE5_val_g4, fin_append_right x (fun _ : Fin m => false) (n + r) (by omega) (by omega)]
        simp
      · intro j
        rw [hE5_val_g5, haccj j, hE5_val_g4, fin_append_right x _ (n + r) (by omega) (by omega)]
        have hpr_indep : val E_3 wPr (Fin.append x (fun l => decide (l = j))) =
            val E_3 wPr (Fin.append x (fun _ : Fin m => false)) :=
          deg_zero_indep n m ⟨E_3, 0⟩ hok3.1 hok3.2 x (fun l => decide (l = j)) wPr hwPr_3 hdwPr
        rw [hpr_indep, hE5_val_g3, huA_val, huB_val]
        by_cases hjr : j.val < r
        · have hne : (⟨n + r - n, by omega⟩ : Fin m) ≠ j := by
            intro h; have := congrArg Fin.val h; dsimp at this; omega
          have hjr1 : j.val < r + 1 := by omega
          rw [if_pos hjr, if_pos hjr1, decide_eq_false hne, Bool.and_false, Bool.or_false]
        · by_cases hjeq : j.val = r
          · have heq : (⟨n + r - n, by omega⟩ : Fin m) = j := by apply Fin.ext; dsimp; omega
            have hjr1 : j.val < r + 1 := by omega
            rw [if_neg hjr, if_pos hjr1, decide_eq_true heq, Bool.and_true, Bool.or_false, hjeq]
          · have hne : (⟨n + r - n, by omega⟩ : Fin m) ≠ j := by
              intro h; have := congrArg Fin.val h; dsimp at this; omega
            have hjr1 : ¬ j.val < r + 1 := by omega
            rw [if_neg hjr, if_neg hjr1, decide_eq_false hne, Bool.and_false, Bool.or_false]

open Classical in
theorem elimCross (n m : ℕ) (C : Circuit)
    (hmono : Monotone2 C) (hback : ReadsBack (n + m) C) :
    let CrossFin : Finset ℕ := (Finset.range C.gates.length).filter (fun j =>
      (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs.length = 2 ∧
      ∀ i ∈ (gateAt C j).inputs, 0 < deg n m C i)
    ∀ p ≤ C.gates.length,
      let c := (CrossFin.filter fun j => j < p).card
      ∃ (E : List Gate) (mp v0 : ℕ → ℕ),
        (∃ rest, E = [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ rest) ∧
        Monotone2 ⟨E, 0⟩ ∧ ReadsBack (n + m) ⟨E, 0⟩ ∧ NoCross n m E ∧
        tCount n m E ≤ p + 2 * c * m ∧
        E.length ≤ 2 + 2 * p + 4 * c * p + 4 * c ^ 2 * m + c * m + c ∧
        (∀ w < n + m + p,
          mp w < n + m + E.length ∧ v0 w < n + m + E.length ∧
          degG n m E (v0 w) = 0 ∧ (deg n m C w = 0 → degG n m E (mp w) = 0)) ∧
        (∀ w < n + m + p, ∀ x : Fin n → Bool,
          let x0 := Fin.append x (fun _ : Fin m => false)
          val E (v0 w) x0 = val C.gates w x0 ∧
          val E (mp w) x0 = val C.gates w x0 ∧
          ∀ j : Fin m, val E (mp w) (Fin.append x (fun l => decide (l = j))) =
            val C.gates w (Fin.append x (fun l => decide (l = j)))) := by
  intro CrossFin p
  have hlegC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg; obtain ⟨h1, h2⟩ := hmono g hg; exact ⟨by simpa using h1, h2⟩
  induction p with
  | zero =>
    intro _
    let E0 : List Gate := [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩]
    obtain ⟨_, hd_f, hd_t, hv_f, _⟩ := base_consts_eval n m E0 [] rfl
    have hmE0 : Monotone2 ⟨E0, 0⟩ := by
      intro g hg; simp [E0] at hg; rcases hg with rfl | rfl
      · exact ⟨Or.inr rfl, by simp⟩
      · exact ⟨Or.inl rfl, by simp⟩
    have hbE0 : ReadsBack (n + m) ⟨E0, 0⟩ := by
      intro j hj i hi; unfold gateAt at hi; rw [List.getD_eq_getElem _ _ hj] at hi
      match j with
      | 0 => simp [E0] at hi
      | 1 => simp [E0] at hi
      | _ + 2 => simp [E0] at hj
    have hncE0 : NoCross n m E0 := by
      intro j hj hop hlen
      match j with
      | 0 => simp [E0] at hop
      | 1 => simp [E0] at hlen
      | _ + 2 => simp [E0] at hj
    have htcE0 : tCount n m E0 = 0 := by
      unfold tCount
      have hmt : ((Finset.range E0.length).filter (fun q => 0 < degG n m E0 (n + m + q))) = ∅ := by
        ext q; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
        intro hq
        have : q = 0 ∨ q = 1 := by simp [E0] at hq; omega
        rcases this with rfl | rfl
        · rw [add_zero, hd_f]; omega
        · rw [hd_t]; omega
      rw [hmt]; rfl
    refine ⟨E0, id, fun w => if w < n then w else n + m, ⟨[], rfl⟩, hmE0, hbE0, hncE0, by omega, by simp [E0], ?_, ?_⟩
    · intro w hw
      have hwm : w < n + m := by omega
      dsimp only
      refine ⟨by simp [E0]; omega, ?_, ?_, ?_⟩
      · split_ifs <;> simp [E0] <;> omega
      · split_ifs with hwn
        · exact degG_input_left n m E0 w hwn
        · exact hd_f
      · intro hdw
        by_cases hwn : w < n
        · exact degG_input_left n m E0 w hwn
        · have := deg_input_right n m C w (by omega) hwm; omega
    · intro w hw x
      have hwm : w < n + m := by omega
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · split_ifs with hwn
        · rw [val_input E0 _ w hwm, val_input C.gates _ w hwm]
        · rw [hv_f, val_input C.gates _ w hwm, fin_append_right x (fun _ : Fin m => false) w (by omega) hwm]
      · rw [id, val_input E0 _ w hwm, val_input C.gates _ w hwm]
      · intro j; rw [id, val_input E0 _ w hwm, val_input C.gates _ w hwm]
  | succ p ih =>
    intro hp_le
    have hp_lt : p < C.gates.length := hp_le
    obtain ⟨E, mp, v0, ⟨rest, hpreE⟩, hmE, hbE, hncE, htcE, hlenE, hmeta, hsemE⟩ := ih (by omega)
    let c := (CrossFin.filter fun j => j < p).card
    have htcE' : tCount n m E ≤ p + 2 * c * m := htcE
    have hlenE' : E.length ≤ 2 + 2 * p + 4 * c * p + 4 * c ^ 2 * m + c * m + c := hlenE
    let g := C.gates[p]
    have hg_mono := hlegC g (List.getElem_mem hp_lt)
    have hback_p : ∀ i ∈ g.inputs, i < n + m + p := by
      intro i hi
      have hb := hback p hp_lt i
      unfold gateAt at hb
      rw [List.getD_eq_getElem _ _ hp_lt] at hb
      exact hb hi
    have hgateAt_p : gateAt C p = g := by
      unfold gateAt; exact List.getD_eq_getElem _ _ hp_lt
    by_cases hcp : p ∈ CrossFin
    · have hc_succ : (CrossFin.filter fun j => j < p + 1).card = c + 1 := by
        have hset : CrossFin.filter (fun j => j < p + 1) = insert p (CrossFin.filter fun j => j < p) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_insert]; constructor
          · rintro ⟨hj, hlt⟩
            by_cases h : j = p
            · exact Or.inl h
            · exact Or.inr ⟨hj, by omega⟩
          · rintro (rfl | ⟨hj, hlt⟩)
            · exact ⟨hcp, by omega⟩
            · exact ⟨hj, by omega⟩
        rw [hset, Finset.card_insert_of_notMem (by simp)]
      have hcp_prop : g.op = GateOp.and ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, 0 < deg n m C i := by
        simp only [CrossFin, Finset.mem_filter, Finset.mem_range, hgateAt_p] at hcp
        exact hcp.2
      obtain ⟨hop_and, hlen2, hdeg_pos⟩ := hcp_prop
      obtain ⟨a, b, hin⟩ : ∃ a b, g.inputs = [a, b] := List.length_eq_two.mp hlen2
      have halt : a < n + m + p := hback_p a (by rw [hin]; simp)
      have hblt : b < n + m + p := hback_p b (by rw [hin]; simp)
      have hda_pos : 0 < deg n m C a := hdeg_pos a (by rw [hin]; simp)
      have hdb_pos : 0 < deg n m C b := hdeg_pos b (by rw [hin]; simp)
      have hdp_pos : 0 < deg n m C (n + m + p) := by
        have h := deg_gate_eq n m C p hp_lt hback_p
        rw [h, if_pos hop_and]
        change 0 < (g.inputs.map fun i => deg n m C i).sum
        rw [hin]; simp; omega
      obtain ⟨hmpa_lt, hv0a_lt, hdv0a, _⟩ := hmeta a halt
      obtain ⟨hmpb_lt, hv0b_lt, hdv0b, _⟩ := hmeta b hblt
      obtain ⟨exA, adjA, hexA_len, hm1, hb1, hnc1, htc1, hvA, hbpA⟩ :=
        backPass n m E rest hpreE hmE hbE hncE (mp a) hmpa_lt
      let E1 := E ++ exA
      have hpre1 : E1 = [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ (rest ++ exA) := by
        simp [E1, hpreE, List.append_assoc]
      have hmpb_1 : mp b < n + m + E1.length := by simp [E1]; omega
      obtain ⟨exB, adjB, hexB_len, hm2, hb2, hnc2, htc2, hvB, hbpB⟩ :=
        backPass n m E1 (rest ++ exA) hpre1 hm1 hb1 hnc1 (mp b) hmpb_1
      let E2 := E1 ++ exB
      have hpre2 : E2 = [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ (rest ++ exA ++ exB) := by
        simp [E2, hpre1, List.append_assoc]
      let wBase := n + m + E2.length
      let gBase : Gate := ⟨GateOp.and, [v0 a, v0 b]⟩
      let E3 := E2 ++ [gBase]
      have hE2_from_E : E2 = E ++ (exA ++ exB) := by simp [E2, E1, List.append_assoc]
      have hv0a_2 : v0 a < n + m + E2.length := by rw [hE2_from_E, List.length_append]; omega
      have hv0b_2 : v0 b < n + m + E2.length := by rw [hE2_from_E, List.length_append]; omega
      have hdv0a_2 : degG n m E2 (v0 a) = 0 := by
        rw [hE2_from_E, degG_prefix n m E (exA ++ exB) (v0 a) hv0a_lt]; exact hdv0a
      have hdv0b_2 : degG n m E2 (v0 b) = 0 := by
        rw [hE2_from_E, degG_prefix n m E (exA ++ exB) (v0 b) hv0b_lt]; exact hdv0b
      have hgB_bk : ∀ i ∈ gBase.inputs, i < n + m + E2.length := by
        intro i hi; simp [gBase] at hi; rcases hi with rfl | rfl <;> assumption
      have hgB_dg : ∀ i ∈ gBase.inputs, degG n m E2 i = 0 := by
        intro i hi; simp [gBase] at hi; rcases hi with rfl | rfl <;> assumption
      have hok3 := append_gate_ok (n + m) E2 gBase hm2 hb2 ⟨Or.inl rfl, by simp [gBase]⟩ hgB_bk
      have hnc3 : NoCross n m E3 := NoCross_snoc n m E2 gBase hnc2 hb2 hgB_bk (fun _ _ => ⟨v0 a, by simp [gBase], hdv0a_2⟩)
      have hdwB : degG n m E3 wBase = 0 := degG_append_zero n m E2 gBase hgB_bk hgB_dg
      have htc3 : tCount n m E3 = tCount n m E2 := tCount_snoc_zero n m E2 gBase hdwB
      have hpre3 : E3 = [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ (rest ++ exA ++ exB ++ [gBase]) := by
        simp [E3, hpre2, List.append_assoc]
      have hv0a_3 : v0 a < n + m + E3.length := by simp [E3]; omega
      have hv0b_3 : v0 b < n + m + E3.length := by simp [E3]; omega
      have hdv0a_3 : degG n m E3 (v0 a) = 0 := by
        rw [degG_prefix n m E2 [gBase] (v0 a) hv0a_2]; exact hdv0a_2
      have hdv0b_3 : degG n m E3 (v0 b) = 0 := by
        rw [degG_prefix n m E2 [gBase] (v0 b) hv0b_2]; exact hdv0b_2
      have hvA3 : ∀ w u, adjA w = some u → u < n + m + E3.length ∧ degG n m E3 u = 0 := by
        intro w u hu
        obtain ⟨hult, hdu⟩ := hvA w u hu
        have hult1 : u < n + m + E1.length := hult
        have hE3_from_1 : E3 = E1 ++ (exB ++ [gBase]) := by simp [E3, E2, List.append_assoc]
        exact ⟨by rw [hE3_from_1, List.length_append]; omega,
          by rw [hE3_from_1, degG_prefix n m E1 (exB ++ [gBase]) u hult1]; exact hdu⟩
      have hvB3 : ∀ w u, adjB w = some u → u < n + m + E3.length ∧ degG n m E3 u = 0 := by
        intro w u hu
        obtain ⟨hult, hdu⟩ := hvB w u hu
        have hult2 : u < n + m + E2.length := hult
        exact ⟨by simp [E3]; omega, by rw [degG_prefix n m E2 [gBase] u hult2]; exact hdu⟩
      obtain ⟨exC, acc, hexC_len, hm4, hb4, hnc4, htc4, hacc4, hsemC⟩ :=
        crossCombine n m E3 (rest ++ exA ++ exB ++ [gBase]) hpre3 hok3.1 hok3.2 hnc3
          (v0 a) (v0 b) wBase hv0a_3 hdv0a_3 hv0b_3 hdv0b_3 (by simp [E3, wBase]) hdwB
          adjA adjB hvA3 hvB3 m le_rfl
      let E4 := E3 ++ exC
      have hE4_from_E : E4 = E ++ (exA ++ exB ++ [gBase] ++ exC) := by
        simp [E4, E3, E2, E1, List.append_assoc]
      have hpre4 : E4 = [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ (rest ++ exA ++ exB ++ [gBase] ++ exC) := by
        simp [E4, hpre3, List.append_assoc]
      have hE3_wBase_val : ∀ x : Fin n → Bool,
          let x0 := Fin.append x (fun _ : Fin m => false)
          val E3 wBase x0 = (val C.gates a x0 && val C.gates b x0) := by
        intro x
        dsimp only
        have hk : E2.length < E3.length := by simp [E3]
        have hget : E3[E2.length] = gBase := by simp [E3]
        apply Bool.eq_iff_iff.mpr
        rw [val_and E3 _ E2.length hk (by rw [hget]), hget]
        have hpa : val E3 (v0 a) (Fin.append x (fun _ : Fin m => false)) =
            val C.gates a (Fin.append x (fun _ : Fin m => false)) := by
          have hp : E3 = E ++ (exA ++ exB ++ [gBase]) := by simp [E3, E2, E1, List.append_assoc]
          rw [hp, val_prefix E (exA ++ exB ++ [gBase]) (v0 a) _ hv0a_lt]
          exact (hsemE a halt x).1
        have hpb : val E3 (v0 b) (Fin.append x (fun _ : Fin m => false)) =
            val C.gates b (Fin.append x (fun _ : Fin m => false)) := by
          have hp : E3 = E ++ (exA ++ exB ++ [gBase]) := by simp [E3, E2, E1, List.append_assoc]
          rw [hp, val_prefix E (exA ++ exB ++ [gBase]) (v0 b) _ hv0b_lt]
          exact (hsemE b hblt x).1
        simp only [gBase, List.mem_cons, List.not_mem_nil, or_false, Bool.and_eq_true]
        constructor
        · intro h
          exact ⟨hpa ▸ (h (v0 a) (Or.inl rfl)).2, hpb ▸ (h (v0 b) (Or.inr rfl)).2⟩
        · rintro ⟨h1, h2⟩ i (rfl | rfl)
          · exact ⟨hv0a_2, hpa.symm ▸ h1⟩
          · exact ⟨hv0b_2, hpb.symm ▸ h2⟩
      have hvalC_p : ∀ z : Fin (n + m) → Bool,
          val C.gates (n + m + p) z = (val C.gates a z && val C.gates b z) := by
        intro z
        apply Bool.eq_iff_iff.mpr
        rw [val_and C.gates z p hp_lt hop_and, hin]
        simp [halt, hblt, Bool.and_eq_true]
      refine ⟨E4, fun w => if w = n + m + p then acc else mp w,
        fun w => if w = n + m + p then wBase else v0 w,
        ⟨rest ++ exA ++ exB ++ [gBase] ++ exC, hpre4⟩, hm4, hb4, hnc4, ?_, ?_, ?_, ?_⟩
      · rw [hc_succ]
        have htc4' : tCount n m E4 ≤ tCount n m E3 + 2 * m := htc4
        have htc3' : tCount n m E3 = tCount n m E := htc3.trans (htc2.trans htc1)
        have hmul : 2 * (c + 1) * m = 2 * c * m + 2 * m := by ring
        omega
      · rw [hc_succ]
        have hlen4 : E4.length = E.length + exA.length + exB.length + 1 + exC.length := by
          simp [E4, E3, E2, E1]; omega
        have hexB_len' : exB.length ≤ 2 * tCount n m E := by
          have : tCount n m E1 = tCount n m E := htc1
          omega
        nlinarith only [hlen4, hlenE', hexA_len, hexB_len', hexC_len, htcE']
      · intro w hw
        dsimp only
        by_cases hwp : w = n + m + p
        · subst hwp
          rw [if_pos rfl, if_pos rfl]
          refine ⟨by simpa [E4] using hacc4, by simp [E4, E3, wBase], ?_, ?_⟩
          · rw [degG_prefix n m E3 exC wBase (by simp [E3, wBase])]; exact hdwB
          · intro h0; omega
        · rw [if_neg hwp, if_neg hwp]
          obtain ⟨h1, h2, h3, h4⟩ := hmeta w (by omega)
          refine ⟨by rw [hE4_from_E, List.length_append]; omega,
            by rw [hE4_from_E, List.length_append]; omega,
            by rw [hE4_from_E, degG_prefix n m E _ (v0 w) h2]; exact h3,
            fun hdw => by rw [hE4_from_E, degG_prefix n m E _ (mp w) h1]; exact h4 hdw⟩
      · intro w hw x
        dsimp only
        by_cases hwp : w = n + m + p
        · subst hwp
          rw [if_pos rfl, if_pos rfl]
          obtain ⟨hacc0, haccj⟩ := hsemC x
          have hwB_keep : val E4 wBase (Fin.append x (fun _ : Fin m => false)) =
              val E3 wBase (Fin.append x (fun _ : Fin m => false)) :=
            val_prefix E3 exC wBase _ (by simp [E3, wBase])
          refine ⟨?_, ?_, ?_⟩
          · rw [hwB_keep, hE3_wBase_val x, hvalC_p]
          · rw [hacc0, hE3_wBase_val x, hvalC_p]
          · intro j
            rw [haccj j, if_pos j.isLt, hE3_wBase_val x, hvalC_p]
            have hE3_v0a : val E3 (v0 a) (Fin.append x (fun _ : Fin m => false)) =
                val E (mp a) (Fin.append x (fun _ : Fin m => false)) := by
              have hp : E3 = E ++ (exA ++ exB ++ [gBase]) := by simp [E3, E2, E1, List.append_assoc]
              rw [hp, val_prefix E (exA ++ exB ++ [gBase]) (v0 a) _ hv0a_lt]
              exact (hsemE a halt x).1.trans (hsemE a halt x).2.1.symm
            have hE3_v0b : val E3 (v0 b) (Fin.append x (fun _ : Fin m => false)) =
                val E1 (mp b) (Fin.append x (fun _ : Fin m => false)) := by
              have hp : E3 = E ++ (exA ++ exB ++ [gBase]) := by simp [E3, E2, E1, List.append_assoc]
              rw [hp, val_prefix E (exA ++ exB ++ [gBase]) (v0 b) _ hv0b_lt]
              rw [val_prefix E exA (mp b) _ hmpb_lt]
              exact (hsemE b hblt x).1.trans (hsemE b hblt x).2.1.symm
            have hoptA : optVal E3 (Fin.append x (fun _ : Fin m => false)) (adjA (n + j.val)) =
                optVal E1 (Fin.append x (fun _ : Fin m => false)) (adjA (n + j.val)) := by
              cases h : adjA (n + j.val) with
              | none => rfl
              | some u =>
                simp only [optVal]
                have hp : E3 = E1 ++ (exB ++ [gBase]) := by simp [E3, E2, List.append_assoc]
                rw [hp]; exact val_prefix E1 (exB ++ [gBase]) u _ (hvA (n + j.val) u h).1
            have hoptB : optVal E3 (Fin.append x (fun _ : Fin m => false)) (adjB (n + j.val)) =
                optVal E2 (Fin.append x (fun _ : Fin m => false)) (adjB (n + j.val)) := by
              cases h : adjB (n + j.val) with
              | none => rfl
              | some u =>
                simp only [optVal]
                exact val_prefix E2 [gBase] u _ (hvB (n + j.val) u h).1
            rw [hE3_v0a, hE3_v0b, hoptA, hoptB, ← hbpA x j, ← hbpB x j]
            have hE1_b : val E1 (mp b) (Fin.append x (fun l => decide (l = j))) =
                val E (mp b) (Fin.append x (fun l => decide (l = j))) :=
              val_prefix E exA (mp b) _ hmpb_lt
            rw [hE1_b, (hsemE a halt x).2.2 j, (hsemE b hblt x).2.2 j]
            have hmono_x : ∀ v : Fin (n + m), Fin.append x (fun _ : Fin m => false) v = true →
                Fin.append x (fun l => decide (l = j)) v = true := by
              intro v hv
              by_cases hvn : v.val < n
              · have hv' : v = ⟨v.val, v.isLt⟩ := rfl
                rw [hv', fin_append_left _ _ v.val hvn] at hv ⊢; exact hv
              · have hv' : v = ⟨v.val, v.isLt⟩ := rfl
                rw [hv', fin_append_right _ _ v.val (by omega) v.isLt] at hv; simp at hv
            have hma := val_mono C.gates hlegC _ _ hmono_x a
            have hmb := val_mono C.gates hlegC _ _ hmono_x b
            cases ha0v : val C.gates a (Fin.append x (fun _ : Fin m => false)) <;>
            cases hb0v : val C.gates b (Fin.append x (fun _ : Fin m => false)) <;>
            simp only [Bool.false_and, Bool.and_false, Bool.false_or, Bool.true_and]
            have hat := hma ha0v
            have hbt := hmb hb0v
            simp [hat, hbt]
        · rw [if_neg hwp, if_neg hwp]
          obtain ⟨h1, h2, _, _⟩ := hmeta w (by omega)
          obtain ⟨hs1, hs2, hs3⟩ := hsemE w (by omega) x
          refine ⟨?_, ?_, ?_⟩
          · rw [hE4_from_E, val_prefix E _ (v0 w) _ h2]; exact hs1
          · rw [hE4_from_E, val_prefix E _ (mp w) _ h1]; exact hs2
          · intro j; rw [hE4_from_E, val_prefix E _ (mp w) _ h1]; exact hs3 j
    · have hc_same : (CrossFin.filter fun j => j < p + 1).card = c := by
        congr 1; ext j; simp only [Finset.mem_filter]; constructor
        · rintro ⟨hj, hlt⟩
          have hne : j ≠ p := fun h => hcp (h ▸ hj)
          exact ⟨hj, by omega⟩
        · rintro ⟨hj, hlt⟩; exact ⟨hj, by omega⟩
      let g1 : Gate := ⟨g.op, g.inputs.map mp⟩
      let g2 : Gate := ⟨g.op, g.inputs.map v0⟩
      let E1 := E ++ [g1]
      let E2 := E1 ++ [g2]
      have hg1_bk : ∀ i ∈ g1.inputs, i < n + m + E.length := by
        intro i hi; simp only [g1, List.mem_map] at hi
        obtain ⟨u, hu, rfl⟩ := hi
        exact (hmeta u (hback_p u hu)).1
      have hg1_nc : g1.op = GateOp.and → g1.inputs.length = 2 → ∃ i ∈ g1.inputs, degG n m E i = 0 := by
        intro hop hlen
        have hnotall : ¬ ∀ u ∈ g.inputs, 0 < deg n m C u := by
          intro hall
          apply hcp
          simp only [CrossFin, Finset.mem_filter, Finset.mem_range, hgateAt_p]
          exact ⟨hp_lt, hop, by simpa [g1] using hlen, hall⟩
        push Not at hnotall
        obtain ⟨u, hu, hdu⟩ := hnotall
        have hdu0 : deg n m C u = 0 := by omega
        exact ⟨mp u, List.mem_map_of_mem hu, (hmeta u (hback_p u hu)).2.2.2 hdu0⟩
      have hok1 := append_gate_ok (n + m) E g1 hmE hbE ⟨hg_mono.1, by simpa [g1] using hg_mono.2⟩ hg1_bk
      have hnc1 : NoCross n m E1 := NoCross_snoc n m E g1 hncE hbE hg1_bk hg1_nc
      have htc1 : tCount n m E1 ≤ tCount n m E + 1 := tCount_snoc_le n m E g1
      have hg2_bk : ∀ i ∈ g2.inputs, i < n + m + E1.length := by
        intro i hi; simp only [g2, List.mem_map] at hi
        obtain ⟨u, hu, rfl⟩ := hi
        have := (hmeta u (hback_p u hu)).2.1
        simp [E1]; omega
      have hg2_dg : ∀ i ∈ g2.inputs, degG n m E1 i = 0 := by
        intro i hi; simp only [g2, List.mem_map] at hi
        obtain ⟨u, hu, rfl⟩ := hi
        have hlt := (hmeta u (hback_p u hu)).2.1
        have hdz := (hmeta u (hback_p u hu)).2.2.1
        rw [degG_prefix n m E [g1] (v0 u) hlt]; exact hdz
      have hok2 := append_gate_ok (n + m) E1 g2 hok1.1 hok1.2 ⟨hg_mono.1, by simpa [g2] using hg_mono.2⟩ hg2_bk
      have hnc2 : NoCross n m E2 := NoCross_snoc n m E1 g2 hnc1 hok1.2 hg2_bk (fun _ hlen => by
        cases hin : g2.inputs with
        | nil => rw [hin] at hlen; simp at hlen
        | cons u _ => exact ⟨u, by simp [hin], hg2_dg u (by simp [hin])⟩)
      have hdg2 : degG n m E2 (n + m + E1.length) = 0 := degG_append_zero n m E1 g2 hg2_bk hg2_dg
      have htc2 : tCount n m E2 = tCount n m E1 := tCount_snoc_zero n m E1 g2 hdg2
      have hE2_from_E : E2 = E ++ [g1, g2] := by simp [E2, E1, List.append_assoc]
      have hpre2 : E2 = [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ (rest ++ [g1, g2]) := by
        simp [E2, E1, hpreE, List.append_assoc]
      have heval_copy : ∀ (f : ℕ → ℕ) (z : Fin (n + m) → Bool),
          (∀ u ∈ g.inputs, f u < n + m + E.length) →
          (∀ u ∈ g.inputs, val E (f u) z = val C.gates u z) →
          val (E ++ [⟨g.op, g.inputs.map f⟩]) (n + m + E.length) z = val C.gates (n + m + p) z := by
        intro f z hfb hfval
        let gf : Gate := ⟨g.op, g.inputs.map f⟩
        have hk : E.length < (E ++ [gf]).length := by simp
        have hget : (E ++ [gf])[E.length] = gf := by simp
        apply Bool.eq_iff_iff.mpr
        rcases hg_mono.1 with hand | hor
        · rw [val_and (E ++ [gf]) z E.length hk (by rw [hget]; exact hand),
              val_and C.gates z p hp_lt hand, hget]
          constructor
          · intro h u hu
            have h1 := h (f u) (List.mem_map_of_mem hu)
            have hp_eq := val_prefix E [gf] (f u) z (hfb u hu)
            exact ⟨hback_p u hu, by rw [← hfval u hu, ← hp_eq]; exact h1.2⟩
          · intro h v hv
            simp only [gf, List.mem_map] at hv
            obtain ⟨u, hu, rfl⟩ := hv
            have hp_eq := val_prefix E [gf] (f u) z (hfb u hu)
            exact ⟨hfb u hu, by rw [hp_eq, hfval u hu]; exact (h u hu).2⟩
        · rw [val_or (E ++ [gf]) z E.length hk (by rw [hget]; exact hor),
              val_or C.gates z p hp_lt hor, hget]
          constructor
          · rintro ⟨v, hv, _, hvv⟩
            simp only [gf, List.mem_map] at hv
            obtain ⟨u, hu, rfl⟩ := hv
            have hp_eq := val_prefix E [gf] (f u) z (hfb u hu)
            exact ⟨u, hu, hback_p u hu, by rw [← hfval u hu, ← hp_eq]; exact hvv⟩
          · rintro ⟨u, hu, _, hvu⟩
            have hp_eq := val_prefix E [gf] (f u) z (hfb u hu)
            exact ⟨f u, List.mem_map_of_mem hu, hfb u hu, by rw [hp_eq, hfval u hu]; exact hvu⟩
      refine ⟨E2, fun w => if w = n + m + p then n + m + E.length else mp w,
        fun w => if w = n + m + p then n + m + E1.length else v0 w,
        ⟨rest ++ [g1, g2], hpre2⟩, hok2.1, hok2.2, hnc2, ?_, ?_, ?_, ?_⟩
      · rw [hc_same]; omega
      · rw [hc_same]
        have hlen2 : E2.length = E.length + 2 := by simp [E2, E1]
        nlinarith only [hlen2, hlenE']
      · intro w hw
        dsimp only
        by_cases hwp : w = n + m + p
        · subst hwp
          rw [if_pos rfl, if_pos rfl]
          refine ⟨by simp [E2, E1], by simp [E2, E1], hdg2, ?_⟩
          intro hdp0
          have hdz_in := deg_zero_inputs n m C p hp_lt hback_p hdp0
          have hdg1 : degG n m E1 (n + m + E.length) = 0 :=
            degG_append_zero n m E g1 hg1_bk (fun i hi => by
              simp only [g1, List.mem_map] at hi
              obtain ⟨u, hu, rfl⟩ := hi
              exact (hmeta u (hback_p u hu)).2.2.2 (hdz_in u hu))
          rw [degG_prefix n m E1 [g2] (n + m + E.length) (by simp [E1])]
          exact hdg1
        · rw [if_neg hwp, if_neg hwp]
          obtain ⟨h1, h2, h3, h4⟩ := hmeta w (by omega)
          refine ⟨by rw [hE2_from_E, List.length_append]; omega,
            by rw [hE2_from_E, List.length_append]; omega,
            by rw [hE2_from_E, degG_prefix n m E [g1, g2] (v0 w) h2]; exact h3,
            fun hdw => by rw [hE2_from_E, degG_prefix n m E [g1, g2] (mp w) h1]; exact h4 hdw⟩
      · intro w hw x
        dsimp only
        by_cases hwp : w = n + m + p
        · subst hwp
          rw [if_pos rfl, if_pos rfl]
          refine ⟨?_, ?_, ?_⟩
          · have hk : E1.length < E2.length := by simp [E2]
            have hget : E2[E1.length] = g2 := by simp [E2]
            apply Bool.eq_iff_iff.mpr
            rcases hg_mono.1 with hand | hor
            · rw [val_and E2 _ E1.length hk (by rw [hget]; exact hand),
                  val_and C.gates _ p hp_lt hand, hget]
              constructor
              · intro h u hu
                have h1 := h (v0 u) (List.mem_map_of_mem hu)
                have hlt := (hmeta u (hback_p u hu)).2.1
                have hp_eq := val_prefix E [g1, g2] (v0 u) (Fin.append x (fun _ : Fin m => false)) hlt
                rw [← hE2_from_E] at hp_eq
                exact ⟨hback_p u hu, by rw [← (hsemE u (hback_p u hu) x).1, ← hp_eq]; exact h1.2⟩
              · intro h v hv
                simp only [g2, List.mem_map] at hv
                obtain ⟨u, hu, rfl⟩ := hv
                have hlt := (hmeta u (hback_p u hu)).2.1
                have hp_eq := val_prefix E [g1, g2] (v0 u) (Fin.append x (fun _ : Fin m => false)) hlt
                rw [← hE2_from_E] at hp_eq
                exact ⟨by simp [E1]; omega, by rw [hp_eq, (hsemE u (hback_p u hu) x).1]; exact (h u hu).2⟩
            · rw [val_or E2 _ E1.length hk (by rw [hget]; exact hor),
                  val_or C.gates _ p hp_lt hor, hget]
              constructor
              · rintro ⟨v, hv, _, hvv⟩
                simp only [g2, List.mem_map] at hv
                obtain ⟨u, hu, rfl⟩ := hv
                have hlt := (hmeta u (hback_p u hu)).2.1
                have hp_eq := val_prefix E [g1, g2] (v0 u) (Fin.append x (fun _ : Fin m => false)) hlt
                rw [← hE2_from_E] at hp_eq
                exact ⟨u, hu, hback_p u hu, by rw [← (hsemE u (hback_p u hu) x).1, ← hp_eq]; exact hvv⟩
              · rintro ⟨u, hu, _, hvu⟩
                have hlt := (hmeta u (hback_p u hu)).2.1
                have hp_eq := val_prefix E [g1, g2] (v0 u) (Fin.append x (fun _ : Fin m => false)) hlt
                rw [← hE2_from_E] at hp_eq
                exact ⟨v0 u, List.mem_map_of_mem hu, by simp [E1]; omega, by rw [hp_eq, (hsemE u (hback_p u hu) x).1]; exact hvu⟩
          · rw [val_prefix E1 [g2] (n + m + E.length) _ (by simp [E1])]
            exact heval_copy mp (Fin.append x (fun _ : Fin m => false))
              (fun u hu => (hmeta u (hback_p u hu)).1)
              (fun u hu => (hsemE u (hback_p u hu) x).2.1)
          · intro j
            rw [val_prefix E1 [g2] (n + m + E.length) _ (by simp [E1])]
            exact heval_copy mp (Fin.append x (fun l => decide (l = j)))
              (fun u hu => (hmeta u (hback_p u hu)).1)
              (fun u hu => (hsemE u (hback_p u hu) x).2.2 j)
        · rw [if_neg hwp, if_neg hwp]
          obtain ⟨h1, h2, _, _⟩ := hmeta w (by omega)
          obtain ⟨hs1, hs2, hs3⟩ := hsemE w (by omega) x
          refine ⟨?_, ?_, ?_⟩
          · rw [hE2_from_E, val_prefix E [g1, g2] (v0 w) _ h2]; exact hs1
          · rw [hE2_from_E, val_prefix E [g1, g2] (mp w) _ h1]; exact hs2
          · intro j; rw [hE2_from_E, val_prefix E [g1, g2] (mp w) _ h1]; exact hs3 j

def dropY (n m : ℕ) (w : ℕ) : ℕ :=
  if w < n then w else if w < n + m then n else w - m

def dropYGates (n m : ℕ) (gs : List Gate) : List Gate :=
  gs.map fun g => ⟨g.op, g.inputs.map (dropY n m)⟩

theorem dropYGates_len (n m : ℕ) (gs : List Gate) : (dropYGates n m gs).length = gs.length := by
  simp [dropYGates]

theorem dropYGates_mono (n m : ℕ) (gs : List Gate) (hmono : Monotone2 ⟨gs, 0⟩) :
    ∀ g ∈ dropYGates n m gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [dropYGates, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨h1, h2⟩ := hmono g0 hg0
  exact ⟨by simpa using h1, by simpa using h2⟩

theorem dropYGates_eval (n m : ℕ) (gs rest : List Gate)
    (hpre : gs = [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ rest)
    (hmono : Monotone2 ⟨gs, 0⟩) (hback : ReadsBack (n + m) ⟨gs, 0⟩)
    (x : Fin n → Bool) :
    ∀ w < n + m + gs.length,
      val (dropYGates n m gs) (dropY n m w) x = val gs w (Fin.append x (fun _ : Fin m => false)) := by
  have h0_lt : 0 < (dropYGates n m gs).length := by rw [dropYGates_len, hpre]; simp
  have h0_get : (dropYGates n m gs)[0]'h0_lt = ⟨GateOp.or, []⟩ := by
    simp [dropYGates, hpre]
  have hfalseD : val (dropYGates n m gs) n x = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hv := (val_or (dropYGates n m gs) x 0 h0_lt (by rw [h0_get])).mp (by simpa using h)
    rcases hv with ⟨_, hi, _⟩
    rw [h0_get] at hi; simp at hi
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hdy : dropY n m w = w := by simp [dropY, hwn]
      rw [hdy, val_input _ x w hwn, val_input gs _ w (by omega), fin_append_left x (fun _ : Fin m => false) w hwn]
    by_cases hwm : w < n + m
    · have hdy : dropY n m w = n := by simp [dropY, hwn, hwm]
      rw [hdy, hfalseD, val_input gs _ w hwm, fin_append_right x (fun _ : Fin m => false) w (by omega) hwm]
    · have hk : w - (n + m) < gs.length := by omega
      have hweq : n + m + (w - (n + m)) = w := by omega
      have hdy : dropY n m w = n + (w - (n + m)) := by
        unfold dropY; rw [if_neg hwn, if_neg hwm]; omega
      have hdk : w - (n + m) < (dropYGates n m gs).length := by rw [dropYGates_len]; exact hk
      have hget : (dropYGates n m gs)[w - (n + m)] = ⟨gs[w - (n + m)].op, gs[w - (n + m)].inputs.map (dropY n m)⟩ := by
        simp [dropYGates]
      have hbk : ∀ i ∈ gs[w - (n + m)].inputs, i < n + m + (w - (n + m)) := by
        intro i hi
        have hb := hback (w - (n + m)) hk i
        unfold gateAt at hb
        rw [List.getD_eq_getElem _ _ hk] at hb
        exact hb hi
      have hbd : ∀ i ∈ gs[w - (n + m)].inputs, dropY n m i < n + (w - (n + m)) := by
        intro i hi
        have hlt := hbk i hi
        by_cases hk0 : w - (n + m) = 0
        · have hget0 : gs[w - (n + m)] = ⟨GateOp.or, []⟩ := by simp [hk0, hpre]
          rw [hget0] at hi; simp at hi
        · unfold dropY; split_ifs <;> omega
      have hop : gs[w - (n + m)].op = GateOp.and ∨ gs[w - (n + m)].op = GateOp.or := by
        simpa using (hmono gs[w - (n + m)] (List.getElem_mem hk)).1
      rw [hdy]
      conv_rhs => rw [← hweq]
      apply Bool.eq_iff_iff.mpr
      rcases hop with hand | hor
      · rw [val_and (dropYGates n m gs) x (w - (n + m)) hdk (by rw [hget]; exact hand),
            val_and gs _ (w - (n + m)) hk hand, hget]
        constructor
        · intro h i hi
          have h1 := h (dropY n m i) (List.mem_map_of_mem hi)
          have hlt := hbk i hi
          exact ⟨hlt, by rw [← ih i (by omega) (by omega)]; exact h1.2⟩
        · intro h v hv
          simp only [List.mem_map] at hv
          obtain ⟨i, hi, rfl⟩ := hv
          have hlt := hbk i hi
          exact ⟨hbd i hi, by rw [ih i (by omega) (by omega)]; exact (h i hi).2⟩
      · rw [val_or (dropYGates n m gs) x (w - (n + m)) hdk (by rw [hget]; exact hor),
            val_or gs _ (w - (n + m)) hk hor, hget]
        constructor
        · rintro ⟨v, hv, _, hvv⟩
          simp only [List.mem_map] at hv
          obtain ⟨i, hi, rfl⟩ := hv
          have hlt := hbk i hi
          exact ⟨i, hi, hlt, by rw [← ih i (by omega) (by omega)]; exact hvv⟩
        · rintro ⟨i, hi, _, hvi⟩
          have hlt := hbk i hi
          exact ⟨dropY n m i, List.mem_map_of_mem hi, hbd i hi, by rw [ih i (by omega) (by omega)]; exact hvi⟩

theorem final_thm : ∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
  classical
  intro n m s k L C hpair hmono hback hsize hcross hsound
  have hzero_out : ∀ x : Fin n → Bool, val C.gates C.output (Fin.append x (fun _ : Fin m => false)) = false := by
    intro x
    apply Bool.eq_false_iff.mpr
    intro h
    have h1 : PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ (∅ : Finset (Fin m))))) = true := by
      simpa [circuitFun, Circuit.eval, Circuit.wires, val, wf] using h
    obtain ⟨j, hj, _⟩ := hsound x ∅ (by simp) h1
    simp at hj
  by_cases hoob : n + m + C.gates.length ≤ C.output
  · have hmt : Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧
        PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true) = ∅ := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
      intro _ hv
      change val C.gates C.output _ = true at hv
      rw [val_big C.gates _ C.output hoob] at hv
      exact absurd hv (by simp)
    rw [hmt]; simp
  by_cases hs0 : C.gates.length = 0
  · have hout_lt : C.output < n + m := by omega
    have hmt : Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧
        PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true) = ∅ := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
      intro _ hv
      change val C.gates C.output (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true at hv
      rw [val_input C.gates _ C.output hout_lt] at hv
      by_cases hwn : C.output < n
      · rw [fin_append_left _ _ C.output hwn] at hv
        have hz := hzero_out (fun i => decide (i = e.1))
        rw [val_input C.gates _ C.output hout_lt, fin_append_left _ _ C.output hwn] at hz
        rw [hv] at hz; exact absurd hz (by simp)
      · rw [fin_append_right _ _ C.output (by omega) hout_lt, decide_eq_true_eq] at hv
        have h1 : PEqualNP.MetaComplexity.circuitFun (n + m) C
            (Fin.append (fun _ : Fin n => false) (fun l => decide (l ∈ ({e.2} : Finset (Fin m))))) = true := by
          change val C.gates C.output _ = true
          rw [val_input C.gates _ C.output hout_lt, fin_append_right _ _ C.output (by omega) hout_lt]
          simp [hv]
        obtain ⟨_, _, _, _, hfp⟩ := hsound (fun _ => false) {e.2} (by simp) h1
        exact absurd hfp (by simp)
    rw [hmt]; simp
  have hs_pos : 1 ≤ s := by
    change C.gates.length ≤ s at hsize
    omega
  have hout_lt : C.output < n + m + C.gates.length := by omega
  let CrossFin : Finset ℕ := (Finset.range C.gates.length).filter (fun j =>
    (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs.length = 2 ∧
    ∀ i ∈ (gateAt C j).inputs, 0 < deg n m C i)
  have hCross_eq : {j : ℕ | j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      (gateAt C j).inputs.length = 2 ∧
      ∀ i ∈ (gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} = (CrossFin : Set ℕ) := by
    ext j; simp [CrossFin, deg]
  have hCross_le : CrossFin.card ≤ k := by
    rw [hCross_eq, Set.ncard_coe_finset] at hcross; exact hcross
  obtain ⟨E, mp, v0, ⟨restE, hpreE⟩, hmE, hbE, hncE, htcE, hlenE, hmetaE, hsemE⟩ :=
    elimCross n m C hmono hback C.gates.length le_rfl
  have hfilt_all : (CrossFin.filter fun j => j < C.gates.length) = CrossFin := by
    ext j; simp only [Finset.mem_filter, and_iff_left_iff_imp]; intro hj
    simp only [CrossFin, Finset.mem_filter, Finset.mem_range] at hj; exact hj.1
  rw [hfilt_all] at htcE hlenE
  obtain ⟨hmp_out, _, _, _⟩ := hmetaE C.output hout_lt
  obtain ⟨exOut, adjOut, hexOut_len, hmF, hbF, hncF, _, hvOut, hbpOut⟩ :=
    backPass n m E restE hpreE hmE hbE hncE (mp C.output) hmp_out
  let Efin := E ++ exOut
  have hpreF : Efin = [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ (restE ++ exOut) := by
    simp [Efin, hpreE, List.append_assoc]
  let Dg := dropYGates n m Efin
  let o : Fin m → ℕ := fun j => match adjOut (n + j.val) with
    | none => n
    | some u => dropY n m u
  have hDg_mono := dropYGates_mono n m Efin hmF
  have hDg_val : ∀ (x : Fin n → Bool) (j : Fin m),
      val Dg (o j) x = val C.gates C.output (Fin.append x (fun l => decide (l = j))) := by
    intro x j
    have hstep1 := hbpOut x j
    rw [(hsemE C.output hout_lt x).2.2 j, (hsemE C.output hout_lt x).2.1, hzero_out x, Bool.false_or] at hstep1
    rw [hstep1]
    dsimp only [o]
    cases h : adjOut (n + j.val) with
    | none =>
      simp only [optVal]
      have hval_n := dropYGates_eval n m Efin (restE ++ exOut) hpreF hmF hbF x (n + m) (by rw [hpreF]; simp)
      have hdy : dropY n m (n + m) = n := by simp [dropY]
      rw [hdy] at hval_n
      rw [hval_n]
      exact (base_consts_eval n m Efin (restE ++ exOut) hpreF).2.2.2.1 _
    | some u =>
      simp only [optVal]
      exact dropYGates_eval n m Efin (restE ++ exOut) hpreF hmF hbF x u (hvOut (n + j.val) u h).1
  let A : Fin m → Finset (Fin n) := fun l =>
    (L l).filter (fun p => val Dg (o l) (fun i => decide (i = p)) = true)
  let I : Fin m → Finset (Fin Dg.length) := fun l =>
    Finset.univ.filter (fun g =>
      (Dg.get g).op = GateOp.or ∧
      val Dg (n + (g : ℕ)) (fun v : Fin n => decide (v ∉ L l)) = false ∧
      ∃ p ∈ A l, ∃ p' ∈ A l, p ≠ p' ∧
        val Dg (n + (g : ℕ)) (fun i => decide (i = p)) = true ∧
        val Dg (n + (g : ℕ)) (fun i => decide (i = p')) = true)
  have hrow : ∀ l : Fin m, (A l).card ≤ 1 + (I l).card := by
    intro l
    apply row_bound n (L l) (A l) (fun p i => decide (i = p)) Dg (o l) hDg_mono
      (Finset.filter_subset _ _)
      (fun p _ v _ => by simp)
      ?_ ?_ (I l) ?_
    · change val Dg (o l) (fun v : Fin n => decide (v ∉ L l)) = false
      rw [hDg_val]
      apply Bool.eq_false_iff.mpr
      intro h
      have h1 : PEqualNP.MetaComplexity.circuitFun (n + m) C
          (Fin.append (fun v : Fin n => decide (v ∉ L l)) (fun l' => decide (l' ∈ ({l} : Finset (Fin m))))) = true := by
        simpa [circuitFun, Circuit.eval, Circuit.wires, val, wf] using h
      obtain ⟨j, hj, p, hpL, hxp⟩ := hsound _ {l} (by simp) h1
      simp only [Finset.mem_singleton] at hj
      subst hj
      simp [hpL] at hxp
    · intro p hp
      simp only [A, Finset.mem_filter] at hp
      exact hp.2
    · intro g hg
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hg
  have hdisj : ∀ l1 l2 : Fin m, l1 ≠ l2 → Disjoint (I l1) (I l2) := by
    intro l1 l2 hne
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hg1 hg2
    obtain ⟨_, _, p, hp1, p', hp'1, hpp', hvp, hvp'⟩ := hg1
    have hpL : p ∈ L l1 := (Finset.mem_filter.mp hp1).1
    have hp'L : p' ∈ L l1 := (Finset.mem_filter.mp hp'1).1
    have hnotboth : p ∉ L l2 ∨ p' ∉ L l2 := by
      by_contra hboth
      push Not at hboth
      have hsub : ({p, p'} : Finset (Fin n)) ⊆ L l1 ∩ L l2 := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hpL, hboth.1⟩
        · exact Finset.mem_inter.mpr ⟨hp'L, hboth.2⟩
      have h2 : 2 ≤ (L l1 ∩ L l2).card := by
        have := Finset.card_le_card hsub
        rw [Finset.card_pair hpp'] at this; exact this
      have := hpair l1 l2 hne
      omega
    rcases hnotboth with hq | hq
    · have htr := val_mono Dg hDg_mono (fun i => decide (i = p)) (fun v => decide (v ∉ L l2))
        (fun v hv => by simp only [decide_eq_true_eq] at hv ⊢; subst hv; exact hq) (n + (g : ℕ)) hvp
      rw [hg2.2.1] at htr; exact absurd htr (by simp)
    · have htr := val_mono Dg hDg_mono (fun i => decide (i = p')) (fun v => decide (v ∉ L l2))
        (fun v hv => by simp only [decide_eq_true_eq] at hv ⊢; subst hv; exact hq) (n + (g : ℕ)) hvp'
      rw [hg2.2.1] at htr; exact absurd htr (by simp)
  have hsumI : ∑ l : Fin m, (I l).card ≤ Dg.length := by
    have hbu : (Finset.univ.biUnion I).card = ∑ l : Fin m, (I l).card :=
      Finset.card_biUnion (fun l1 _ l2 _ hne => hdisj l1 l2 hne)
    rw [← hbu]
    have hle := Finset.card_le_card (Finset.subset_univ (Finset.univ.biUnion I))
    simpa using hle
  have hacc_eq : (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧
      PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card =
      ∑ l : Fin m, (A l).card := by
    let S : Fin m → Finset (Fin n × Fin m) := fun l =>
      (A l).map ⟨fun p => (p, l), fun p1 p2 h => (Prod.mk.inj h).1⟩
    have hSet : Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧
        PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true) =
        Finset.univ.biUnion S := by
      ext ⟨p, l⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_map,
        Function.Embedding.coeFn_mk, S, A]
      constructor
      · rintro ⟨hpL, hv⟩
        refine ⟨l, p, ⟨hpL, ?_⟩, rfl⟩
        rw [hDg_val]; exact hv
      · rintro ⟨l', p', ⟨hpL, hv⟩, heq⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        refine ⟨hpL, ?_⟩
        change val C.gates C.output _ = true
        rw [← hDg_val]; exact hv
    rw [hSet, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro l _; simp [S]
    · intro l1 _ l2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e he1 he2
      simp only [S, Finset.mem_map, Function.Embedding.coeFn_mk] at he1 he2
      obtain ⟨_, _, rfl⟩ := he1
      obtain ⟨_, _, h2⟩ := he2
      exact hne (Prod.mk.inj h2).2.symm
  have hsumA : ∑ l : Fin m, (A l).card ≤ m + Dg.length := by
    have h1 : ∑ l : Fin m, (A l).card ≤ ∑ l : Fin m, (1 + (I l).card) :=
      Finset.sum_le_sum (fun l _ => hrow l)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
    omega
  have hDg_len : Dg.length = E.length + exOut.length := by
    simp [Dg, dropYGates_len, Efin]
  have hCg_le : C.gates.length ≤ s := hsize
  have hCross_sq : CrossFin.card ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hCross_le 2
  have h1 : CrossFin.card ^ 2 * m ≤ k ^ 2 * m := Nat.mul_le_mul_right m hCross_sq
  have h2 : CrossFin.card * C.gates.length ≤ k * s := Nat.mul_le_mul hCross_le hCg_le
  have h3 : CrossFin.card * m ≤ k * m := Nat.mul_le_mul_right m hCross_le
  rw [hacc_eq]
  nlinarith only [hsumA, hDg_len, hlenE, hexOut_len, htcE, hCg_le, hCross_le, hs_pos, h1, h2, h3]

end PEqualNP.Outside.L_meta_1625_aux


theorem PEqualNP.Outside.L_meta_1625 : ∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
  exact PEqualNP.Outside.L_meta_1625_aux.final_thm

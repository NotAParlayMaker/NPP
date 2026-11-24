import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1645

open PEqualNP.CircuitLowerBounds

/-- One evaluation step: appending the value of a gate to the wire list. -/
def Step (v : List Bool) (g : Gate) : List Bool :=
  v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]

theorem wires_eq (gs : List Gate) (v : List Bool) :
    Circuit.wires ⟨gs, 0⟩ v = gs.foldl Step v := rfl

theorem length_foldl (gs : List Gate) (v : List Bool) :
    (gs.foldl Step v).length = v.length + gs.length := by
  induction gs generalizing v with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons, ih]
      have h1 : (Step v g).length = v.length + 1 := by simp [Step]
      rw [h1]
      simp only [List.length_cons]
      omega

theorem getD_foldl_lt (gs : List Gate) (v : List Bool) {k : ℕ} (hk : k < v.length) :
    (gs.foldl Step v).getD k false = v.getD k false := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
      rw [List.foldl_cons]
      have h1 : k < (Step v g).length := by
        have h2 : (Step v g).length = v.length + 1 := by simp [Step]
        omega
      rw [ih (v := Step v g) h1]
      simp only [Step]
      exact List.getD_append v _ false k hk

theorem getD_foldl_gate (gs : List Gate) :
    ∀ (v : List Bool)
      (htop : ∀ (i : ℕ) (hi : i < gs.length), ∀ w ∈ (gs.get ⟨i, hi⟩).inputs, w < v.length + i)
      (i : ℕ) (hi : i < gs.length),
      (gs.foldl Step v).getD (v.length + i) false
        = (gs.get ⟨i, hi⟩).op.eval
            ((gs.get ⟨i, hi⟩).inputs.map fun w => (gs.foldl Step v).getD w false) := by
  induction gs with
  | nil => intro v _htop i hi; exact absurd hi (by simp)
  | cons g gs ih =>
      intro v htop i hi
      have hlen : (Step v g).length = v.length + 1 := by simp [Step]
      have htop' : ∀ (k : ℕ) (hk : k < gs.length),
          ∀ w ∈ (gs.get ⟨k, hk⟩).inputs, w < (Step v g).length + k := by
        intro k hk w hw
        rw [hlen]
        have hk1 : k + 1 < (g :: gs).length := by simp only [List.length_cons]; omega
        have hgt : (g :: gs).get ⟨k + 1, hk1⟩ = gs.get ⟨k, hk⟩ := by simp
        have h1 := htop (k + 1) hk1
        rw [hgt] at h1
        have h2 := h1 w hw
        omega
      rw [List.foldl_cons]
      cases i with
      | zero =>
          rw [Nat.add_zero]
          have h0 : (gs.foldl Step (Step v g)).getD v.length false
              = (Step v g).getD v.length false := by
            rw [getD_foldl_lt gs (Step v g) (k := v.length) (by rw [hlen]; omega)]
          rw [h0]
          have hg : (Step v g).getD v.length false
              = g.op.eval (g.inputs.map fun w => v.getD w false) := by
            simp only [Step]
            rw [List.getD_append_right _ _ _ _ (le_refl v.length), Nat.sub_self]
            rfl
          rw [hg]
          have hmap : g.inputs.map (fun w => (gs.foldl Step (Step v g)).getD w false)
              = g.inputs.map (fun w => v.getD w false) := by
            apply List.map_congr_left
            intro w hw
            have hwv : w < v.length := by
              have h1 := htop 0 hi w hw
              simpa using h1
            rw [getD_foldl_lt gs (Step v g) (k := w) (by rw [hlen]; omega)]
            simp only [Step]
            exact List.getD_append v _ false w hwv
          rw [← hmap]
          simp
      | succ i' =>
          have hi' : i' < gs.length := by simpa using hi
          have hshift : v.length + (i' + 1) = (Step v g).length + i' := by rw [hlen]; omega
          rw [hshift, ih (Step v g) htop' i' hi']
          simp

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (f f' : ℕ → Bool)
    (h : ∀ i ∈ ins, f i = true → f' i = true) :
    op.eval (ins.map f) = true → op.eval (ins.map f') = true := by
  rcases hop with rfl | rfl
  · show (ins.map f).all id = true → (ins.map f').all id = true
    rw [List.all_eq_true, List.all_eq_true]
    intro hall i hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
    exact h k hk (by simpa using hall (f k) (List.mem_map.mpr ⟨k, hk, rfl⟩))
  · show (ins.map f).any id = true → (ins.map f').any id = true
    rw [List.any_eq_true, List.any_eq_true]
    rintro ⟨a, ha, ha'⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
    exact ⟨f' k, List.mem_map.mpr ⟨k, hk, rfl⟩, by simpa using h k hk (by simpa using ha')⟩

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) {w : ℕ} (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  rw [List.getD_eq_get (i := ⟨w, by simpa using hw⟩), List.get_ofFn]
  exact congrArg x (Fin.ext rfl)

end PEqualNP.Outside.L_meta_1645

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1645

theorem PEqualNP.Outside.L_meta_1645 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    (∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev (N + (h : ℕ)) x = false ∧ ev (N + (j : ℕ)) x = true) ∧
    (∀ w ∈ L i0, w ≠ p0 → w ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = w)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = w)) = true) ∧
    ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)) = false ∧
    ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v : Fin N, x v = true → v ∉ L i0) → (∀ v : Fin N, y v = true → v ∉ L i0) → (∀ v : Fin N, x v = true → y v = true) → ev w x = true → ev w y = true := by
  intro q N L i0 p0 p1 hq hN hcard hinter hcoll hpne hpL0 hpL1 gates o j h hopOK htop hjop hjun hjlt hhead hcorr ev hev h0 h1 hother hcomp
  classical
  have key : ∀ (w : ℕ) (x : Fin N → Bool),
      ev w x = (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD w false := by
    intro w x
    rw [hev w x]
    rfl
  have hofn : ∀ (x : Fin N → Bool), (List.ofFn x).length = N := by
    intro x
    simp
  have hlenW : ∀ (x : Fin N → Bool),
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).length = N + gates.length := by
    intro x
    rw [wires_eq, length_foldl, hofn x]
  have hread : ∀ (x : Fin N → Bool) (i : ℕ) (hi : i < gates.length),
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (N + i) false =
        (gates.get ⟨i, hi⟩).op.eval ((gates.get ⟨i, hi⟩).inputs.map fun w =>
          (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD w false) := by
    intro x i hi
    have htop' : ∀ (k : ℕ) (hk : k < gates.length),
        ∀ w ∈ (gates.get ⟨k, hk⟩).inputs, w < (List.ofFn x).length + k := by
      intro k hk w hw
      rw [hofn x]
      exact htop ⟨k, hk⟩ w hw
    have hg := getD_foldl_gate gates (List.ofFn x) htop' i hi
    rw [hofn x, ← wires_eq] at hg
    exact hg
  have hnot : ∀ (x : Fin N → Bool),
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (N + (j : ℕ)) false =
        !((Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (N + (h : ℕ)) false) := by
    intro x
    obtain ⟨r, hr⟩ := hhead
    have hge : gates.get (⟨(j : ℕ), j.isLt⟩ : Fin gates.length) = gates.get j := rfl
    have hj := hread x (j : ℕ) j.isLt
    rw [hge, hjop, hr] at hj
    rw [hj]
    simp only [GateOp.eval, List.map_cons, List.headD_cons]
  have hmono_pre : ∀ (i : ℕ) (hi : i < gates.length), i < (j : ℕ) →
      ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) →
        (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (N + i) false = true →
        (Circuit.wires ⟨gates, 0⟩ (List.ofFn y)).getD (N + i) false = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi hij x y hxy hx
      have hine : (⟨i, hi⟩ : Fin gates.length) ≠ j := by
        intro heq
        have hv : i = (j : ℕ) := congrArg Fin.val heq
        omega
      have hop : (gates.get ⟨i, hi⟩).op = GateOp.and ∨ (gates.get ⟨i, hi⟩).op = GateOp.or := by
        rcases (hopOK (gates.get ⟨i, hi⟩) (List.get_mem gates ⟨i, hi⟩)).1 with hh | hh | hh
        · exact Or.inl hh
        · exact Or.inr hh
        · exact absurd (hjun ⟨i, hi⟩ hh) hine
      rw [hread x i hi] at hx
      rw [hread y i hi]
      refine eval_mono (gates.get ⟨i, hi⟩).op hop _ _ _ ?_ hx
      intro w hw hwx
      have hwN : w < N + i := htop ⟨i, hi⟩ w hw
      rcases lt_or_ge w N with hwlt | hwge
      · have ex : (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD w false = x ⟨w, hwlt⟩ := by
          rw [wires_eq, getD_foldl_lt gates (List.ofFn x) (by simpa using hwlt)]
          exact ofFn_getD x hwlt
        have ey : (Circuit.wires ⟨gates, 0⟩ (List.ofFn y)).getD w false = y ⟨w, hwlt⟩ := by
          rw [wires_eq, getD_foldl_lt gates (List.ofFn y) (by simpa using hwlt)]
          exact ofFn_getD y hwlt
        rw [ex] at hwx
        rw [ey]
        exact hxy ⟨w, hwlt⟩ hwx
      · obtain ⟨k, hkw⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < i := by omega
        have hki : k < gates.length := by omega
        rw [hkw] at hwx ⊢
        exact ih k hk hki (by omega) x y hxy hwx
  have hfalse : ∀ x : Fin N → Bool, (∀ v, x v = true → v ∉ L i0) →
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (N + (h : ℕ)) false = false := by
    intro x hxoff
    have hcomp' : (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0)))).getD (N + (h : ℕ)) false = false := by
      rw [← key (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0))]
      exact hcomp
    have hxC : ∀ v, x v = true → (fun v : Fin N => decide (v ∉ L i0)) v = true := by
      intro v hv
      exact decide_eq_true (hxoff v hv)
    cases hb : (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (N + (h : ℕ)) false with
    | false => rfl
    | true =>
        exfalso
        have hmono := hmono_pre (h : ℕ) h.isLt hjlt x (fun v : Fin N => decide (v ∉ L i0)) hxC hb
        rw [hcomp'] at hmono
        exact absurd hmono (by simp)
  have hmono_off : ∀ (i : ℕ), i < gates.length → ∀ x y : Fin N → Bool,
      (∀ v, x v = true → v ∉ L i0) → (∀ v, y v = true → v ∉ L i0) →
      (∀ v, x v = true → y v = true) →
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (N + i) false = true →
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn y)).getD (N + i) false = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi x y hxoff hyoff hxy hx
      rcases lt_or_ge i (j : ℕ) with hij | hji
      · exact hmono_pre i hi hij x y hxy hx
      · rcases lt_or_eq_of_le hji with hlt | heq
        · have hine : (⟨i, hi⟩ : Fin gates.length) ≠ j := by
            intro heq'
            have hv : i = (j : ℕ) := congrArg Fin.val heq'
            omega
          have hop : (gates.get ⟨i, hi⟩).op = GateOp.and ∨ (gates.get ⟨i, hi⟩).op = GateOp.or := by
            rcases (hopOK (gates.get ⟨i, hi⟩) (List.get_mem gates ⟨i, hi⟩)).1 with hh | hh | hh
            · exact Or.inl hh
            · exact Or.inr hh
            · exact absurd (hjun ⟨i, hi⟩ hh) hine
          rw [hread x i hi] at hx
          rw [hread y i hi]
          refine eval_mono (gates.get ⟨i, hi⟩).op hop _ _ _ ?_ hx
          intro w hw hwx
          have hwN : w < N + i := htop ⟨i, hi⟩ w hw
          rcases lt_or_ge w N with hwlt | hwge
          · have ex : (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD w false = x ⟨w, hwlt⟩ := by
              rw [wires_eq, getD_foldl_lt gates (List.ofFn x) (by simpa using hwlt)]
              exact ofFn_getD x hwlt
            have ey : (Circuit.wires ⟨gates, 0⟩ (List.ofFn y)).getD w false = y ⟨w, hwlt⟩ := by
              rw [wires_eq, getD_foldl_lt gates (List.ofFn y) (by simpa using hwlt)]
              exact ofFn_getD y hwlt
            rw [ex] at hwx
            rw [ey]
            exact hxy ⟨w, hwlt⟩ hwx
          · obtain ⟨k, hkw⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
            have hk : k < i := by omega
            have hki : k < gates.length := by omega
            rw [hkw] at hwx ⊢
            exact ih k hk hki x y hxoff hyoff hxy hwx
        · rw [← heq, hnot y, hfalse y hyoff]
          rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hxoff
    have hfx := hfalse x hxoff
    exact ⟨by rw [key (N + (h : ℕ)) x]; exact hfx,
      by rw [key (N + (j : ℕ)) x, hnot x, hfx]; rfl⟩
  · intro w hw hw0 hw1
    have hw' : (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun v : Fin N => decide (v = w)))).getD (N + (h : ℕ)) false = false := by
      rw [← key (N + (h : ℕ)) (fun v : Fin N => decide (v = w))]
      exact hother w hw0 hw1
    exact ⟨by rw [key (N + (h : ℕ)) (fun v : Fin N => decide (v = w))]; exact hw',
      by rw [key (N + (j : ℕ)) (fun v : Fin N => decide (v = w)), hnot (fun v : Fin N => decide (v = w)), hw']; rfl⟩
  · rw [key (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)),
      hnot (fun v : Fin N => decide (v = p0)),
      ← key (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)), h0]
    rfl
  · rw [key (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)),
      hnot (fun v : Fin N => decide (v = p1)),
      ← key (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)), h1]
    rfl
  · intro w x y hxoff hyoff hxy htrue
    rw [key w x] at htrue
    rw [key w y]
    rcases lt_or_ge w N with hwlt | hwge
    · have ex : (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD w false = x ⟨w, hwlt⟩ := by
        rw [wires_eq, getD_foldl_lt gates (List.ofFn x) (by simpa using hwlt)]
        exact ofFn_getD x hwlt
      have ey : (Circuit.wires ⟨gates, 0⟩ (List.ofFn y)).getD w false = y ⟨w, hwlt⟩ := by
        rw [wires_eq, getD_foldl_lt gates (List.ofFn y) (by simpa using hwlt)]
        exact ofFn_getD y hwlt
      rw [ex] at htrue
      rw [ey]
      exact hxy ⟨w, hwlt⟩ htrue
    · obtain ⟨k, hkw⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
      rw [hkw] at htrue ⊢
      by_cases hk : k < gates.length
      · exact hmono_off k hk x y hxoff hyoff hxy htrue
      · have hle : (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).length ≤ N + k := by
          rw [hlenW x]
          omega
        rw [List.getD_eq_default _ _ hle] at htrue
        exact absurd htrue (by simp)

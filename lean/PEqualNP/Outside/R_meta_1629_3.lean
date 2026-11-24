import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.FactorSubst PEqualNP.CrossAnd PEqualNP.ReadK

-- Promise-minimal reduction of L-meta-1629 into line-single, point-single, and
-- a factor-substitution-irredundant, few-cross-AND, 80%-double-reread core for q >= 200.
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_1629_3
    (h_lineSingle :
      ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
        (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l')) →
        IsAO2 (N + N) C →
        (∀ z : Fin (N + N) → Bool,
          Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 1 →
          (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
          circuitFun (N + N) C z = false) →
        Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
          lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true} ≤
          10 * C.size)
    (h_pointSingle :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
        2 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
        (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
        IsAO2 (N + N) C →
        (∀ z : Fin (N + N) → Bool,
          Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
          (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
          circuitFun (N + N) C z = false) →
        Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
          lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = true} ≤
          10 * C.size)
    (h_core :
      ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
        200 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, (S l).card = q + 1) →
        (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, p ∈ S l ∧ r ∈ S l) →
        IsAO2 (N + N) C →
        N + N ≤ C.output →
        C.output < N + N + C.size →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        liveSize (N + N) C = C.size →
        RightOnIncidentPairs S C →
        (∀ Y : Finset (Fin N), Y.card ≤ q →
          C.eval (incidenceInput (zeroSet S Y) Y) = false) →
        (∀ (c : ℕ) (σ : ℕ → ℕ), c < C.size →
          (gateAt C c).op = GateOp.and →
          C.output ≠ N + N + c →
          (∀ r : ℕ, σ r ∈ (gateAt C c).inputs) →
          ∃ Y : Finset (Fin N), Y.card ≤ q ∧
            (substReads C (N + N) c σ).eval (incidenceInput (zeroSet S Y) Y) = true) →
        100 * crossCount (N + N) (Finset.univ.image (Fin.natAdd N)) C < N * q →
        4 * N * q < 5 * Fintype.card {e : Fin N × Fin N // e.1 ∈ S e.2 ∧
          lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
          lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false} →
        N * q ≤ 100 * C.size) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * q ≤ 100 * C.size := by
  classical
  intro q N I instI C₀ hq hN hcol huniq hmono₀ hacc₀ hsound₀
  let n : ℕ := N + N
  let S : Fin N → Finset (Fin N) := fun l => Finset.univ.filter (fun p => I p l)
  have hS_mem : ∀ (p l : Fin N), p ∈ S l ↔ I p l := by
    intro p l; simp [S]
  have hS_card : ∀ l : Fin N, (S l).card = q + 1 := hcol
  have hS_uniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, p ∈ S l ∧ r ∈ S l := by
    intro p r hne
    simpa only [hS_mem] using huniq p r hne
  have hNpos : 7 ≤ N := by nlinarith
  have hcast_ne_nat : ∀ (p l : Fin N), Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro p l h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega

  -- Definition-equality helpers (avoiding simp-generated .eq_1 lemmas)
  have heval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have heval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have hsize_eq : ∀ D : Circuit, D.size = D.gates.length := fun _ => rfl
  have hconeStep_eq : ∀ (cs : List (List ℕ)) (g : Gate),
      PEqualNP.EdgeOwnership.coneStep n cs g =
        cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => (w - n) :: cs.getD (w - n) [])] := fun _ _ => rfl
  have hincDef : ∀ (X Y : Finset (Fin N)),
      incidenceInput X Y =
        List.ofFn (fun p : Fin N => decide (p ∈ X)) ++ List.ofFn (fun l : Fin N => decide (l ∈ Y)) :=
    fun _ _ => rfl
  have hsubstReads_gates : ∀ (D : Circuit) (c : ℕ) (σ : ℕ → ℕ),
      (substReads D n c σ).gates =
        D.gates.mapIdx fun r g => ⟨g.op, g.inputs.map fun i => if i = n + c then σ r else i⟩ :=
    fun _ _ _ => rfl

  -- Wire evaluation helpers
  let stepW : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hwires_eq : ∀ (D : Circuit) (x : List Bool), D.wires x = D.gates.foldl stepW x :=
    fun _ _ => rfl
  have hfold_snoc : ∀ (gs : List Gate) (g : Gate) (x : List Bool),
      (gs ++ [g]).foldl stepW x = stepW (gs.foldl stepW x) g := by
    intro gs g x; simp [List.foldl_append]
  have hfold_len : ∀ (gs : List Gate) (x : List Bool),
      (gs.foldl stepW x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs g ih =>
      rw [hfold_snoc]
      simp only [stepW, List.length_append, List.length_singleton, ih]
      omega
  have hfold_getD_lt : ∀ (gs : List Gate) (x : List Bool) (i : ℕ),
      i < x.length → (gs.foldl stepW x).getD i false = x.getD i false := by
    intro gs x i hi
    induction gs using List.reverseRecOn with
    | nil => rfl
    | append_singleton gs g ih =>
      rw [hfold_snoc]
      have hlt : i < (gs.foldl stepW x).length := by rw [hfold_len]; omega
      simp only [stepW]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
        ← List.getD_eq_getElem?_getD, ih]
  have hfold_getD_take : ∀ (gs : List Gate) (x : List Bool) (j i : ℕ),
      j ≤ gs.length → i < x.length + j →
      (gs.foldl stepW x).getD i false = ((gs.take j).foldl stepW x).getD i false := by
    intro gs x j i hj hi
    conv_lhs => rw [← List.take_append_drop j gs, List.foldl_append]
    rw [hfold_getD_lt (gs.drop j) _ i (by rw [hfold_len, List.length_take, Nat.min_eq_left hj]; exact hi)]
  have hfold_getD_gate : ∀ (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate),
      gs[j]? = some g →
      (gs.foldl stepW x).getD (x.length + j) false =
        g.op.eval (g.inputs.map fun i => ((gs.take j).foldl stepW x).getD i false) := by
    intro gs x j g hg
    have hj : j < gs.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hg
      cases hg
    have htake : gs.take (j + 1) = gs.take j ++ [g] := by
      rw [List.take_add_one, hg]; simp
    rw [hfold_getD_take gs x (j + 1) (x.length + j) (by omega) (by omega), htake, hfold_snoc]
    have hlen : ((gs.take j).foldl stepW x).length = x.length + j := by
      rw [hfold_len, List.length_take, Nat.min_eq_left (by omega)]
    simp only [stepW]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]), hlen]
    simp
  have hfold_getD_ge : ∀ (gs : List Gate) (x : List Bool) (i : ℕ),
      x.length + gs.length ≤ i → (gs.foldl stepW x).getD i false = false := by
    intro gs x i hi
    apply List.getD_eq_default
    rw [hfold_len]; exact hi

  -- Monotonicity of Monotone2 circuits
  have hgate_mono : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) →
      ∀ (w₁ w₂ : List Bool), (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      g.op.eval (g.inputs.map fun i => w₁.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w₂.getD i false) = true := by
    intro g hg w₁ w₂ hle h1
    rcases hg with hop | hop
    · rw [hop] at h1 ⊢
      simp only [heval_and, List.all_eq_true, List.mem_map, id] at h1 ⊢
      rintro b ⟨i, hi, rfl⟩
      exact hle i (h1 _ ⟨i, hi, rfl⟩)
    · rw [hop] at h1 ⊢
      simp only [heval_or, List.any_eq_true, List.mem_map, id] at h1 ⊢
      rcases h1 with ⟨b, ⟨i, hi, rfl⟩, hb⟩
      exact ⟨_, ⟨i, hi, rfl⟩, hle i hb⟩
  have hwires_mono : ∀ (D : Circuit), Monotone2 D →
      ∀ (x y : List Bool), x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ w, (D.wires x).getD w false = true → (D.wires y).getD w false = true := by
    intro D hM x y hlen hxy
    have hfold : ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
        ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
        (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
        ∀ i, (gs.foldl stepW w₁).getD i false = true → (gs.foldl stepW w₂).getD i false = true := by
      intro gs hgs
      induction gs with
      | nil => intro w₁ w₂ _ h i hi; exact h i hi
      | cons g gs ih =>
        intro w₁ w₂ hl h
        simp only [List.foldl_cons]
        apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
        · simp [stepW, hl]
        · intro i hi
          by_cases hlt : i < w₁.length
          · simp only [stepW] at hi ⊢
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
              ← List.getD_eq_getElem?_getD] at hi
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
              ← List.getD_eq_getElem?_getD]
            exact h i hi
          · by_cases heq : i = w₁.length
            · subst heq
              simp only [stepW] at hi ⊢
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl] at hi
              simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
              rw [List.getD_eq_getElem?_getD, hl, List.getElem?_append_right le_rfl]
              simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              exact hgate_mono g (hgs g List.mem_cons_self) w₁ w₂ h hi
            · have hge : (stepW w₁ g).length ≤ i := by simp [stepW]; omega
              rw [List.getD_eq_default _ _ hge] at hi
              cases hi
    exact hfold D.gates (fun g hg => (hM g hg).1) x y hlen hxy

  -- Promise predicate and extraction of a promise-minimal circuit C
  let Valid : Circuit → Prop := fun D =>
    Monotone2 D ∧
    (∀ p l : Fin N, I p l →
      circuitFun n D (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) ∧
    (∀ z : Fin n → Bool,
      (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun n D z = false)
  have hexMin : ∃ s : ℕ, ∃ D : Circuit, D.size = s ∧ Valid D :=
    ⟨C₀.size, C₀, rfl, hmono₀, hacc₀, hsound₀⟩
  obtain ⟨C, hCsizeEq, hCmono, hCacc, hCsound⟩ := Nat.find_spec hexMin
  have hCmin : ∀ D : Circuit, Valid D → C.size ≤ D.size := by
    intro D hD
    rw [hCsizeEq]
    exact Nat.find_min' hexMin ⟨D, rfl, hD⟩
  have hCle0 : C.size ≤ C₀.size := hCmin C₀ ⟨hmono₀, hacc₀, hsound₀⟩
  suffices hGoal : N * q ≤ 100 * C.size from hGoal.trans (Nat.mul_le_mul_left 100 hCle0)

  -- Basic facts about C
  have h0_lt_N : 0 < N := by omega
  have hex_inc : ∃ p l : Fin N, I p l := by
    let l0 : Fin N := ⟨0, h0_lt_N⟩
    have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p l0)).card := by
      rw [hcol l0]; omega
    obtain ⟨p0, hp0⟩ := Finset.card_pos.mp hpos
    exact ⟨p0, l0, (Finset.mem_filter.mp hp0).2⟩
  have hpoint_has_line : ∀ p : Fin N, ∃ l : Fin N, I p l := by
    intro p
    let p' : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, h0_lt_N⟩
    have hne : p ≠ p' := by
      intro h
      have hv := congrArg Fin.val h
      by_cases hp0 : p.val = 0 <;> simp [p', hp0] at hv
    obtain ⟨l, ⟨hpl, _⟩, _⟩ := huniq p p' hne
    exact ⟨l, hpl⟩
  have hline_has_point : ∀ l : Fin N, ∃ p : Fin N, I p l := by
    intro l
    have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p l)).card := by
      rw [hcol l]; omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    exact ⟨p, (Finset.mem_filter.mp hp).2⟩
  have hsingle_off : ∀ w : Fin n, circuitFun n C (fun k => decide (k = w)) = false := by
    intro w
    apply hCsound
    · have hsub : Finset.univ.filter (fun l : Fin N => decide (Fin.natAdd N l = w) = true) ⊆
          (if hw : N ≤ w.val then ({⟨w.val - N, by omega⟩} : Finset (Fin N)) else ∅) := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hl
        have hv := congrArg Fin.val hl
        simp only [Fin.val_natAdd] at hv
        have hge : N ≤ w.val := by omega
        simp only [hge, ↓reduceDIte, Finset.mem_singleton]
        exact Fin.ext (by simp; omega)
      have hcard_le : (if hw : N ≤ w.val then ({⟨w.val - N, by omega⟩} : Finset (Fin N)) else ∅).card ≤ 1 := by
        split_ifs <;> simp
      exact (Finset.card_le_card hsub).trans (hcard_le.trans (by omega))
    · rintro ⟨p, l, _, hp, hl⟩
      simp only [decide_eq_true_eq] at hp hl
      exact hcast_ne_nat p l (hp.trans hl.symm)
  have hfalse_off : circuitFun n C (fun _ => false) = false := by
    apply hCsound
    · simp
    · rintro ⟨p, l, _, hp, _⟩; cases hp

  -- Output bounds: n <= C.output < n + C.size
  have hCout_lt : C.output < n + C.size := by
    by_contra hge
    obtain ⟨p0, l0, hI0⟩ := hex_inc
    have h1 := hCacc p0 l0 hI0
    unfold circuitFun Circuit.eval at h1
    rw [hwires_eq, hfold_getD_ge C.gates _ C.output (by simp only [hsize_eq, List.length_ofFn] at hge ⊢; omega)] at h1
    cases h1
  have hCout_ge : n ≤ C.output := by
    by_contra hlt
    have hlt' : C.output < n := by omega
    let w0 : Fin n := ⟨C.output, hlt'⟩
    have h0 := hsingle_off w0
    unfold circuitFun Circuit.eval at h0
    rw [hwires_eq, hfold_getD_lt C.gates _ C.output (by simp; exact hlt')] at h0
    rw [List.getD_eq_getElem _ _ (by simp; exact hlt'), List.getElem_ofFn] at h0
    simp [w0] at h0

  -- Universal gate deletion with wire replacement:
  -- replace n + c by (if c < r then σ r else n + D.gates.length) in gate r,
  -- replace output n + c by outRep, erase gate c, shift wires > n + c down by 1.
  let shiftWire : ℕ → ℕ → ℕ := fun c w => if w < n + c then w else w - 1
  let substDel : Circuit → ℕ → (ℕ → ℕ) → ℕ → Circuit := fun D c σ outRep =>
    let gs1 : List Gate := D.gates.mapIdx fun r g =>
      ⟨g.op, g.inputs.map fun i =>
        if i = n + c then (if c < r then σ r else n + D.gates.length) else i⟩
    let gs2 : List Gate := (gs1.eraseIdx c).map fun g =>
      ⟨g.op, g.inputs.map (shiftWire c)⟩
    let out1 : ℕ := if D.output = n + c then outRep else D.output
    ⟨gs2, shiftWire c out1⟩
  have hsubstDel_mono : ∀ (D : Circuit) (c : ℕ) (σ : ℕ → ℕ) (outRep : ℕ),
      Monotone2 D → Monotone2 (substDel D c σ outRep) := by
    intro D c σ outRep hM g hg
    simp only [substDel, List.mem_map] at hg
    rcases hg with ⟨g1, hg1, rfl⟩
    have hg1' := List.mem_of_mem_eraseIdx hg1
    rw [List.mem_mapIdx] at hg1'
    rcases hg1' with ⟨r, hr, rfl⟩
    have hm := hM _ (List.getElem_mem hr)
    exact ⟨hm.1, by simpa using hm.2⟩
  have hsubstDel_size : ∀ (D : Circuit) (c : ℕ) (σ : ℕ → ℕ) (outRep : ℕ),
      c < D.gates.length → (substDel D c σ outRep).size = D.size - 1 := by
    intro D c σ outRep hc
    simp [substDel, hsize_eq, List.length_eraseIdx, hc]

  -- Case A + B combined: if gate c is equivalent to wire v (where v < n + c or v = n + C.gates.length)
  -- on all inputs of length n, then C cannot be promise-minimal.
  have hno_equiv : ∀ (c v : ℕ), c < C.gates.length →
      (v < n + c ∨ v = n + C.gates.length) →
      (∀ x : List Bool, x.length = n → (C.wires x).getD (n + c) false = (C.wires x).getD v false) →
      False := by
    intro c v hc hv heqv
    let D := substDel C c (fun _ => v) v
    have hDmono : Monotone2 D := hsubstDel_mono C c (fun _ => v) v hCmono
    have hDsize : D.size = C.size - 1 := hsubstDel_size C c (fun _ => v) v hc
    have hDlen : D.gates.length = C.gates.length - 1 := hDsize
    have hDwires : ∀ (x : List Bool), x.length = n →
        ∀ w < n + C.gates.length, w ≠ n + c →
          (D.wires x).getD (shiftWire c w) false = (C.wires x).getD w false := by
      intro x hxlen w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hne
        by_cases hwin : w < n
        · have hsh : shiftWire c w = w := by simp [shiftWire]; omega
          rw [hsh, hwires_eq, hwires_eq, hfold_getD_lt _ _ w (by omega),
            hfold_getD_lt _ _ w (by omega)]
        · let j : ℕ := w - n
          have hwj : w = n + j := by omega
          have hjlt : j < C.gates.length := by omega
          have hjne : j ≠ c := by omega
          let j' : ℕ := if j < c then j else j - 1
          have hj'lt : j' < D.gates.length := by
            rw [hDlen]; simp only [j']; split_ifs <;> omega
          have hsh : shiftWire c w = n + j' := by
            simp only [shiftWire, j']; rw [hwj]; split_ifs <;> omega
          let gs1 : List Gate := C.gates.mapIdx fun r g =>
            ⟨g.op, g.inputs.map fun i =>
              if i = n + c then (if c < r then v else n + C.gates.length) else i⟩
          have hgs1_get : gs1[j]? = some ⟨(C.gates[j]).op,
              (C.gates[j]).inputs.map fun i =>
                if i = n + c then (if c < j then v else n + C.gates.length) else i⟩ := by
            simp [gs1, hjlt]
          have hDget : D.gates[j']? = some ⟨(C.gates[j]).op,
              ((C.gates[j]).inputs.map fun i =>
                if i = n + c then (if c < j then v else n + C.gates.length) else i).map (shiftWire c)⟩ := by
            have herase : (gs1.eraseIdx c)[j']? = gs1[j]? := by
              by_cases hjc : j < c
              · have hj'eq : j' = j := if_pos hjc
                rw [hj'eq, List.getElem?_eraseIdx_of_lt hjc]
              · have hj'eq : j' = j - 1 := if_neg hjc
                have hge : c ≤ j' := by omega
                rw [List.getElem?_eraseIdx_of_ge hge]
                have : j' + 1 = j := by omega
                rw [this]
            simp only [D, substDel, List.getElem?_map]
            change Option.map (fun g : Gate => ({ op := g.op, inputs := g.inputs.map (shiftWire c) } : Gate))
              ((gs1.eraseIdx c)[j']?) = _
            rw [herase, hgs1_get]
            rfl
          have hCget : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem hjlt
          rw [hsh, hwj, hwires_eq, hwires_eq, ← hxlen]
          rw [hfold_getD_gate D.gates x j' _ hDget]
          rw [hfold_getD_gate C.gates x j _ hCget]
          congr 1
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro i _
          simp only [Function.comp_apply]
          by_cases hic : i = n + c
          · subst hic
            rw [if_pos rfl]
            by_cases hcj : c < j
            · rw [if_pos hcj]
              rw [← hfold_getD_take C.gates x j (n + c) (by omega) (by rw [hxlen]; omega)]
              rw [← hwires_eq, heqv x hxlen]
              rcases hv with hvlt | hveq
              · have hshv : shiftWire c v = v := by simp [shiftWire]; omega
                have hj'v : v < n + j' := by simp only [j']; rw [if_neg (by omega)]; omega
                rw [hshv, ← hfold_getD_take D.gates x j' v (by omega) (by rw [hxlen]; exact hj'v)]
                rw [← hwires_eq]
                have hih := ih v (by omega) (by omega) (by omega)
                rw [hshv] at hih
                exact hih
              · subst hveq
                have hshv : shiftWire c (n + C.gates.length) = n + C.gates.length - 1 := by
                  simp [shiftWire]; omega
                rw [hshv]
                trans false
                · exact hfold_getD_ge _ _ _ (by rw [hxlen, List.length_take, Nat.min_eq_left (by omega)]; omega)
                · rw [hwires_eq]
                  exact (hfold_getD_ge _ _ _ (by rw [hxlen])).symm
            · rw [if_neg hcj]
              have hshv : shiftWire c (n + C.gates.length) = n + C.gates.length - 1 := by
                simp [shiftWire]; omega
              rw [hshv]
              trans false
              · exact hfold_getD_ge _ _ _ (by rw [hxlen, List.length_take, Nat.min_eq_left (by omega)]; omega)
              · exact (hfold_getD_ge _ _ _ (by rw [hxlen, List.length_take, Nat.min_eq_left (by omega)]; omega)).symm
          · rw [if_neg hic]
            by_cases hilt : i < n + j
            · have hshlt : shiftWire c i < n + j' := by
                simp only [shiftWire, j']
                by_cases hjc : j < c
                · rw [if_pos hjc, if_pos (by omega)]; exact hilt
                · rw [if_neg hjc]; split_ifs <;> omega
              rw [← hfold_getD_take D.gates x j' _ (by omega) (by rw [hxlen]; exact hshlt)]
              rw [← hfold_getD_take C.gates x j _ (by omega) (by rw [hxlen]; exact hilt)]
              exact ih i (by omega) (by omega) hic
            · have hshge : n + j' ≤ shiftWire c i := by
                simp only [shiftWire, j']
                by_cases hjc : j < c
                · rw [if_pos hjc]; split_ifs <;> omega
                · rw [if_neg hjc]; split_ifs <;> omega
              trans false
              · exact hfold_getD_ge _ _ _ (by rw [hxlen, List.length_take, Nat.min_eq_left (by omega)]; exact hshge)
              · exact (hfold_getD_ge _ _ _ (by rw [hxlen, List.length_take, Nat.min_eq_left (by omega)]; omega)).symm
    have hDeval : ∀ z : Fin n → Bool, circuitFun n D z = circuitFun n C z := by
      intro z
      unfold circuitFun Circuit.eval
      have hxlen : (List.ofFn z).length = n := List.length_ofFn
      change (D.wires (List.ofFn z)).getD (shiftWire c (if C.output = n + c then v else C.output)) false = _
      by_cases hout : C.output = n + c
      · rw [if_pos hout, hout, heqv (List.ofFn z) hxlen]
        rcases hv with hvlt | hveq
        · exact hDwires (List.ofFn z) hxlen v (by omega) (by omega)
        · subst hveq
          have hshv : shiftWire c (n + C.gates.length) = n + C.gates.length - 1 := by
            simp [shiftWire]; omega
          rw [hshv, hwires_eq, hwires_eq]
          trans false
          · exact hfold_getD_ge D.gates _ _ (by rw [hxlen, hDlen]; omega)
          · exact (hfold_getD_ge C.gates _ _ (by rw [hxlen])).symm
      · rw [if_neg hout]
        exact hDwires (List.ofFn z) hxlen C.output hCout_lt hout
    have hDvalid : Valid D := by
      refine ⟨hDmono, ?_, ?_⟩
      · intro p l hI; rw [hDeval]; exact hCacc p l hI
      · intro z hle hno; rw [hDeval]; exact hCsound z hle hno
    have hle := hCmin D hDvalid
    have hCpos : 0 < C.size := by change 0 < C.gates.length; omega
    omega

  -- Case C: no gate c can evaluate to constant true on all inputs of length n
  have hno_true : ∀ (c : ℕ), c < C.gates.length →
      (∀ x : List Bool, x.length = n → (C.wires x).getD (n + c) false = true) → False := by
    intro c hc htrue
    have hout_ne : C.output ≠ n + c := by
      intro heq
      have h0 := hfalse_off
      unfold circuitFun Circuit.eval at h0
      rw [heq, htrue _ List.length_ofFn] at h0
      cases h0
    let fixGate : ℕ → Gate → Gate := fun r g =>
      if c < r then
        if g.op = GateOp.or ∧ n + c ∈ g.inputs then ⟨GateOp.and, []⟩
        else ⟨g.op, g.inputs.filter (fun i => decide (i ≠ n + c))⟩
      else ⟨g.op, g.inputs.map fun i => if i = n + c then n + C.gates.length else i⟩
    let gs1 : List Gate := C.gates.mapIdx fixGate
    let D : Circuit := ⟨(gs1.eraseIdx c).map fun g => ⟨g.op, g.inputs.map (shiftWire c)⟩,
      shiftWire c C.output⟩
    have hDmono : Monotone2 D := by
      intro g hg
      simp only [D, List.mem_map] at hg
      rcases hg with ⟨g1, hg1, rfl⟩
      have hg1' := List.mem_of_mem_eraseIdx hg1
      rw [List.mem_mapIdx] at hg1'
      rcases hg1' with ⟨r, hr, rfl⟩
      have hm := hCmono _ (List.getElem_mem hr)
      simp only [fixGate]
      split_ifs with h1 h2
      · exact ⟨Or.inl rfl, by simp⟩
      · refine ⟨hm.1, ?_⟩
        simp only [List.length_map]
        exact (List.length_filter_le _ _).trans hm.2
      · exact ⟨hm.1, by simpa using hm.2⟩
    have hDlen : D.gates.length = C.gates.length - 1 := by
      simp [D, gs1, List.length_eraseIdx, hc]
    have hDwires : ∀ (x : List Bool), x.length = n →
        ∀ w < n + C.gates.length, w ≠ n + c →
          (D.wires x).getD (shiftWire c w) false = (C.wires x).getD w false := by
      intro x hxlen w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hne
        by_cases hwin : w < n
        · have hsh : shiftWire c w = w := by simp [shiftWire]; omega
          rw [hsh, hwires_eq, hwires_eq, hfold_getD_lt _ _ w (by omega),
            hfold_getD_lt _ _ w (by omega)]
        · let j : ℕ := w - n
          have hwj : w = n + j := by omega
          have hjlt : j < C.gates.length := by omega
          have hjne : j ≠ c := by omega
          let j' : ℕ := if j < c then j else j - 1
          have hj'lt : j' < D.gates.length := by
            rw [hDlen]; simp only [j']; split_ifs <;> omega
          have hsh : shiftWire c w = n + j' := by
            simp only [shiftWire, j']; rw [hwj]; split_ifs <;> omega
          have hgs1_get : gs1[j]? = some (fixGate j (C.gates[j])) := by
            simp [gs1, hjlt]
          have hDget : D.gates[j']? = some ⟨(fixGate j (C.gates[j])).op,
              (fixGate j (C.gates[j])).inputs.map (shiftWire c)⟩ := by
            have herase : (gs1.eraseIdx c)[j']? = gs1[j]? := by
              by_cases hjc : j < c
              · have hj'eq : j' = j := if_pos hjc
                rw [hj'eq, List.getElem?_eraseIdx_of_lt hjc]
              · have hj'eq : j' = j - 1 := if_neg hjc
                have hge : c ≤ j' := by omega
                rw [List.getElem?_eraseIdx_of_ge hge]
                have : j' + 1 = j := by omega
                rw [this]
            simp only [D, List.getElem?_map]
            rw [herase, hgs1_get]
            rfl
          have hCget : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem hjlt
          have hwire_i : ∀ i : ℕ, i ≠ n + c →
              ((D.gates.take j').foldl stepW x).getD (shiftWire c i) false =
                ((C.gates.take j).foldl stepW x).getD i false := by
            intro i hic
            by_cases hilt : i < n + j
            · have hshlt : shiftWire c i < n + j' := by
                simp only [shiftWire, j']
                by_cases hjc : j < c
                · rw [if_pos hjc, if_pos (by omega)]; exact hilt
                · rw [if_neg hjc]; split_ifs <;> omega
              rw [← hfold_getD_take D.gates x j' _ (by omega) (by rw [hxlen]; exact hshlt)]
              rw [← hfold_getD_take C.gates x j _ (by omega) (by rw [hxlen]; exact hilt)]
              exact ih i (by omega) (by omega) hic
            · have hshge : n + j' ≤ shiftWire c i := by
                simp only [shiftWire, j']
                by_cases hjc : j < c
                · rw [if_pos hjc]; split_ifs <;> omega
                · rw [if_neg hjc]; split_ifs <;> omega
              rw [hfold_getD_ge _ _ _ (by rw [hxlen, List.length_take, Nat.min_eq_left (by omega)]; exact hshge)]
              rw [hfold_getD_ge _ _ _ (by rw [hxlen, List.length_take, Nat.min_eq_left (by omega)]; omega)]
          rw [hsh, hwj, hwires_eq, hwires_eq, ← hxlen]
          rw [hfold_getD_gate D.gates x j' _ hDget]
          rw [hfold_getD_gate C.gates x j _ hCget]
          simp only [fixGate]
          by_cases hcj : c < j
          · rw [if_pos hcj]
            by_cases hor : (C.gates[j]).op = GateOp.or ∧ n + c ∈ (C.gates[j]).inputs
            · rw [if_pos hor]
              simp only [heval_and, List.map_nil, List.all_nil]
              rw [hor.1, heval_or]
              symm
              simp only [List.any_eq_true, List.mem_map, id]
              refine ⟨true, ⟨n + c, hor.2, ?_⟩, rfl⟩
              rw [← hfold_getD_take C.gates x j (n + c) (by omega) (by rw [hxlen]; omega)]
              exact htrue x hxlen
            · rw [if_neg hor]
              rcases (hCmono _ (List.getElem_mem hjlt)).1 with hop | hop
              · rw [hop]
                apply Bool.eq_iff_iff.mpr
                simp only [heval_and, List.map_map, List.all_eq_true, List.mem_map, List.mem_filter,
                  decide_eq_true_eq, Function.comp_apply, id]
                constructor
                · rintro hL b ⟨i, hi, rfl⟩
                  by_cases hic : i = n + c
                  · subst hic
                    rw [← hfold_getD_take C.gates x j (n + c) (by omega) (by rw [hxlen]; omega)]
                    exact htrue x hxlen
                  · rw [← hwire_i i hic]
                    exact hL _ ⟨i, ⟨hi, hic⟩, rfl⟩
                · rintro hR b ⟨i, ⟨hi, hic⟩, rfl⟩
                  rw [hwire_i i hic]
                  exact hR _ ⟨i, hi, rfl⟩
              · rw [hop]
                have hnotmem : n + c ∉ (C.gates[j]).inputs := fun hm => hor ⟨hop, hm⟩
                apply Bool.eq_iff_iff.mpr
                simp only [heval_or, List.map_map, List.any_eq_true, List.mem_map, List.mem_filter,
                  decide_eq_true_eq, Function.comp_apply, id]
                constructor
                · rintro ⟨b, ⟨i, ⟨hi, hic⟩, rfl⟩, hb⟩
                  exact ⟨_, ⟨i, hi, rfl⟩, by rwa [← hwire_i i hic]⟩
                · rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
                  have hic : i ≠ n + c := fun he => hnotmem (he ▸ hi)
                  exact ⟨_, ⟨i, ⟨hi, hic⟩, rfl⟩, by rwa [hwire_i i hic]⟩
          · rw [if_neg hcj]
            congr 1
            rw [List.map_map, List.map_map]
            apply List.map_congr_left
            intro i _
            simp only [Function.comp_apply]
            by_cases hic : i = n + c
            · subst hic
              rw [if_pos rfl]
              have hshv : shiftWire c (n + C.gates.length) = n + C.gates.length - 1 := by
                simp [shiftWire]; omega
              rw [hshv]
              rw [hfold_getD_ge _ _ _ (by rw [hxlen, List.length_take, Nat.min_eq_left (by omega)]; omega)]
              rw [hfold_getD_ge _ _ _ (by rw [hxlen, List.length_take, Nat.min_eq_left (by omega)]; omega)]
            · rw [if_neg hic]
              exact hwire_i i hic
    have hDeval : ∀ z : Fin n → Bool, circuitFun n D z = circuitFun n C z := by
      intro z
      unfold circuitFun Circuit.eval
      exact hDwires (List.ofFn z) List.length_ofFn C.output hCout_lt hout_ne
    have hDvalid : Valid D := by
      refine ⟨hDmono, ?_, ?_⟩
      · intro p l hI; rw [hDeval]; exact hCacc p l hI
      · intro z hle hno; rw [hDeval]; exact hCsound z hle hno
    have hle := hCmin D hDvalid
    have hDsize : D.size = C.size - 1 := hDlen
    have hCpos : 0 < C.size := by change 0 < C.gates.length; omega
    omega

  -- Deduce full structural normal form of C: strict fan-in-2, reads back, Nodup
  have hCstrict : ∀ (c : ℕ) (hc : c < C.gates.length),
      ∃ a b : ℕ, (C.gates[c]'hc).inputs = [a, b] ∧ a ≠ b ∧ a < n + c ∧ b < n + c := by
    intro c hc
    have hm := hCmono _ (List.getElem_mem hc)
    have hCget : C.gates[c]? = some (C.gates[c]'hc) := List.getElem?_eq_getElem hc
    have hlen2 : (C.gates[c]'hc).inputs.length ≤ 2 := hm.2
    generalize hlist : (C.gates[c]'hc).inputs = inp
    cases inp with
    | nil =>
      exfalso
      rcases hm.1 with hop | hop
      · apply hno_true c hc
        intro x hxlen
        rw [hwires_eq, ← hxlen, hfold_getD_gate C.gates x c _ hCget, hop, hlist]
        rfl
      · apply hno_equiv c (n + C.gates.length) hc (Or.inr rfl)
        intro x hxlen
        rw [hwires_eq, ← hxlen, hfold_getD_gate C.gates x c _ hCget, hop, hlist]
        rw [hfold_getD_ge C.gates x (x.length + C.gates.length) (by omega)]
        rfl
    | cons a rest =>
      cases rest with
      | nil =>
        exfalso
        by_cases ha : a < n + c
        · apply hno_equiv c a hc (Or.inl ha)
          intro x hxlen
          rw [hwires_eq, ← hxlen, hfold_getD_gate C.gates x c _ hCget, hlist]
          simp only [List.map_cons, List.map_nil]
          rw [← hfold_getD_take C.gates x c a (by omega) (by omega)]
          rcases hm.1 with hop | hop
          · rw [hop, heval_and]; simp
          · rw [hop, heval_or]; simp
        · apply hno_equiv c (n + C.gates.length) hc (Or.inr rfl)
          intro x hxlen
          rw [hwires_eq, ← hxlen, hfold_getD_gate C.gates x c _ hCget, hlist]
          simp only [List.map_cons, List.map_nil]
          rw [hfold_getD_ge (C.gates.take c) x a (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega)]
          rw [hfold_getD_ge C.gates x (x.length + C.gates.length) (by omega)]
          rcases hm.1 with hop | hop
          · rw [hop, heval_and]; simp
          · rw [hop, heval_or]; simp
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          by_cases ha : a < n + c
          · by_cases hb : b < n + c
            · by_cases hab : a = b
              · exfalso
                subst hab
                apply hno_equiv c a hc (Or.inl ha)
                intro x hxlen
                rw [hwires_eq, ← hxlen, hfold_getD_gate C.gates x c _ hCget, hlist]
                simp only [List.map_cons, List.map_nil]
                rw [← hfold_getD_take C.gates x c a (by omega) (by omega)]
                rcases hm.1 with hop | hop
                · rw [hop, heval_and]; simp
                · rw [hop, heval_or]; simp
              · exact ⟨a, b, rfl, hab, ha, hb⟩
            · exfalso
              rcases hm.1 with hop | hop
              · apply hno_equiv c (n + C.gates.length) hc (Or.inr rfl)
                intro x hxlen
                rw [hwires_eq, ← hxlen, hfold_getD_gate C.gates x c _ hCget, hlist, hop, heval_and]
                simp only [List.map_cons, List.map_nil]
                rw [hfold_getD_ge (C.gates.take c) x b (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega)]
                rw [hfold_getD_ge C.gates x (x.length + C.gates.length) (by omega)]
                simp
              · apply hno_equiv c a hc (Or.inl ha)
                intro x hxlen
                rw [hwires_eq, ← hxlen, hfold_getD_gate C.gates x c _ hCget, hlist, hop, heval_or]
                simp only [List.map_cons, List.map_nil]
                rw [hfold_getD_ge (C.gates.take c) x b (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega)]
                rw [← hfold_getD_take C.gates x c a (by omega) (by omega)]
                simp
          · exfalso
            rcases hm.1 with hop | hop
            · apply hno_equiv c (n + C.gates.length) hc (Or.inr rfl)
              intro x hxlen
              rw [hwires_eq, ← hxlen, hfold_getD_gate C.gates x c _ hCget, hlist, hop, heval_and]
              simp only [List.map_cons, List.map_nil]
              rw [hfold_getD_ge (C.gates.take c) x a (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega)]
              rw [hfold_getD_ge C.gates x (x.length + C.gates.length) (by omega)]
              simp
            · by_cases hb : b < n + c
              · apply hno_equiv c b hc (Or.inl hb)
                intro x hxlen
                rw [hwires_eq, ← hxlen, hfold_getD_gate C.gates x c _ hCget, hlist, hop, heval_or]
                simp only [List.map_cons, List.map_nil]
                rw [hfold_getD_ge (C.gates.take c) x a (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega)]
                rw [← hfold_getD_take C.gates x c b (by omega) (by omega)]
                simp
              · apply hno_equiv c (n + C.gates.length) hc (Or.inr rfl)
                intro x hxlen
                rw [hwires_eq, ← hxlen, hfold_getD_gate C.gates x c _ hCget, hlist, hop, heval_or]
                simp only [List.map_cons, List.map_nil]
                rw [hfold_getD_ge (C.gates.take c) x a (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega)]
                rw [hfold_getD_ge (C.gates.take c) x b (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega)]
                rw [hfold_getD_ge C.gates x (x.length + C.gates.length) (by omega)]
                simp
        | cons _ _ =>
          rw [hlist] at hlen2; simp at hlen2

  have hCAO2 : IsAO2 n C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rcases (hCmono g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro j hj i hi
      have hgate : gateAt C j = C.gates[j] := by
        unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
      rw [hgate] at hi
      obtain ⟨a, b, hab, _, ha, hb⟩ := hCstrict j hj
      rw [hab] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨a, b, hab, _, _, _⟩ := hCstrict j hj
      rw [hab]; rfl

  have hCNodup : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨a, b, hab, hne, _, _⟩ := hCstrict j hj
    rw [hab]; simp [hne]

  -- Prove every gate of C is live: liveSize n C = C.size
  have hcones_len : ∀ gs : List Gate, (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs g ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, hconeStep_eq, List.length_append, List.length_singleton, ih]
  have hcones_getD_lt : ∀ (gs : List Gate) (g : Gate) (i : ℕ), i < gs.length →
      ((gs ++ [g]).foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD i [] =
        (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD i [] := by
    intro gs g i hi
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, hconeStep_eq]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hcones_len]; exact hi),
      ← List.getD_eq_getElem?_getD]
  have hcones_getD_take : ∀ (gs : List Gate) (j i : ℕ), j ≤ gs.length → i < j →
      (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD i [] =
        ((gs.take j).foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD i [] := by
    intro gs j i hj hi
    induction gs using List.reverseRecOn with
    | nil => simp at hj; omega
    | append_singleton gs g ih =>
      by_cases hjeq : j = gs.length + 1
      · subst hjeq
        rw [show gs.length + 1 = (gs ++ [g]).length by simp, List.take_length]
      · have hjle : j ≤ gs.length := by simp at hj; omega
        rw [hcones_getD_lt gs g i (by omega), List.take_append_of_le_length hjle]
        exact ih hjle
  have hcones_at : ∀ (j : ℕ) (hj : j < C.gates.length),
      (PEqualNP.EdgeOwnership.cones n C).getD j [] =
        ((C.gates[j]'hj).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
          (fun w => (w - n) :: (PEqualNP.EdgeOwnership.cones n C).getD (w - n) []) := by
    intro j hj
    unfold PEqualNP.EdgeOwnership.cones
    have htake : C.gates.take (j + 1) = C.gates.take j ++ [C.gates[j]'hj] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; simp
    rw [hcones_getD_take C.gates (j + 1) j (by omega) (by omega), htake, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, hconeStep_eq]
    have hlen : ((C.gates.take j).foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = j := by
      rw [hcones_len, List.length_take, Nat.min_eq_left (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    apply List.flatMap_congr
    intro w hw
    rw [List.mem_filter] at hw
    have hwlt : n ≤ w ∧ w < n + j := of_decide_eq_true hw.2
    congr 1
    exact (hcones_getD_take C.gates j (w - n) (by omega) (by omega)).symm
  have hInCone_iff : ∀ (i j : ℕ) (hj : j < C.gates.length),
      (PEqualNP.EdgeOwnership.InCone n C i j ↔
        ∃ w ∈ (C.gates[j]'hj).inputs, n ≤ w ∧ w < n + j ∧
          (i = w - n ∨ PEqualNP.EdgeOwnership.InCone n C i (w - n))) := by
    intro i j hj
    unfold PEqualNP.EdgeOwnership.InCone
    rw [hcones_at j hj, List.mem_flatMap]
    constructor
    · rintro ⟨w, hw, hi⟩
      rw [List.mem_filter] at hw
      have hwb : n ≤ w ∧ w < n + j := of_decide_eq_true hw.2
      rw [List.mem_cons] at hi
      exact ⟨w, hw.1, hwb.1, hwb.2, hi⟩
    · rintro ⟨w, hw, hge, hlt, hi⟩
      refine ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨hge, hlt⟩⟩, List.mem_cons.mpr hi⟩
  have hInCone_step : ∀ (j k : ℕ) (hj : j < C.gates.length), k < j →
      n + k ∈ (C.gates[j]'hj).inputs →
      (j = C.output - n ∨ PEqualNP.EdgeOwnership.InCone n C j (C.output - n)) →
      PEqualNP.EdgeOwnership.InCone n C k (C.output - n) := by
    intro j k hj hkj hmem hlive
    have houtj : C.output - n < C.gates.length := by change C.output - n < C.size; omega
    have hkjCone : PEqualNP.EdgeOwnership.InCone n C k j := by
      rw [hInCone_iff k j hj]
      exact ⟨n + k, hmem, by omega, by omega, Or.inl (by omega)⟩
    rcases hlive with rfl | hcone
    · exact hkjCone
    · -- transitivity of InCone by induction on m
      have htrans : ∀ m < C.gates.length, ∀ a b : ℕ,
          PEqualNP.EdgeOwnership.InCone n C a b → PEqualNP.EdgeOwnership.InCone n C b m →
          PEqualNP.EdgeOwnership.InCone n C a m := by
        intro m
        induction m using Nat.strong_induction_on with
        | ind m ih =>
          intro hm a b hab hbm
          rw [hInCone_iff b m hm] at hbm
          rcases hbm with ⟨w, hw, hge, hlt, hbw⟩
          rw [hInCone_iff a m hm]
          refine ⟨w, hw, hge, hlt, Or.inr ?_⟩
          rcases hbw with rfl | hbc
          · exact hab
          · exact ih (w - n) (by omega) (by omega) a b hab hbc
      exact htrans (C.output - n) houtj k j hkjCone hcone

  have hClive_mem : ∀ c < C.gates.length, c ∈ liveGates n C := by
    intro c hc
    by_contra hnot
    have hnot_out : c ≠ C.output - n := fun he =>
      hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, hCout_ge, Or.inl he⟩)
    have hnot_cone : ¬ PEqualNP.EdgeOwnership.InCone n C c (C.output - n) := fun he =>
      hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, hCout_ge, Or.inr he⟩)
    let D := substDel C c (fun _ => 0) 0
    have hDmono : Monotone2 D := hsubstDel_mono C c (fun _ => 0) 0 hCmono
    have hDlen : D.gates.length = C.gates.length - 1 := hsubstDel_size C c (fun _ => 0) 0 hc
    have hDwires_live : ∀ (x : List Bool), x.length = n →
        ∀ w < n + C.gates.length,
          (w < n ∨ (w - n = C.output - n ∨ PEqualNP.EdgeOwnership.InCone n C (w - n) (C.output - n))) →
          (D.wires x).getD (shiftWire c w) false = (C.wires x).getD w false := by
      intro x hxlen w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hlive
        by_cases hwin : w < n
        · have hsh : shiftWire c w = w := by simp [shiftWire]; omega
          rw [hsh, hwires_eq, hwires_eq, hfold_getD_lt _ _ w (by omega),
            hfold_getD_lt _ _ w (by omega)]
        · have hliveG : w - n = C.output - n ∨ PEqualNP.EdgeOwnership.InCone n C (w - n) (C.output - n) :=
            hlive.resolve_left hwin
          let j : ℕ := w - n
          have hwj : w = n + j := by omega
          have hjlt : j < C.gates.length := by omega
          have hjne : j ≠ c := by
            intro heq
            rcases hliveG with h1 | h2
            · exact hnot_out (heq.symm.trans h1)
            · exact hnot_cone (heq ▸ h2)
          let j' : ℕ := if j < c then j else j - 1
          have hj'lt : j' < D.gates.length := by
            rw [hDlen]; simp only [j']; split_ifs <;> omega
          have hsh : shiftWire c w = n + j' := by
            simp only [shiftWire, j']; rw [hwj]; split_ifs <;> omega
          let gs1 : List Gate := C.gates.mapIdx fun r g =>
            ⟨g.op, g.inputs.map fun i =>
              if i = n + c then (if c < r then 0 else n + C.gates.length) else i⟩
          have hgs1_get : gs1[j]? = some ⟨(C.gates[j]).op,
              (C.gates[j]).inputs.map fun i =>
                if i = n + c then (if c < j then 0 else n + C.gates.length) else i⟩ := by
            simp [gs1, hjlt]
          have hDget : D.gates[j']? = some ⟨(C.gates[j]).op,
              ((C.gates[j]).inputs.map fun i =>
                if i = n + c then (if c < j then 0 else n + C.gates.length) else i).map (shiftWire c)⟩ := by
            have herase : (gs1.eraseIdx c)[j']? = gs1[j]? := by
              by_cases hjc : j < c
              · have hj'eq : j' = j := if_pos hjc
                rw [hj'eq, List.getElem?_eraseIdx_of_lt hjc]
              · have hj'eq : j' = j - 1 := if_neg hjc
                have hge : c ≤ j' := by omega
                rw [List.getElem?_eraseIdx_of_ge hge]
                have : j' + 1 = j := by omega
                rw [this]
            simp only [D, substDel, List.getElem?_map]
            change Option.map (fun g : Gate => ({ op := g.op, inputs := g.inputs.map (shiftWire c) } : Gate))
              ((gs1.eraseIdx c)[j']?) = _
            rw [herase, hgs1_get]
            rfl
          have hCget : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem hjlt
          rw [hsh, hwj, hwires_eq, hwires_eq, ← hxlen]
          rw [hfold_getD_gate D.gates x j' _ hDget]
          rw [hfold_getD_gate C.gates x j _ hCget]
          congr 1
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro i hi
          simp only [Function.comp_apply]
          have hilt : i < n + j := by
            have hgate : gateAt C j = C.gates[j] := by unfold gateAt; rw [List.getD_eq_getElem _ _ hjlt]
            exact hCAO2.2.1 j hjlt i (hgate ▸ hi)
          have hine : i ≠ n + c := by
            intro heq
            subst heq
            have hck := hInCone_step j c hjlt (by omega) hi hliveG
            exact hnot_cone hck
          rw [if_neg hine]
          have hshlt : shiftWire c i < n + j' := by
            simp only [shiftWire, j']
            by_cases hjc : j < c
            · rw [if_pos hjc, if_pos (by omega)]; exact hilt
            · rw [if_neg hjc]; split_ifs <;> omega
          rw [← hfold_getD_take D.gates x j' _ (by omega) (by rw [hxlen]; exact hshlt)]
          rw [← hfold_getD_take C.gates x j _ (by omega) (by rw [hxlen]; exact hilt)]
          apply ih i (by omega) (by omega)
          by_cases hin : i < n
          · exact Or.inl hin
          · refine Or.inr (Or.inr ?_)
            have hmem' : n + (i - n) ∈ (C.gates[j]).inputs := by
              have : n + (i - n) = i := by omega
              rw [this]; exact hi
            exact hInCone_step j (i - n) hjlt (by omega) hmem' hliveG
    have hDeval : ∀ z : Fin n → Bool, circuitFun n D z = circuitFun n C z := by
      intro z
      unfold circuitFun Circuit.eval
      have houtne : C.output ≠ n + c := by omega
      change (D.wires (List.ofFn z)).getD (shiftWire c (if C.output = n + c then 0 else C.output)) false = _
      rw [if_neg houtne]
      exact hDwires_live (List.ofFn z) List.length_ofFn C.output hCout_lt (Or.inr (Or.inl rfl))
    have hDvalid : Valid D := by
      refine ⟨hDmono, ?_, ?_⟩
      · intro p l hI; rw [hDeval]; exact hCacc p l hI
      · intro z hle hno; rw [hDeval]; exact hCsound z hle hno
    have hle := hCmin D hDvalid
    have hDsize : D.size = C.size - 1 := hDlen
    have hCpos : 0 < C.size := by change 0 < C.gates.length; omega
    omega

  have hCliveSize : liveSize n C = C.size := by
    unfold liveSize
    have hEq : liveGates n C = Finset.range C.gates.length := by
      ext j
      simp only [Finset.mem_range]
      constructor
      · intro hj; exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      · intro hj; exact hClive_mem j hj
    rw [hEq, Finset.card_range]
    rfl

  -- Linear sensitivity bound 2 * N <= C.size + 1 (closes q <= 199)
  have hC_lin : n ≤ C.size + 1 := by
    let U : Finset ℕ := (Finset.range C.gates.length).biUnion (fun j => (C.gates[j]?.map Gate.inputs |>.getD []).toFinset)
    have hsub : (Finset.range (n + C.gates.length)).erase C.output ⊆ U := by
      intro w hw
      obtain ⟨hne, hlt⟩ := Finset.mem_erase.mp hw
      rw [Finset.mem_range] at hlt
      by_cases hwin : w < n
      · -- Input w is essential for C, so some gate must read w
        by_contra hnotU
        have hnotread : ∀ (j : ℕ) (hj : j < C.gates.length), w ∉ (C.gates[j]'hj).inputs := by
          intro j hj hmem
          apply hnotU
          rw [Finset.mem_biUnion]
          refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
          simp [List.getElem?_eq_getElem hj, hmem]
        have hindep : ∀ (x y : List Bool), x.length = n → y.length = n →
            (∀ i : ℕ, i ≠ w → x.getD i false = y.getD i false) →
            ∀ u < n + C.gates.length, u ≠ w → (C.wires x).getD u false = (C.wires y).getD u false := by
          intro x y hxlen hylen hxy u
          induction u using Nat.strong_induction_on with
          | ind u ih =>
            intro hu hune
            by_cases huin : u < n
            · rw [hwires_eq, hwires_eq, hfold_getD_lt _ _ u (by omega),
                hfold_getD_lt _ _ u (by omega)]
              exact hxy u hune
            · let j : ℕ := u - n
              have huj : u = n + j := by omega
              have hjlt : j < C.gates.length := by omega
              have hCget : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
              rw [huj, hwires_eq, hwires_eq]
              rw [show n = x.length from hxlen.symm, hfold_getD_gate C.gates x j _ hCget]
              rw [show x.length = y.length from hxlen.trans hylen.symm, hfold_getD_gate C.gates y j _ hCget]
              congr 1
              apply List.map_congr_left
              intro i hi
              have hilt : i < n + j := by
                have hgate : gateAt C j = C.gates[j] := by unfold gateAt; rw [List.getD_eq_getElem _ _ hjlt]
                exact hCAO2.2.1 j hjlt i (hgate ▸ hi)
              have hine : i ≠ w := fun he => hnotread j hjlt (he ▸ hi)
              rw [← hfold_getD_take C.gates x j i (by omega) (by rw [hxlen]; exact hilt)]
              rw [← hfold_getD_take C.gates y j i (by omega) (by rw [hylen]; exact hilt)]
              exact ih i (by omega) (by omega) hine
        -- Exhibit x, y differing only at w where C disagrees
        let wFin : Fin n := ⟨w, hwin⟩
        by_cases hwN : w < N
        · let p : Fin N := ⟨w, hwN⟩
          obtain ⟨l, hIpl⟩ := hpoint_has_line p
          let x : Fin n → Bool := fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
          let y : Fin n → Bool := fun k => decide (k = Fin.natAdd N l)
          have hxy : ∀ i : ℕ, i ≠ w → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
            intro i hi
            by_cases hil : i < n
            · rw [List.getD_eq_getElem _ _ (by simp; exact hil), List.getElem_ofFn,
                List.getD_eq_getElem _ _ (by simp; exact hil), List.getElem_ofFn]
              have hne' : (⟨i, hil⟩ : Fin n) ≠ Fin.castAdd N p := by
                intro he; exact hi (congrArg Fin.val he)
              simp only [x, y, hne', false_or]
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          have heq := hindep (List.ofFn x) (List.ofFn y) List.length_ofFn List.length_ofFn hxy
            C.output hCout_lt (by omega)
          have hx1 : circuitFun n C x = true := hCacc p l hIpl
          have hy0 : circuitFun n C y = false := hsingle_off (Fin.natAdd N l)
          unfold circuitFun Circuit.eval at hx1 hy0
          rw [heq, hy0] at hx1
          cases hx1
        · let l : Fin N := ⟨w - N, by omega⟩
          obtain ⟨p, hIpl⟩ := hline_has_point l
          let x : Fin n → Bool := fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
          let y : Fin n → Bool := fun k => decide (k = Fin.castAdd N p)
          have hxy : ∀ i : ℕ, i ≠ w → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
            intro i hi
            by_cases hil : i < n
            · rw [List.getD_eq_getElem _ _ (by simp; exact hil), List.getElem_ofFn,
                List.getD_eq_getElem _ _ (by simp; exact hil), List.getElem_ofFn]
              have hne' : (⟨i, hil⟩ : Fin n) ≠ Fin.natAdd N l := by
                intro he
                have hv := congrArg Fin.val he
                simp only [Fin.val_natAdd, l] at hv
                omega
              simp only [x, y, hne', or_false]
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          have heq := hindep (List.ofFn x) (List.ofFn y) List.length_ofFn List.length_ofFn hxy
            C.output hCout_lt (by omega)
          have hx1 : circuitFun n C x = true := hCacc p l hIpl
          have hy0 : circuitFun n C y = false := hsingle_off (Fin.castAdd N p)
          unfold circuitFun Circuit.eval at hx1 hy0
          rw [heq, hy0] at hx1
          cases hx1
      · -- Gate wire w = n + c with c != C.output - n is in InCone of C.output - n, so some gate reads w
        let c : ℕ := w - n
        have hwc : w = n + c := by omega
        have hclt : c < C.gates.length := by omega
        have hlive := (Finset.mem_filter.mp (hClive_mem c hclt)).2.2
        have hcone : PEqualNP.EdgeOwnership.InCone n C c (C.output - n) :=
          hlive.resolve_left (by omega)
        have hread : ∀ m < C.gates.length, PEqualNP.EdgeOwnership.InCone n C c m →
            ∃ (j : ℕ) (hj : j < C.gates.length), n + c ∈ (C.gates[j]'hj).inputs := by
          intro m
          induction m using Nat.strong_induction_on with
          | ind m ih =>
            intro hm hcm
            rw [hInCone_iff c m hm] at hcm
            rcases hcm with ⟨u, hu, hge, hlt', hcu⟩
            rcases hcu with heq | hrec
            · have hnu : n + c = u := by omega
              exact ⟨m, hm, hnu.symm ▸ hu⟩
            · exact ih (u - n) (by omega) (by omega) hrec
        obtain ⟨j, hj, hmem⟩ := hread (C.output - n) (by change C.output - n < C.size; omega) hcone
        rw [Finset.mem_biUnion]
        refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
        simp [List.getElem?_eq_getElem hj, hwc, hmem]
    have hcard_le := Finset.card_le_card hsub
    have hU_le : U.card ≤ 2 * C.gates.length := by
      calc U.card
          ≤ ∑ j ∈ Finset.range C.gates.length,
              ((C.gates[j]?.map Gate.inputs |>.getD []).toFinset).card := Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ Finset.range C.gates.length, 2 := by
            apply Finset.sum_le_sum
            intro j hj
            have hjlt : j < C.gates.length := Finset.mem_range.mp hj
            simp only [List.getElem?_eq_getElem hjlt, Option.map_some, Option.getD_some]
            exact (List.toFinset_card_le _).trans (hCmono _ (List.getElem_mem hjlt)).2
        _ = 2 * C.gates.length := by simp [Nat.mul_comm]
    have hL : ((Finset.range (n + C.gates.length)).erase C.output).card = n + C.gates.length - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (show C.output < n + C.gates.length from hCout_lt)),
        Finset.card_range]
    change n ≤ C.gates.length + 1
    omega

  -- Close all 2 <= q <= 199 using 2 * N <= C.size + 1
  by_cases hq200 : q < 200
  · have hq199 : q ≤ 199 := by omega
    have hmul : N * q ≤ N * 199 := Nat.mul_le_mul_left N hq199
    have hN100 : 100 ≤ N * (200 - q) := by
      by_cases hq10 : q < 10
      · have h1 : 191 ≤ 200 - q := by omega
        nlinarith
      · have h2 : 111 ≤ N := by nlinarith
        have h3 : 1 ≤ 200 - q := by omega
        nlinarith
    have : 2 * N ≤ C.size + 1 := by simp only [n] at hC_lin; omega
    nlinarith

  have hq_ge200 : 200 ≤ q := by omega

  -- Bridge between incidenceInput and List.ofFn
  have hincInput_eq : ∀ (X Y : Finset (Fin N)),
      incidenceInput X Y = List.ofFn (fun k : Fin n =>
        Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y)) k) := by
    intro X Y
    apply List.ext_getElem
    · simp only [hincDef, List.length_append, List.length_ofFn, n]
    · intro i h1 h2
      have h2' : i < N + N := by simpa [n] using h2
      simp only [hincDef, List.getElem_ofFn]
      by_cases hi : i < N
      · rw [List.getElem_append_left (by simp; exact hi), List.getElem_ofFn]
        have hk : (⟨i, h2'⟩ : Fin (N + N)) = Fin.castAdd N ⟨i, hi⟩ := Fin.ext rfl
        rw [hk, Fin.addCases_left]
      · rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn]
        have hi2 : i - N < N := by omega
        have hk : (⟨i, h2'⟩ : Fin (N + N)) = Fin.natAdd N ⟨i - N, hi2⟩ := Fin.ext (by simp; omega)
        rw [hk, Fin.addCases_right]
        simp

  have hCright : RightOnIncidentPairs S C := by
    intro l p hp
    have hIpl : I p l := (hS_mem p l).mp hp
    have h1 := hCacc p l hIpl
    unfold circuitFun at h1
    rw [hincInput_eq {p} {l}]
    convert h1 using 2
    apply List.ofFn_inj.mpr
    funext k
    refine Fin.addCases (fun p' => ?_) (fun l' => ?_) k
    · simp only [Fin.addCases_left, Finset.mem_singleton]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro h; subst h; exact Or.inl rfl
      · rintro (h | h)
        · exact Fin.castAdd_inj.mp h
        · exact (hcast_ne_nat p' l h).elim
    · simp only [Fin.addCases_right, Finset.mem_singleton]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro h; subst h; exact Or.inr rfl
      · rintro (h | h)
        · exact (hcast_ne_nat p l' h.symm).elim
        · exact (Fin.natAdd_inj N).mp h

  have hCzeroSound : ∀ Y : Finset (Fin N), Y.card ≤ q →
      C.eval (incidenceInput (zeroSet S Y) Y) = false := by
    intro Y hY
    rw [hincInput_eq (zeroSet S Y) Y]
    apply hCsound
    · have hEq : Finset.univ.filter (fun l : Fin N =>
          Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ zeroSet S Y))
            (fun l => decide (l ∈ Y)) (Fin.natAdd N l) = true) = Y := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Fin.addCases_right]
        simp
      rw [hEq]; exact hY
    · rintro ⟨p, l, hIpl, hp, hl⟩
      simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hp hl
      have hmiss := (Finset.mem_filter.mp hp).2 l hl
      exact hmiss ((hS_mem p l).mpr hIpl)

  -- Factor-substitution irredundancy at every non-output AND gate c
  have hCfactorIrr : ∀ (c : ℕ) (σ : ℕ → ℕ), c < C.size →
      (gateAt C c).op = GateOp.and →
      C.output ≠ n + c →
      (∀ r : ℕ, σ r ∈ (gateAt C c).inputs) →
      ∃ Y : Finset (Fin N), Y.card ≤ q ∧
        (substReads C n c σ).eval (incidenceInput (zeroSet S Y) Y) = true := by
    intro c σ hc hop houtne hσmem
    have hclt : c < C.gates.length := hc
    have hgatec : gateAt C c = C.gates[c] := by unfold gateAt; rw [List.getD_eq_getElem _ _ hclt]
    rw [hgatec] at hop hσmem
    have hσlt : ∀ r, σ r < n + c := fun r =>
      hCAO2.2.1 c hclt (σ r) (hgatec ▸ hσmem r)
    let D1 : Circuit := substReads C n c σ
    let D2 : Circuit := substDel C c σ 0
    have hD2mono : Monotone2 D2 := hsubstDel_mono C c σ 0 hCmono
    have hD2len : D2.gates.length = C.gates.length - 1 := hsubstDel_size C c σ 0 hclt
    -- D1 >= C pointwise on all inputs of length n
    have hD1_ge_C : ∀ (x : List Bool), x.length = n →
        ∀ w < n + C.gates.length, (C.wires x).getD w false = true → (D1.wires x).getD w false = true := by
      intro x hxlen w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hCw
        by_cases hwin : w < n
        · rw [hwires_eq, hfold_getD_lt _ _ w (by omega)] at hCw ⊢; exact hCw
        · let j : ℕ := w - n
          have hwj : w = n + j := by omega
          have hjlt : j < C.gates.length := by omega
          have hCget : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem hjlt
          have hD1get : D1.gates[j]? = some ⟨(C.gates[j]).op,
              (C.gates[j]).inputs.map fun i => if i = n + c then σ j else i⟩ := by
            simp only [D1, hsubstReads_gates]; simp [hjlt]
          rw [hwj, hwires_eq, ← hxlen, hfold_getD_gate C.gates x j _ hCget] at hCw
          rw [hwj, hwires_eq, ← hxlen, hfold_getD_gate D1.gates x j _ hD1get]
          have hsub_in : ∀ i ∈ (C.gates[j]).inputs,
              ((C.gates.take j).foldl stepW x).getD i false = true →
              ((D1.gates.take j).foldl stepW x).getD (if i = n + c then σ j else i) false = true := by
            intro i hi hCi
            have hilt : i < n + j := by
              have hgj : gateAt C j = C.gates[j] := by unfold gateAt; rw [List.getD_eq_getElem _ _ hjlt]
              exact hCAO2.2.1 j hjlt i (hgj ▸ hi)
            rw [← hfold_getD_take C.gates x j i (by omega) (by rw [hxlen]; exact hilt)] at hCi
            by_cases hic : i = n + c
            · subst hic
              rw [if_pos rfl]
              have hσlt_j : σ j < n + j := by have := hσlt j; omega
              rw [← hfold_getD_take D1.gates x j (σ j) (by simp only [D1, hsubstReads_gates, List.length_mapIdx]; omega) (by rw [hxlen]; exact hσlt_j)]
              apply ih (σ j) (by have := hσlt j; omega) (by have := hσlt j; omega)
              -- Since gate c is AND and σ j ∈ inputs of gate c, w_C(n + c) = true implies w_C(σ j) = true
              have hCc : (C.wires x).getD (n + c) false = true := hCi
              rw [hwires_eq, ← hxlen, hfold_getD_gate C.gates x c _ (List.getElem?_eq_getElem hclt), hop] at hCc
              simp only [heval_and, List.all_eq_true, List.mem_map, id] at hCc
              have hres := hCc _ ⟨σ j, hσmem j, rfl⟩
              rw [← hfold_getD_take C.gates x c (σ j) (by omega) (by rw [hxlen]; exact hσlt j)] at hres
              exact hres
            · rw [if_neg hic]
              rw [← hfold_getD_take D1.gates x j i (by simp only [D1, hsubstReads_gates, List.length_mapIdx]; omega) (by rw [hxlen]; exact hilt)]
              exact ih i (by omega) (by omega) hCi
          rcases (hCmono _ (List.getElem_mem hjlt)).1 with hjop | hjop
          · rw [hjop] at hCw ⊢
            simp only [heval_and, List.map_map, List.all_eq_true, List.mem_map, Function.comp_apply, id] at hCw ⊢
            rintro b ⟨i, hi, rfl⟩
            exact hsub_in i hi (hCw _ ⟨i, hi, rfl⟩)
          · rw [hjop] at hCw ⊢
            simp only [heval_or, List.map_map, List.any_eq_true, List.mem_map, Function.comp_apply, id] at hCw ⊢
            rcases hCw with ⟨b, ⟨i, hi, rfl⟩, hb⟩
            exact ⟨_, ⟨i, hi, rfl⟩, hsub_in i hi hb⟩
    -- D2 agrees with D1 on every wire w != n + c
    have hD2_eq_D1 : ∀ (x : List Bool), x.length = n →
        ∀ w < n + C.gates.length, w ≠ n + c →
          (D2.wires x).getD (shiftWire c w) false = (D1.wires x).getD w false := by
      intro x hxlen w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hne
        by_cases hwin : w < n
        · have hsh : shiftWire c w = w := by simp [shiftWire]; omega
          rw [hsh, hwires_eq, hwires_eq, hfold_getD_lt _ _ w (by omega),
            hfold_getD_lt _ _ w (by omega)]
        · let j : ℕ := w - n
          have hwj : w = n + j := by omega
          have hjlt : j < C.gates.length := by omega
          have hjne : j ≠ c := by omega
          let j' : ℕ := if j < c then j else j - 1
          have hj'lt : j' < D2.gates.length := by
            rw [hD2len]; simp only [j']; split_ifs <;> omega
          have hsh : shiftWire c w = n + j' := by
            simp only [shiftWire, j']; rw [hwj]; split_ifs <;> omega
          let gs1 : List Gate := C.gates.mapIdx fun r g =>
            ⟨g.op, g.inputs.map fun i =>
              if i = n + c then (if c < r then σ r else n + C.gates.length) else i⟩
          have hgs1_get : gs1[j]? = some ⟨(C.gates[j]).op,
              (C.gates[j]).inputs.map fun i =>
                if i = n + c then (if c < j then σ j else n + C.gates.length) else i⟩ := by
            simp [gs1, hjlt]
          have hD2get : D2.gates[j']? = some ⟨(C.gates[j]).op,
              ((C.gates[j]).inputs.map fun i =>
                if i = n + c then (if c < j then σ j else n + C.gates.length) else i).map (shiftWire c)⟩ := by
            have herase : (gs1.eraseIdx c)[j']? = gs1[j]? := by
              by_cases hjc : j < c
              · have hj'eq : j' = j := if_pos hjc
                rw [hj'eq, List.getElem?_eraseIdx_of_lt hjc]
              · have hj'eq : j' = j - 1 := if_neg hjc
                have hge : c ≤ j' := by omega
                rw [List.getElem?_eraseIdx_of_ge hge]
                have : j' + 1 = j := by omega
                rw [this]
            simp only [D2, substDel, List.getElem?_map]
            change Option.map (fun g : Gate => ({ op := g.op, inputs := g.inputs.map (shiftWire c) } : Gate))
              ((gs1.eraseIdx c)[j']?) = _
            rw [herase, hgs1_get]
            rfl
          have hD1get : D1.gates[j]? = some ⟨(C.gates[j]).op,
              (C.gates[j]).inputs.map fun i => if i = n + c then σ j else i⟩ := by
            simp only [D1, hsubstReads_gates]; simp [hjlt]
          rw [hsh, hwj, hwires_eq, hwires_eq, ← hxlen]
          rw [hfold_getD_gate D2.gates x j' _ hD2get]
          rw [hfold_getD_gate D1.gates x j _ hD1get]
          congr 1
          rw [List.map_map, List.map_map, List.map_map]
          apply List.map_congr_left
          intro i hi
          simp only [Function.comp_apply]
          have hilt : i < n + j := by
            have hgj : gateAt C j = C.gates[j] := by unfold gateAt; rw [List.getD_eq_getElem _ _ hjlt]
            exact hCAO2.2.1 j hjlt i (hgj ▸ hi)
          by_cases hic : i = n + c
          · subst hic
            have hcj : c < j := by omega
            simp only [↓reduceIte, hcj]
            have hσj_lt : σ j < n + c := hσlt j
            have hshσ : shiftWire c (σ j) = σ j := by simp [shiftWire]; omega
            have hσj_lt' : σ j < n + j' := by simp only [j']; rw [if_neg (by omega)]; omega
            rw [hshσ]
            rw [← hfold_getD_take D2.gates x j' (σ j) (by omega) (by rw [hxlen]; exact hσj_lt')]
            rw [← hfold_getD_take D1.gates x j (σ j) (by simp only [D1, hsubstReads_gates, List.length_mapIdx]; omega) (by rw [hxlen]; omega)]
            have hih := ih (σ j) (by omega) (by omega) (by omega)
            rw [hshσ] at hih
            exact hih
          · simp only [hic, ↓reduceIte]
            have hshlt : shiftWire c i < n + j' := by
              simp only [shiftWire, j']
              by_cases hjc : j < c
              · rw [if_pos hjc, if_pos (by omega)]; exact hilt
              · rw [if_neg hjc]; split_ifs <;> omega
            rw [← hfold_getD_take D2.gates x j' _ (by omega) (by rw [hxlen]; exact hshlt)]
            rw [← hfold_getD_take D1.gates x j _ (by simp only [D1, hsubstReads_gates, List.length_mapIdx]; omega) (by rw [hxlen]; exact hilt)]
            exact ih i (by omega) (by omega) hic
    have hD2eval : ∀ z : Fin n → Bool, circuitFun n D2 z = circuitFun n D1 z := by
      intro z
      unfold circuitFun Circuit.eval
      change (D2.wires (List.ofFn z)).getD (shiftWire c (if C.output = n + c then 0 else C.output)) false =
        (D1.wires (List.ofFn z)).getD C.output false
      rw [if_neg houtne]
      exact hD2_eq_D1 (List.ofFn z) List.length_ofFn C.output hCout_lt houtne
    have hD2acc : ∀ p l : Fin N, I p l →
        circuitFun n D2 (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true := by
      intro p l hI
      rw [hD2eval]
      exact hD1_ge_C _ List.length_ofFn C.output hCout_lt (hCacc p l hI)
    have hnotSound : ¬ (∀ z : Fin n → Bool,
        (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun n D2 z = false) := by
      intro hsd
      have hle := hCmin D2 ⟨hD2mono, hD2acc, hsd⟩
      have hD2sz : D2.size = C.size - 1 := hD2len
      have hCpos : 0 < C.size := by omega
      omega
    push Not at hnotSound
    obtain ⟨z, hzcard, hzno, hztrue⟩ := hnotSound
    have hzD1 : circuitFun n D1 z = true := by
      rw [← hD2eval]
      by_cases h : circuitFun n D2 z = true
      · exact h
      · exact absurd (Bool.eq_false_iff.mpr h) hztrue
    let Y : Finset (Fin N) := Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)
    refine ⟨Y, hzcard, ?_⟩
    have hD1mono : Monotone2 D1 := by
      intro g hg
      simp only [D1, hsubstReads_gates, List.mem_mapIdx] at hg
      rcases hg with ⟨r, hr, rfl⟩
      have hm := hCmono _ (List.getElem_mem hr)
      exact ⟨hm.1, by simpa using hm.2⟩
    have hle_in : ∀ i : ℕ, (List.ofFn z).getD i false = true →
        (incidenceInput (zeroSet S Y) Y).getD i false = true := by
      intro i hi
      by_cases hil : i < n
      · rw [List.getD_eq_getElem _ _ (by simp; exact hil), List.getElem_ofFn] at hi
        rw [hincInput_eq (zeroSet S Y) Y,
          List.getD_eq_getElem _ _ (by simp; exact hil), List.getElem_ofFn]
        by_cases hiN : i < N
        · have hk : (⟨i, hil⟩ : Fin n) = Fin.castAdd N ⟨i, hiN⟩ := Fin.ext rfl
          rw [hk, Fin.addCases_left, decide_eq_true_eq]
          rw [hk] at hi
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          intro l hl hmem
          have hlz : z (Fin.natAdd N l) = true := (Finset.mem_filter.mp hl).2
          exact hzno ⟨i, hiN⟩ l ((hS_mem _ _).mp hmem) hi hlz
        · have hi2 : i - N < N := by omega
          have hk : (⟨i, hil⟩ : Fin n) = Fin.natAdd N ⟨i - N, hi2⟩ := Fin.ext (by simp; omega)
          rw [hk, Fin.addCases_right, decide_eq_true_eq]
          rw [hk] at hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        cases hi
    exact hwires_mono D1 hD1mono (List.ofFn z) (incidenceInput (zeroSet S Y) Y)
      (by rw [List.length_ofFn, hincInput_eq, List.length_ofFn]) hle_in D1.output hzD1

  -- Now combine h_lineSingle, h_pointSingle, crossCount <= C.size, and h_core
  by_cases hdone : N * q ≤ 100 * C.size
  · exact hdone
  have hsmall : 100 * C.size < N * q := by omega
  have hcross_le : crossCount n (Finset.univ.image (Fin.natAdd N)) C ≤ C.size := by
    unfold crossCount Circuit.size
    exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
  have hcross_lt : 100 * crossCount n (Finset.univ.image (Fin.natAdd N)) C < N * q := by omega

  -- Apply h_lineSingle and h_pointSingle
  have hC4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l') := by
    intro p p' l l' hpp hll h
    exact hll ((huniq p p' hpp).unique ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩)
  have hcol' : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1 := by
    intro l; rw [Fintype.card_subtype]; exact hcol l
  have hsound_card : ∀ z : Fin n → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun n C z = false := by
    intro z hle hno
    rw [Fintype.card_subtype] at hle
    exact hCsound z hle hno
  have hLS_y := h_lineSingle N I C hC4 hCAO2 (fun z hle hno => hsound_card z (by omega) hno)
  have hLS_x := h_pointSingle q N I C hq hN hcol' huniq hCAO2 hsound_card

  -- Count all incident pairs vs line-single, point-single, double-reread
  let E_all : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  let E_y : Finset (Fin N × Fin N) := Finset.univ.filter (fun e =>
    I e.1 e.2 ∧ lineSingle C n (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true)
  let E_x : Finset (Fin N × Fin N) := Finset.univ.filter (fun e =>
    I e.1 e.2 ∧ lineSingle C n (fun i => decide (i < N)) e.1.val (N + e.2.val) = true)
  let E_d : Finset (Fin N × Fin N) := Finset.univ.filter (fun e =>
    I e.1 e.2 ∧ lineSingle C n (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
      lineSingle C n (fun i => decide (i < N)) e.1.val (N + e.2.val) = false)
  have hE_all_card : E_all.card = N * (q + 1) := by
    have hbij : E_all.card = ∑ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card := by
      have : E_all = Finset.univ.biUnion (fun l : Fin N =>
          (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
        ext ⟨p, l⟩
        simp [E_all]
      rw [this, Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro l _
        exact Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)
      · intro l₁ _ l₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro e he1 he2
        rcases Finset.mem_image.mp he1 with ⟨p₁, _, rfl⟩
        rcases Finset.mem_image.mp he2 with ⟨p₂, _, heq⟩
        exact hne (congrArg Prod.snd heq).symm
    rw [hbij]
    calc ∑ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card
        = ∑ _l : Fin N, (q + 1) := Finset.sum_congr rfl (fun l _ => hcol l)
      _ = N * (q + 1) := by simp
  have hcover : E_all ⊆ E_y ∪ (E_x ∪ E_d) := by
    intro e he
    have hIe : I e.1 e.2 := (Finset.mem_filter.mp he).2
    by_cases hy : lineSingle C n (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIe, hy⟩)
    · have hyf : lineSingle C n (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false :=
        Bool.eq_false_iff.mpr hy
      by_cases hx : lineSingle C n (fun i => decide (i < N)) e.1.val (N + e.2.val) = true
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIe, hx⟩))
      · have hxf : lineSingle C n (fun i => decide (i < N)) e.1.val (N + e.2.val) = false :=
          Bool.eq_false_iff.mpr hx
        exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIe, hyf, hxf⟩))
  have hEy_le : E_y.card ≤ 10 * C.size := by
    simpa only [E_y, Fintype.card_subtype] using hLS_y
  have hEx_le : E_x.card ≤ 10 * C.size := by
    simpa only [E_x, Fintype.card_subtype] using hLS_x
  have hsum_le : N * (q + 1) ≤ E_y.card + E_x.card + E_d.card := by
    rw [← hE_all_card]
    calc E_all.card ≤ (E_y ∪ (E_x ∪ E_d)).card := Finset.card_le_card hcover
      _ ≤ E_y.card + (E_x ∪ E_d).card := Finset.card_union_le _ _
      _ ≤ E_y.card + (E_x.card + E_d.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ = E_y.card + E_x.card + E_d.card := by omega
  have hEd_card : Fintype.card {e : Fin N × Fin N // e.1 ∈ S e.2 ∧
      lineSingle C n (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
      lineSingle C n (fun i => decide (i < N)) e.1.val (N + e.2.val) = false} = E_d.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext e
    simp only [E_d, Finset.mem_filter, Finset.mem_univ, true_and, hS_mem]
  have hEd_big : 4 * N * q < 5 * Fintype.card {e : Fin N × Fin N // e.1 ∈ S e.2 ∧
      lineSingle C n (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
      lineSingle C n (fun i => decide (i < N)) e.1.val (N + e.2.val) = false} := by
    rw [hEd_card]
    nlinarith
  exact h_core q N S C hq_ge200 hN hS_card hS_uniq hCAO2 hCout_ge hCout_lt hCNodup hCliveSize
    hCright hCzeroSound hCfactorIrr hcross_lt hEd_big

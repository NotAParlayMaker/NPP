import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2274

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
   (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
   (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def hit (x : Fin 14 → Bool) : Prop :=
  ∃ u v : Fin 14, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true

def tailOK (T : Circuit) (j : Fin 14) : Prop :=
  ∀ x : Fin 14 → Bool, T.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x j]]) = true ↔ hit x

def withoutEdge (T : Circuit) : Prop :=
  (∀ x : Fin 14 → Bool, (x 0 = false ∨ x 7 = false) →
    (T.eval (List.ofFn x) = true ↔ hit x)) ∧
  T.eval (List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7))) = false

def adj (u v : Fin 14) : Bool :=
  edges.any (fun p => (p.1 == u.val && p.2 == v.val) || (p.1 == v.val && p.2 == u.val))

lemma hit_iff_adj (x : Fin 14 → Bool) :
    hit x ↔ ∃ u v : Fin 14, adj u v = true ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    refine ⟨u, v, ?_, hu, hv⟩
    simp only [adj, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact ⟨(u.val, v.val), huv, Or.inl ⟨rfl, rfl⟩⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    simp only [adj, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at huv
    rcases huv with ⟨⟨a, b⟩, hab, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨u, v, hab, hu, hv⟩
    · exact ⟨v, u, hab, hv, hu⟩

def applyList (L : List ℕ) (i : Fin 14) : Fin 14 :=
  Fin.ofNat 14 (L.getD i.val 0)

def isAutoBool (f : Fin 14 → Fin 14) : Bool :=
  (List.finRange 14).all (fun u =>
    (List.finRange 14).any (fun v => f v == u) &&
    (List.finRange 14).all (fun v => adj (f u) (f v) == adj u v))

def IsAuto (f : Fin 14 → Fin 14) : Prop :=
  (∀ u : Fin 14, ∃ v : Fin 14, f v = u) ∧ (∀ u v : Fin 14, adj (f u) (f v) = adj u v)

lemma isAuto_of_bool (f : Fin 14 → Fin 14) (h : isAutoBool f = true) : IsAuto f := by
  simp only [isAutoBool, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    List.any_eq_true, beq_iff_eq] at h
  exact ⟨fun u => let ⟨v, _, hv⟩ := (h u).1; ⟨v, hv⟩, fun u v => (h u).2 v⟩

lemma isAuto_comp (f g : Fin 14 → Fin 14) (hf : IsAuto f) (hg : IsAuto g) :
    IsAuto (fun i => f (g i)) := by
  constructor
  · intro u
    rcases hf.1 u with ⟨w, hw⟩
    rcases hg.1 w with ⟨v, hv⟩
    exact ⟨v, by simp [hv, hw]⟩
  · intro u v
    rw [hf.2, hg.2]

lemma isAuto_inj (f : Fin 14 → Fin 14) (hf : IsAuto f) : Function.Injective f :=
  Finite.injective_iff_surjective.mpr hf.1

lemma hit_comp_auto (f : Fin 14 → Fin 14) (hf : IsAuto f) (x : Fin 14 → Bool) :
    hit (fun i => x (f i)) ↔ hit x := by
  rw [hit_iff_adj, hit_iff_adj]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    refine ⟨f u, f v, ?_, hu, hv⟩
    rw [hf.2 u v]
    exact huv
  · rintro ⟨u', v', huv', hu', hv'⟩
    rcases hf.1 u' with ⟨u, rfl⟩
    rcases hf.1 v' with ⟨v, rfl⟩
    refine ⟨u, v, ?_, hu', hv'⟩
    rw [← hf.2 u v]
    exact huv'

def toZero : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
   [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8],
   [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8],
   [1, 3, 2, 0, 5, 6, 4, 7, 13, 11, 9, 10, 8, 12],
   [1, 2, 6, 4, 0, 3, 5, 13, 9, 12, 7, 10, 11, 8],
   [1, 2, 5, 4, 3, 0, 6, 13, 9, 8, 7, 11, 10, 12],
   [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12],
   [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6],
   [7, 9, 8, 13, 11, 12, 10, 1, 0, 5, 3, 4, 2, 6],
   [9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3],
   [7, 9, 11, 13, 8, 10, 12, 1, 3, 5, 0, 2, 4, 6],
   [9, 11, 12, 8, 7, 13, 10, 6, 5, 4, 1, 0, 2, 3],
   [9, 11, 7, 8, 12, 10, 13, 6, 1, 4, 5, 2, 0, 3],
   [9, 7, 8, 13, 10, 12, 11, 1, 6, 3, 5, 4, 2, 0]]

def stabCover : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
   [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13],
   [0, 2, 4, 6, 1, 3, 5, 8, 10, 12, 7, 9, 11, 13],
   [0, 1, 5, 3, 6, 2, 4, 7, 10, 13, 8, 11, 12, 9],
   [0, 2, 3, 6, 5, 4, 1, 8, 7, 13, 10, 9, 11, 12],
   [0, 2, 5, 6, 3, 1, 4, 8, 10, 13, 7, 11, 9, 12],
   [0, 3, 2, 1, 5, 4, 6, 7, 8, 11, 10, 9, 13, 12]]

lemma toZero_ok :
    (List.finRange 14).all (fun a =>
      isAutoBool (applyList (toZero.getD a.val [])) &&
      (applyList (toZero.getD a.val []) a == 0)) = true := by
  decide

lemma stabCover_valid :
    stabCover.all (fun L => isAutoBool (applyList L) && (applyList L 0 == 0)) = true := by
  decide

lemma stabCover_cov :
    (List.finRange 14).all (fun b =>
      (b == 0) ||
      (stabCover.any (fun L =>
        let j := applyList L b
        (j == 1) || (j == 7) || (j == 9)) &&
       (!adj 0 b || stabCover.any (fun L => applyList L b == 7)))) = true := by
  decide

lemma exists_auto_pair (a b : Fin 14) (hab : a ≠ b) :
    ∃ f : Fin 14 → Fin 14, IsAuto f ∧ f a = 0 ∧
      (f b = 1 ∨ f b = 7 ∨ f b = 9) ∧ (adj a b = true → f b = 7) := by
  have htz := toZero_ok
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    beq_iff_eq] at htz
  rcases htz a with ⟨hτa, hτ0⟩
  let τ := applyList (toZero.getD a.val [])
  have hτ : IsAuto τ := isAuto_of_bool τ hτa
  have hτb0 : τ b ≠ 0 := by
    intro heq
    exact hab (isAuto_inj τ hτ (hτ0.trans heq.symm))
  have hsc := stabCover_cov
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hsc
  rcases hsc (τ b) with hb0 | ⟨⟨L1, hL1m, hL1j⟩, hL2⟩
  · exact absurd hb0 hτb0
  · have hsv := stabCover_valid
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hsv
    by_cases hadj : adj a b = true
    · have hadj0 : adj 0 (τ b) = true := by
        rw [← hτ0, hτ.2 a b, hadj]
      have hL2' : ∃ L2 ∈ stabCover, applyList L2 (τ b) = 7 := by
        rcases hL2 with hfalse | ⟨L2, hL2m, hL27⟩
        · simp [hadj0] at hfalse
        · exact ⟨L2, hL2m, hL27⟩
      rcases hL2' with ⟨L2, hL2m, hL27⟩
      rcases hsv L2 hL2m with ⟨hρa, hρ0⟩
      let ρ := applyList L2
      refine ⟨fun i => ρ (τ i), isAuto_comp ρ τ (isAuto_of_bool ρ hρa) hτ, ?_, ?_, ?_⟩
      · dsimp [τ, ρ]; rw [hτ0, hρ0]
      · exact Or.inr (Or.inl hL27)
      · intro _; exact hL27
    · rcases hsv L1 hL1m with ⟨hρa, hρ0⟩
      let ρ := applyList L1
      refine ⟨fun i => ρ (τ i), isAuto_comp ρ τ (isAuto_of_bool ρ hρa) hτ, ?_, ?_, ?_⟩
      · dsimp [τ, ρ]; rw [hτ0, hρ0]
      · simpa [or_assoc] using hL1j
      · intro hbad; exact absurd hbad hadj

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepW x := rfl

lemma stepW_length (w : List Bool) (g : Gate) :
    (stepW w g).length = w.length + 1 := by
  simp [stepW]

lemma foldl_stepW_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, stepW_length]
    simp only [List.length_cons]
    omega

lemma foldl_stepW_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    exact List.getD_append _ _ _ _ hi

def permWire (f : Fin 14 → Fin 14) (i : ℕ) : ℕ :=
  if h : i < 14 then (f ⟨i, h⟩).val else i

def permGate (f : Fin 14 → Fin 14) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (permWire f)⟩

def permCircuit (f : Fin 14 → Fin 14) (C : Circuit) : Circuit :=
  ⟨C.gates.map (permGate f), permWire f C.output⟩

lemma permCircuit_size (f : Fin 14 → Fin 14) (C : Circuit) :
    (permCircuit f C).size = C.size := by
  simp [permCircuit, Circuit.size]

lemma permCircuit_mono (f : Fin 14 → Fin 14) (C : Circuit) (hC : Monotone2 C) :
    Monotone2 (permCircuit f C) := by
  intro g hg
  simp only [permCircuit, List.mem_map] at hg
  rcases hg with ⟨g0, hg0, rfl⟩
  exact ⟨(hC g0 hg0).1, by simp [permGate, (hC g0 hg0).2]⟩

lemma permWires_inv (f : Fin 14 → Fin 14) (gs : List Gate) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (h14 : 14 ≤ w₁.length)
    (hlo : ∀ i : Fin 14, w₁.getD (f i).val false = w₂.getD i.val false)
    (hhi : ∀ i, 14 ≤ i → w₁.getD i false = w₂.getD i false) :
    let w₁' := (gs.map (permGate f)).foldl stepW w₁
    let w₂' := gs.foldl stepW w₂
    w₁'.length = w₂'.length ∧ 14 ≤ w₁'.length ∧
    (∀ i : Fin 14, w₁'.getD (f i).val false = w₂'.getD i.val false) ∧
    (∀ i, 14 ≤ i → w₁'.getD i false = w₂'.getD i false) := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, h14, hlo, hhi⟩
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hmap : g.inputs.map (fun i => w₁.getD (permWire f i) false) =
        g.inputs.map (fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i _
      by_cases hi : i < 14
      · simp only [permWire, hi, dite_true]
        exact hlo ⟨i, hi⟩
      · simp only [permWire, hi, dite_false]
        exact hhi i (by omega)
    have hstep : stepW w₁ (permGate f g) = w₁ ++ [g.op.eval (g.inputs.map fun i => w₂.getD i false)] := by
      simp only [stepW, permGate, List.map_map, Function.comp_def, hmap]
    rw [hstep]
    apply ih
    · simp [stepW, hlen]
    · simp; omega
    · intro i
      have hfi : (f i).val < w₁.length := lt_of_lt_of_le (f i).isLt h14
      have hi2 : i.val < w₂.length := lt_of_lt_of_le i.isLt (hlen ▸ h14)
      simp only [stepW]
      rw [List.getD_append _ _ _ _ hfi, List.getD_append _ _ _ _ hi2]
      exact hlo i
    · intro i hi
      rcases lt_trichotomy i w₁.length with hlt | heq | hgt
      · have hlt2 : i < w₂.length := hlen ▸ hlt
        simp only [stepW]
        rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt2]
        exact hhi i hi
      · have h1 : (w₁ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]).getD i false =
            g.op.eval (g.inputs.map fun j => w₂.getD j false) := by
          rw [List.getD_append_right _ _ _ _ (le_of_eq heq.symm), heq, Nat.sub_self]
          rfl
        have h2 : (stepW w₂ g).getD i false = g.op.eval (g.inputs.map fun j => w₂.getD j false) := by
          simp only [stepW]
          rw [List.getD_append_right _ _ _ _ (by omega), show i - w₂.length = 0 by omega]
          rfl
        rw [h1, h2]
      · have h1 : (w₁ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]).getD i false = false :=
          List.getD_eq_default _ _ (by simp; omega)
        have h2 : (stepW w₂ g).getD i false = false :=
          List.getD_eq_default _ _ (by simp [stepW]; omega)
        rw [h1, h2]

lemma permCircuit_eval (f : Fin 14 → Fin 14) (C : Circuit) (x : Fin 14 → Bool) :
    (permCircuit f C).eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (f i))) := by
  have hinv := permWires_inv f C.gates (List.ofFn x) (List.ofFn (fun i => x (f i)))
    (by simp) (by simp)
    (fun i => by
      have h1 : (f i).val < (List.ofFn x).length := by simp
      have h2 : i.val < (List.ofFn (fun j => x (f j))).length := by simp
      rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2,
        List.getElem_ofFn, List.getElem_ofFn])
    (fun i hi => by
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
  simp only [Circuit.eval, permCircuit, Circuit.wires]
  change ((C.gates.map (permGate f)).foldl stepW (List.ofFn x)).getD (permWire f C.output) false =
    (C.gates.foldl stepW (List.ofFn (fun i => x (f i)))).getD C.output false
  by_cases ho : C.output < 14
  · simp only [permWire, ho, dite_true]
    exact hinv.2.2.1 ⟨C.output, ho⟩
  · simp only [permWire, ho, dite_false]
    exact hinv.2.2.2 C.output (by omega)

def shiftWire (i : ℕ) : ℕ :=
  if i < 14 then i else i + 1

def shiftCircuit (C : Circuit) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map shiftWire⟩), shiftWire C.output⟩

lemma shiftCircuit_size (C : Circuit) : (shiftCircuit C).size = C.size := by
  simp [shiftCircuit, Circuit.size]

lemma shiftCircuit_mono (C : Circuit) (hC : Monotone2 C) : Monotone2 (shiftCircuit C) := by
  intro g hg
  simp only [shiftCircuit, List.mem_map] at hg
  rcases hg with ⟨g0, hg0, rfl⟩
  exact ⟨(hC g0 hg0).1, by simp [(hC g0 hg0).2]⟩

lemma shiftWires_inv (gs : List Gate) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length + 1) (h14 : 14 ≤ w₂.length)
    (hmap : ∀ i, w₁.getD (shiftWire i) false = w₂.getD i false) :
    let w₁' := (gs.map (fun g => ⟨g.op, g.inputs.map shiftWire⟩)).foldl stepW w₁
    let w₂' := gs.foldl stepW w₂
    w₁'.length = w₂'.length + 1 ∧ 14 ≤ w₂'.length ∧
    (∀ i, w₁'.getD (shiftWire i) false = w₂'.getD i false) := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, h14, hmap⟩
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hinputs : g.inputs.map (fun i => w₁.getD (shiftWire i) false) =
        g.inputs.map (fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i _
      exact hmap i
    have hstep : stepW w₁ ⟨g.op, g.inputs.map shiftWire⟩ =
        w₁ ++ [g.op.eval (g.inputs.map fun i => w₂.getD i false)] := by
      simp only [stepW, List.map_map, Function.comp_def, hinputs]
    rw [hstep]
    apply ih
    · simp [stepW, hlen]
    · simp [stepW]; omega
    · intro i
      let bit := g.op.eval (g.inputs.map fun j => w₂.getD j false)
      by_cases hi : i < 14
      · simp only [shiftWire, hi, ite_true]
        have h1 : i < w₁.length := by omega
        have h2 : i < w₂.length := by omega
        simp only [stepW]
        rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
        simpa [shiftWire, hi] using hmap i
      · simp only [shiftWire, hi, ite_false]
        rcases lt_trichotomy i w₂.length with hlt | heq | hgt
        · have hlt1 : i + 1 < w₁.length := by omega
          simp only [stepW]
          rw [List.getD_append _ _ _ _ hlt1, List.getD_append _ _ _ _ hlt]
          simpa [shiftWire, hi] using hmap i
        · have h1 : (w₁ ++ [bit]).getD (i + 1) false = bit := by
            rw [List.getD_append_right _ _ _ _ (by omega), show i + 1 - w₁.length = 0 by omega]
            rfl
          have h2 : (stepW w₂ g).getD i false = bit := by
            simp only [stepW]
            rw [List.getD_append_right _ _ _ _ (by omega), show i - w₂.length = 0 by omega]
            rfl
          rw [h1, h2]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [stepW]; omega)]

lemma shiftCircuit_eval (C : Circuit) (x : Fin 14 → Bool) (b : Bool) :
    (shiftCircuit C).eval (List.ofFn x ++ [b]) = C.eval (List.ofFn x) := by
  have hinv := shiftWires_inv C.gates (List.ofFn x ++ [b]) (List.ofFn x)
    (by simp) (by simp)
    (fun i => by
      by_cases hi : i < 14
      · simp only [shiftWire, hi, ite_true]
        rw [List.getD_append _ _ _ _ (by simp; exact hi)]
      · simp only [shiftWire, hi, ite_false]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
  exact hinv.2.2 C.output

lemma wires_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w₁ w₂ : List Bool) (hlen : w₁.length = w₂.length)
    (hle : ∀ i, w₁.getD i false = true → w₂.getD i false = true) :
    (gs.foldl stepW w₁).length = (gs.foldl stepW w₂).length ∧
    (∀ i, (gs.foldl stepW w₁).getD i false = true → (gs.foldl stepW w₂).getD i false = true) := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hle⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hgs g List.mem_cons_self
    have hbit : g.op.eval (g.inputs.map fun i => w₁.getD i false) = true →
        g.op.eval (g.inputs.map fun i => w₂.getD i false) = true := by
      rcases hg with hop | hop
      · simp only [hop, GateOp.eval, List.all_eq_true, id_eq, List.mem_map, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂]
        intro h i hi
        exact hle i (h i hi)
      · simp only [hop, GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
        rintro ⟨_, ⟨i, hi, rfl⟩, htrue⟩
        exact ⟨true, ⟨i, hi, hle i htrue⟩, rfl⟩
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
    · simp [stepW, hlen]
    · intro i hi
      rcases lt_trichotomy i w₁.length with hlt | heq | hgt
      · have hlt2 : i < w₂.length := hlen ▸ hlt
        simp only [stepW] at hi ⊢
        rw [List.getD_append _ _ _ _ hlt] at hi
        rw [List.getD_append _ _ _ _ hlt2]
        exact hle i hi
      · simp only [stepW] at hi ⊢
        rw [List.getD_append_right _ _ _ _ (by omega), show i - w₁.length = 0 by omega] at hi
        rw [List.getD_append_right _ _ _ _ (by omega), show i - w₂.length = 0 by omega]
        exact hbit hi
      · simp only [stepW] at hi
        rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        cases hi

lemma circuit_mono (C : Circuit) (hC : Monotone2 C) (x₁ x₂ : Fin 14 → Bool)
    (hx : ∀ i, x₁ i = true → x₂ i = true) :
    C.eval (List.ofFn x₁) = true → C.eval (List.ofFn x₂) = true := by
  have hm := wires_mono C.gates (fun g hg => (hC g hg).1) (List.ofFn x₁) (List.ofFn x₂)
    (by simp)
    (fun i hi => by
      by_cases h : i < 14
      · have h1 : i < (List.ofFn x₁).length := by simp; exact h
        have h2 : i < (List.ofFn x₂).length := by simp; exact h
        rw [List.getD_eq_getElem _ _ h1, List.getElem_ofFn] at hi
        rw [List.getD_eq_getElem _ _ h2, List.getElem_ofFn]
        exact hx ⟨i, h⟩ hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        cases hi)
  exact hm.2 C.output

def evalSum (w : List Bool) : Sum Bool ℕ → Bool
  | Sum.inl b => b
  | Sum.inr k => w.getD k false

def simpAnd2 (u v : Sum Bool ℕ) (nextIdx : ℕ) : Sum Bool ℕ × Option Gate :=
  match u, v with
  | Sum.inl false, _ => (Sum.inl false, none)
  | _, Sum.inl false => (Sum.inl false, none)
  | Sum.inl true, x => (x, none)
  | x, Sum.inl true => (x, none)
  | Sum.inr a, Sum.inr b =>
    if a = b then (Sum.inr a, none)
    else (Sum.inr nextIdx, some ⟨GateOp.and, [a, b]⟩)

def simpOr2 (u v : Sum Bool ℕ) (nextIdx : ℕ) : Sum Bool ℕ × Option Gate :=
  match u, v with
  | Sum.inl true, _ => (Sum.inl true, none)
  | _, Sum.inl true => (Sum.inl true, none)
  | Sum.inl false, x => (x, none)
  | x, Sum.inl false => (x, none)
  | Sum.inr a, Sum.inr b =>
    if a = b then (Sum.inr a, none)
    else (Sum.inr nextIdx, some ⟨GateOp.or, [a, b]⟩)

def simpGate (env : List (Sum Bool ℕ)) (nextIdx : ℕ) (g : Gate) : Sum Bool ℕ × Option Gate :=
  let vals := g.inputs.map (fun i => env.getD i (Sum.inl false))
  match g.op with
  | GateOp.and =>
    match vals with
    | [] => (Sum.inl true, none)
    | [u] => (u, none)
    | [u, v] => simpAnd2 u v nextIdx
    | _ => (Sum.inl false, none)
  | _ =>
    match vals with
    | [] => (Sum.inl false, none)
    | [u] => (u, none)
    | [u, v] => simpOr2 u v nextIdx
    | _ => (Sum.inl false, none)

def stepSimp (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    List (Sum Bool ℕ) × List Gate :=
  let res := simpGate acc.1 (14 + acc.2.length) g
  match res.2 with
  | none => (acc.1 ++ [res.1], acc.2)
  | some g' => (acc.1 ++ [res.1], acc.2 ++ [g'])

lemma simpGate_none_false (env : List (Sum Bool ℕ)) (nextIdx : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hf : ∃ i ∈ g.inputs, env.getD i (Sum.inl false) = Sum.inl false) :
    (simpGate env nextIdx g).2 = none := by
  rcases hf with ⟨i, hi, hval⟩
  rcases hg with ⟨hop, hlen⟩
  cases h_in : g.inputs with
  | nil => simp [h_in] at hi
  | cons a t =>
    cases t with
    | nil =>
      simp only [h_in, List.mem_singleton] at hi
      subst hi
      rcases hop with hop | hop <;> simp only [simpGate, h_in, hop, List.map_cons, List.map_nil]
    | cons b t2 =>
      cases t2 with
      | nil =>
        simp only [h_in, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hop with hop | hop
        · rcases hi with rfl | rfl
          · cases hB : env.getD b (Sum.inl false) with
            | inl bb => cases bb <;> simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, hval, hB, simpAnd2]
            | inr kb => simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, hval, hB, simpAnd2]
          · cases hA : env.getD a (Sum.inl false) with
            | inl ba => cases ba <;> simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, hA, hval, simpAnd2]
            | inr ka => simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, hA, hval, simpAnd2]
        · rcases hi with rfl | rfl
          · cases hB : env.getD b (Sum.inl false) with
            | inl bb => cases bb <;> simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, hval, hB, simpOr2]
            | inr kb => simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, hval, hB, simpOr2]
          · cases hA : env.getD a (Sum.inl false) with
            | inl ba => cases ba <;> simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, hA, hval, simpOr2]
            | inr ka => simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, hA, hval, simpOr2]
      | cons _ _ =>
        simp [h_in] at hlen

lemma simpGate_spec (env : List (Sum Bool ℕ)) (w_orig w_new : List Bool) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hnext : w_new.length = 14 + (w_new.length - 14))
    (heq : ∀ i, evalSum w_new (env.getD i (Sum.inl false)) = w_orig.getD i false)
    (hbnd : ∀ i k, env.getD i (Sum.inl false) = Sum.inr k → k < w_new.length) :
    let res := simpGate env w_new.length g
    let bit := g.op.eval (g.inputs.map fun i => w_orig.getD i false)
    match res.2 with
    | none =>
      evalSum w_new res.1 = bit ∧
      (∀ k, res.1 = Sum.inr k → k < w_new.length)
    | some g' =>
      (g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
      res.1 = Sum.inr w_new.length ∧
      g'.op.eval (g'.inputs.map fun i => w_new.getD i false) = bit := by
  rcases hg with ⟨hop, hlen⟩
  cases h_in : g.inputs with
  | nil =>
    rcases hop with hop | hop <;> simp [simpGate, h_in, hop, GateOp.eval, evalSum]
  | cons a t =>
    cases t with
    | nil =>
      rcases hop with hop | hop
      · simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, GateOp.eval,
          List.all_cons, List.all_nil, id_eq, Bool.and_true]
        exact ⟨heq a, fun k hk => hbnd a k hk⟩
      · simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, GateOp.eval,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact ⟨heq a, fun k hk => hbnd a k hk⟩
    | cons b t2 =>
      cases t2 with
      | nil =>
        have ha := heq a
        have hb := heq b
        rcases hop with hop | hop
        · simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, GateOp.eval,
            List.all_cons, List.all_nil, id_eq, Bool.and_true]
          cases hA : env.getD a (Sum.inl false) with
          | inl ba =>
            rw [hA] at ha; simp only [evalSum] at ha
            cases hB : env.getD b (Sum.inl false) with
            | inl bb =>
              rw [hB] at hb; simp only [evalSum] at hb
              rw [← ha, ← hb]
              cases ba <;> cases bb <;> simp [simpAnd2, evalSum]
            | inr kb =>
              rw [hB] at hb; simp only [evalSum] at hb
              rw [← ha, ← hb]
              cases ba
              · simp [simpAnd2, evalSum]
              · simp [simpAnd2, evalSum]
                exact hbnd b kb hB
          | inr ka =>
            rw [hA] at ha; simp only [evalSum] at ha
            cases hB : env.getD b (Sum.inl false) with
            | inl bb =>
              rw [hB] at hb; simp only [evalSum] at hb
              rw [← ha, ← hb]
              cases bb
              · simp [simpAnd2, evalSum]
              · simp [simpAnd2, evalSum]
                exact hbnd a ka hA
            | inr kb =>
              rw [hB] at hb; simp only [evalSum] at hb
              rw [← ha, ← hb]
              by_cases heqk : ka = kb
              · subst heqk
                simp [simpAnd2, evalSum]
                exact hbnd a _ hA
              · simp [simpAnd2, heqk, GateOp.eval]
        · simp only [simpGate, h_in, hop, List.map_cons, List.map_nil, GateOp.eval,
            List.any_cons, List.any_nil, id_eq, Bool.or_false]
          cases hA : env.getD a (Sum.inl false) with
          | inl ba =>
            rw [hA] at ha; simp only [evalSum] at ha
            cases hB : env.getD b (Sum.inl false) with
            | inl bb =>
              rw [hB] at hb; simp only [evalSum] at hb
              rw [← ha, ← hb]
              cases ba <;> cases bb <;> simp [simpOr2, evalSum]
            | inr kb =>
              rw [hB] at hb; simp only [evalSum] at hb
              rw [← ha, ← hb]
              cases ba
              · simp [simpOr2, evalSum]
                exact hbnd b kb hB
              · simp [simpOr2, evalSum]
          | inr ka =>
            rw [hA] at ha; simp only [evalSum] at ha
            cases hB : env.getD b (Sum.inl false) with
            | inl bb =>
              rw [hB] at hb; simp only [evalSum] at hb
              rw [← ha, ← hb]
              cases bb
              · simp [simpOr2, evalSum]
                exact hbnd a ka hA
              · simp [simpOr2, evalSum]
            | inr kb =>
              rw [hB] at hb; simp only [evalSum] at hb
              rw [← ha, ← hb]
              by_cases heqk : ka = kb
              · subst heqk
                simp [simpOr2, evalSum]
                exact hbnd a _ hA
              · simp [simpOr2, heqk, GateOp.eval]
      | cons _ _ =>
        simp [h_in] at hlen

lemma foldl_stepSimp_inv (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (env : List (Sum Bool ℕ)) (outGs : List Gate) (w_orig initW : List Bool)
    (hinit : initW.length = 14)
    (hout_mono : ∀ g ∈ outGs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hlen : env.length = w_orig.length)
    (heq : ∀ i, evalSum (outGs.foldl stepW initW) (env.getD i (Sum.inl false)) = w_orig.getD i false)
    (hbnd : ∀ i k, env.getD i (Sum.inl false) = Sum.inr k → k < (outGs.foldl stepW initW).length) :
    let res := gs.foldl stepSimp (env, outGs)
    let w_orig' := gs.foldl stepW w_orig
    let w_new' := res.2.foldl stepW initW
    (∀ g ∈ res.2, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
    res.2.length ≤ outGs.length + gs.length ∧
    (∀ i, evalSum w_new' (res.1.getD i (Sum.inl false)) = w_orig'.getD i false) ∧
    (∀ i k, res.1.getD i (Sum.inl false) = Sum.inr k → k < w_new'.length) ∧
    (14 < env.length → env.getD 14 (Sum.inl false) = Sum.inl false →
      (∃ g ∈ gs, 14 ∈ g.inputs) → res.2.length < outGs.length + gs.length) := by
  induction gs generalizing env outGs w_orig with
  | nil =>
    refine ⟨hout_mono, le_rfl, heq, hbnd, ?_⟩
    intro _ _ ⟨g, hg, _⟩
    cases hg
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hgs g List.mem_cons_self
    have hwlen : (outGs.foldl stepW initW).length = 14 + outGs.length := by
      rw [foldl_stepW_length, hinit]
    have hsp := simpGate_spec env w_orig (outGs.foldl stepW initW) g hg (by omega) heq hbnd
    have hidx : 14 + outGs.length = (outGs.foldl stepW initW).length := hwlen.symm
    cases hopt : (simpGate env (outGs.foldl stepW initW).length g).2 with
    | none =>
      dsimp only at hsp
      rw [hopt] at hsp
      dsimp only at hsp
      have hstep_eq : stepSimp (env, outGs) g =
          (env ++ [(simpGate env (outGs.foldl stepW initW).length g).1], outGs) := by
        simp only [stepSimp, hidx, hopt]
      rw [hstep_eq]
      have heq' : ∀ i, evalSum (outGs.foldl stepW initW)
          ((env ++ [(simpGate env (outGs.foldl stepW initW).length g).1]).getD i (Sum.inl false)) =
          (stepW w_orig g).getD i false := by
        intro i
        rcases lt_trichotomy i env.length with hlt | heqi | hgt
        · rw [List.getD_append _ _ _ _ hlt, heq i]
          simp only [stepW]
          rw [List.getD_append _ _ _ _ (hlen ▸ hlt)]
        · rw [List.getD_append_right _ _ _ _ (by omega), show i - env.length = 0 by omega]
          simp only [List.getD_cons_zero, stepW]
          rw [List.getD_append_right _ _ _ _ (by omega), show i - w_orig.length = 0 by omega]
          exact hsp.1
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [stepW]; omega)]
          rfl
      have hbnd' : ∀ i k,
          (env ++ [(simpGate env (outGs.foldl stepW initW).length g).1]).getD i (Sum.inl false) = Sum.inr k →
          k < (outGs.foldl stepW initW).length := by
        intro i k hik
        rcases lt_trichotomy i env.length with hlt | heqi | hgt
        · rw [List.getD_append _ _ _ _ hlt] at hik
          exact hbnd i k hik
        · rw [List.getD_append_right _ _ _ _ (by omega), show i - env.length = 0 by omega] at hik
          exact hsp.2 k hik
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hik
          cases hik
      have hih := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
        (env ++ [(simpGate env (outGs.foldl stepW initW).length g).1]) outGs (stepW w_orig g)
        hout_mono (by simp [stepW, hlen]) heq' hbnd'
      refine ⟨hih.1, Nat.le_trans hih.2.1 (by simp), hih.2.2.1, hih.2.2.2.1, ?_⟩
      intro _ _ _
      exact lt_of_le_of_lt hih.2.1 (by simp)
    | some g' =>
      dsimp only at hsp
      rw [hopt] at hsp
      dsimp only at hsp
      have hstep_eq : stepSimp (env, outGs) g =
          (env ++ [(simpGate env (outGs.foldl stepW initW).length g).1], outGs ++ [g']) := by
        simp only [stepSimp, hidx, hopt]
      rw [hstep_eq]
      have hout_fold : (outGs ++ [g']).foldl stepW initW = stepW (outGs.foldl stepW initW) g' := by
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hout_mono' : ∀ x ∈ outGs ++ [g'],
          x.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ x.inputs.length ≤ 2 := by
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hout_mono x hx
        · exact hsp.1
      have heq' : ∀ i, evalSum ((outGs ++ [g']).foldl stepW initW)
          ((env ++ [(simpGate env (outGs.foldl stepW initW).length g).1]).getD i (Sum.inl false)) =
          (stepW w_orig g).getD i false := by
        intro i
        rw [hout_fold]
        rcases lt_trichotomy i env.length with hlt | heqi | hgt
        · rw [List.getD_append _ _ _ _ hlt]
          have hrhs : (stepW w_orig g).getD i false = w_orig.getD i false := by
            simp only [stepW]
            exact List.getD_append _ _ _ _ (hlen ▸ hlt)
          rw [hrhs, ← heq i]
          cases hval : env.getD i (Sum.inl false) with
          | inl b => rfl
          | inr k =>
            have hk := hbnd i k hval
            simp only [evalSum, stepW]
            exact List.getD_append _ _ _ _ hk
        · rw [List.getD_append_right _ _ _ _ (by omega), show i - env.length = 0 by omega]
          simp only [List.getD_cons_zero, hsp.2.1, evalSum, stepW]
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
          rw [List.getD_append_right _ _ _ _ (by omega), show i - w_orig.length = 0 by omega]
          exact hsp.2.2
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [stepW]; omega)]
          rfl
      have hbnd' : ∀ i k,
          (env ++ [(simpGate env (outGs.foldl stepW initW).length g).1]).getD i (Sum.inl false) = Sum.inr k →
          k < ((outGs ++ [g']).foldl stepW initW).length := by
        intro i k hik
        rw [hout_fold, stepW_length]
        rcases lt_trichotomy i env.length with hlt | heqi | hgt
        · rw [List.getD_append _ _ _ _ hlt] at hik
          exact lt_trans (hbnd i k hik) (Nat.lt_succ_self _)
        · rw [List.getD_append_right _ _ _ _ (by omega), show i - env.length = 0 by omega] at hik
          simp only [List.getD_cons_zero, hsp.2.1, Sum.inr.injEq] at hik
          omega
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hik
          cases hik
      have hih := ih (fun g0 hg0 => hgs g0 (List.mem_cons_of_mem g hg0))
        (env ++ [(simpGate env (outGs.foldl stepW initW).length g).1]) (outGs ++ [g']) (stepW w_orig g)
        hout_mono' (by simp [stepW, hlen]) heq' hbnd'
      refine ⟨hih.1, by have hsz := hih.2.1; simp only [List.length_append, List.length_cons, List.length_nil] at hsz ⊢; omega, hih.2.2.1, hih.2.2.2.1, ?_⟩
      intro h14 h14f ⟨g0, hg0, hg0in⟩
      simp only [List.mem_cons] at hg0
      rcases hg0 with rfl | hg0
      · have hnone := simpGate_none_false env (outGs.foldl stepW initW).length g0 hg ⟨14, hg0in, h14f⟩
        rw [hopt] at hnone
        cases hnone
      · have h14' : 14 < (env ++ [(simpGate env (outGs.foldl stepW initW).length g).1]).length := by
          simp; omega
        have h14f' : (env ++ [(simpGate env (outGs.foldl stepW initW).length g).1]).getD 14 (Sum.inl false) =
            Sum.inl false := by
          rw [List.getD_append _ _ _ _ h14, h14f]
        have hlt := hih.2.2.2.2 h14' h14f' ⟨g0, hg0, hg0in⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at hlt ⊢
        omega

lemma foldl_unused14 (gs : List Gate) (hunused : ∀ g ∈ gs, 14 ∉ g.inputs)
    (w₁ w₂ : List Bool) (hlen : w₁.length = w₂.length)
    (h15 : 15 ≤ w₁.length)
    (heq : ∀ i, i ≠ 14 → w₁.getD i false = w₂.getD i false) :
    (gs.foldl stepW w₁).length = (gs.foldl stepW w₂).length ∧
    ∀ i, i ≠ 14 → (gs.foldl stepW w₁).getD i false = (gs.foldl stepW w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, heq⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hunused g List.mem_cons_self
    have hmap : g.inputs.map (fun i => w₁.getD i false) = g.inputs.map (fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact heq i (fun h14 => hg (h14 ▸ hi))
    have hstep : stepW w₁ g = w₁ ++ [g.op.eval (g.inputs.map fun i => w₂.getD i false)] := by
      simp only [stepW, hmap]
    rw [hstep]
    apply ih (fun g' hg' => hunused g' (List.mem_cons_of_mem g hg'))
    · simp [stepW, hlen]
    · simp; omega
    · intro i hi14
      rcases lt_trichotomy i w₁.length with hlt | heqi | hgt
      · simp only [stepW]
        rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hlen ▸ hlt)]
        exact heq i hi14
      · simp only [stepW]
        rw [List.getD_append_right _ _ _ _ (by omega), show i - w₁.length = 0 by omega]
        rw [List.getD_append_right _ _ _ _ (by omega), show i - w₂.length = 0 by omega]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [stepW]; omega)]

def env0 (init : Sum Bool ℕ) : List (Sum Bool ℕ) :=
  (List.range 14).map Sum.inr ++ [init]

def simpFrom (init : Sum Bool ℕ) (gs : List Gate) (out : ℕ) : Circuit × Sum Bool ℕ :=
  let res := gs.foldl stepSimp (env0 init, [])
  (⟨res.2, match res.1.getD out (Sum.inl false) with | Sum.inl _ => 0 | Sum.inr k => k⟩,
   res.1.getD out (Sum.inl false))

lemma env0_length (init : Sum Bool ℕ) : (env0 init).length = 15 := by
  simp [env0]

lemma simpFrom_spec (init : Sum Bool ℕ) (hinit_bnd : ∀ k, init = Sum.inr k → k < 14)
    (gs : List Gate) (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (out : ℕ) (x : Fin 14 → Bool) (b0 : Bool) (hb0 : evalSum (List.ofFn x) init = b0) :
    let pr := simpFrom init gs out
    Monotone2 pr.1 ∧
    pr.1.size ≤ gs.length ∧
    evalSum (pr.1.wires (List.ofFn x)) pr.2 = (gs.foldl stepW (List.ofFn x ++ [b0])).getD out false ∧
    (∀ k, pr.2 = Sum.inr k → pr.1.eval (List.ofFn x) = (gs.foldl stepW (List.ofFn x ++ [b0])).getD out false) ∧
    (init = Sum.inl false → (∃ g ∈ gs, 14 ∈ g.inputs) → pr.1.size < gs.length) := by
  have heq0 : ∀ i, evalSum (([] : List Gate).foldl stepW (List.ofFn x)) ((env0 init).getD i (Sum.inl false)) =
      (List.ofFn x ++ [b0]).getD i false := by
    intro i
    simp only [List.foldl_nil]
    rcases lt_trichotomy i 14 with hlt | rfl | hgt
    · have h1 : i < ((List.range 14).map (Sum.inr : ℕ → Sum Bool ℕ)).length := by simp; exact hlt
      simp only [env0]
      rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1, List.getElem_map,
        List.getElem_range]
      simp only [evalSum]
      exact (List.getD_append (List.ofFn x) [b0] false i (by simp; exact hlt)).symm
    · simp only [env0]
      rw [List.getD_append_right _ _ _ _ (by simp), show 14 - ((List.range 14).map (Sum.inr : ℕ → Sum Bool ℕ)).length = 0 by simp]
      simp only [List.getD_cons_zero]
      rw [hb0, List.getD_append_right (List.ofFn x) [b0] false 14 (by simp)]
      simp
    · rw [List.getD_eq_default _ _ (by rw [env0_length]; omega)]
      rw [List.getD_eq_default _ _ (by simp; omega)]
      rfl
  have hbnd0 : ∀ i k, (env0 init).getD i (Sum.inl false) = Sum.inr k →
      k < (([] : List Gate).foldl stepW (List.ofFn x)).length := by
    intro i k hik
    simp only [List.foldl_nil, List.length_ofFn]
    rcases lt_trichotomy i 14 with hlt | rfl | hgt
    · have h1 : i < ((List.range 14).map (Sum.inr : ℕ → Sum Bool ℕ)).length := by simp; exact hlt
      simp only [env0] at hik
      rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1, List.getElem_map,
        List.getElem_range, Sum.inr.injEq] at hik
      omega
    · simp only [env0] at hik
      rw [List.getD_append_right _ _ _ _ (by simp), show 14 - ((List.range 14).map (Sum.inr : ℕ → Sum Bool ℕ)).length = 0 by simp] at hik
      simp only [List.getD_cons_zero] at hik
      exact hinit_bnd k hik
    · rw [List.getD_eq_default _ _ (by rw [env0_length]; omega)] at hik
      cases hik
  have hinv := foldl_stepSimp_inv gs hgs (env0 init) [] (List.ofFn x ++ [b0]) (List.ofFn x)
    (by simp) (fun _ h => nomatch h) (by simp [env0_length]) heq0 hbnd0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact hinv.1 g hg
  · simpa [simpFrom, Circuit.size] using hinv.2.1
  · exact hinv.2.2.1 out
  · intro k hk
    dsimp only [simpFrom] at hk
    have hval := hinv.2.2.1 out
    simp only [Circuit.eval, Circuit.wires, simpFrom, evalSum, hk] at hval ⊢
    exact hval
  · intro hinit_f hex
    have h14 : 14 < (env0 init).length := by rw [env0_length]; omega
    have h14f : (env0 init).getD 14 (Sum.inl false) = Sum.inl false := by
      subst hinit_f
      simp [env0]
    simpa [simpFrom, Circuit.size] using hinv.2.2.2.2 h14 h14f hex

lemma not_const_hit (f : (Fin 14 → Bool) → Bool) (hf : ∀ x, f x = true ↔ hit x) :
    (f (fun _ => false) = false) ∧
    (f (fun i => decide (i = 0 ∨ i = 7)) = true) := by
  constructor
  · by_contra h
    have h1 : f (fun _ => false) = true := Bool.eq_true_of_not_eq_false h
    rcases (hf _).1 h1 with ⟨_, _, _, hu, _⟩
    cases hu
  · apply (hf _).2
    refine ⟨0, 7, ?_, by decide, by decide⟩
    simp [edges]

lemma deg0_not_nil (C : Circuit) (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x) :
    C.gates ≠ [] := by
  intro hnil
  have h0 := (not_const_hit (fun x => C.eval (List.ofFn x)) hC).1
  have h07 := (not_const_hit (fun x => C.eval (List.ofFn x)) hC).2
  by_cases ho : C.output < 14
  · let y : Fin 14 → Bool := fun i => decide (i.val = C.output)
    have hy : C.eval (List.ofFn y) = true := by
      simp only [Circuit.eval, Circuit.wires, hnil, List.foldl_nil]
      rw [List.getD_eq_getElem _ _ (by simp; exact ho), List.getElem_ofFn]
      simp [y]
    rcases (hC y).1 hy with ⟨u, v, huv, hu, hv⟩
    simp only [y, decide_eq_true_eq] at hu hv
    have huv_eq : u.val = v.val := hu.trans hv.symm
    have hne : ∀ p ∈ edges, p.1 ≠ p.2 := by decide
    exact hne (u.val, v.val) huv huv_eq
  · simp only [Circuit.eval, Circuit.wires, hnil, List.foldl_nil] at h07
    rw [List.getD_eq_default _ _ (by simp; omega)] at h07
    cases h07

lemma main :
    ∀ C : Circuit, Monotone2 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x) →
      ∃ T : Circuit, Monotone2 T ∧
        ((T.size + 2 ≤ C.size ∧ withoutEdge T) ∨
         (T.size + 1 ≤ C.size ∧ (tailOK T 1 ∨ tailOK T 7 ∨ tailOK T 9))) := by
  intro C hC_mono hC_hit
  by_cases hmin : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ hit x) → C.size ≤ D.size
  · have hne : C.gates ≠ [] := deg0_not_nil C hC_hit
    cases hgs_eq : C.gates with
    | nil => exact absurd hgs_eq hne
    | cons g₀ gs =>
      have hg₀ : (g₀.op = GateOp.and ∨ g₀.op = GateOp.or) ∧ g₀.inputs.length ≤ 2 := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using
          hC_mono g₀ (by rw [hgs_eq]; exact List.mem_cons_self)
      have hgs_mono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using
          hC_mono g (by rw [hgs_eq]; exact List.mem_cons_of_mem g₀ hg)
      have elim_const_or_wire :
          ∀ (init : Sum Bool ℕ),
            (∀ k, init = Sum.inr k → k < 14) →
            (∀ x : Fin 14 → Bool, evalSum (List.ofFn x) init =
              g₀.op.eval (g₀.inputs.map fun i => (List.ofFn x).getD i false)) →
            False := by
        intro init hinit_bnd hinit_eq
        let pr := simpFrom init gs C.output
        have hfalse := not_const_hit (fun x => C.eval (List.ofFn x)) hC_hit
        have heval_orig : ∀ x : Fin 14 → Bool,
            (gs.foldl stepW (List.ofFn x ++ [evalSum (List.ofFn x) init])).getD C.output false =
            C.eval (List.ofFn x) := by
          intro x
          simp only [Circuit.eval, Circuit.wires, hgs_eq, List.foldl_cons, hinit_eq x]
          rfl
        have hsp_f := simpFrom_spec init hinit_bnd gs hgs_mono C.output (fun _ => false)
          (evalSum (List.ofFn (fun _ => false)) init) rfl
        have hsp_t := simpFrom_spec init hinit_bnd gs hgs_mono C.output
          (fun i => decide (i = 0 ∨ i = 7))
          (evalSum (List.ofFn (fun i => decide (i = 0 ∨ i = 7))) init) rfl
        cases hres : pr.2 with
        | inl b =>
          have hb1 : b = false := by
            have h1 := hsp_f.2.2.1
            change evalSum _ pr.2 = _ at h1
            rw [hres, heval_orig, hfalse.1] at h1
            exact h1
          have hb2 : b = true := by
            have h2 := hsp_t.2.2.1
            change evalSum _ pr.2 = _ at h2
            rw [hres, heval_orig, hfalse.2] at h2
            exact h2
          cases hb1.symm.trans hb2
        | inr out' =>
          have hD_hit : ∀ x : Fin 14 → Bool, pr.1.eval (List.ofFn x) = true ↔ hit x := by
            intro x
            have hsp_x := simpFrom_spec init hinit_bnd gs hgs_mono C.output x
              (evalSum (List.ofFn x) init) rfl
            rw [hsp_x.2.2.2.1 out' hres, heval_orig x]
            exact hC_hit x
          have hle := hmin pr.1 hsp_f.1 hD_hit
          have hsz : pr.1.size ≤ gs.length := hsp_f.2.1
          have hCsz : C.size = gs.length + 1 := by simp [Circuit.size, hgs_eq]
          omega
      have wire_val : ∀ (x : Fin 14 → Bool) (i : ℕ),
          (List.ofFn x).getD i false =
            if h : i < 14 then x ⟨i, h⟩ else false := by
        intro x i
        by_cases h : i < 14
        · simp only [h, dite_true]
          rw [List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn]
        · simp only [h, dite_false]
          exact List.getD_eq_default _ _ (by simp; omega)
      cases h_in : g₀.inputs with
      | nil =>
        rcases hg₀.1 with hop | hop
        · exact False.elim (elim_const_or_wire (Sum.inl true) (fun _ h => by cases h)
            (fun x => by simp [hop, h_in, GateOp.eval, evalSum]))
        · exact False.elim (elim_const_or_wire (Sum.inl false) (fun _ h => by cases h)
            (fun x => by simp [hop, h_in, GateOp.eval, evalSum]))
      | cons a t1 =>
        cases t1 with
        | nil =>
          by_cases ha : a < 14
          · exact False.elim (elim_const_or_wire (Sum.inr a) (fun k hk => by cases hk; exact ha)
              (fun x => by
                rcases hg₀.1 with hop | hop <;>
                  simp [hop, h_in, GateOp.eval, evalSum, wire_val, ha]))
          · exact False.elim (elim_const_or_wire (Sum.inl false) (fun _ h => by cases h)
              (fun x => by
                rcases hg₀.1 with hop | hop <;>
                  simp [hop, h_in, GateOp.eval, evalSum, wire_val, ha]))
        | cons b t2 =>
          cases t2 with
          | nil =>
            by_cases ha : a < 14
            · by_cases hb : b < 14
              · by_cases hab : a = b
                · exact False.elim (elim_const_or_wire (Sum.inr a) (fun k hk => by cases hk; exact ha)
                    (fun x => by
                      subst hab
                      rcases hg₀.1 with hop | hop <;>
                        simp [hop, h_in, GateOp.eval, evalSum, wire_val, ha]))
                · let fa : Fin 14 := ⟨a, ha⟩
                  let fb : Fin 14 := ⟨b, hb⟩
                  have hfab : fa ≠ fb := fun h => hab (Fin.ext_iff.mp h)
                  rcases exists_auto_pair fa fb hfab with ⟨f, hf_auto, hfa, hfb_or, hfb_edge⟩
                  rcases hg₀.1 with hop | hop
                  · by_cases hadj : adj fa fb = true
                    · let C' := permCircuit f C
                      have hC'_mono : Monotone2 C' := permCircuit_mono f C hC_mono
                      have hC'_size : C'.size = C.size := permCircuit_size f C
                      have hC'_hit : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = true ↔ hit x := by
                        intro x
                        rw [permCircuit_eval, hC_hit, hit_comp_auto f hf_auto]
                      have hC'_gates : C'.gates = ⟨GateOp.and, [0, 7]⟩ :: gs.map (permGate f) := by
                        simp only [C', permCircuit, hgs_eq, List.map_cons, permGate, h_in, hop,
                          List.map_nil, permWire, ha, hb, dite_true]
                        rw [show (f fa).val = 0 by rw [hfa]; rfl,
                            show (f fb).val = 7 by rw [hfb_edge hadj]; rfl]
                      let gs' := gs.map (permGate f)
                      have hgs'_mono : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
                        intro g hg
                        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using
                          hC'_mono g (by rw [hC'_gates]; exact List.mem_cons_of_mem _ hg)
                      set pr := simpFrom (Sum.inl false) gs' C'.output
                      have h_orig_eq : ∀ x : Fin 14 → Bool, (x 0 = false ∨ x 7 = false) →
                          (gs'.foldl stepW (List.ofFn x ++ [false])).getD C'.output false =
                          C'.eval (List.ofFn x) := by
                        intro x hx07
                        have hce : C'.eval (List.ofFn x) =
                            (gs'.foldl stepW (stepW (List.ofFn x) ⟨GateOp.and, [0, 7]⟩)).getD C'.output false := by
                          simp only [Circuit.eval, Circuit.wires, hC'_gates, List.foldl_cons]
                          rfl
                        have hand : stepW (List.ofFn x) ⟨GateOp.and, [0, 7]⟩ = List.ofFn x ++ [false] := by
                          simp only [stepW, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
                            List.all_nil, id_eq, Bool.and_true, wire_val]
                          rcases hx07 with h0 | h7
                          · simp [h0]
                          · simp [h7]
                        rw [hce, hand]
                      have hsp_0 := simpFrom_spec (Sum.inl false) (fun _ h => by cases h)
                        gs' hgs'_mono C'.output (fun _ => false) false rfl
                      have hsp_17 := simpFrom_spec (Sum.inl false) (fun _ h => by cases h)
                        gs' hgs'_mono C'.output (fun i => decide (i = 1 ∨ i = 7)) false rfl
                      have hx17_false : (fun i : Fin 14 => decide (i = 1 ∨ i = 7)) 0 = false := by decide
                      have hx17_hit : hit (fun i : Fin 14 => decide (i = 1 ∨ i = 7)) := by
                        refine ⟨1, 7, ?_, by decide, by decide⟩
                        simp [edges]
                      cases hres : pr.2 with
                      | inl b0 =>
                        have hb_f : b0 = false := by
                          have h1 := hsp_0.2.2.1
                          change evalSum _ pr.2 = _ at h1
                          rw [hres, h_orig_eq _ (Or.inl rfl), (not_const_hit _ hC'_hit).1] at h1
                          exact h1
                        have hb_t : b0 = true := by
                          have h2 := hsp_17.2.2.1
                          change evalSum _ pr.2 = _ at h2
                          rw [hres, h_orig_eq _ (Or.inl hx17_false), (hC'_hit _).2 hx17_hit] at h2
                          exact h2
                        cases hb_f.symm.trans hb_t
                      | inr out' =>
                        have hT_off : ∀ x : Fin 14 → Bool, (x 0 = false ∨ x 7 = false) →
                            (pr.1.eval (List.ofFn x) = true ↔ hit x) := by
                          intro x hx07
                          have hspx := simpFrom_spec (Sum.inl false) (fun _ h => by cases h)
                            gs' hgs'_mono C'.output x false rfl
                          rw [hspx.2.2.2.1 out' hres, h_orig_eq x hx07, hC'_hit x]
                        have hT_sz2 : pr.1.size + 2 ≤ C.size := by
                          by_cases hread : ∃ g ∈ gs', 14 ∈ g.inputs
                          · have hlt : pr.1.size < gs'.length := hsp_0.2.2.2.2 rfl hread
                            have hsz' : C.size = gs'.length + 1 := by
                              rw [← hC'_size, Circuit.size, hC'_gates, List.length_cons]
                            omega
                          · push_neg at hread
                            have hT_all : ∀ x : Fin 14 → Bool, pr.1.eval (List.ofFn x) = true ↔ hit x := by
                              intro x
                              have hspx := simpFrom_spec (Sum.inl false) (fun _ h => by cases h)
                                gs' hgs'_mono C'.output x false rfl
                              rw [hspx.2.2.2.1 out' hres]
                              have hun := foldl_unused14 gs' hread (List.ofFn x ++ [false])
                                (List.ofFn x ++ [x 0 && x 7]) (by simp) (by simp)
                                (fun i hi14 => by
                                  rcases lt_trichotomy i 14 with h14 | rfl | h14
                                  · rw [List.getD_append _ _ _ _ (by simp; exact h14),
                                      List.getD_append _ _ _ _ (by simp; exact h14)]
                                  · exact absurd rfl hi14
                                  · rw [List.getD_eq_default _ _ (by simp; omega),
                                      List.getD_eq_default _ _ (by simp; omega)])
                              have hC'out14 : C'.output ≠ 14 := by
                                intro ho14
                                have h1 := (hC'_hit (fun i => decide (i = 1 ∨ i = 7))).2 hx17_hit
                                simp only [Circuit.eval, Circuit.wires, hC'_gates, ho14,
                                  List.foldl_cons] at h1
                                have hlen14 : 14 < (stepW (List.ofFn (fun i : Fin 14 => decide (i = 1 ∨ i = 7)))
                                    ⟨GateOp.and, [0, 7]⟩).length := by simp [stepW]
                                have hpres : (gs'.foldl stepW (stepW (List.ofFn (fun i : Fin 14 => decide (i = 1 ∨ i = 7)))
                                    ⟨GateOp.and, [0, 7]⟩)).getD 14 false =
                                    (stepW (List.ofFn (fun i : Fin 14 => decide (i = 1 ∨ i = 7)))
                                    ⟨GateOp.and, [0, 7]⟩).getD 14 false :=
                                  foldl_stepW_preserves gs' _ 14 hlen14
                                have h1' : (gs'.foldl stepW (stepW (List.ofFn (fun i : Fin 14 => decide (i = 1 ∨ i = 7)))
                                    ⟨GateOp.and, [0, 7]⟩)).getD 14 false = true := h1
                                rw [hpres] at h1'
                                simp [stepW, GateOp.eval, wire_val] at h1'
                              rw [hun.2 C'.output hC'out14]
                              have hstep_eq : stepW (List.ofFn x) ⟨GateOp.and, [0, 7]⟩ =
                                  List.ofFn x ++ [x 0 && x 7] := by
                                simp [stepW, GateOp.eval, wire_val]
                              have hce : C'.eval (List.ofFn x) =
                                  (gs'.foldl stepW (stepW (List.ofFn x) ⟨GateOp.and, [0, 7]⟩)).getD C'.output false := by
                                simp only [Circuit.eval, Circuit.wires, hC'_gates, List.foldl_cons]
                                rfl
                              rw [← hstep_eq, ← hce]
                              exact hC'_hit x
                            have hmin_bad := hmin pr.1 hsp_0.1 hT_all
                            have hsz' : C.size = gs'.length + 1 := by
                              rw [← hC'_size, Circuit.size, hC'_gates, List.length_cons]
                            have hle_gs : pr.1.size ≤ gs'.length := hsp_0.2.1
                            omega
                        have hT_07 : pr.1.eval (List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7))) = false := by
                          by_contra htrue
                          have h07_t : pr.1.eval (List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7))) = true :=
                            Bool.eq_true_of_not_eq_false htrue
                          have hT_all : ∀ x : Fin 14 → Bool, pr.1.eval (List.ofFn x) = true ↔ hit x := by
                            intro x
                            by_cases hx07 : x 0 = false ∨ x 7 = false
                            · exact hT_off x hx07
                            · have hx0 : x 0 = true := by cases h0 : x 0 <;> simp_all
                              have hx7 : x 7 = true := by cases h7 : x 7 <;> simp_all
                              constructor
                              · intro _
                                refine ⟨0, 7, ?_, hx0, hx7⟩
                                simp [edges]
                              · intro _
                                apply circuit_mono pr.1 hsp_0.1
                                  (fun i : Fin 14 => decide (i = 0 ∨ i = 7)) x _ h07_t
                                intro i hi
                                simp only [decide_eq_true_eq] at hi
                                rcases hi with rfl | rfl <;> assumption
                          have hmin_bad := hmin pr.1 hsp_0.1 hT_all
                          omega
                        exact ⟨pr.1, hsp_0.1, Or.inl ⟨hT_sz2, ⟨hT_off, hT_07⟩⟩⟩
                    · set pr := simpFrom (Sum.inl false) gs C.output
                      have hnot_eq : ∀ u v : Fin 14, (u.val, v.val) ∈ edges →
                          ¬ (u.val = a ∧ v.val = b) ∧ ¬ (u.val = b ∧ v.val = a) := by
                        intro u v huv
                        have hadj_uv : adj u v = true := by
                          simp only [adj, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
                          exact ⟨(u.val, v.val), huv, Or.inl ⟨rfl, rfl⟩⟩
                        constructor
                        · rintro ⟨hua, hvb⟩
                          have hu : u = fa := Fin.ext hua
                          have hv : v = fb := Fin.ext hvb
                          rw [hu, hv] at hadj_uv
                          exact hadj hadj_uv
                        · rintro ⟨hub, hva⟩
                          have hadj_symm : ∀ x y : Fin 14, adj x y = adj y x := by decide
                          have hu : u = fb := Fin.ext hub
                          have hv : v = fa := Fin.ext hva
                          rw [hu, hv, hadj_symm fb fa] at hadj_uv
                          exact hadj hadj_uv
                      have hle_C : ∀ x : Fin 14 → Bool,
                          (gs.foldl stepW (List.ofFn x ++ [false])).getD C.output false = true →
                          C.eval (List.ofFn x) = true := by
                        intro x htrue
                        simp only [Circuit.eval, Circuit.wires, hgs_eq, List.foldl_cons]
                        have hm := wires_mono gs (fun g hg => (hgs_mono g hg).1) (List.ofFn x ++ [false])
                          (stepW (List.ofFn x) g₀) (by simp [stepW])
                          (fun i hi => by
                            rcases lt_trichotomy i 14 with h14 | rfl | h14
                            · rw [List.getD_append _ _ _ _ (by simp; exact h14)] at hi
                              simp only [stepW]
                              rw [List.getD_append _ _ _ _ (by simp; exact h14)]
                              exact hi
                            · rw [List.getD_append_right _ _ _ _ (by simp)] at hi
                              simp at hi
                            · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
                              cases hi)
                        exact hm.2 C.output htrue
                      have hsp_0 := simpFrom_spec (Sum.inl false) (fun _ h => by cases h)
                        gs hgs_mono C.output (fun _ => false) false rfl
                      have hsp_07 := simpFrom_spec (Sum.inl false) (fun _ h => by cases h)
                        gs hgs_mono C.output (fun i => decide (i = 0 ∨ i = 7)) false rfl
                      have h_orig_07 : (gs.foldl stepW (List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7)) ++ [false])).getD C.output false = true := by
                        have hne07 := hnot_eq 0 7 (by simp [edges])
                        have hg0_07 : GateOp.and.eval (g₀.inputs.map fun i => (List.ofFn (fun k : Fin 14 => decide (k = 0 ∨ k = 7))).getD i false) = false := by
                          simp only [h_in, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
                            List.all_nil, id_eq, Bool.and_true, wire_val, ha, hb, dite_true]
                          by_cases ha0 : (⟨a, ha⟩ : Fin 14) = 0 ∨ (⟨a, ha⟩ : Fin 14) = 7
                          · by_cases hb0 : (⟨b, hb⟩ : Fin 14) = 0 ∨ (⟨b, hb⟩ : Fin 14) = 7
                            · exfalso
                              rcases ha0 with ha0 | ha0 <;> rcases hb0 with hb0 | hb0
                              · exact hab (congrArg Fin.val (ha0.trans hb0.symm))
                              · exact hne07.1 ⟨(congrArg Fin.val ha0).symm, (congrArg Fin.val hb0).symm⟩
                              · exact hne07.2 ⟨(congrArg Fin.val hb0).symm, (congrArg Fin.val ha0).symm⟩
                              · exact hab (congrArg Fin.val (ha0.trans hb0.symm))
                            · rw [decide_eq_false hb0, Bool.and_false]
                          · rw [decide_eq_false ha0, Bool.false_and]
                        have hc := (not_const_hit _ hC_hit).2
                        simp only [Circuit.eval, Circuit.wires, hgs_eq, List.foldl_cons] at hc
                        have hst : stepW (List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7))) g₀ =
                            List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7)) ++ [false] := by
                          simp only [stepW, hop]
                          rw [hg0_07]
                        rwa [← hst]
                      cases hres : pr.2 with
                      | inl b0 =>
                        have hb_f : b0 = false := by
                          have h1 := hsp_0.2.2.1
                          change evalSum _ pr.2 = _ at h1
                          rw [hres] at h1
                          by_contra hbt
                          have hb_eq : b0 = true := Bool.eq_true_of_not_eq_false hbt
                          rw [hb_eq] at h1
                          have hC0 := hle_C (fun _ => false) h1.symm
                          rw [(not_const_hit _ hC_hit).1] at hC0
                          cases hC0
                        have hb_t : b0 = true := by
                          have h2 := hsp_07.2.2.1
                          change evalSum _ pr.2 = _ at h2
                          rw [hres, h_orig_07] at h2
                          exact h2
                        cases hb_f.symm.trans hb_t
                      | inr out' =>
                        have hD_hit : ∀ x : Fin 14 → Bool, pr.1.eval (List.ofFn x) = true ↔ hit x := by
                          intro x
                          constructor
                          · intro hx
                            have hspx := simpFrom_spec (Sum.inl false) (fun _ h => by cases h)
                              gs hgs_mono C.output x false rfl
                            rw [hspx.2.2.2.1 out' hres] at hx
                            exact (hC_hit x).1 (hle_C x hx)
                          · rintro ⟨u, v, huv, hu, hv⟩
                            let xuv : Fin 14 → Bool := fun i => decide (i = u ∨ i = v)
                            have hneuv := hnot_eq u v huv
                            have hg0_uv : GateOp.and.eval (g₀.inputs.map fun i => (List.ofFn xuv).getD i false) = false := by
                              simp only [h_in, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
                                List.all_nil, id_eq, Bool.and_true, wire_val, ha, hb, dite_true,
                                xuv, decide_eq_true_eq]
                              by_cases hau : ⟨a, ha⟩ = u ∨ ⟨a, ha⟩ = v
                              · by_cases hbv : ⟨b, hb⟩ = u ∨ ⟨b, hb⟩ = v
                                · exfalso
                                  rcases hau with hau | hau <;> rcases hbv with hbv | hbv
                                  · exact hab (congrArg Fin.val (hau.trans hbv.symm))
                                  · exact hneuv.1 ⟨congrArg Fin.val hau.symm, congrArg Fin.val hbv.symm⟩
                                  · exact hneuv.2 ⟨congrArg Fin.val hbv.symm, congrArg Fin.val hau.symm⟩
                                  · exact hab (congrArg Fin.val (hau.trans hbv.symm))
                                · simp [hbv]
                              · simp [hau]
                            have hCuv : C.eval (List.ofFn xuv) = true :=
                              (hC_hit xuv).2 ⟨u, v, huv, by simp [xuv], by simp [xuv]⟩
                            have h_orig_uv : (gs.foldl stepW (List.ofFn xuv ++ [false])).getD C.output false = true := by
                              simp only [Circuit.eval, Circuit.wires, hgs_eq, List.foldl_cons] at hCuv
                              have hst : stepW (List.ofFn xuv) g₀ = List.ofFn xuv ++ [false] := by
                                simp only [stepW, hop]
                                rw [hg0_uv]
                              rwa [← hst]
                            have hspuv := simpFrom_spec (Sum.inl false) (fun _ h => by cases h)
                              gs hgs_mono C.output xuv false rfl
                            have hDuv : pr.1.eval (List.ofFn xuv) = true := by
                              rw [hspuv.2.2.2.1 out' hres, h_orig_uv]
                            apply circuit_mono pr.1 hsp_0.1 xuv x _ hDuv
                            intro i hi
                            simp only [xuv, decide_eq_true_eq] at hi
                            rcases hi with rfl | rfl <;> assumption
                        have hmin_bad := hmin pr.1 hsp_0.1 hD_hit
                        have hsz' : C.size = gs.length + 1 := by simp [Circuit.size, hgs_eq]
                        have hle_gs : pr.1.size ≤ gs.length := hsp_0.2.1
                        omega
                  · let C' := permCircuit f C
                    have hC'_mono : Monotone2 C' := permCircuit_mono f C hC_mono
                    have hC'_size : C'.size = C.size := permCircuit_size f C
                    have hC'_hit : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = true ↔ hit x := by
                      intro x
                      rw [permCircuit_eval, hC_hit, hit_comp_auto f hf_auto]
                    have hC'_gates : C'.gates = ⟨GateOp.or, [0, (f fb).val]⟩ :: gs.map (permGate f) := by
                      simp only [C', permCircuit, hgs_eq, List.map_cons, permGate, h_in, hop,
                        List.map_nil, permWire, ha, hb, dite_true]
                      rw [show (f fa).val = 0 by rw [hfa]; rfl]
                    let T : Circuit := ⟨gs.map (permGate f), C'.output⟩
                    have hT_mono : Monotone2 T := by
                      intro g hg
                      exact hC'_mono g (by rw [hC'_gates]; exact List.mem_cons_of_mem _ hg)
                    have hT_sz : T.size + 1 ≤ C.size := by
                      rw [← hC'_size, Circuit.size, Circuit.size, hC'_gates, List.length_cons]
                    have hT_ok : tailOK T (f fb) := by
                      intro x
                      have hfb14 : (f fb).val < 14 := (f fb).isLt
                      have hstep : stepW (List.ofFn x) ⟨GateOp.or, [0, (f fb).val]⟩ =
                          List.ofFn x ++ [GateOp.or.eval [x 0, x (f fb)]] := by
                        simp only [stepW, List.map_cons, List.map_nil, wire_val, hfb14,
                          dite_true, show (0 : ℕ) < 14 by omega]
                        rfl
                      have hev : T.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x (f fb)]]) =
                          C'.eval (List.ofFn x) := by
                        have hce : C'.eval (List.ofFn x) =
                            ((gs.map (permGate f)).foldl stepW (stepW (List.ofFn x) ⟨GateOp.or, [0, (f fb).val]⟩)).getD C'.output false := by
                          simp only [Circuit.eval, Circuit.wires, hC'_gates, List.foldl_cons]
                          rfl
                        rw [hce, hstep]
                        rfl
                      rw [hev, hC'_hit x]
                    refine ⟨T, hT_mono, Or.inr ⟨hT_sz, ?_⟩⟩
                    rcases hfb_or with h1 | h7 | h9
                    · exact Or.inl (h1 ▸ hT_ok)
                    · exact Or.inr (Or.inl (h7 ▸ hT_ok))
                    · exact Or.inr (Or.inr (h9 ▸ hT_ok))
              · rcases hg₀.1 with hop | hop
                · exact False.elim (elim_const_or_wire (Sum.inl false) (fun _ h => by cases h)
                    (fun x => by simp [hop, h_in, GateOp.eval, evalSum, wire_val, hb]))
                · exact False.elim (elim_const_or_wire (Sum.inr a) (fun k hk => by cases hk; exact ha)
                    (fun x => by simp [hop, h_in, GateOp.eval, evalSum, wire_val, ha, hb]))
            · rcases hg₀.1 with hop | hop
              · exact False.elim (elim_const_or_wire (Sum.inl false) (fun _ h => by cases h)
                  (fun x => by simp [hop, h_in, GateOp.eval, evalSum, wire_val, ha]))
              · by_cases hb : b < 14
                · exact False.elim (elim_const_or_wire (Sum.inr b) (fun k hk => by cases hk; exact hb)
                    (fun x => by simp [hop, h_in, GateOp.eval, evalSum, wire_val, ha, hb]))
                · exact False.elim (elim_const_or_wire (Sum.inl false) (fun _ h => by cases h)
                    (fun x => by simp [hop, h_in, GateOp.eval, evalSum, wire_val, ha, hb]))
          | cons _ _ =>
            have hlen := hg₀.2
            rw [h_in] at hlen
            simp at hlen
  · push_neg at hmin
    rcases hmin with ⟨D, hD_mono, hD_hit, hD_lt⟩
    refine ⟨shiftCircuit D, shiftCircuit_mono D hD_mono, Or.inr ⟨?_, Or.inr (Or.inl ?_)⟩⟩
    · rw [shiftCircuit_size]
      omega
    · intro x
      rw [shiftCircuit_eval, hD_hit x]

end PEqualNP.Outside.L_meta_2274

theorem PEqualNP.Outside.L_meta_2274 : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Fin (14 : ℕ) → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (14 : ℕ)) => ∀ (x5 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x5 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 (0 : Fin (14 : ℕ)), x5 x4]]) = Bool.true ↔ x2 x5; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 : Fin (14 : ℕ) → Bool), x5 (0 : Fin (14 : ℕ)) = Bool.false ∨ x5 (7 : Fin (14 : ℕ)) = Bool.false → (x4.eval (List.ofFn x5) = Bool.true ↔ x2 x5)) ∧ x4.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = (0 : Fin (14 : ℕ)) ∨ x5 = (7 : Fin (14 : ℕ)))) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x7 : Fin (14 : ℕ) → Bool), x5.eval (List.ofFn x7) = Bool.true ↔ x2 x7) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (x8.size + (2 : ℕ) ≤ x5.size ∧ x4 x8 ∨ x8.size + (1 : ℕ) ≤ x5.size ∧ (x3 x8 (1 : Fin (14 : ℕ)) ∨ x3 x8 (7 : Fin (14 : ℕ)) ∨ x3 x8 (9 : Fin (14 : ℕ)))) := by
  exact PEqualNP.Outside.L_meta_2274.main

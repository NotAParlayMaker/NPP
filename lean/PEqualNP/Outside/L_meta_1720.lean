import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1720

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def F {α : Type} (f : Gate → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun d g => d ++ [f g d]) init

def ev (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = F ev C.gates x := rfl

theorem getD_app_lt {α : Type} (A B : List α) (d : α) (i : ℕ) (h : i < A.length) :
    (A ++ B).getD i d = A.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_ge {α : Type} (A B : List α) (d : α) (i : ℕ) (h : A.length ≤ i) :
    (A ++ B).getD i d = B.getD (i - A.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_big {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_true_lt (l : List Bool) (i : ℕ) (h : l.getD i false = true) : i < l.length := by
  by_contra hc
  rw [getD_big l false i (by omega)] at h
  exact absurd h (by decide)

theorem pre_getD {α : Type} {P Q : List α} (h : P <+: Q) (i : ℕ) (d : α) (hi : i < P.length) :
    Q.getD i d = P.getD i d := by
  obtain ⟨r, rfl⟩ := h
  exact getD_app_lt _ _ _ _ hi

theorem pre_zero {P Q : List ℕ} (h : P <+: Q) (u : ℕ) (hu : Q.getD u 0 = 0) : P.getD u 0 = 0 := by
  by_cases hlt : u < P.length
  · rw [← pre_getD h u 0 hlt]
    exact hu
  · exact getD_big _ _ _ (by omega)

theorem F_snoc {α : Type} (f : Gate → List α → α) (gs : List Gate) (g : Gate) (init : List α) :
    F f (gs ++ [g]) init = F f gs init ++ [f g (F f gs init)] := by
  simp [F, List.foldl_append]

theorem F_cons {α : Type} (f : Gate → List α → α) (gs : List Gate) (g : Gate) (init : List α) :
    F f (g :: gs) init = F f gs (init ++ [f g init]) := rfl

theorem F_app {α : Type} (f : Gate → List α → α) (A B : List Gate) (init : List α) :
    F f (A ++ B) init = F f B (F f A init) := by
  simp [F, List.foldl_append]

theorem F_len {α : Type} (f : Gate → List α → α) (gs : List Gate) (init : List α) :
    (F f gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [F]
  | append_singleton gs g ih =>
    rw [F_snoc]
    simp [ih]
    omega

theorem F_pre {α : Type} (f : Gate → List α → α) (gs : List Gate) (init : List α) :
    init <+: F f gs init := by
  induction gs using List.reverseRecOn with
  | nil => exact List.prefix_refl _
  | append_singleton gs g ih =>
    rw [F_snoc]
    exact ih.trans (List.prefix_append _ _)

theorem F_at {α : Type} (f : Gate → List α → α) (g0 : Gate) (d : α) (gs : List Gate) (init : List α)
    (j : ℕ) (hj : j < gs.length) :
    ∃ pre : List α, pre <+: F f gs init ∧ pre.length = init.length + j ∧
      (F f gs init).getD (init.length + j) d = f (gs.getD j g0) pre := by
  induction gs using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton gs g ih =>
    rw [F_snoc]
    by_cases h : j < gs.length
    · obtain ⟨pre, h1, h2, h3⟩ := ih h
      refine ⟨pre, h1.trans (List.prefix_append _ _), h2, ?_⟩
      rw [getD_app_lt _ _ _ _ (by rw [F_len]; omega), h3, getD_app_lt _ _ _ _ h]
    · have hj' : j = gs.length := by
        simp at hj
        omega
      subst hj'
      refine ⟨F f gs init, List.prefix_append _ _, F_len _ _ _, ?_⟩
      rw [getD_app_ge _ _ _ _ (by rw [F_len]), getD_app_ge _ _ _ _ (le_refl _)]
      simp [F_len]

def DP (N : ℕ) (C : Circuit) (w : ℕ) : ℕ := (C.lineDegrees (N + N) (Finset.range N)).getD w 0

def DL (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0

def V (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (Fin.append x y))).getD w false

def AO (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Fr (N : ℕ) (C : Circuit) (h : ℕ) : Prop :=
  DP N C h = 0 ∧ 0 < DL N C h ∧ ∃ j, j < C.gates.length ∧ h ∈ (gateAt C j).inputs ∧
    0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)

def Bd (N : ℕ) (C : Circuit) (j h : ℕ) : Prop :=
  DP N C h = 0 ∧ 0 < DL N C h ∧ h ∈ (gateAt C j).inputs

def SL (N : ℕ) (C : Circuit) (h : ℕ) (w : Fin N) : Prop :=
  V N C (fun _ => false) (fun a => decide (a = w)) h = true ∧
    ∀ w' : Fin N, V N C (fun _ => false) (fun a => decide (a = w')) h = true → w' = w

def IsX (N : ℕ) (C X : Circuit) (ph hb : ℕ → ℕ) (j : ℕ) : Prop :=
  Fr N C (hb j) ∧ ph (hb j) < N + X.gates.length ∧ ∃ w : Fin N, SL N C (hb j) w

def PT (N : ℕ) (C X : Circuit) (ph hb : ℕ → ℕ) (j : ℕ) (p : Fin N) : Prop :=
  Fr N C (hb j) ∧ (X.wires (List.ofFn (fun a : Fin N => decide (a = p)))).getD (ph (hb j)) false = true ∧
    ∃ w1 w2 : Fin N, w1 ≠ w2 ∧ V N C (fun _ => false) (fun a => decide (a = w1)) (hb j) = true ∧
      V N C (fun _ => false) (fun a => decide (a = w2)) (hb j) = true

theorem DP_in (N : ℕ) (C : Circuit) (h : ℕ) (hlt : h < N) : DP N C h = 1 := by
  show (F (fun g d => g.lineDegree d) C.gates
    ((List.range (N + N)).map fun i => if i ∈ Finset.range N then 1 else 0)).getD h 0 = 1
  rw [pre_getD (F_pre _ _ _) h 0 (by simp; omega)]
  have h2 : h < N + N := by omega
  simp [List.getD_eq_getElem?_getD, h2, hlt]

theorem DP_gate0 (n : ℕ) (M : Finset ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (u v : ℕ)
    (hin : (gateAt C j).inputs = [u, v]) (hu : (C.lineDegrees n M).getD u 0 = 0)
    (hv : (C.lineDegrees n M).getD v 0 = 0) : (C.lineDegrees n M).getD (n + j) 0 = 0 := by
  obtain ⟨pre, h1, _, h3⟩ := F_at (fun g d => g.lineDegree d) ⟨GateOp.or, []⟩ 0 C.gates
    ((List.range n).map fun i => if i ∈ M then 1 else 0) j hj
  have hl : ((List.range n).map fun i => if i ∈ M then 1 else 0).length = n := by simp
  rw [hl] at h3
  have pu : pre.getD u 0 = 0 := pre_zero h1 u hu
  have pv : pre.getD v 0 = 0 := pre_zero h1 v hv
  have hin' : (C.gates.getD j ⟨GateOp.or, []⟩).inputs = [u, v] := hin
  show (F (fun g d => g.lineDegree d) C.gates
    ((List.range n).map fun i => if i ∈ M then 1 else 0)).getD (n + j) 0 = 0
  rw [h3]
  unfold Gate.lineDegree
  rw [hin']
  split <;> simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.foldr_cons, List.foldr_nil, pu, pv] <;> simp

def lastIdx {κ : Type} [DecidableEq κ] (cls : ℕ → κ) (c : κ) : ℕ → Option ℕ
  | 0 => none
  | k + 1 => if cls k = c then some k else lastIdx cls c k

theorem lastIdx_none {κ : Type} [DecidableEq κ] (cls : ℕ → κ) (c : κ) :
    ∀ k, lastIdx cls c k = none → ∀ i, i < k → cls i ≠ c := by
  intro k
  induction k with
  | zero =>
    intro _ i hi
    omega
  | succ k ih =>
    intro h i hi
    unfold lastIdx at h
    split at h
    · cases h
    · rename_i hne
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h1 | h1
      · exact ih h i h1
      · rw [h1]
        exact hne

theorem lastIdx_some {κ : Type} [DecidableEq κ] (cls : ℕ → κ) (c : κ) :
    ∀ k i, lastIdx cls c k = some i → i < k ∧ cls i = c ∧ ∀ i', i' < k → cls i' = c → i' ≤ i := by
  intro k
  induction k with
  | zero =>
    intro i h
    simp [lastIdx] at h
  | succ k ih =>
    intro i h
    unfold lastIdx at h
    split at h
    · rename_i he
      have hik : k = i := by
        injection h
      rw [← hik]
      exact ⟨Nat.lt_succ_self _, he, fun i' hi' _ => Nat.lt_succ_iff.1 hi'⟩
    · rename_i hne
      obtain ⟨h1, h2, h3⟩ := ih i h
      refine ⟨Nat.lt_succ_of_lt h1, h2, fun i' hi' hc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h4 | h4
      · exact h3 i' h4 hc
      · rw [h4] at hc
        exact absurd hc hne

def pick (o : Option ℕ) (dflt B : ℕ) : ℕ :=
  match o with
  | some i => B + i
  | none => dflt

theorem pick_cases {κ : Type} [DecidableEq κ] (cls : ℕ → κ) (c : κ) (k dflt B : ℕ) :
    pick (lastIdx cls c k) dflt B = dflt ∨ ∃ i, i < k ∧ pick (lastIdx cls c k) dflt B = B + i := by
  cases hl : lastIdx cls c k with
  | none =>
    left
    rfl
  | some i =>
    right
    exact ⟨i, (lastIdx_some cls c k i hl).1, rfl⟩

def cg {κ : Type} [DecidableEq κ] (B : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (k : ℕ) : Gate :=
  ⟨GateOp.or, [a k, pick (lastIdx cls (cls k) k) (a k) B]⟩

def blk {κ : Type} [DecidableEq κ] (B : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (m : ℕ) : List Gate :=
  (List.range m).map (cg B a cls)

def outw {κ : Type} [DecidableEq κ] (B : ℕ) (cls : ℕ → κ) (m : ℕ) (c : κ) : ℕ :=
  pick (lastIdx cls c m) (B + m) B

theorem blk_len {κ : Type} [DecidableEq κ] (B : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (m : ℕ) :
    (blk B a cls m).length = m := by
  simp [blk]

theorem blk_getD {κ : Type} [DecidableEq κ] (B : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (m k : ℕ) (hk : k < m) :
    (blk B a cls m).getD k ⟨GateOp.or, []⟩ = cg B a cls k := by
  rw [List.getD_eq_getElem _ _ (by rw [blk_len]; exact hk)]
  simp [blk]

theorem evO (a b : ℕ) (w : List Bool) :
    ev ⟨GateOp.or, [a, b]⟩ w = (w.getD a false || w.getD b false) := by
  simp [ev, GateOp.eval]

theorem blk_val {κ : Type} [DecidableEq κ] (W0 : List Bool) (B : ℕ) (hB : W0.length = B) (a : ℕ → ℕ)
    (cls : ℕ → κ) (m : ℕ) (ha : ∀ i, i < m → a i < B) :
    ∀ k, k < m → ((F ev (blk B a cls m) W0).getD (B + k) false = true ↔
      ∃ i, i ≤ k ∧ cls i = cls k ∧ W0.getD (a i) false = true) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨pre, hp1, hp2, hp3⟩ := F_at ev ⟨GateOp.or, []⟩ false (blk B a cls m) W0 k
      (by rw [blk_len]; exact hk)
    rw [hB] at hp2 hp3
    rw [hp3, blk_getD B a cls m k hk]
    have hW0 : W0 <+: F ev (blk B a cls m) W0 := F_pre _ _ _
    have hak := ha k hk
    have e1 : pre.getD (a k) false = W0.getD (a k) false := by
      rw [← pre_getD hp1 (a k) false (by omega), pre_getD hW0 (a k) false (by omega)]
    cases hl : lastIdx cls (cls k) k with
    | none =>
      have hv : ev (cg B a cls k) pre = W0.getD (a k) false := by
        unfold cg
        rw [evO, hl]
        simp only [pick]
        rw [e1, Bool.or_self]
      rw [hv]
      constructor
      · intro h
        exact ⟨k, le_refl _, rfl, h⟩
      · rintro ⟨i, hi, hc, hv'⟩
        rcases Nat.lt_or_eq_of_le hi with h1 | h1
        · exact absurd hc (lastIdx_none cls (cls k) k hl i h1)
        · rw [h1] at hv'
          exact hv'
    | some i0 =>
      obtain ⟨h1, h2, h3⟩ := lastIdx_some cls (cls k) k i0 hl
      have e2 : pre.getD (B + i0) false = (F ev (blk B a cls m) W0).getD (B + i0) false :=
        (pre_getD hp1 (B + i0) false (by omega)).symm
      have hv : ev (cg B a cls k) pre
          = (W0.getD (a k) false || (F ev (blk B a cls m) W0).getD (B + i0) false) := by
        unfold cg
        rw [evO, hl]
        simp only [pick]
        rw [e1, e2]
      rw [hv, Bool.or_eq_true, ih i0 h1 (by omega)]
      constructor
      · rintro (h | ⟨i, hi, hc, hv'⟩)
        · exact ⟨k, le_refl _, rfl, h⟩
        · exact ⟨i, by omega, hc.trans h2, hv'⟩
      · rintro ⟨i, hi, hc, hv'⟩
        rcases Nat.lt_or_eq_of_le hi with h4 | h4
        · exact Or.inr ⟨i, h3 i h4 hc, hc.trans h2.symm, hv'⟩
        · rw [h4] at hv'
          exact Or.inl hv'

theorem blk_out {κ : Type} [DecidableEq κ] (W0 : List Bool) (B : ℕ) (hB : W0.length = B) (a : ℕ → ℕ)
    (cls : ℕ → κ) (m : ℕ) (ha : ∀ i, i < m → a i < B) (c : κ) :
    ((F ev (blk B a cls m) W0).getD (outw B cls m c) false = true ↔
      ∃ i, i < m ∧ cls i = c ∧ W0.getD (a i) false = true) := by
  unfold outw
  cases hl : lastIdx cls c m with
  | none =>
    have hlen : (F ev (blk B a cls m) W0).length = B + m := by
      rw [F_len, hB, blk_len]
    have hf : (F ev (blk B a cls m) W0).getD (B + m) false = false := getD_big _ _ _ (by omega)
    simp only [pick]
    rw [hf]
    constructor
    · intro h
      exact absurd h (by decide)
    · rintro ⟨i, hi, hc, _⟩
      exact absurd hc (lastIdx_none cls c m hl i hi)
  | some i0 =>
    obtain ⟨h1, h2, h3⟩ := lastIdx_some cls c m i0 hl
    simp only [pick]
    rw [blk_val W0 B hB a cls m ha i0 h1]
    constructor
    · rintro ⟨i, hi, hc, hv⟩
      exact ⟨i, by omega, hc.trans h2, hv⟩
    · rintro ⟨i, hi, hc, hv⟩
      exact ⟨i, h3 i hi hc, hc.trans h2.symm, hv⟩

theorem XX_sem {κ : Type} [DecidableEq κ] (n : ℕ) (G : List Gate) (a : ℕ → ℕ) (cls : ℕ → κ) (m : ℕ)
    (ha : ∀ i, i < m → a i < n + G.length) (x : List Bool) (hx : x.length = n) (c : κ) :
    ((Circuit.wires ⟨G ++ blk (n + G.length) a cls m, 0⟩ x).getD (outw (n + G.length) cls m c) false = true ↔
      ∃ i, i < m ∧ cls i = c ∧ (F ev G x).getD (a i) false = true) := by
  have h := blk_out (F ev G x) (n + G.length) (by rw [F_len, hx]) a cls m ha c
  rw [← F_app] at h
  exact h

theorem XX_ao {κ : Type} [DecidableEq κ] (G : List Gate) (B : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (m : ℕ)
    (h0 : ∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ g ∈ (Circuit.mk (G ++ blk B a cls m) 0).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hgm
  rcases List.mem_append.1 hgm with h | h
  · exact h0 g h
  · unfold blk at h
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 h
    exact ⟨Or.inr rfl, rfl⟩

theorem XX_rb {κ : Type} [DecidableEq κ] (n : ℕ) (G : List Gate) (o : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (m : ℕ)
    (h0 : ReadsBack n ⟨G, o⟩) (ha : ∀ i, i < m → a i < n + G.length) :
    ReadsBack n ⟨G ++ blk (n + G.length) a cls m, 0⟩ := by
  intro j hj i hi
  have hj' : j < G.length + m := by
    have h1 : j < (G ++ blk (n + G.length) a cls m).length := hj
    rw [List.length_append, blk_len] at h1
    exact h1
  by_cases h : j < G.length
  · have e : gateAt ⟨G ++ blk (n + G.length) a cls m, 0⟩ j = gateAt ⟨G, o⟩ j :=
      getD_app_lt _ _ _ _ h
    rw [e] at hi
    exact h0 j h i hi
  · have e : gateAt ⟨G ++ blk (n + G.length) a cls m, 0⟩ j = cg (n + G.length) a cls (j - G.length) := by
      show (G ++ blk (n + G.length) a cls m).getD j ⟨GateOp.or, []⟩ = _
      rw [getD_app_ge _ _ _ _ (by omega)]
      exact blk_getD _ _ _ _ _ (by omega)
    rw [e] at hi
    have hi' : i = a (j - G.length) ∨
        i = pick (lastIdx cls (cls (j - G.length)) (j - G.length)) (a (j - G.length)) (n + G.length) := by
      simpa [cg] using hi
    have hak := ha (j - G.length) (by omega)
    rcases hi' with e1 | e1
    · omega
    · rcases pick_cases cls (cls (j - G.length)) (j - G.length) (a (j - G.length)) (n + G.length) with e2 | ⟨i0, hi0, e2⟩
      · omega
      · omega

def tg (N : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun i => i - N)⟩

theorem ycopy (N : ℕ) (y0 : Bool) (gs : List Gate) :
    ∀ wY : List Bool, 0 < wY.length → wY.getD 0 false = y0 →
      F ev gs (List.replicate N y0 ++ wY) = List.replicate N y0 ++ F ev (gs.map (tg N)) wY := by
  induction gs with
  | nil =>
    intro wY _ _
    rfl
  | cons g gs ih =>
    intro wY hpos h0
    rw [F_cons, List.map_cons, F_cons]
    have key : ev g (List.replicate N y0 ++ wY) = ev (tg N g) wY := by
      unfold ev tg
      rw [List.map_map]
      congr 1
      refine List.map_congr_left (fun i _ => ?_)
      show (List.replicate N y0 ++ wY).getD i false = wY.getD (i - N) false
      by_cases hi : i < N
      · rw [getD_app_lt _ _ _ _ (by simp; exact hi), Nat.sub_eq_zero_of_le (Nat.le_of_lt hi), h0]
        simp [List.getD_eq_getElem?_getD, hi]
      · rw [getD_app_ge _ _ _ _ (by simp; omega)]
        simp
    rw [key, List.append_assoc]
    refine ih (wY ++ [ev (tg N g) wY]) (by simp) ?_
    rw [getD_app_lt _ _ _ _ hpos]
    exact h0

theorem aoY (N : ℕ) (C : Circuit) (hg : AO C) :
    ∀ g ∈ C.gates.map (tg N), (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hgm
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hgm
  have := hg g' hg'
  exact ⟨this.1, by simp [tg, this.2]⟩

theorem rbY (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) : ReadsBack N ⟨C.gates.map (tg N), 0⟩ := by
  intro j hj i hi
  have hj' : j < C.gates.length := by
    have h1 : j < (C.gates.map (tg N)).length := hj
    rw [List.length_map] at h1
    exact h1
  have e : gateAt ⟨C.gates.map (tg N), 0⟩ j = tg N (gateAt C j) := by
    show (C.gates.map (tg N)).getD j ⟨GateOp.or, []⟩ = tg N (C.gates.getD j ⟨GateOp.or, []⟩)
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj'), List.getD_eq_getElem _ _ hj']
    simp
  rw [e] at hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hi
  have := hrb j hj' a ha
  omega

theorem filt_len {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun a => !p a)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : p a <;> simp [List.filter_cons, h] <;> omega

theorem getD_mem' (l : List ℕ) (i : ℕ) (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

theorem mem_getD' (l : List ℕ) (j : ℕ) (hj : j ∈ l) : ∃ i, i < l.length ∧ l.getD i 0 = j := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hj
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩

theorem core (N k : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hN0 : 0 < N)
    (hinc : ∃ p l : Fin N, I p l)
    (huq : ∀ p p' w w' : Fin N, p ≠ p' → I p w → I p' w → I p w' → I p' w' → w = w')
    (hk : 1 ≤ k)
    (hA : ∀ (w : ℕ) (xa xb ya yb : Fin N → Bool), (DL N C w = 0 → V N C xa ya w = V N C xa yb w) ∧ (DP N C w = 0 → V N C xa ya w = V N C xb ya w) ∧ V N C (fun _ => false) (fun _ => false) w = false)
    (hB : 0 < DP N C C.output → 0 < DL N C C.output → ∃ (X : Circuit) (ph : ℕ → ℕ) (H : Set ℕ), (AO X ∧ ReadsBack N X) ∧ X.size ≤ Set.ncard {j : ℕ | j < C.gates.length ∧ DL N C (N + N + j) = 0} + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)} ∧ (∀ h ∈ H, Fr N C h) ∧ ∀ x y : Fin N → Bool, (circuitFun (N + N) C (Fin.append x y) = true ↔ (circuitFun (N + N) C (Fin.append x (fun _ => false)) = true ∨ ∃ h : ℕ, Fr N C h ∧ V N C (fun _ => false) y h = true ∧ (h ∈ H ∨ (X.wires (List.ofFn x)).getD (ph h) false = true))))
    (hg : AO C) (hrb : ReadsBack (N + N) C)
    (hacc : ∀ p l : Fin N, I p l → V N C (fun a => decide (a = p)) (fun a => decide (a = l)) C.output = true)
    (hrej : ∀ x y : Fin N → Bool, (Finset.univ.filter (fun l : Fin N => y l = true)).card ≤ k → (∀ p l : Fin N, I p l → x p = true → y l = true → False) → V N C x y C.output = false) :
    ∃ (X Y : Circuit) (ps rh : Fin N → ℕ), (AO X ∧ ReadsBack N X) ∧ (AO Y ∧ ReadsBack N Y) ∧ X.size + Y.size ≤ 5 * C.size ∧ (∀ w p : Fin N, (X.wires (List.ofFn (fun a => decide (a = p)))).getD (ps w) false = true → I p w) ∧ (∀ (w : Fin N) (x : Fin N → Bool), (∀ p : Fin N, I p w → x p = false) → (X.wires (List.ofFn x)).getD (ps w) false = false) ∧ (∀ p l : Fin N, (Y.wires (List.ofFn (fun a => decide (a = l)))).getD (rh p) false = true → I p l) ∧ (∀ (p : Fin N) (y : Fin N → Bool), (Finset.univ.filter (fun l : Fin N => y l = true)).card ≤ k → (∀ l : Fin N, I p l → y l = false) → (Y.wires (List.ofFn y)).getD (rh p) false = false) ∧ (∀ p w : Fin N, I p w → (X.wires (List.ofFn (fun a => decide (a = p)))).getD (ps w) false = true ∨ (Y.wires (List.ofFn (fun a => decide (a = w)))).getD (rh p) false = true) := by
  classical
  obtain ⟨p0, l0, hpl0⟩ := hinc
  have hrej1 : ∀ (x : Fin N → Bool) (w : Fin N), (∀ p, I p w → x p = false) →
      V N C x (fun a => decide (a = w)) C.output = false := by
    intro x w hx
    refine hrej x _ ?_ ?_
    · have e : (Finset.univ.filter (fun l : Fin N => decide (l = w) = true)) = {w} := by
        ext l
        simp
      rw [e, Finset.card_singleton]
      exact hk
    · intro p l hI hp hl
      have e : l = w := of_decide_eq_true hl
      rw [e] at hI
      rw [hx p hI] at hp
      exact absurd hp (by decide)
  have hrej0 : ∀ x : Fin N → Bool, V N C x (fun _ => false) C.output = false := by
    intro x
    refine hrej x _ ?_ ?_
    · simp
    · intro p l _ _ hl
      exact absurd hl (by decide)
  have hoP : 0 < DP N C C.output := by
    by_contra h0
    have h0' : DP N C C.output = 0 := by omega
    have h1 := (hA C.output (fun a => decide (a = p0)) (fun _ => false) (fun a => decide (a = l0)) (fun a => decide (a = l0))).2.1 h0'
    rw [hacc p0 l0 hpl0, hrej1 (fun _ => false) l0 (fun _ _ => rfl)] at h1
    exact absurd h1 (by decide)
  have hoL : 0 < DL N C C.output := by
    by_contra h0
    have h0' : DL N C C.output = 0 := by omega
    have h1 := (hA C.output (fun a => decide (a = p0)) (fun a => decide (a = p0)) (fun a => decide (a = l0)) (fun _ => false)).1 h0'
    rw [hacc p0 l0 hpl0, hrej0] at h1
    exact absurd h1 (by decide)
  obtain ⟨X, ph, H, ⟨hXg, hXr⟩, hXs, hH, hiff⟩ := hB hoP hoL
  have hiff' : ∀ x y : Fin N → Bool, (V N C x y C.output = true ↔ (V N C x (fun _ => false) C.output = true ∨ ∃ h : ℕ, Fr N C h ∧ V N C (fun _ => false) y h = true ∧ (h ∈ H ∨ (X.wires (List.ofFn x)).getD (ph h) false = true))) := hiff
  have hK : ∀ (h : ℕ) (x y : Fin N → Bool), Fr N C h → V N C (fun _ => false) y h = true →
      (X.wires (List.ofFn x)).getD (ph h) false = true → V N C x y C.output = true :=
    fun h x y h1 h2 h3 => (hiff' x y).2 (Or.inr ⟨h, h1, h2, Or.inr h3⟩)
  have hKH : ∀ (h : ℕ) (x y : Fin N → Bool), h ∈ H → V N C (fun _ => false) y h = true →
      V N C x y C.output = true :=
    fun h x y h1 h2 => (hiff' x y).2 (Or.inr ⟨h, hH h h1, h2, Or.inl h1⟩)
  have f2 : ∀ (h : ℕ) (w : Fin N) (x : Fin N → Bool), Fr N C h →
      V N C (fun _ => false) (fun a => decide (a = w)) h = true → (∀ p, I p w → x p = false) →
      (X.wires (List.ofFn x)).getD (ph h) false = false := by
    intro h w x hf hv hx
    by_contra hc
    have h1 := hK h x _ hf hv (Bool.of_not_eq_false hc)
    rw [hrej1 x w hx] at h1
    exact absurd h1 (by decide)
  have f3 : ∀ (h : ℕ) (p l : Fin N), Fr N C h →
      (X.wires (List.ofFn (fun a : Fin N => decide (a = p)))).getD (ph h) false = true →
      V N C (fun _ => false) (fun a => decide (a = l)) h = true → I p l := by
    intro h p l hf hx hv
    by_contra hI
    have h1 := hK h _ _ hf hv hx
    rw [hrej1 _ l (fun p' hp' => decide_eq_false (fun e : p' = p => hI (e ▸ hp')))] at h1
    exact absurd h1 (by decide)
  have f4 : ∀ (h : ℕ) (p : Fin N) (y : Fin N → Bool), Fr N C h →
      (X.wires (List.ofFn (fun a : Fin N => decide (a = p)))).getD (ph h) false = true →
      (Finset.univ.filter (fun l : Fin N => y l = true)).card ≤ k → (∀ l, I p l → y l = false) →
      V N C (fun _ => false) y h = false := by
    intro h p y hf hx hc hy
    by_contra hv
    have h1 := hK h _ y hf (Bool.of_not_eq_false hv) hx
    rw [hrej _ y hc (fun p' l hI hp' hl => by
      have e : p' = p := of_decide_eq_true hp'
      rw [e] at hI
      rw [hy l hI] at hl
      exact absurd hl (by decide))] at h1
    exact absurd h1 (by decide)
  have f5 : ∀ p w : Fin N, I p w → ∃ h, Fr N C h ∧
      V N C (fun _ => false) (fun a => decide (a = w)) h = true ∧
      (X.wires (List.ofFn (fun a : Fin N => decide (a = p)))).getD (ph h) false = true := by
    intro p w hI
    rcases (hiff' _ _).1 (hacc p w hI) with h | ⟨h, hf, hv, hh | hx⟩
    · rw [hrej0] at h
      exact absurd h (by decide)
    · have h1 := hKH h (fun _ => false) _ hh hv
      rw [hrej1 _ w (fun _ _ => rfl)] at h1
      exact absurd h1 (by decide)
    · exact ⟨h, hf, hv, hx⟩
  have hDPin : ∀ h, DP N C h = 0 → N ≤ h := by
    intro h h0
    by_contra hlt
    have h1 := DP_in N C h (by omega)
    omega
  have hYv : ∀ (h : ℕ) (y : Fin N → Bool), DP N C h = 0 →
      (F ev (C.gates.map (tg N)) (List.ofFn y)).getD (h - N) false = V N C (fun _ => false) y h := by
    intro h y h0
    have hNh := hDPin h h0
    have hy1 : 0 < (List.ofFn y).length := by
      rw [List.length_ofFn]
      exact hN0
    have hy2 : (List.ofFn y).getD 0 false = y ⟨0, hN0⟩ := by
      rw [List.getD_eq_getElem _ _ hy1]
      simp
    have e := ycopy N (y ⟨0, hN0⟩) C.gates (List.ofFn y) hy1 hy2
    refine Eq.trans ?_ ((hA h (fun _ => y ⟨0, hN0⟩) (fun _ => false) y y).2.1 h0)
    show _ = (C.wires (List.ofFn (Fin.append (fun _ => y ⟨0, hN0⟩) y))).getD h false
    rw [List.ofFn_fin_append, List.ofFn_const, wires_eq, e,
      getD_app_ge _ _ _ _ (by rw [List.length_replicate]; exact hNh), List.length_replicate]
  have hgate : ∀ j, j < C.gates.length → gateAt C j ∈ C.gates := by
    intro j hj
    show C.gates.getD j ⟨GateOp.or, []⟩ ∈ C.gates
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have huniqB : ∀ j h h', j < C.gates.length → 0 < DP N C (N + N + j) → DP N C h = 0 →
      DP N C h' = 0 → h ∈ (gateAt C j).inputs → h' ∈ (gateAt C j).inputs → h = h' := by
    intro j h h' hj hm h0 h0' hi hi'
    by_contra hne
    obtain ⟨u, v, huv⟩ := List.length_eq_two.1 (hg _ (hgate j hj)).2
    rw [huv] at hi hi'
    have hi2 : h = u ∨ h = v := by simpa using hi
    have hi2' : h' = u ∨ h' = v := by simpa using hi'
    have huv0 : DP N C u = 0 ∧ DP N C v = 0 := by
      rcases hi2 with e1 | e1 <;> rcases hi2' with e2 | e2
      · exact absurd (e1.trans e2.symm) hne
      · rw [← e1, ← e2]
        exact ⟨h0, h0'⟩
      · rw [← e1, ← e2]
        exact ⟨h0', h0⟩
      · exact absurd (e1.trans e2.symm) hne
    have h1 : DP N C (N + N + j) = 0 :=
      DP_gate0 (N + N) (Finset.range N) C j hj u v huv huv0.1 huv0.2
    omega
  have hex : ∀ j, ∃ hbj : ℕ, (∀ h, Bd N C j h → Bd N C j hbj) ∧ ((¬ ∃ h, Bd N C j h) → hbj = N) := by
    intro j
    by_cases hh : ∃ h, Bd N C j h
    · obtain ⟨h0, hh0⟩ := hh
      exact ⟨h0, fun _ _ => hh0, fun hn => absurd ⟨h0, hh0⟩ hn⟩
    · exact ⟨N, fun h hh' => absurd ⟨h, hh'⟩ hh, fun _ => rfl⟩
  choose hb hb1 hb2 using hex
  have hbeq : ∀ j h, j < C.gates.length → 0 < DP N C (N + N + j) → Bd N C j h → hb j = h := by
    intro j h hj hm hbd
    have h' := hb1 j h hbd
    exact huniqB j _ _ hj hm h'.1 hbd.1 h'.2.2 hbd.2.2
  have hblt : ∀ j, j < C.gates.length → hb j < N + N + C.gates.length := by
    intro j hj
    by_cases hh : ∃ h, Bd N C j h
    · obtain ⟨h, hh⟩ := hh
      have h1 := hrb j hj _ (hb1 j h hh).2.2
      omega
    · rw [hb2 j hh]
      omega
  have hXlen : ∀ x : Fin N → Bool, (F ev X.gates (List.ofFn x)).length = N + X.gates.length := by
    intro x
    rw [F_len, List.length_ofFn]
  have hexw : ∀ j, ∃ o : Option (Fin N), (∀ w, SL N C (hb j) w → o = some w) ∧
      (∀ w, o = some w → SL N C (hb j) w) := by
    intro j
    by_cases hh : ∃ w, SL N C (hb j) w
    · obtain ⟨w0, hw0⟩ := hh
      refine ⟨some w0, fun w hw => congrArg some (hw0.2 w hw.1).symm, fun w e => ?_⟩
      cases e
      exact hw0
    · exact ⟨none, fun w hw => absurd ⟨w, hw⟩ hh, fun w e => by cases e⟩
  choose wx wx1 wx2 using hexw
  have hexp : ∀ j, ∃ o : Option (Fin N), (∀ p, PT N C X ph hb j p → o = some p) ∧
      (∀ p, o = some p → PT N C X ph hb j p) := by
    intro j
    by_cases hh : ∃ p, PT N C X ph hb j p
    · obtain ⟨p1, hp1⟩ := hh
      refine ⟨some p1, fun p hp => ?_, fun p e => ?_⟩
      · by_contra hne
        have hne' : p ≠ p1 := fun e => hne (by rw [e])
        obtain ⟨hf, hx, w1, w2, hw, hv1, hv2⟩ := hp
        exact hw (huq p p1 w1 w2 hne' (f3 _ p w1 hf hx hv1) (f3 _ p1 w1 hf hp1.2.1 hv1)
          (f3 _ p w2 hf hx hv2) (f3 _ p1 w2 hf hp1.2.1 hv2))
      · cases e
        exact hp1
    · exact ⟨none, fun p hp => absurd ⟨p, hp⟩ hh, fun p e => by cases e⟩
  choose py py1 py2 using hexp
  obtain ⟨ML, hML, hMLlen⟩ : ∃ ML : List ℕ, (∀ j, j ∈ ML ↔ (j < C.gates.length ∧ 0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j))) ∧ ML.length = (Finset.filter (fun j => 0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)) (Finset.range C.gates.length)).card :=
    ⟨(Finset.filter (fun j => 0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)) (Finset.range C.gates.length)).toList, by intro j; simp, Finset.length_toList _⟩
  obtain ⟨MLX, MLY, hMLX, hMLY, hsum⟩ : ∃ MLX MLY : List ℕ, (∀ j, j ∈ MLX ↔ (j ∈ ML ∧ IsX N C X ph hb j)) ∧ (∀ j, j ∈ MLY ↔ (j ∈ ML ∧ ¬ IsX N C X ph hb j)) ∧ MLX.length + MLY.length = ML.length :=
    ⟨ML.filter (fun j => decide (IsX N C X ph hb j)), ML.filter (fun j => !decide (IsX N C X ph hb j)), by intro j; simp, by intro j; simp, filt_len _ _⟩
  obtain ⟨aX, haXd⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = ph (hb (MLX.getD i 0)) := ⟨_, fun _ => rfl⟩
  obtain ⟨cX, hcXd⟩ : ∃ f : ℕ → Option (Fin N), ∀ i, f i = wx (MLX.getD i 0) := ⟨_, fun _ => rfl⟩
  obtain ⟨aY, haYd⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = hb (MLY.getD i 0) - N := ⟨_, fun _ => rfl⟩
  obtain ⟨cY, hcYd⟩ : ∃ f : ℕ → Option (Fin N), ∀ i, f i = py (MLY.getD i 0) := ⟨_, fun _ => rfl⟩
  have haX : ∀ i, i < MLX.length → aX i < N + X.gates.length := by
    intro i hi
    rw [haXd]
    exact ((hMLX _).1 (getD_mem' MLX i hi)).2.2.1
  have hYGlen : (C.gates.map (tg N)).length = C.gates.length := List.length_map _
  have haY : ∀ i, i < MLY.length → aY i < N + (C.gates.map (tg N)).length := by
    intro i hi
    rw [haYd, hYGlen]
    have h1 := hblt _ ((hML _).1 ((hMLY _).1 (getD_mem' MLY i hi)).1).1
    omega
  have semX : ∀ (w : Fin N) (x : Fin N → Bool),
      ((Circuit.wires ⟨X.gates ++ blk (N + X.gates.length) aX cX MLX.length, 0⟩ (List.ofFn x)).getD
        (outw (N + X.gates.length) cX MLX.length (some w)) false = true ↔
      ∃ i, i < MLX.length ∧ cX i = some w ∧ (F ev X.gates (List.ofFn x)).getD (aX i) false = true) :=
    fun w x => XX_sem N X.gates aX cX MLX.length haX (List.ofFn x) (List.length_ofFn) (some w)
  have semY : ∀ (p : Fin N) (y : Fin N → Bool),
      ((Circuit.wires ⟨C.gates.map (tg N) ++ blk (N + (C.gates.map (tg N)).length) aY cY MLY.length, 0⟩ (List.ofFn y)).getD
        (outw (N + (C.gates.map (tg N)).length) cY MLY.length (some p)) false = true ↔
      ∃ i, i < MLY.length ∧ cY i = some p ∧ (F ev (C.gates.map (tg N)) (List.ofFn y)).getD (aY i) false = true) :=
    fun p y => XX_sem N (C.gates.map (tg N)) aY cY MLY.length haY (List.ofFn y) (List.length_ofFn) (some p)
  have hc2 : ∀ (w : Fin N) (x : Fin N → Bool), (∀ p : Fin N, I p w → x p = false) →
      (Circuit.wires ⟨X.gates ++ blk (N + X.gates.length) aX cX MLX.length, 0⟩ (List.ofFn x)).getD
        (outw (N + X.gates.length) cX MLX.length (some w)) false = false := by
    intro w x hx
    by_contra hc
    obtain ⟨i, hi, hc1, hv⟩ := (semX w x).1 (Bool.of_not_eq_false hc)
    have hj := (hMLX _).1 (getD_mem' MLX i hi)
    rw [hcXd] at hc1
    rw [haXd] at hv
    have hsl := wx2 _ w hc1
    have h1 := f2 _ w x hj.2.1 hsl.1 hx
    have hv' : (X.wires (List.ofFn x)).getD (ph (hb (MLX.getD i 0))) false = true := hv
    rw [h1] at hv'
    exact absurd hv' (by decide)
  refine ⟨⟨X.gates ++ blk (N + X.gates.length) aX cX MLX.length, 0⟩,
    ⟨C.gates.map (tg N) ++ blk (N + (C.gates.map (tg N)).length) aY cY MLY.length, 0⟩,
    fun w => outw (N + X.gates.length) cX MLX.length (some w),
    fun p => outw (N + (C.gates.map (tg N)).length) cY MLY.length (some p),
    ⟨XX_ao _ _ _ _ _ hXg, XX_rb N X.gates X.output aX cX MLX.length hXr haX⟩,
    ⟨XX_ao _ _ _ _ _ (aoY N C hg), XX_rb N (C.gates.map (tg N)) 0 aY cY MLY.length (rbY N C hrb) haY⟩,
    ?_, ?_, hc2, ?_, ?_, ?_⟩
  · show (X.gates ++ blk (N + X.gates.length) aX cX MLX.length).length
      + (C.gates.map (tg N) ++ blk (N + (C.gates.map (tg N)).length) aY cY MLY.length).length ≤ 5 * C.gates.length
    rw [List.length_append, List.length_append, blk_len, blk_len, hYGlen]
    have e1 : {j : ℕ | j < C.gates.length ∧ DL N C (N + N + j) = 0} = ↑(Finset.filter (fun j => DL N C (N + N + j) = 0) (Finset.range C.gates.length)) := by
      ext j
      simp
    have e2 : {j : ℕ | j < C.gates.length ∧ 0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)} = ↑(Finset.filter (fun j => 0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)) (Finset.range C.gates.length)) := by
      ext j
      simp
    rw [e1, e2, Set.ncard_coe_finset, Set.ncard_coe_finset] at hXs
    have hXs' : X.gates.length ≤ (Finset.filter (fun j => DL N C (N + N + j) = 0) (Finset.range C.gates.length)).card + 3 * (Finset.filter (fun j => 0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)) (Finset.range C.gates.length)).card := hXs
    have hdis : (Finset.filter (fun j => DL N C (N + N + j) = 0) (Finset.range C.gates.length)).card + (Finset.filter (fun j => 0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)) (Finset.range C.gates.length)).card ≤ C.gates.length := by
      rw [← Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_filter]
        intro j _ h1 h2
        omega)]
      calc _ ≤ (Finset.range C.gates.length).card :=
            Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
        _ = C.gates.length := Finset.card_range _
    omega
  · intro w p hv
    by_contra hI
    rw [hc2 w _ (fun p' hp' => decide_eq_false (fun e : p' = p => hI (e ▸ hp')))] at hv
    exact absurd hv (by decide)
  · intro p l hv
    obtain ⟨i, hi, hc1, hv1⟩ := (semY p _).1 hv
    rw [hcYd] at hc1
    rw [haYd] at hv1
    have hpt := py2 _ p hc1
    rw [hYv _ _ hpt.1.1] at hv1
    exact f3 _ p l hpt.1 hpt.2.1 hv1
  · intro p y hcard hy
    by_contra hc
    obtain ⟨i, hi, hc1, hv1⟩ := (semY p y).1 (Bool.of_not_eq_false hc)
    rw [hcYd] at hc1
    rw [haYd] at hv1
    have hpt := py2 _ p hc1
    rw [hYv _ _ hpt.1.1, f4 _ p y hpt.1 hpt.2.1 hcard hy] at hv1
    exact absurd hv1 (by decide)
  · intro p w hI
    obtain ⟨h, hf, hv, hx⟩ := f5 p w hI
    obtain ⟨hf0, hf1, j, hj, hin, hm1, hm2⟩ := id hf
    have hbj : hb j = h := hbeq j h hj hm1 ⟨hf0, hf1, hin⟩
    have hjML : j ∈ ML := (hML j).2 ⟨hj, hm1, hm2⟩
    by_cases hs : ∀ w' : Fin N, V N C (fun _ => false) (fun a => decide (a = w')) h = true → w' = w
    · left
      have hlt : ph h < N + X.gates.length := by
        have h1 : (F ev X.gates (List.ofFn (fun a : Fin N => decide (a = p)))).getD (ph h) false = true := hx
        have h2 := getD_true_lt _ _ h1
        rw [hXlen] at h2
        exact h2
      have hX : IsX N C X ph hb j := by
        show Fr N C (hb j) ∧ ph (hb j) < N + X.gates.length ∧ ∃ w : Fin N, SL N C (hb j) w
        rw [hbj]
        exact ⟨hf, hlt, w, hv, hs⟩
      obtain ⟨i, hi, e⟩ := mem_getD' MLX j ((hMLX j).2 ⟨hjML, hX⟩)
      refine (semX w _).2 ⟨i, hi, ?_, ?_⟩
      · rw [hcXd, e]
        refine wx1 j w ?_
        rw [hbj]
        exact ⟨hv, hs⟩
      · rw [haXd, e, hbj]
        exact hx
    · right
      push_neg at hs
      obtain ⟨w', hv', hne⟩ := hs
      have hnX : ¬ IsX N C X ph hb j := by
        rintro ⟨_, _, w0, hw0⟩
        rw [hbj] at hw0
        exact hne ((hw0.2 w' hv').trans (hw0.2 w hv).symm)
      obtain ⟨i, hi, e⟩ := mem_getD' MLY j ((hMLY j).2 ⟨hjML, hnX⟩)
      refine (semY p _).2 ⟨i, hi, ?_, ?_⟩
      · rw [hcYd, e]
        refine py1 j p ?_
        show Fr N C (hb j) ∧ (X.wires (List.ofFn (fun a : Fin N => decide (a = p)))).getD (ph (hb j)) false = true ∧ ∃ w1 w2 : Fin N, w1 ≠ w2 ∧ V N C (fun _ => false) (fun a => decide (a = w1)) (hb j) = true ∧ V N C (fun _ => false) (fun a => decide (a = w2)) (hb j) = true
        rw [hbj]
        exact ⟨hf, hx, w, w', fun e' => hne e'.symm, hv, hv'⟩
      · rw [haYd, e, hbj, hYv h _ hf0]
        exact hv

end PEqualNP.Outside.L_meta_1720

theorem PEqualNP.Outside.L_meta_1720 : (∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → (∀ (N22 : ℕ) (C22 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g22 ∈ C22.gates, (g22.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N22 + N22) C22 → (∀ j22b < C22.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD i22 0 = 0) ∨ (∀ h22b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22b 0 = 0)) → 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD C22.output 0 → 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD C22.output 0 → ∃ (X22 : PEqualNP.CircuitLowerBounds.Circuit) (ph22 : ℕ → ℕ) (H22 : Set ℕ), ((∀ g22a ∈ X22.gates, (g22a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N22 X22) ∧ X22.size ≤ Set.ncard {j22 : ℕ | j22 < C22.gates.length ∧ (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22) 0 = 0} + 3 * Set.ncard {j22a : ℕ | j22a < C22.gates.length ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22a) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22a) 0} ∧ (∀ h22 ∈ H22, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22 0 ∧ ∃ j22c < C22.gates.length, h22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22c).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22c) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22c) 0)) ∧ ∀ x22 y22 : Fin N22 → Bool, (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 y22) = true ↔ (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 (fun u22 : Fin N22 => false)) = true ∨ ∃ h22a : ℕ, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22a 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22a 0 ∧ ∃ j22d < C22.gates.length, h22a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22d).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22d) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22d) 0) ∧ (C22.wires (List.ofFn (Fin.append (fun u22a : Fin N22 => false) y22))).getD h22a false = true ∧ (h22a ∈ H22 ∨ (X22.wires (List.ofFn x22)).getD (ph22 h22a) false = true)))) → ∀ (q20 N20 k20 : ℕ) (I20 : Fin N20 → Fin N20 → Prop) [DecidableRel I20] (C20 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q20 → N20 = q20 ^ 2 + q20 + 1 → (∀ l20c : Fin N20, (Finset.univ.filter (fun p20f => I20 p20f l20c)).card = q20 + 1) → (∀ pa20 pb20 : Fin N20, pa20 ≠ pb20 → ∃! lb20 : Fin N20, I20 pa20 lb20 ∧ I20 pb20 lb20) → 1 ≤ k20 → (∀ g20 ∈ C20.gates, (g20.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N20 + N20) C20 → (∀ j20 < C20.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.Ico N20 (N20 + N20))).getD i20 0 = 0) ∨ (∀ h20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.range N20)).getD h20 0 = 0)) → (∀ p20g l20d : Fin N20, I20 p20g l20d → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 (fun i20a => decide (i20a = Fin.castAdd N20 p20g ∨ i20a = Fin.natAdd N20 l20d)) = true) → (∀ z20 : Fin (N20 + N20) → Bool, (Finset.univ.filter (fun l20e : Fin N20 => z20 (Fin.natAdd N20 l20e) = true)).card ≤ k20 → (¬ ∃ p20h l20f : Fin N20, I20 p20h l20f ∧ z20 (Fin.castAdd N20 p20h) = true ∧ z20 (Fin.natAdd N20 l20f) = true) → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 z20 = false) → ∃ (X20 Y20 : PEqualNP.CircuitLowerBounds.Circuit) (ps20 rh20 : Fin N20 → ℕ), ((∀ g20a ∈ X20.gates, (g20a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 X20) ∧ ((∀ g20b ∈ Y20.gates, (g20b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 Y20) ∧ X20.size + Y20.size ≤ 5 * C20.size ∧ (∀ w20 p20 : Fin N20, (X20.wires (List.ofFn (fun a20 => decide (a20 = p20)))).getD (ps20 w20) false = true → I20 p20 w20) ∧ (∀ (w20a : Fin N20) (x20 : Fin N20 → Bool), (∀ p20a : Fin N20, I20 p20a w20a → x20 p20a = false) → (X20.wires (List.ofFn x20)).getD (ps20 w20a) false = false) ∧ (∀ p20b l20 : Fin N20, (Y20.wires (List.ofFn (fun a20a => decide (a20a = l20)))).getD (rh20 p20b) false = true → I20 p20b l20) ∧ (∀ (p20c : Fin N20) (y20 : Fin N20 → Bool), (Finset.univ.filter (fun l20a : Fin N20 => y20 l20a = true)).card ≤ k20 → (∀ l20b : Fin N20, I20 p20c l20b → y20 l20b = false) → (Y20.wires (List.ofFn y20)).getD (rh20 p20c) false = false) ∧ (∀ p20d w20b : Fin N20, I20 p20d w20b → (X20.wires (List.ofFn (fun a20b => decide (a20b = p20d)))).getD (ps20 w20b) false = true ∨ (Y20.wires (List.ofFn (fun a20c => decide (a20c = w20b)))).getD (rh20 p20d) false = true) := by
  intro hA hB q N k I _ C hq hN hline huniq hk hg hrb hkm0 hacc hrej
  have hN0 : 0 < N := by
    rw [hN]
    exact Nat.succ_pos _
  have hinc : ∃ p l : Fin N, I p l := by
    have h1 := hline ⟨0, hN0⟩
    have h2 : 0 < (Finset.univ.filter (fun p => I p ⟨0, hN0⟩)).card := by
      rw [h1]
      exact Nat.succ_pos _
    obtain ⟨p, hp⟩ := Finset.card_pos.1 h2
    exact ⟨p, ⟨0, hN0⟩, (Finset.mem_filter.1 hp).2⟩
  have huq : ∀ p p' w w' : Fin N, p ≠ p' → I p w → I p' w → I p w' → I p' w' → w = w' := by
    intro p p' w w' hne h1 h2 h3 h4
    exact (huniq p p' hne).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  have happ : ∀ (p l : Fin N), (fun i : Fin (N + N) => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = Fin.append (fun a => decide (a = p)) (fun a => decide (a = l)) := by
    intro p l
    funext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [Fin.append_left]
      have h1 : Fin.castAdd N a ≠ Fin.natAdd N l := by
        intro h
        have h' := congrArg Fin.val h
        simp at h'
        omega
      have h2 : (Fin.castAdd N a = Fin.castAdd N p) ↔ a = p := by
        constructor
        · intro h
          have h' := congrArg Fin.val h
          exact Fin.ext (by simpa using h')
        · intro h
          rw [h]
      exact decide_eq_decide.2 ⟨fun h => h.elim h2.1 (fun h' => absurd h' h1), fun h => Or.inl (h2.2 h)⟩
    · rw [Fin.append_right]
      have h1 : Fin.natAdd N a ≠ Fin.castAdd N p := by
        intro h
        have h' := congrArg Fin.val h
        simp at h'
        omega
      have h2 : (Fin.natAdd N a = Fin.natAdd N l) ↔ a = l := by
        constructor
        · intro h
          have h' := congrArg Fin.val h
          exact Fin.ext (by simpa using h')
        · intro h
          rw [h]
      exact decide_eq_decide.2 ⟨fun h => h.elim (fun h' => absurd h' h1) h2.1, fun h => Or.inr (h2.2 h)⟩
  refine PEqualNP.Outside.L_meta_1720.core N k I C hN0 hinc huq hk (hA N C hg hrb hkm0).1 (hB N C hg hrb hkm0) hg hrb ?_ ?_
  · intro p l hI
    have h1 := hacc p l hI
    rw [happ] at h1
    exact h1
  · intro x y hc hno
    refine hrej (Fin.append x y) ?_ ?_
    · have e : (Finset.univ.filter (fun l : Fin N => Fin.append x y (Fin.natAdd N l) = true)) = (Finset.univ.filter (fun l : Fin N => y l = true)) := by
        ext l
        rw [Finset.mem_filter, Finset.mem_filter, Fin.append_right]
      rw [e]
      exact hc
    · rintro ⟨p, l, hI, hp, hl⟩
      rw [Fin.append_left] at hp
      rw [Fin.append_right] at hl
      exact hno p l hI hp hl

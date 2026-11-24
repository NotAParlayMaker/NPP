import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1600

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl stp (List.ofFn x)

def K (n : ℕ) (gs : List Gate) : List (List ℕ) :=
  gs.foldl (coneStep n) []

def dg : Gate := ⟨GateOp.or, []⟩

theorem getD_snoc {α : Type} (L : List α) (v d : α) (i : ℕ) :
    (L ++ [v]).getD i d = if i = L.length then v else L.getD i d := by
  rcases lt_trichotomy i L.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem W_snoc {n : ℕ} (x : Fin n → Bool) (gs : List Gate) (g : Gate) :
    W (gs ++ [g]) x
      = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  unfold W
  rw [List.foldl_append]
  rfl

theorem W_len {n : ℕ} (x : Fin n → Bool) (gs : List Gate) :
    (W gs x).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, List.length_append, ih, List.length_append]
    simp
    omega

theorem K_snoc (n : ℕ) (gs : List Gate) (g : Gate) :
    K n (gs ++ [g]) = K n gs ++
      [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + (K n gs).length))).flatMap
        (fun w => (w - n) :: (K n gs).getD (w - n) [])] := by
  unfold K
  rw [List.foldl_append]
  rfl

theorem K_len (n : ℕ) (gs : List Gate) : (K n gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [K]
  | append_singleton gs g ih =>
    rw [K_snoc, List.length_append, ih, List.length_append]
    simp

theorem W_inp {n : ℕ} (x : Fin n → Bool) (gs : List Gate) (r : Fin n) :
    (W gs x).getD r.val false = x r := by
  induction gs using List.reverseRecOn with
  | nil =>
    show (List.ofFn x).getD r.val false = x r
    rw [ofFn_getD, dif_pos r.isLt]
  | append_singleton gs g ih =>
    rw [W_snoc, getD_snoc, W_len, if_neg (by have := r.isLt; omega), ih]

theorem W_gate {n : ℕ} (x : Fin n → Bool) (gs : List Gate) : ∀ k, k < gs.length →
    (W gs x).getD (n + k) false = (gs.getD k dg).op.eval ((gs.getD k dg).inputs.map
      fun i => decide (i < n + k) && (W gs x).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil => intro k hk; simp at hk
  | append_singleton gs g ih =>
    intro k hk
    have hk' : k < gs.length ∨ k = gs.length := by
      rw [List.length_append] at hk
      simp at hk
      omega
    have e1 : (W (gs ++ [g]) x).getD (n + k) false
        = if k = gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
          else (W gs x).getD (n + k) false := by
      rw [W_snoc, getD_snoc, W_len]
      by_cases h : k = gs.length
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    have e2 : (gs ++ [g]).getD k dg = if k = gs.length then g else gs.getD k dg :=
      getD_snoc gs g dg k
    have e3 : ∀ i, i < n + k → (W (gs ++ [g]) x).getD i false = (W gs x).getD i false := by
      intro i hi
      rw [W_snoc, getD_snoc, W_len, if_neg (by omega)]
    rw [e1, e2]
    rcases hk' with h | h
    · rw [if_neg (by omega), if_neg (by omega), ih k h]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [e3 i hi]
      · simp [hi]
    · subst h
      rw [if_pos rfl, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + gs.length
      · rw [e3 i hi]
        simp [hi]
      · have : (W gs x).getD i false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [W_len]; omega)]
          rfl
        rw [this]
        simp [hi]

theorem K_mem (n : ℕ) (gs : List Gate) : ∀ k, k < gs.length →
    ∀ w ∈ (gs.getD k dg).inputs, n ≤ w → w < n + k →
    (w - n) ∈ (K n gs).getD k [] ∧
      ∀ i ∈ (K n gs).getD (w - n) [], i ∈ (K n gs).getD k [] := by
  induction gs using List.reverseRecOn with
  | nil => intro k hk; simp at hk
  | append_singleton gs g ih =>
    intro k hk w hw h1 h2
    have hk' : k < gs.length ∨ k = gs.length := by
      rw [List.length_append] at hk
      simp at hk
      omega
    have e2 : (gs ++ [g]).getD k dg = if k = gs.length then g else gs.getD k dg :=
      getD_snoc gs g dg k
    rw [e2] at hw
    rw [K_snoc]
    simp only [getD_snoc, K_len]
    rcases hk' with h | h
    · rw [if_neg (by omega)] at hw
      rw [if_neg (by omega), if_neg (by omega)]
      exact ih k h w hw h1 h2
    · subst h
      rw [if_pos rfl] at hw
      rw [if_pos rfl, if_neg (by omega)]
      constructor
      · simp only [List.mem_flatMap, List.mem_filter]
        exact ⟨w, ⟨hw, by simp; omega⟩, by simp⟩
      · intro i hi
        simp only [List.mem_flatMap, List.mem_filter]
        exact ⟨w, ⟨hw, by simp; omega⟩, List.mem_cons_of_mem _ hi⟩

theorem orpath {n : ℕ} (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) : ∀ k, k < gs.length →
    (∀ i < k, i ∈ (K n gs).getD k [] → (gs.getD i dg).op = GateOp.and →
      (W gs x).getD (n + i) false = false) →
    ∀ w ∈ (gs.getD k dg).inputs, w < n + k → (W gs x).getD w false = true →
    ∃ r : Fin n, x r = true ∧
      ∀ y : Fin n → Bool, y r = true → (W gs y).getD w false = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk H w hw hwk hwt
    by_cases hwn : w < n
    · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · have := W_inp x gs ⟨w, hwn⟩
        rw [← this]
        exact hwt
      · intro y hy
        have := W_inp y gs ⟨w, hwn⟩
        rw [← hy, ← this]
    · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
      have hk'k : k' < k := by omega
      have hk'l : k' < gs.length := by omega
      have hc := K_mem n gs k hk (n + k') hw (by omega) hwk
      have e : n + k' - n = k' := by omega
      rw [e] at hc
      have hmem : gs.getD k' dg ∈ gs := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'l]
        simp
      rcases hop _ hmem with ha | ho
      · rw [H k' hk'k hc.1 ha] at hwt
        exact absurd hwt (by simp)
      · rw [W_gate x gs k' hk'l, ev_or _ _ ho] at hwt
        obtain ⟨w', hw', hw't⟩ := hwt
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw't
        obtain ⟨r, hr, hry⟩ := ih k' hk'k hk'l
          (fun i hi hic hia => H i (by omega) (hc.2 i hic) hia) w' hw' hw't.1 hw't.2
        refine ⟨r, hr, fun y hy => ?_⟩
        rw [W_gate y gs k' hk'l, ev_or _ _ ho]
        refine ⟨w', hw', ?_⟩
        rw [hry y hy, Bool.and_true, decide_eq_true_eq]
        exact hw't.1

theorem star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (P1 P2 : (Fin n → Bool) → Prop) (O : Fin n → Fin n → Prop)
    (hE : ∀ y, P1 y → P2 y → ∃ u v, G.Adj u v ∧ y u = true ∧ y v = true)
    (hO : ∀ p q, O p q →
      (∃ r, (r = p ∨ r = q) ∧ ∀ y : Fin n → Bool, y r = true → P1 y) ∧
      (∃ r, (r = p ∨ r = q) ∧ ∀ y : Fin n → Bool, y r = true → P2 y)) :
    (∀ u v : Fin n, G.Adj u v → ¬ O u v) ∨
      ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → O p q → p = s ∨ q = s := by
  have hadj : ∀ a b, (∀ y : Fin n → Bool, y a = true → P1 y) →
      (∀ y : Fin n → Bool, y b = true → P2 y) → G.Adj a b := by
    intro a b ha hb
    obtain ⟨u, v, huv, hu, hv⟩ := hE (fun w => decide (w = a ∨ w = b))
      (ha _ (by simp)) (hb _ (by simp))
    simp only [decide_eq_true_eq] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · rw [hu, hv] at huv
      exact absurd huv (G.irrefl)
    · rw [hu, hv] at huv
      exact huv
    · rw [hu, hv] at huv
      exact huv.symm
    · rw [hu, hv] at huv
      exact absurd huv (G.irrefl)
  have hsplit : ∀ p q, O p q → ∃ a b, ((a = p ∧ b = q) ∨ (a = q ∧ b = p)) ∧
      (∀ y : Fin n → Bool, y a = true → P1 y) ∧
      (∀ y : Fin n → Bool, y b = true → P2 y) := by
    intro p q h
    obtain ⟨⟨r, hr, h1⟩, ⟨r', hr', h2⟩⟩ := hO p q h
    have hne : r ≠ r' := fun e => by
      rw [← e] at h2
      exact G.irrefl (hadj r r h1 h2)
    refine ⟨r, r', ?_, h1, h2⟩
    rcases hr with hr | hr <;> rcases hr' with hr' | hr'
    · exact absurd (hr.trans hr'.symm) hne
    · left; exact ⟨hr, hr'⟩
    · right; exact ⟨hr, hr'⟩
    · exact absurd (hr.trans hr'.symm) hne
  by_cases hex : ∃ p q, G.Adj p q ∧ O p q
  · right
    obtain ⟨p0, q0, _, h0⟩ := hex
    obtain ⟨a0, b0, _, hU0, hV0⟩ := hsplit p0 q0 h0
    by_cases hU : ∀ a, (∀ y : Fin n → Bool, y a = true → P1 y) → a = a0
    · refine ⟨a0, fun p q _ hpq => ?_⟩
      obtain ⟨a, b, hab, hUa, _⟩ := hsplit p q hpq
      have := hU a hUa
      rcases hab with ⟨h1, _⟩ | ⟨h1, _⟩
      · left; rw [← h1]; exact this
      · right; rw [← h1]; exact this
    · push_neg at hU
      obtain ⟨a1, hU1, hne⟩ := hU
      have hV : ∀ b, (∀ y : Fin n → Bool, y b = true → P2 y) → b = b0 := by
        intro b hb
        by_contra hbne
        exact h4 a0 b0 a1 b (Ne.symm hne) (Ne.symm hbne)
          ⟨hadj a0 b0 hU0 hV0, (hadj a1 b0 hU1 hV0).symm, hadj a1 b hU1 hb,
            (hadj a0 b hU0 hb).symm⟩
      refine ⟨b0, fun p q _ hpq => ?_⟩
      obtain ⟨a, b, hab, _, hVb⟩ := hsplit p q hpq
      have := hV b hVb
      rcases hab with ⟨_, h2⟩ | ⟨_, h2⟩
      · right; rw [← h2]; exact this
      · left; rw [← h2]; exact this
  · left
    intro u v huv ho
    exact hex ⟨u, v, huv, ho⟩

theorem core {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (j : ℕ) (hj : j < C.gates.length) (hand : (C.gates.getD j dg).op = GateOp.and)
    (hsub : ∀ x : Fin n → Bool, (W C.gates x).getD (n + j) false = true →
      graphFun G ∅ x = true)
    (w1 w2 : ℕ) (h1 : w1 ∈ (C.gates.getD j dg).inputs)
    (h2 : w2 ∈ (C.gates.getD j dg).inputs)
    (hv : ∀ y : Fin n → Bool, (w1 < n + j ∧ (W C.gates y).getD w1 false = true) →
      (w2 < n + j ∧ (W C.gates y).getD w2 false = true) →
      (W C.gates y).getD (n + j) false = true) :
    (∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v) ∨
      ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → Owns n C j p q → p = s ∨ q = s := by
  apply star G h4 (fun y => w1 < n + j ∧ (W C.gates y).getD w1 false = true)
    (fun y => w2 < n + j ∧ (W C.gates y).getD w2 false = true)
    (fun p q => Owns n C j p q)
  · intro y hy1 hy2
    have := hsub y (hv y hy1 hy2)
    simpa [graphFun] using this
  · intro p q ho
    obtain ⟨_, _, hgv, hcone⟩ := ho
    have hall : ∀ i ∈ (C.gates.getD j dg).inputs,
        i < n + j ∧ (W C.gates (pairInput p q)).getD i false = true := by
      have h0 : (W C.gates (pairInput p q)).getD (n + j) false = true := hgv
      rw [W_gate _ C.gates j hj, ev_and _ _ hand] at h0
      intro i hi
      simpa using h0 i hi
    have key : ∀ w ∈ (C.gates.getD j dg).inputs, ∃ r, (r = p ∨ r = q) ∧
        ∀ y : Fin n → Bool, y r = true →
          (w < n + j ∧ (W C.gates y).getD w false = true) := by
      intro w hw
      obtain ⟨r, hr, hry⟩ := orpath C.gates hop (pairInput p q) j hj
        (fun i hi hic hia => hcone i hi hic hia) w hw (hall w hw).1 (hall w hw).2
      exact ⟨r, by simpa [pairInput] using hr, fun y hy => ⟨(hall w hw).1, hry y hy⟩⟩
    exact ⟨key w1 h1, key w2 h2⟩

end PEqualNP.Outside.L_meta_1600

open PEqualNP.Outside.L_meta_1600 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership in
theorem PEqualNP.Outside.L_meta_1600 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → ∀ j : ℕ, j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C j x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) → (∀ u v : Fin n, G.Adj u v → ¬ PEqualNP.EdgeOwnership.Owns n C j u v) ∨ ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → PEqualNP.EdgeOwnership.Owns n C j p q → p = s ∨ q = s := by
  intro n G inst h4 C hM j hj hand hsub
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    have := (hM g hg).1
    simpa using this
  have hmem : C.gates.getD j dg ∈ C.gates := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp
  have hlen := (hM _ hmem).2
  have hand' : (C.gates.getD j dg).op = GateOp.and := hand
  have hval : ∀ y : Fin n → Bool, (∀ i ∈ (C.gates.getD j dg).inputs,
      i < n + j ∧ (W C.gates y).getD i false = true) →
      (W C.gates y).getD (n + j) false = true := by
    intro y hy
    rw [W_gate y C.gates j hj, ev_and _ _ hand']
    intro i hi
    simpa using hy i hi
  rcases hin : (C.gates.getD j dg).inputs with _ | ⟨w1, _ | ⟨w2, rest⟩⟩
  · exfalso
    have := hsub (fun _ => false) (hval _ (by rw [hin]; simp))
    simp [graphFun] at this
  · exact core G h4 C hop j hj hand' hsub w1 w1 (by rw [hin]; simp) (by rw [hin]; simp)
      (fun y a _ => hval y (by rw [hin]; simpa using a))
  · have hr : rest = [] := by
      rw [hin] at hlen
      simp at hlen
      exact hlen
    subst hr
    exact core G h4 C hop j hj hand' hsub w1 w2 (by rw [hin]; simp) (by rw [hin]; simp)
      (fun y a b => hval y (by rw [hin]; simpa using ⟨a, b⟩))

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_653_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

private def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

private def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

private def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

private lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

private lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

private lemma relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

private lemma run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append,
      List.length_cons, List.length_nil]; omega

private lemma run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private def preserve (k o : ℕ) : ℕ := if o < k then o else o + 2

private def triple (l c r k o : ℕ) : List Gate :=
  [⟨GateOp.or, [l, r]⟩, ⟨GateOp.and, [c, k]⟩,
    ⟨GateOp.or, [preserve k o, k + 1]⟩]

private lemma triple_eval (w : List Bool) (l c r o : ℕ) (hc : c < w.length) :
    ((triple l c r w.length o).foldl step w).getD (w.length + 2) false =
      (w.getD o false || (w.getD c false && (w.getD l false || w.getD r false))) := by
  let v := w.getD l false || w.getD r false
  let w₁ := w ++ [v]
  let t := w.getD c false && v
  let w₂ := w₁ ++ [t]
  have h₁ : w₁.length = w.length + 1 := by simp [w₁]
  have h₂ : w₂.length = w.length + 2 := by simp [w₂, h₁]
  have hv : w₁.getD w.length false = v := getD_snoc_eq _ _ _
  have ht : w₂.getD (w.length + 1) false = t := by rw [← h₁]; exact getD_snoc_eq _ _ _
  have hcenter : w₁.getD c false = w.getD c false := List.getD_append _ _ _ _ hc
  have ho : w₂.getD (preserve w.length o) false = w.getD o false := by
    unfold preserve
    split
    · rename_i hi
      exact (List.getD_append _ _ _ _ (by omega : o < w₁.length)).trans
        (List.getD_append _ _ _ _ hi)
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  have hs₁ : step w ⟨GateOp.or, [l, r]⟩ = w₁ := by
    simp [step, GateOp.eval, w₁, v]
  have hs₂ : step w₁ ⟨GateOp.and, [c, w.length]⟩ = w₂ := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, hcenter, hv, w₂, t]
  simp only [triple, List.foldl_cons, List.foldl_nil, hs₁, hs₂]
  rw [← h₂]
  simp only [step, getD_snoc_eq, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
    List.any_nil, id_eq, Bool.or_false, ho, ht, t, v]

private def grow {m : ℕ} (a : ℕ → Fin m) (C : Circuit) : ℕ → Circuit
  | 0 => C
  | k + 1 =>
    let D := grow a C k
    let w := m + D.gates.length
    ⟨D.gates ++ triple (a (2 * k + 1)).val (a (2 * k + 2)).val
      (a (2 * k + 3)).val w D.output, w + 2⟩

private lemma grow_size {m : ℕ} (a : ℕ → Fin m) (C : Circuit) (k : ℕ) :
    (grow a C k).size = C.size + 3 * k := by
  induction k with
  | zero => simp [grow]
  | succ k ih =>
    simp only [Circuit.size] at ih ⊢
    simp only [grow, triple, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma grow_ok {m : ℕ} (a : ℕ → Fin m) (C : Circuit) (ok : FanInTwo C) (k : ℕ) :
    FanInTwo (grow a C k) := by
  induction k with
  | zero => exact ok
  | succ k ih =>
    intro g hg
    change g ∈ (grow a C k).gates ++ triple _ _ _ _ _ at hg
    rcases List.mem_append.1 hg with hg | hg
    · exact ih g hg
    · simp only [triple, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp

private def cover (b : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => cover b k || (b (2 * k + 2) && (b (2 * k + 1) || b (2 * k + 3)))

private lemma grow_eval {m : ℕ} (a : ℕ → Fin m) (C : Circuit)
    (x : Fin m → Bool) (k : ℕ) :
    (grow a C k).eval (List.ofFn x) = (C.eval (List.ofFn x) || cover (x ∘ a) k) := by
  induction k with
  | zero => simp [grow, cover]
  | succ k ih =>
    let D := grow a C k
    let w := D.gates.foldl step (List.ofFn x)
    have hw : w.length = m + D.gates.length := by simp [w, run_length]
    have hr (i : ℕ) : w.getD (a i).val false = x (a i) := by
      change (D.gates.foldl step (List.ofFn x)).getD (a i).val false = _
      rw [run_keep _ _ _ (by simp)]
      simp
    change ((D.gates ++ triple _ _ _ _ D.output).foldl step (List.ofFn x)).getD
      (m + D.gates.length + 2) false = _
    rw [List.foldl_append]
    change ((triple _ _ _ _ D.output).foldl step w).getD
      (m + D.gates.length + 2) false = _
    rw [← hw, triple_eval _ _ _ _ _ (by have := (a (2 * k + 2)).isLt; omega),
      hr, hr, hr]
    change (D.eval (List.ofFn x) || _) = _
    rw [ih]
    simp [cover, Bool.or_assoc]

private lemma cover_true (b : ℕ → Bool) (h : ℕ) :
    cover b h = true ↔
      ∃ k < h, b (2 * k + 2) = true ∧ (b (2 * k + 1) = true ∨ b (2 * k + 3) = true) := by
  induction h with
  | zero => simp [cover]
  | succ h ih =>
    simp only [cover, Bool.or_eq_true, Bool.and_eq_true, ih]
    constructor
    · rintro (⟨k, hk, hp⟩ | hp)
      · exact ⟨k, by omega, hp⟩
      · exact ⟨h, by omega, hp⟩
    · rintro ⟨k, hk, hp⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
      · exact Or.inl ⟨k, hlt, hp⟩
      · exact Or.inr hp

private def edges (b : ℕ → Bool) (d : ℕ) : Prop :=
  ∃ i < d, b i = true ∧ b (i + 1) = true

private lemma cover_edges (b : ℕ → Bool) (h : ℕ) :
    ((b 0 && b 1) || cover b h) = true ↔ edges b (2 * h + 1) := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, cover_true, edges]
  constructor
  · rintro (⟨hl, hr⟩ | ⟨k, hk, hc, hl | hr⟩)
    · exact ⟨0, by omega, hl, hr⟩
    · exact ⟨2 * k + 1, by omega, hl, hc⟩
    · exact ⟨2 * k + 2, by omega, hc, hr⟩
  · rintro ⟨i, hi, hl, hr⟩
    by_cases hz : i = 0
    · subst i
      exact Or.inl ⟨hl, hr⟩
    · let k := (i - 1) / 2
      have hk : k < h := by dsimp [k]; omega
      have hp : i = 2 * k + 1 ∨ i = 2 * k + 2 := by dsimp [k]; omega
      rcases hp with hi | hi
      · rw [hi] at hl hr
        exact Or.inr ⟨k, hk, hr, Or.inl hl⟩
      · rw [hi] at hl hr
        exact Or.inr ⟨k, hk, hl, Or.inr hr⟩

private lemma edges_reverse (b : ℕ → Bool) (d : ℕ) :
    edges (fun i => b (d - i)) d ↔ edges b d := by
  constructor <;> rintro ⟨i, hi, hl, hr⟩
  · refine ⟨d - (i + 1), by omega, hr, ?_⟩
    rwa [show d - (i + 1) + 1 = d - i by omega]
  · refine ⟨d - (i + 1), by omega, ?_, ?_⟩
    · change b (d - (d - (i + 1))) = true
      rwa [show d - (d - (i + 1)) = i + 1 by omega]
    · change b (d - (d - (i + 1) + 1)) = true
      rwa [show d - (d - (i + 1) + 1) = i by omega]

private def pathWire {N : ℕ} (h : ℕ) (u v : Fin N) (i : ℕ) : Fin (N + 2 * h) :=
  if i = 0 then Fin.castAdd (2 * h) u
  else if hi : 0 < i ∧ i ≤ 2 * h then Fin.natAdd N ⟨i - 1, by omega⟩
  else Fin.castAdd (2 * h) v

private lemma pathWire_inner {N h : ℕ} (u v : Fin N) (i : Fin (2 * h)) :
    pathWire h u v (i.val + 1) = Fin.natAdd N i := by
  have hi := i.isLt
  simp [pathWire, show i.val + 1 ≤ 2 * h by omega]

private def target {N h : ℕ} (u v : Fin N) (g : (Fin N → Bool) → Bool)
    (x : Fin (N + 2 * h) → Bool) : Bool :=
  g (fun i => x (Fin.castAdd (2 * h) i)) ||
    decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧
      ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨
       (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨
       ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))

private lemma path_edges {N h : ℕ} (u v : Fin N) (hh : 1 ≤ h)
    (x : Fin (N + 2 * h) → Bool) :
    edges (x ∘ pathWire h u v) (2 * h + 1) ↔
      ∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧
        ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨
         (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨
         ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true) := by
  unfold edges
  simp only [Function.comp_apply]
  have hfirst : pathWire h u v 0 = Fin.castAdd (2 * h) u := by simp [pathWire]
  have hlast : pathWire h u v (2 * h + 1) = Fin.castAdd (2 * h) v := by simp [pathWire]
  constructor
  · rintro ⟨i, hi, hl, hr⟩
    by_cases hz : i = 0
    · subst i
      let j : Fin (2 * h) := ⟨0, by omega⟩
      rw [hfirst] at hl
      rw [show pathWire h u v 1 = Fin.natAdd N j from pathWire_inner u v j] at hr
      exact ⟨j, hr, Or.inl ⟨rfl, hl⟩⟩
    · let j : Fin (2 * h) := ⟨i - 1, by omega⟩
      have hj : j.val + 1 = i := by dsimp [j]; omega
      rw [← hj, pathWire_inner] at hl
      refine ⟨j, hl, ?_⟩
      by_cases he : i = 2 * h
      · rw [he, hlast] at hr
        exact Or.inr (Or.inl ⟨hj.trans he, hr⟩)
      · let k : Fin (2 * h) := ⟨i, by omega⟩
        rw [show pathWire h u v (i + 1) = Fin.natAdd N k from pathWire_inner u v k] at hr
        exact Or.inr (Or.inr ⟨k, hj.symm, hr⟩)
  · rintro ⟨i, hx, ⟨hz, hl⟩ | ⟨he, hr⟩ | ⟨j, hj, hr⟩⟩
    · refine ⟨0, by omega, by rwa [hfirst], ?_⟩
      rwa [← show i.val + 1 = 0 + 1 by omega, pathWire_inner]
    · refine ⟨i.val + 1, by omega, by rwa [pathWire_inner], ?_⟩
      rwa [he, hlast]
    · refine ⟨i.val + 1, by have := i.isLt; omega, by rwa [pathWire_inner], ?_⟩
      rwa [← hj, pathWire_inner]

private lemma add_path {N h : ℕ} (u v e : Fin N) (g : (Fin N → Bool) → Bool)
    (s : ℕ) (a : ℕ → Fin (N + 2 * h))
    (ha : a 0 = Fin.castAdd (2 * h) e)
    (he : ∀ x : Fin (N + 2 * h) → Bool,
      edges (x ∘ a) (2 * h + 1) ↔ edges (x ∘ pathWire h u v) (2 * h + 1))
    (hh : 1 ≤ h)
    (hc : HasCircuitSize (N + 1)
      (fun x => g (fun i : Fin N => x i.castSucc) || (x e.castSucc && x (Fin.last N))) s) :
    HasCircuitSize (N + 2 * h) (target u v g) (3 * h + s) := by
  let π : Fin (N + 1) → Fin (N + 2 * h) :=
    Fin.lastCases (a 1) (Fin.castAdd (2 * h))
  obtain ⟨C, hok, hsz, hev⟩ := relabel_size π _ s hc
  refine ⟨grow a C h, grow_ok a C hok h, ?_, ?_⟩
  · rw [grow_size]
    omega
  · intro x
    rw [grow_eval, hev]
    simp only [Function.comp_apply, π, Fin.lastCases_castSucc, Fin.lastCases_last, ← ha,
      Bool.or_assoc]
    apply Bool.eq_iff_iff.mpr
    simp only [target, Bool.or_eq_true, decide_eq_true_eq]
    rw [← path_edges u v hh x, ← he x, ← cover_edges (x ∘ a) h]
    simp only [Function.comp_apply, Bool.or_eq_true]

end PEqualNP.Outside.L_meta_653_aux

open PEqualNP.Outside.L_meta_653_aux

theorem PEqualNP.Outside.L_meta_653 : ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), 1 ≤ h → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x u.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x v.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) := by
  intro N h u v g hh s
  constructor
  · intro hc
    exact add_path u v u g s (pathWire h u v) (by simp [pathWire]) (fun _ => Iff.rfl) hh hc
  · intro hc
    let a : ℕ → Fin (N + 2 * h) := fun i => pathWire h u v (2 * h + 1 - i)
    refine add_path u v v g s a (by simp [a, pathWire]) ?_ hh hc
    intro x
    exact edges_reverse (x ∘ pathWire h u v) (2 * h + 1)

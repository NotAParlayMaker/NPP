import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_654_aux

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

private abbrev Triple (m : ℕ) := Fin m × Fin m × Fin m

private def term {m : ℕ} (x : Fin m → Bool) (t : Triple m) : Bool :=
  x t.1 && (x t.2.1 || x t.2.2)

private def old (k o : ℕ) : ℕ := if o < k then o else k + 3

private def termGates {m : ℕ} (t : Triple m) (k o : ℕ) : List Gate :=
  [⟨GateOp.or, [t.2.1.val, t.2.2.val]⟩,
   ⟨GateOp.and, [t.1.val, k]⟩,
   ⟨GateOp.or, [old k o, k + 1]⟩]

private lemma term_eval {m : ℕ} (x : Fin m → Bool) (t : Triple m) (w : List Bool)
    (o : ℕ) (hw : ∀ i : Fin m, w.getD i.val false = x i) (hm : m ≤ w.length) :
    ((termGates t w.length o).foldl step w).getD (w.length + 2) false =
      (w.getD o false || term x t) := by
  let p := x t.2.1 || x t.2.2
  let w₁ := w ++ [p]
  have h₁ : step w ⟨GateOp.or, [t.2.1.val, t.2.2.val]⟩ = w₁ := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, id_eq, Bool.or_false, hw, w₁, p]
  let w₂ := w₁ ++ [term x t]
  have hi : w₁.getD t.1.val false = x t.1 :=
    (List.getD_append _ _ _ _ (lt_of_lt_of_le t.1.isLt hm)).trans (hw _)
  have hp : w₁.getD w.length false = p := getD_snoc_eq _ _ _
  have h₂ : step w₁ ⟨GateOp.and, [t.1.val, w.length]⟩ = w₂ := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, hi, hp, w₂, term, p]
  have hlen₁ : w₁.length = w.length + 1 := by simp [w₁]
  have hlen₂ : w₂.length = w.length + 2 := by simp [w₂, hlen₁]
  have ht : w₂.getD (w.length + 1) false = term x t := by
    rw [← hlen₁]
    exact getD_snoc_eq _ _ _
  have ho : w₂.getD (old w.length o) false = w.getD o false := by
    unfold old
    split
    · rename_i ho
      rw [List.getD_append _ _ _ _ (by rw [hlen₁]; omega), List.getD_append _ _ _ _ ho]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  simp only [termGates, List.foldl_cons, List.foldl_nil, h₁, h₂]
  rw [← hlen₂]
  simp only [step, getD_snoc_eq, GateOp.eval, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, id_eq, Bool.or_false, ho, ht]

private lemma append_term {m s : ℕ} (f : (Fin m → Bool) → Bool)
    (t : Triple m) (hf : HasCircuitSize m f s) :
    HasCircuitSize m (fun x => f x || term x t) (s + 3) := by
  obtain ⟨C, hok, hsz, hev⟩ := hf
  let k := m + C.gates.length
  refine ⟨⟨C.gates ++ termGates t k C.output, k + 2⟩, ?_, ?_, ?_⟩
  · intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact hok z hz
    · simp only [termGates, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> simp
  · change (C.gates ++ termGates t k C.output).length ≤ s + 3
    have : C.gates.length ≤ s := hsz
    simpa [termGates] using Nat.add_le_add_right this 3
  · intro x
    let w := C.gates.foldl step (List.ofFn x)
    have hk : w.length = k := by simp [w, run_length, k]
    have hw (i : Fin m) : w.getD i.val false = x i := by
      rw [show w.getD i.val false = (List.ofFn x).getD i.val false from
        run_keep _ _ _ (by simp)]
      simp
    have ho : w.getD C.output false = f x := hev x
    change ((C.gates ++ termGates t k C.output).foldl step (List.ofFn x)).getD (k + 2)
      false = _
    rw [List.foldl_append]
    change ((termGates t k C.output).foldl step w).getD (k + 2) false = _
    rw [← hk, term_eval x t w C.output hw (by omega), ho]

private lemma append_terms {m s : ℕ} (ts : List (Triple m))
    (f : (Fin m → Bool) → Bool) (hf : HasCircuitSize m f s) :
    HasCircuitSize m (fun x => f x || ts.any (term x)) (s + 3 * ts.length) := by
  induction ts generalizing f s with
  | nil => simpa using hf
  | cons t ts ih =>
    have h := ih (fun x => f x || term x t) (append_term f t hf)
    have hs : s + 3 + 3 * ts.length = s + 3 * (t :: ts).length := by simp; omega
    rw [hs] at h
    simpa only [List.any_cons, Bool.or_assoc] using h

private def point {N h : ℕ} (u v : Fin N) (j : ℕ) : Fin (N + (2 * h + 1)) :=
  if j = 0 then Fin.castAdd (2 * h + 1) u else
  if hj : j < 2 * h + 2 then Fin.natAdd N ⟨j - 1, by omega⟩
  else Fin.castAdd (2 * h + 1) v

private lemma point_start {N h : ℕ} (u v : Fin N) :
    point (h := h) u v 0 = Fin.castAdd (2 * h + 1) u := by simp [point]

private lemma point_end {N h : ℕ} (u v : Fin N) :
    point (h := h) u v (2 * h + 2) = Fin.castAdd (2 * h + 1) v := by
  simp [point]

private lemma point_fresh {N h : ℕ} (u v : Fin N) (i : Fin (2 * h + 1)) :
    point (h := h) u v (i.val + 1) = Fin.natAdd N i := by
  unfold point
  rw [ite_eq_right (by omega), dite_eq_left (by have := i.isLt; omega)]
  congr 1

private abbrev path {N h : ℕ} (u v : Fin N) (x : Fin (N + (2 * h + 1)) → Bool) : Prop :=
  ∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧
    ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨
      (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨
      ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true)

private def edge (p : ℕ → Prop) (j : ℕ) : Prop := p j ∧ p (j + 1)

private lemma path_edges {N h : ℕ} (u v : Fin N) (x : Fin (N + (2 * h + 1)) → Bool) :
    path u v x ↔ ∃ j < 2 * h + 2, edge (fun a => x (point (h := h) u v a) = true) j := by
  let p := fun j => x (point (h := h) u v j) = true
  have hu : p 0 ↔ x (Fin.castAdd (2 * h + 1) u) = true := by simp [p, point_start]
  have hv : p (2 * h + 2) ↔ x (Fin.castAdd (2 * h + 1) v) = true := by
    simp [p, point_end]
  have hf (i : Fin (2 * h + 1)) : p (i.val + 1) ↔ x (Fin.natAdd N i) = true := by
    simp [p, point_fresh]
  change path u v x ↔ ∃ j < 2 * h + 2, edge p j
  constructor
  · rintro ⟨i, hi, ⟨iz, hx⟩ | ⟨il, hx⟩ | ⟨j, hj, hx⟩⟩
    · have hpi := (hf i).2 hi
      rw [iz] at hpi
      exact ⟨0, by omega, hu.2 hx, hpi⟩
    · have hj : i.val + 1 + 1 = 2 * h + 2 := by omega
      exact ⟨i.val + 1, by omega, (hf i).2 hi, hj ▸ hv.2 hx⟩
    · have hpi := (hf i).2 hi
      have hpj := (hf j).2 hx
      rw [hj] at hpj
      exact ⟨i.val + 1, by have := i.isLt; omega, hpi, hpj⟩
  · rintro ⟨j, hj, ha, hb⟩
    by_cases hz : j = 0
    · subst j
      let i : Fin (2 * h + 1) := ⟨0, by omega⟩
      exact ⟨i, (hf i).1 hb, Or.inl ⟨rfl, hu.1 ha⟩⟩
    · let i : Fin (2 * h + 1) := ⟨j - 1, by omega⟩
      have hi : i.val + 1 = j := by dsimp [i]; omega
      refine ⟨i, (hf i).1 (hi ▸ ha), Or.inr ?_⟩
      by_cases hl : j + 1 = 2 * h + 2
      · exact Or.inl ⟨by omega, hv.1 (hl ▸ hb)⟩
      · let a : Fin (2 * h + 1) := ⟨j, by omega⟩
        exact Or.inr ⟨a, hi.symm, (hf a).1 hb⟩

private def evenTerms {N h : ℕ} (u v : Fin N) : List (Triple (N + (2 * h + 1))) :=
  List.ofFn fun k : Fin (h + 1) =>
    (point u v (2 * k.val + 1), point u v (2 * k.val), point u v (2 * k.val + 2))

private def oddTerms {N h : ℕ} (u v : Fin N) : List (Triple (N + (2 * h + 1))) :=
  List.ofFn fun k : Fin h =>
    (point u v (2 * k.val + 2), point u v (2 * k.val + 1), point u v (2 * k.val + 3))

private lemma even_cover (h : ℕ) (p : ℕ → Prop) :
    (∃ k : Fin (h + 1), p (2 * k.val + 1) ∧ (p (2 * k.val) ∨ p (2 * k.val + 2))) ↔
      ∃ j < 2 * h + 2, edge p j := by
  constructor
  · rintro ⟨k, hc, hl | hr⟩
    · exact ⟨2 * k.val, by omega, hl, hc⟩
    · exact ⟨2 * k.val + 1, by omega, hc, hr⟩
  · rintro ⟨j, hj, hl, hr⟩
    let k : Fin (h + 1) := ⟨j / 2, by omega⟩
    refine ⟨k, ?_⟩
    have ha : j = 2 * k.val ∨ j = 2 * k.val + 1 := by dsimp [k]; omega
    rcases ha with ha | ha
    · rw [ha] at hl hr
      exact ⟨hr, Or.inl hl⟩
    · rw [ha] at hl hr
      exact ⟨hl, Or.inr hr⟩

private lemma odd_cover (h : ℕ) (p : ℕ → Prop) :
    (edge p 0 ∨ edge p (2 * h + 1) ∨
      ∃ k : Fin h, p (2 * k.val + 2) ∧ (p (2 * k.val + 1) ∨ p (2 * k.val + 3))) ↔
      ∃ j < 2 * h + 2, edge p j := by
  constructor
  · rintro (hl | hr | ⟨k, hc, hl | hr⟩)
    · exact ⟨0, by omega, hl⟩
    · exact ⟨2 * h + 1, by omega, hr⟩
    · exact ⟨2 * k.val + 1, by omega, hl, hc⟩
    · exact ⟨2 * k.val + 2, by omega, hc, hr⟩
  · rintro ⟨j, hj, hl, hr⟩
    by_cases hz : j = 0
    · subst j
      exact Or.inl ⟨hl, hr⟩
    by_cases he : j = 2 * h + 1
    · subst j
      exact Or.inr (Or.inl ⟨hl, hr⟩)
    let k : Fin h := ⟨(j - 1) / 2, by omega⟩
    refine Or.inr (Or.inr ⟨k, ?_⟩)
    have ha : j = 2 * k.val + 1 ∨ j = 2 * k.val + 2 := by dsimp [k]; omega
    rcases ha with ha | ha
    · rw [ha] at hl hr
      exact ⟨hr, Or.inl hl⟩
    · rw [ha] at hl hr
      exact ⟨hl, Or.inr hr⟩

private lemma even_eval {N h : ℕ} (u v : Fin N) (x : Fin (N + (2 * h + 1)) → Bool) :
    (evenTerms u v).any (term x) = true ↔ path u v x := by
  rw [path_edges u v x, ← even_cover]
  simp only [evenTerms, List.any_eq_true, List.mem_ofFn, exists_exists_eq_and,
    term, Bool.and_eq_true, Bool.or_eq_true]

private lemma odd_eval {N h : ℕ} (u v : Fin N) (x : Fin (N + (2 * h + 1)) → Bool) :
    (x (point u v 0) && x (point u v 1) ||
      (x (point u v (2 * h + 1)) && x (point u v (2 * h + 2)) ||
        (oddTerms u v).any (term x))) = true ↔ path u v x := by
  rw [path_edges u v x, ← odd_cover]
  simp [oddTerms, List.any_eq_true, List.mem_ofFn, term, edge]

private def endpointMap {N h : ℕ} (u v : Fin N) : Fin (N + 2) → Fin (N + (2 * h + 1)) :=
  Fin.addCases (Fin.castAdd (2 * h + 1)) fun i =>
    if i.val = 0 then point u v 1 else point u v (2 * h + 1)

private lemma endpoint_eval {N h : ℕ} (u v : Fin N) (x : Fin (N + (2 * h + 1)) → Bool)
    (g : (Fin N → Bool) → Bool) :
    (g (fun i : Fin N => (x ∘ endpointMap u v) (Fin.castAdd 2 i)) ||
       ((x ∘ endpointMap u v) (Fin.castAdd 2 u) &&
         (x ∘ endpointMap u v) (Fin.natAdd N (0 : Fin 2))) ||
       ((x ∘ endpointMap u v) (Fin.castAdd 2 v) &&
         (x ∘ endpointMap u v) (Fin.natAdd N (1 : Fin 2)))) =
    (g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) ||
      (x (point u v 0) && x (point u v 1)) ||
      (x (point u v (2 * h + 1)) && x (point u v (2 * h + 2)))) := by
  simp [endpointMap, point_start, point_end, Bool.and_comm]

end PEqualNP.Outside.L_meta_654_aux

open PEqualNP.Outside.L_meta_654_aux PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_654 : ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize N g s → PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1)) (fun x : Fin (N + 2 * h + 1) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨ (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨ ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s + 3)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 2) (fun x : Fin (N + 2) → Bool => g (fun i : Fin N => x (Fin.castAdd 2 i)) || (x (Fin.castAdd 2 u) && x (Fin.natAdd N (0 : Fin 2))) || (x (Fin.castAdd 2 v) && x (Fin.natAdd N (1 : Fin 2)))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1)) (fun x : Fin (N + 2 * h + 1) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨ (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨ ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) := by
  intro N h u v g s
  constructor
  · intro hg
    have hc := relabel_size (Fin.castAdd (2 * h + 1)) g s hg
    have ht := append_terms (evenTerms u v) _ hc
    have hs : s + 3 * (evenTerms (h := h) u v).length = 3 * h + s + 3 := by
      simp [evenTerms]; omega
    rw [hs] at ht
    obtain ⟨C, hfan, hsize, heval⟩ := ht
    refine ⟨C, hfan, hsize, fun x => ?_⟩
    rw [heval x]
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_def, Bool.or_eq_true, even_eval, decide_eq_true_eq, path]
  · intro hg
    have hc := relabel_size (endpointMap (h := h) u v) _ s hg
    have ht := append_terms (oddTerms u v) _ hc
    have hs : s + 3 * (oddTerms (h := h) u v).length = 3 * h + s := by
      simp [oddTerms]; omega
    rw [hs] at ht
    obtain ⟨C, hfan, hsize, heval⟩ := ht
    refine ⟨C, hfan, hsize, fun x => ?_⟩
    rw [heval x]
    dsimp only
    rw [endpoint_eval u v x g]
    simp only [Bool.or_assoc]
    apply congrArg (fun b => g (fun i => x (Fin.castAdd (2 * h + 1) i)) || b)
    apply Bool.eq_iff_iff.mpr
    rw [odd_eval u v x, decide_eq_true_eq]

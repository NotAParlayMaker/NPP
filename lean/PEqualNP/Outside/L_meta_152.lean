import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_152

open PEqualNP.CircuitLowerBounds

def lin (s x : Fin 4 → Bool) : Bool :=
  (s 0 && x 0) || (s 1 && x 1) || (s 2 && x 2) || (s 3 && x 3)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Good (K : ((Fin 4 → Bool) → Bool) → Prop) (W : (Fin 4 → Bool) → List Bool) : Prop :=
  (∃ m, ∀ x, (W x).length = m) ∧ ∀ i, K (fun x => (W x).getD i false)

def Lin (f : (Fin 4 → Bool) → Bool) : Prop := ∃ s, ∀ x, f x = lin s x

def K1 (gf : (Fin 4 → Bool) → Bool) (f : (Fin 4 → Bool) → Bool) : Prop :=
  ∃ s, (∀ x, f x = lin s x) ∨ (∀ x, f x = (lin s x || gf x))

def Gform (gf : (Fin 4 → Bool) → Bool) : Prop :=
  (∀ x, gf x = true) ∨ ∃ t u, ∀ x, gf x = (lin t x && lin u x)

lemma bool12 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 p0 p1 p2 p3 : Bool,
    (((a0 && p0) || (a1 && p1) || (a2 && p2) || (a3 && p3)) ||
      ((b0 && p0) || (b1 && p1) || (b2 && p2) || (b3 && p3))) =
    (((a0 || b0) && p0) || ((a1 || b1) && p1) || ((a2 || b2) && p2) || ((a3 || b3) && p3)) := by
  decide

lemma lin_or (s t x : Fin 4 → Bool) : (lin s x || lin t x) = lin (fun i => s i || t i) x :=
  bool12 (s 0) (s 1) (s 2) (s 3) (t 0) (t 1) (t 2) (t 3) (x 0) (x 1) (x 2) (x 3)

lemma lin_zero (x : Fin 4 → Bool) : lin (fun _ => false) x = false := by
  simp [lin]

lemma Lin_false : Lin (fun _ => false) := ⟨fun _ => false, fun x => (lin_zero x).symm⟩

lemma Lin_or (f f' : (Fin 4 → Bool) → Bool) (h : Lin f) (h' : Lin f') :
    Lin (fun x => f x || f' x) := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, ht⟩ := h'
  refine ⟨fun i => s i || t i, fun x => ?_⟩
  show (f x || f' x) = _
  rw [hs x, ht x, lin_or]

lemma K1_false (gf : (Fin 4 → Bool) → Bool) : K1 gf (fun _ => false) :=
  ⟨fun _ => false, Or.inl fun x => (lin_zero x).symm⟩

lemma b3a : ∀ a b c : Bool, (a || (b || c)) = ((a || b) || c) := by decide

lemma b3b : ∀ a b c : Bool, ((a || c) || b) = ((a || b) || c) := by decide

lemma b3c : ∀ a b c : Bool, ((a || c) || (b || c)) = ((a || b) || c) := by decide

lemma K1_or (gf : (Fin 4 → Bool) → Bool) (f f' : (Fin 4 → Bool) → Bool)
    (h : K1 gf f) (h' : K1 gf f') : K1 gf (fun x => f x || f' x) := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, ht⟩ := h'
  refine ⟨fun i => s i || t i, ?_⟩
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · left
    intro x
    show (f x || f' x) = _
    rw [hs x, ht x, lin_or]
  · right
    intro x
    show (f x || f' x) = _
    rw [hs x, ht x, b3a, lin_or]
  · right
    intro x
    show (f x || f' x) = _
    rw [hs x, ht x, b3b, lin_or]
  · right
    intro x
    show (f x || f' x) = _
    rw [hs x, ht x, b3c, lin_or]

lemma good_snoc (K : ((Fin 4 → Bool) → Bool) → Prop) (hfalse : K (fun _ => false))
    (W : (Fin 4 → Bool) → List Bool) (m : ℕ) (hm : ∀ x, (W x).length = m)
    (hK : ∀ i, K (fun x => (W x).getD i false)) (v : (Fin 4 → Bool) → Bool) (hv : K v) :
    Good K (fun x => W x ++ [v x]) := by
  refine ⟨⟨m + 1, fun x => by simp [hm x]⟩, fun i => ?_⟩
  rcases lt_trichotomy i m with h | h | h
  · have e : (fun x => (W x ++ [v x]).getD i false) = fun x => (W x).getD i false := by
      funext x
      exact List.getD_append _ _ _ _ (by rw [hm x]; exact h)
    rw [e]
    exact hK i
  · have e : (fun x => (W x ++ [v x]).getD i false) = v := by
      funext x
      rw [List.getD_append_right _ _ _ _ (by rw [hm x]; omega), hm x, h]
      simp
    rw [e]
    exact hv
  · have e : (fun x => (W x ++ [v x]).getD i false) = fun _ => false := by
      funext x
      rw [List.getD_append_right _ _ _ _ (by rw [hm x]; omega), hm x]
      obtain ⟨k, hk⟩ : ∃ k, i - m = k + 1 := ⟨i - m - 1, by omega⟩
      rw [hk]
      rfl
    rw [e]
    exact hfalse

lemma or_val (K : ((Fin 4 → Bool) → Bool) → Prop) (hfalse : K (fun _ => false))
    (hor : ∀ f f', K f → K f' → K (fun x => f x || f' x))
    (W : (Fin 4 → Bool) → List Bool) (hK : ∀ i, K (fun x => (W x).getD i false)) :
    ∀ l : List ℕ, l.length ≤ 2 →
      K (fun x => GateOp.or.eval (l.map fun i => (W x).getD i false))
  | [], _ => hfalse
  | [a], _ => by
    have e : (fun x => GateOp.or.eval ([a].map fun i => (W x).getD i false)) =
        fun x => (W x).getD a false := by
      funext x
      show ((W x).getD a false || false) = _
      rw [Bool.or_false]
    rw [e]
    exact hK a
  | [a, b], _ => by
    have e : (fun x => GateOp.or.eval ([a, b].map fun i => (W x).getD i false)) =
        fun x => ((W x).getD a false || (W x).getD b false) := by
      funext x
      show ((W x).getD a false || ((W x).getD b false || false)) = _
      rw [Bool.or_false]
    rw [e]
    exact hor _ _ (hK a) (hK b)
  | _ :: _ :: _ :: _, h => by simp at h

lemma and_val (W : (Fin 4 → Bool) → List Bool) (hK : ∀ i, Lin (fun x => (W x).getD i false)) :
    ∀ l : List ℕ, l.length ≤ 2 →
      Gform (fun x => GateOp.and.eval (l.map fun i => (W x).getD i false))
  | [], _ => Or.inl fun _ => rfl
  | [a], _ => by
    obtain ⟨s, hs⟩ := hK a
    refine Or.inr ⟨s, s, fun x => ?_⟩
    have h1 : (W x).getD a false = lin s x := hs x
    show ((W x).getD a false && true) = _
    rw [h1, Bool.and_true, Bool.and_self]
  | [a, b], _ => by
    obtain ⟨s, hs⟩ := hK a
    obtain ⟨t, ht⟩ := hK b
    refine Or.inr ⟨s, t, fun x => ?_⟩
    have h1 : (W x).getD a false = lin s x := hs x
    have h2 : (W x).getD b false = lin t x := ht x
    show ((W x).getD a false && ((W x).getD b false && true)) = _
    rw [h1, h2, Bool.and_true]
  | _ :: _ :: _ :: _, h => by simp at h

lemma step_or (K : ((Fin 4 → Bool) → Bool) → Prop) (hfalse : K (fun _ => false))
    (hor : ∀ f f', K f → K f' → K (fun x => f x || f' x))
    (W : (Fin 4 → Bool) → List Bool) (hW : Good K W) (g : Gate)
    (hop : g.op = GateOp.or) (hlen : g.inputs.length ≤ 2) :
    Good K (fun x => step (W x) g) := by
  obtain ⟨⟨m, hm⟩, hK⟩ := hW
  have val : K (fun x => g.op.eval (g.inputs.map fun i => (W x).getD i false)) := by
    rw [hop]
    exact or_val K hfalse hor W hK g.inputs hlen
  exact good_snoc K hfalse W m hm hK _ val

lemma fold_or (K : ((Fin 4 → Bool) → Bool) → Prop) (hfalse : K (fun _ => false))
    (hor : ∀ f f', K f → K f' → K (fun x => f x || f' x)) :
    ∀ gs : List Gate, (∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2) →
      ∀ W : (Fin 4 → Bool) → List Bool, Good K W → Good K (fun x => gs.foldl step (W x)) := by
  intro gs
  induction gs with
  | nil =>
    intro _ W hW
    exact hW
  | cons g gs ih =>
    intro hgs W hW
    have h1 := hgs g List.mem_cons_self
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _
      (step_or K hfalse hor W hW g h1.1 h1.2)

lemma step_and (W : (Fin 4 → Bool) → List Bool) (hW : Good Lin W) (g : Gate)
    (hop : g.op = GateOp.and) (hlen : g.inputs.length ≤ 2) :
    ∃ gf, Gform gf ∧ Good (K1 gf) (fun x => step (W x) g) := by
  obtain ⟨⟨m, hm⟩, hK⟩ := hW
  refine ⟨fun x => g.op.eval (g.inputs.map fun i => (W x).getD i false), ?_, ?_⟩
  · rw [hop]
    exact and_val W hK g.inputs hlen
  · refine good_snoc (K1 _) (K1_false _) W m hm (fun i => ?_) _ ?_
    · obtain ⟨s, hs⟩ := hK i
      exact ⟨s, Or.inl hs⟩
    · refine ⟨fun _ => false, Or.inr fun x => ?_⟩
      rw [lin_zero, Bool.false_or]

lemma init_good : Good Lin (fun x : Fin 4 → Bool => List.ofFn x) := by
  refine ⟨⟨4, fun x => List.length_ofFn⟩, fun i => ?_⟩
  refine ⟨fun j => decide (j.val = i), fun x => ?_⟩
  show (List.ofFn x).getD i false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < 4
  · interval_cases i <;> simp [lin]
  · have h0 : ¬ (0 = i) := by omega
    have h1 : ¬ (1 = i) := by omega
    have h2 : ¬ (2 = i) := by omega
    have h3 : ¬ (3 = i) := by omega
    simp [lin, h, h0, h1, h2, h3]

lemma split (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (A : Finset ℕ) (hA : A.card ≤ 1)
    (hand : ∀ (j : ℕ) (g : Gate), gates[j]? = some g → g.op = GateOp.and → j ∈ A) :
    (∀ g ∈ gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∨
    ∃ pre g post, gates = pre ++ g :: post ∧ g.op = GateOp.and ∧ g.inputs.length ≤ 2 ∧
      (∀ g' ∈ pre, g'.op = GateOp.or ∧ g'.inputs.length ≤ 2) ∧
      (∀ g' ∈ post, g'.op = GateOp.or ∧ g'.inputs.length ≤ 2) := by
  have hop : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    have := (hmono g hg).1
    simpa using this
  by_cases hex : ∃ g ∈ gates, g.op = GateOp.and
  · right
    obtain ⟨g, hg, hgop⟩ := hex
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
    have hidx : gates[pre.length]? = some g := by
      rw [hsplit]
      simp
    have hmem := hand _ _ hidx hgop
    refine ⟨pre, g, post, hsplit, hgop, (hmono g hg).2, ?_, ?_⟩
    · intro g' hg'
      have hg'm : g' ∈ gates := by
        rw [hsplit]
        exact List.mem_append_left _ hg'
      refine ⟨?_, (hmono g' hg'm).2⟩
      rcases hop g' hg'm with h | h
      · exfalso
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg'
        have hlt : i < pre.length := (List.getElem?_eq_some_iff.mp hi).1
        have hi' : gates[i]? = some g' := by
          rw [hsplit, List.getElem?_append_left hlt]
          exact hi
        have := Finset.card_le_one.mp hA _ (hand _ _ hi' h) _ hmem
        omega
      · exact h
    · intro g' hg'
      have hg'm : g' ∈ gates := by
        rw [hsplit]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ hg')
      refine ⟨?_, (hmono g' hg'm).2⟩
      rcases hop g' hg'm with h | h
      · exfalso
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg'
        have hi' : gates[pre.length + 1 + i]? = some g' := by
          rw [hsplit, List.getElem?_append_right (by omega)]
          have e : pre.length + 1 + i - pre.length = i + 1 := by omega
          rw [e]
          exact hi
        have := Finset.card_le_one.mp hA _ (hand _ _ hi' h) _ hmem
        omega
      · exact h
  · left
    intro g hg
    refine ⟨?_, (hmono g hg).2⟩
    rcases hop g hg with h | h
    · exact absurd ⟨g, hg, h⟩ hex
    · exact h

lemma tb (x : Fin 4 → Bool) :
    (∃ a b : Fin 4, a.val + 1 = b.val ∧ x a = true ∧ x b = true) ↔
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)) = true := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    fin_cases a <;> fin_cases b <;> simp_all
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (⟨h0, h1⟩ | ⟨h1, h2⟩) | ⟨h2, h3⟩
    · exact ⟨0, 1, rfl, h0, h1⟩
    · exact ⟨1, 2, rfl, h1, h2⟩
    · exact ⟨2, 3, rfl, h2, h3⟩

lemma bash : ∀ s0 s1 s2 s3 t0 t1 t2 t3 u0 u1 u2 u3 : Bool,
    (∀ p0 p1 p2 p3 : Bool,
      ((((s0 && p0) || (s1 && p1) || (s2 && p2) || (s3 && p3)) ||
        (((t0 && p0) || (t1 && p1) || (t2 && p2) || (t3 && p3)) &&
          ((u0 && p0) || (u1 && p1) || (u2 && p2) || (u3 && p3)))) = true ↔
        ((p0 && p1) || (p1 && p2) || (p2 && p3)) = true)) → False := by
  decide

lemma final (f : (Fin 4 → Bool) → Bool) (s t u : Fin 4 → Bool)
    (hf : ∀ x, f x = (lin s x || (lin t x && lin u x)))
    (hP : ∀ x, f x = true ↔ ∃ a b : Fin 4, a.val + 1 = b.val ∧ x a = true ∧ x b = true) :
    False := by
  refine bash (s 0) (s 1) (s 2) (s 3) (t 0) (t 1) (t 2) (t 3) (u 0) (u 1) (u 2) (u 3)
    (fun p0 p1 p2 p3 => ?_)
  have h := hP ![p0, p1, p2, p3]
  rw [hf, tb] at h
  exact h

end PEqualNP.Outside.L_meta_152

open PEqualNP.Outside.L_meta_152 in
theorem PEqualNP.Outside.L_meta_152 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 1 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true) := by
  rintro ⟨C, hmono, ⟨A, hA, hand⟩, hf⟩
  have hw : ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) =
      (C.gates.foldl step (List.ofFn x)).getD C.output false := fun x => rfl
  rcases split C.gates hmono A hA hand with
    hall | ⟨pre, g, post, hsplit, hgop, hglen, hpre, hpost⟩
  · have hgood := fold_or Lin Lin_false Lin_or C.gates hall _ init_good
    obtain ⟨s, hs⟩ := hgood.2 C.output
    refine final (fun x => C.eval (List.ofFn x)) s (fun _ => false) (fun _ => false)
      (fun x => ?_) hf
    have h1 : C.eval (List.ofFn x) = lin s x := by
      rw [hw x]
      exact hs x
    show C.eval (List.ofFn x) = _
    rw [h1, lin_zero, Bool.and_self, Bool.or_false]
  · have hgood0 := fold_or Lin Lin_false Lin_or pre hpre _ init_good
    obtain ⟨gf, hgf, hgood1⟩ := step_and _ hgood0 g hgop hglen
    have hgood2 := fold_or (K1 gf) (K1_false gf) (K1_or gf) post hpost _ hgood1
    have hfold : ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) =
        (post.foldl step (step (pre.foldl step (List.ofFn x)) g)).getD C.output false := by
      intro x
      rw [hw x, hsplit, List.foldl_append, List.foldl_cons]
    obtain ⟨s, hs⟩ := hgood2.2 C.output
    rcases hs with hs | hs
    · refine final (fun x => C.eval (List.ofFn x)) s (fun _ => false) (fun _ => false)
        (fun x => ?_) hf
      have h1 : C.eval (List.ofFn x) = lin s x := by
        rw [hfold x]
        exact hs x
      show C.eval (List.ofFn x) = _
      rw [h1, lin_zero, Bool.and_self, Bool.or_false]
    · rcases hgf with hg | ⟨t, u, hg⟩
      · have h1 : C.eval (List.ofFn (fun _ : Fin 4 => false)) = true := by
          rw [hfold]
          have h2 := hs (fun _ => false)
          rw [hg, Bool.or_true] at h2
          exact h2
        obtain ⟨a, b, _, ha, _⟩ := (hf (fun _ => false)).mp h1
        exact Bool.false_ne_true ha
      · refine final (fun x => C.eval (List.ofFn x)) s t u (fun x => ?_) hf
        have h1 : C.eval (List.ofFn x) = (lin s x || gf x) := by
          rw [hfold x]
          exact hs x
        show C.eval (List.ofFn x) = _
        rw [h1, hg x]

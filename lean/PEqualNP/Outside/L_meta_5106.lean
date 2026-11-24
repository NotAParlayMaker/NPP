import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5106

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.TwoColour PEqualNP.EdgeOwnership

/-! Wire values. -/

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def wv (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma wv_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    wv C x u = x.getD u false := by
  unfold wv; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma wv_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : wv C x u = false := by
  unfold wv; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma wv_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    wv C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then wv C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma wv_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    wv C (List.ofFn x) u.val = x u := by
  rw [wv_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma wv_append (gs t : List Gate) (o : ℕ) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs.length) : wv ⟨gs ++ t, o⟩ x w = wv ⟨gs, o⟩ x w := by
  show ((gs ++ t).foldl stepWire x).getD w false = (gs.foldl stepWire x).getD w false
  rw [List.foldl_append]
  exact foldl_getD_lt t _ w (by rw [foldl_length]; omega)

lemma wv_out (gs : List Gate) (o o' : ℕ) (x : List Bool) (w : ℕ) :
    wv ⟨gs, o⟩ x w = wv ⟨gs, o'⟩ x w := rfl


/-! The construction. -/

def pin (n a b F : ℕ) (m : List ℕ) (w : ℕ) : ℕ :=
  if w < n then (if w = a ∨ w = b then F else w) else m.getD (w - n) F

def cStep (n a b F : ℕ) (S : Finset ℕ) (t : ℕ → ℕ) (T : List Gate × List ℕ) (g : Gate) :
    List Gate × List ℕ :=
  if T.2.length ∈ S then (T.1, T.2 ++ [pin n a b F T.2 (t T.2.length)])
  else (T.1 ++ [⟨g.op, g.inputs.map (pin n a b F T.2)⟩], T.2 ++ [n + T.1.length])

def run (n a b F : ℕ) (S : Finset ℕ) (t : ℕ → ℕ) (gs : List Gate) : List Gate × List ℕ :=
  gs.foldl (cStep n a b F S t) ([], [])

def sv (n : ℕ) (gs : List Gate) (x : List Bool) (r : ℕ) : Bool :=
  if r < n + gs.length then wv ⟨gs, 0⟩ x r else false

def Rng (n N : ℕ) (gs : List Gate) (r : ℕ) : Prop := r < n + gs.length ∨ n + N ≤ r

def rs {n : ℕ} (a b : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  Function.update (Function.update x a false) b false

lemma sv_app {n N : ℕ} (gs t : List Gate) (x : List Bool) {r : ℕ} (hr : Rng n N gs r)
    (hl : (gs ++ t).length ≤ N) (hx : x.length = n) : sv n (gs ++ t) x r = sv n gs x r := by
  have hl' : gs.length + t.length ≤ N := by simpa using hl
  rcases hr with h | h
  · have h' : r < n + (gs ++ t).length := by simp; omega
    unfold sv
    rw [if_pos h, if_pos h']
    exact wv_append gs t 0 x r (by rw [hx]; omega)
  · have h1 : ¬ r < n + (gs ++ t).length := by simp; omega
    have h2 : ¬ r < n + gs.length := by omega
    unfold sv
    rw [if_neg h1, if_neg h2]

lemma card_succ (S : Finset ℕ) (k : ℕ) :
    (S.filter (· < k + 1)).card = (S.filter (· < k)).card + (if k ∈ S then 1 else 0) := by
  by_cases hk : k ∈ S
  · have e : S.filter (· < k + 1) = insert k (S.filter (· < k)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
        · exact Or.inr ⟨h1, h⟩
        · exact Or.inl h
      · rintro (h | ⟨h1, h2⟩)
        · subst h; exact ⟨hk, by omega⟩
        · exact ⟨h1, by omega⟩
    rw [e, Finset.card_insert_of_notMem (by simp), if_pos hk]
  · have e : S.filter (· < k + 1) = S.filter (· < k) := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
        · exact ⟨h1, h⟩
        · exact absurd (h ▸ h1) hk
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    rw [e, if_neg hk, Nat.add_zero]

def Inv (n : ℕ) (a b : Fin n) (S : Finset ℕ) (C : Circuit) (T : List Gate × List ℕ) (k : ℕ) :
    Prop :=
  (∀ g ∈ T.1, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    g.inputs.length ≤ 2) ∧
  T.2.length = k ∧
  (∀ j < k, Rng n C.gates.length T.1 (T.2.getD j (n + C.gates.length))) ∧
  (∀ j < k, ∀ x : Fin n → Bool,
    wv C (List.ofFn (rs a b x)) (n + j) =
      sv n T.1 (List.ofFn x) (T.2.getD j (n + C.gates.length))) ∧
  T.1.length + (S.filter (· < k)).card = k

lemma pin_ok {n : ℕ} {a b : Fin n} {S : Finset ℕ} {C : Circuit} {T : List Gate × List ℕ}
    {k : ℕ} (hI : Inv n a b S C T k) (w : ℕ) :
    Rng n C.gates.length T.1 (pin n a.val b.val (n + C.gates.length) T.2 w) := by
  unfold pin
  split_ifs with h1 h2
  · exact Or.inr le_rfl
  · exact Or.inl (by omega)
  · by_cases hj : w - n < k
    · exact hI.2.2.1 (w - n) hj
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hI.2.1]; omega)]
      exact Or.inr le_rfl

lemma pin_sem {n : ℕ} {a b : Fin n} {S : Finset ℕ} {C : Circuit} {T : List Gate × List ℕ}
    {k : ℕ} (hI : Inv n a b S C T k) (hk : k ≤ C.gates.length) (w : ℕ) (x : Fin n → Bool) :
    (if w < n + k then wv C (List.ofFn (rs a b x)) w else false) =
      sv n T.1 (List.ofFn x) (pin n a.val b.val (n + C.gates.length) T.2 w) := by
  have hlen : T.1.length ≤ C.gates.length := by have := hI.2.2.2.2; omega
  have hF : sv n T.1 (List.ofFn x) (n + C.gates.length) = false := by
    unfold sv; rw [if_neg (by omega)]
  by_cases hwn : w < n
  · rw [if_pos (by omega)]
    have e1 := wv_ofFn C (rs a b x) ⟨w, hwn⟩
    simp only at e1
    rw [e1]
    by_cases hab : w = a.val ∨ w = b.val
    · unfold pin
      rw [if_pos hwn, if_pos hab, hF]
      unfold rs
      rw [Function.update_apply, Function.update_apply]
      split_ifs with h1 h2
      · rfl
      · rfl
      · exfalso
        rcases hab with h | h
        · exact h2 (Fin.ext h)
        · exact h1 (Fin.ext h)
    · unfold pin
      rw [if_pos hwn, if_neg hab]
      push_neg at hab
      have ha : (⟨w, hwn⟩ : Fin n) ≠ a := fun h => hab.1 (by rw [← h])
      have hb : (⟨w, hwn⟩ : Fin n) ≠ b := fun h => hab.2 (by rw [← h])
      unfold rs
      rw [Function.update_of_ne hb, Function.update_of_ne ha]
      unfold sv
      rw [if_pos (by omega)]
      have e2 := wv_ofFn (⟨T.1, 0⟩ : Circuit) x ⟨w, hwn⟩
      simp only at e2
      rw [e2]
  · unfold pin
    rw [if_neg hwn]
    by_cases hj : w - n < k
    · rw [if_pos (by omega)]
      have e : n + (w - n) = w := by omega
      have := hI.2.2.2.1 (w - n) hj x
      rw [e] at this
      exact this
    · rw [if_neg (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [hI.2.1]; omega)]
      exact hF.symm

lemma inv_step {n : ℕ} {a b : Fin n} {S : Finset ℕ} {C : Circuit} (hC : FanInTwo C)
    {t : ℕ → ℕ}
    (ht : ∀ g ∈ S, (t g < n + g ∨ n + C.gates.length ≤ t g) ∧ ∀ x : Fin n → Bool,
       wv C (List.ofFn (rs a b x)) (n + g) = wv C (List.ofFn (rs a b x)) (t g))
    {k : ℕ} (hk : k < C.gates.length) {T : List Gate × List ℕ} (hI : Inv n a b S C T k) :
    Inv n a b S C (cStep n a.val b.val (n + C.gates.length) S t T (gateAt C k)) (k + 1) := by
  have hsem := pin_sem hI hk.le
  have hok := pin_ok hI
  obtain ⟨hW, hT2, hR, hS, hc⟩ := hI
  have hcs := card_succ S k
  set P := pin n a.val b.val (n + C.gates.length) T.2 with hP
  unfold cStep
  rw [hT2]
  by_cases hkS : k ∈ S
  · rw [if_pos hkS]
    rw [if_pos hkS] at hcs
    have eold : ∀ j < k, (T.2 ++ [P (t k)]).getD j (n + C.gates.length) =
        T.2.getD j (n + C.gates.length) := by
      intro j hj
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    have enew : (T.2 ++ [P (t k)]).getD k (n + C.gates.length) = P (t k) := by
      simp [List.getD_eq_getElem?_getD, hT2]
    refine ⟨hW, by simp [hT2], ?_, ?_, by dsimp only; omega⟩
    · intro j hj
      dsimp only
      rcases Nat.lt_or_ge j k with h | h
      · rw [eold j h]; exact hR j h
      · rw [show j = k by omega, enew]; exact hok _
    · intro j hj x
      dsimp only
      rcases Nat.lt_or_ge j k with h | h
      · rw [eold j h]; exact hS j h x
      · rw [show j = k by omega, enew, ← hsem (t k) x, (ht k hkS).2 x]
        obtain ⟨hr, _⟩ := ht k hkS
        split_ifs with h'
        · rfl
        · exact wv_ge (n := n) (by simp) (by omega)
  · rw [if_neg hkS]
    rw [if_neg hkS] at hcs
    set g' : Gate := ⟨(gateAt C k).op, (gateAt C k).inputs.map P⟩ with hg'
    have hl1 : (T.1 ++ [g']).length ≤ C.gates.length := by simp; omega
    have eold : ∀ j < k, (T.2 ++ [n + T.1.length]).getD j (n + C.gates.length) =
        T.2.getD j (n + C.gates.length) := by
      intro j hj
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    have enew : (T.2 ++ [n + T.1.length]).getD k (n + C.gates.length) = n + T.1.length := by
      simp [List.getD_eq_getElem?_getD, hT2]
    refine ⟨?_, by simp [hT2], ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact hW g h
      · rw [List.mem_singleton.mp h]
        have := hC (gateAt C k) (gateAt_mem hk)
        exact ⟨this.1, by simp [hg', this.2]⟩
    · intro j hj
      dsimp only
      rcases Nat.lt_or_ge j k with h | h
      · rw [eold j h]
        rcases hR j h with h1 | h1
        · left; simp only [List.length_append, List.length_singleton]; omega
        · right; exact h1
      · rw [show j = k by omega, enew]; left; simp
    · intro j hj x
      have hx : (List.ofFn x).length = n := by simp
      dsimp only
      rcases Nat.lt_or_ge j k with h | h
      · rw [eold j h, sv_app _ _ _ (hR j h) hl1 hx]; exact hS j h x
      · rw [show j = k by omega, enew]
        have lhs : wv C (List.ofFn (rs a b x)) (n + k) = (gateAt C k).op.eval
            ((gateAt C k).inputs.map fun i => sv n T.1 (List.ofFn x) (P i)) := by
          rw [wv_gate (by simp) hk]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hsem i x
        have rhs : sv n (T.1 ++ [g']) (List.ofFn x) (n + T.1.length) =
            g'.op.eval (g'.inputs.map fun i => sv n T.1 (List.ofFn x) i) := by
          have hj' : T.1.length < (⟨T.1 ++ [g'], 0⟩ : Circuit).gates.length := by simp
          have hin : n + T.1.length < n + (T.1 ++ [g']).length := by simp
          have hg : gateAt (⟨T.1 ++ [g'], 0⟩ : Circuit) T.1.length = g' := by
            simp [gateAt, List.getD_eq_getElem?_getD]
          unfold sv
          rw [if_pos hin, wv_gate hx hj', hg]
          congr 1
          apply List.map_congr_left
          intro i _
          split_ifs with h1
          · exact wv_append T.1 _ 0 _ _ (by rw [hx]; exact h1)
          · rfl
        rw [lhs, rhs, hg']
        simp only [List.map_map]
        rfl
    · simp only [List.length_append, List.length_singleton]
      omega

lemma inv_run {n : ℕ} {a b : Fin n} {S : Finset ℕ} {C : Circuit} (hC : FanInTwo C)
    {t : ℕ → ℕ}
    (ht : ∀ g ∈ S, (t g < n + g ∨ n + C.gates.length ≤ t g) ∧ ∀ x : Fin n → Bool,
       wv C (List.ofFn (rs a b x)) (n + g) = wv C (List.ofFn (rs a b x)) (t g)) :
    ∀ k, k ≤ C.gates.length →
      Inv n a b S C (run n a.val b.val (n + C.gates.length) S t (C.gates.take k)) k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [List.take_zero, run, List.foldl_nil]
    refine ⟨fun g hg => by simp at hg, rfl, fun j hj => by omega, fun j hj => by omega,
      by simp⟩
  | succ k ih =>
    intro hk
    have hk' : k < C.gates.length := by omega
    have e : C.gates.take (k + 1) = C.gates.take k ++ [gateAt C k] := by
      rw [List.take_succ, List.getElem?_eq_getElem hk', gateAt_eq hk']
      rfl
    rw [e, run, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact inv_step hC ht hk' (ih (by omega))

theorem main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1) (x5 : Finset ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     (∀ x7 ∈ x5, x7 < x2.size) →       (∀ x8 ∈ x5,           ∃ (x10 : ℕ),             (x10 < x1 + x8 ∨ x1 + x2.size ≤ x10) ∧               ∀ (x11 : Fin x1 → Bool),                 have x12 : List Bool := x2.wires (List.ofFn (Function.update (Function.update x11 x3 Bool.false) x4 Bool.false));                 x12.getD (x1 + x8) Bool.false = x12.getD x10 Bool.false) →         PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x9 : Fin x1 → Bool) => x2.eval (List.ofFn (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false))) (x2.size - x5.card) := by
  intro n C a b S hC hS H
  have H' : ∀ g ∈ S, ∃ t, (t < n + g ∨ n + C.gates.length ≤ t) ∧ ∀ x : Fin n → Bool,
      wv C (List.ofFn (rs a b x)) (n + g) = wv C (List.ofFn (rs a b x)) t := by
    intro g hg
    obtain ⟨t, h1, h2⟩ := H g hg
    exact ⟨t, h1, fun x => h2 x⟩
  choose! t ht using H'
  have hI := inv_run (a := a) (b := b) hC ht C.gates.length le_rfl
  rw [List.take_length] at hI
  generalize hT : run n a.val b.val (n + C.gates.length) S t C.gates = T at hI
  have hsem := pin_sem hI le_rfl C.output
  generalize hP : pin n a.val b.val (n + C.gates.length) T.2 C.output = Q at hsem
  refine ⟨⟨T.1, Q⟩, hI.1, ?_, ?_⟩
  · have hc := hI.2.2.2.2
    have hf : S.filter (· < C.gates.length) = S :=
      Finset.filter_true_of_mem (fun x hx => hS x hx)
    rw [hf] at hc
    show T.1.length ≤ C.gates.length - S.card
    omega
  · intro x
    have e1 := hsem x
    have hl : C.eval (List.ofFn (rs a b x)) = wv C (List.ofFn (rs a b x)) C.output := rfl
    have hr : (⟨T.1, Q⟩ : Circuit).eval (List.ofFn x) = sv n T.1 (List.ofFn x) Q := by
      show wv ⟨T.1, Q⟩ (List.ofFn x) Q = _
      rw [wv_out T.1 Q 0]
      unfold sv
      split_ifs with h
      · rfl
      · exact wv_ge (n := n) (by simp) (by show n + T.1.length ≤ Q; omega)
    show _ = C.eval (List.ofFn (rs a b x))
    rw [hr, hl, ← e1]
    split_ifs with h
    · rfl
    · exact (wv_ge (n := n) (by simp) (by omega)).symm

end PEqualNP.Outside.L_meta_5106

theorem PEqualNP.Outside.L_meta_5106 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1) (x5 : Finset ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     (∀ x7 ∈ x5, x7 < x2.size) →       (∀ x8 ∈ x5,           ∃ (x10 : ℕ),             (x10 < x1 + x8 ∨ x1 + x2.size ≤ x10) ∧               ∀ (x11 : Fin x1 → Bool),                 have x12 : List Bool := x2.wires (List.ofFn (Function.update (Function.update x11 x3 Bool.false) x4 Bool.false));                 x12.getD (x1 + x8) Bool.false = x12.getD x10 Bool.false) →         PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x9 : Fin x1 → Bool) => x2.eval (List.ofFn (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false))) (x2.size - x5.card) :=
  PEqualNP.Outside.L_meta_5106.main

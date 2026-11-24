import Mathlib
import PEqualNP.Defs

-- Adding three star gadgets to a monotone circuit on 25 inputs.

namespace PEqualNP.Outside.L_meta_2573_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def og (a b : ℕ) : Gate := ⟨GateOp.or, [a, b]⟩
def ag (a b : ℕ) : Gate := ⟨GateOp.and, [a, b]⟩

def gs (N o w : ℕ) : List Gate :=
  [og 12 14, og N 20, og (N + 1) 24, ag 0 (N + 2),
   og 12 18, og (N + 4) 22, og (N + 5) 23, ag 2 (N + 6),
   og 12 16, og (N + 8) 17, og (N + 9) 19, ag 8 (N + 10),
   og (N + 3) (N + 7), og (N + 12) (N + 11), og o (N + 13), og w 12]

theorem gs_len (N o w : ℕ) : (gs N o w).length = 16 := rfl

theorem gs_mono (N o w : ℕ) : ∀ g ∈ gs N o w,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp [gs] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> simp [og, ag]

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem node (gl : List Gate) (W : List Bool) (k : ℕ) (g : Gate) (hg : gl[k]? = some g)
    (hin : ∀ i ∈ g.inputs, i < W.length + k) :
    (wiresFrom gl W).getD (W.length + k) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom gl W).getD i false) := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gl k g hg
  have hl : (wiresFrom pre W).length = W.length + pre.length := length_wiresFrom pre W
  have h1 : wiresFrom (pre ++ g :: post) W = wiresFrom post
      (wiresFrom pre W ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre W).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i, i < W.length + pre.length →
      (wiresFrom (pre ++ g :: post) W).getD i false = (wiresFrom pre W).getD i false := by
    intro i hi
    rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [hl]; exact hi)]
  rw [h1] at hpre
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl])]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hl, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hpre i (hin i hi)).symm

theorem ext (W : List Bool) (h25 : 25 ≤ W.length) (o w : ℕ) (ho : o < W.length)
    (hw : w < W.length) :
    (wiresFrom (gs W.length o w) W).getD (W.length + 14) false =
      (W.getD o false ||
        ((W.getD 0 false && (W.getD 12 false || W.getD 14 false || W.getD 20 false
            || W.getD 24 false)) ||
         (W.getD 2 false && (W.getD 12 false || W.getD 18 false || W.getD 22 false
            || W.getD 23 false)) ||
         (W.getD 8 false && (W.getD 12 false || W.getD 16 false || W.getD 17 false
            || W.getD 19 false)))) ∧
    (wiresFrom (gs W.length o w) W).getD (W.length + 15) false =
      (W.getD w false || W.getD 12 false) := by
  generalize hN : W.length = N at *
  have hF : ∀ i, i < N → (wiresFrom (gs N o w) W).getD i false = W.getD i false := by
    intro i hi; exact getD_wiresFrom _ _ _ (by omega)
  have nd : ∀ k g, (gs N o w)[k]? = some g → (∀ i ∈ g.inputs, i < N + k) →
      (wiresFrom (gs N o w) W).getD (N + k) false
        = g.op.eval (g.inputs.map fun i => (wiresFrom (gs N o w) W).getD i false) := by
    intro k g hg hi; subst hN; exact node _ _ k g hg hi
  generalize hF' : (wiresFrom (gs N o w) W).getD = F at hF nd
  have e : ∀ k a b, (gs N o w)[k]? = some (og a b) → a < N + k → b < N + k →
      F (N + k) false = (F a false || F b false) := by
    intro k a b hg ha hb
    rw [nd k _ hg (by simp [og]; omega)]; simp [og, GateOp.eval]
  have e' : ∀ k a b, (gs N o w)[k]? = some (ag a b) → a < N + k → b < N + k →
      F (N + k) false = (F a false && F b false) := by
    intro k a b hg ha hb
    rw [nd k _ hg (by simp [ag]; omega)]; simp [ag, GateOp.eval]
  have g0 := e 0 12 14 rfl (by omega) (by omega)
  have g1 := e 1 (N + 0) 20 rfl (by omega) (by omega)
  have g2 := e 2 (N + 1) 24 rfl (by omega) (by omega)
  have g3 := e' 3 0 (N + 2) rfl (by omega) (by omega)
  have g4 := e 4 12 18 rfl (by omega) (by omega)
  have g5 := e 5 (N + 4) 22 rfl (by omega) (by omega)
  have g6 := e 6 (N + 5) 23 rfl (by omega) (by omega)
  have g7 := e' 7 2 (N + 6) rfl (by omega) (by omega)
  have g8 := e 8 12 16 rfl (by omega) (by omega)
  have g9 := e 9 (N + 8) 17 rfl (by omega) (by omega)
  have g10 := e 10 (N + 9) 19 rfl (by omega) (by omega)
  have g11 := e' 11 8 (N + 10) rfl (by omega) (by omega)
  have g12 := e 12 (N + 3) (N + 7) rfl (by omega) (by omega)
  have g13 := e 13 (N + 12) (N + 11) rfl (by omega) (by omega)
  have g14 := e 14 o (N + 13) rfl (by omega) (by omega)
  have g15 := e 15 w 12 rfl (by omega) (by omega)
  rw [g14, g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, g0, g15]
  simp only [Nat.add_zero] at *
  rw [hF o ho, hF w hw, hF 0 (by omega), hF 2 (by omega), hF 8 (by omega), hF 12 (by omega),
    hF 14 (by omega), hF 16 (by omega), hF 17 (by omega), hF 18 (by omega), hF 19 (by omega),
    hF 20 (by omega), hF 22 (by omega), hF 23 (by omega), hF 24 (by omega)]
  constructor
  · cases W.getD o false <;> cases W.getD 0 false <;> cases W.getD 2 false <;>
      cases W.getD 8 false <;> simp [Bool.or_assoc]
  · rfl

theorem inp (gl : List Gate) (x : Fin 25 → Bool) (i : Fin 25) :
    (wiresFrom gl (List.ofFn x)).getD i false = x i := by
  rw [getD_wiresFrom _ _ _ (by simp)]
  fin_cases i <;> rfl

theorem star (x : Fin 25 → Bool) :
    (∃ (p : Fin 25) (l : Fin 25), (p : ℕ) < 12 ∧ 12 ≤ (l : ℕ) ∧
      ((p : ℕ) + l + 2) % 13 ∈ [0, 1, 3, 9] ∧ (p : ℕ) ∈ [0, 2, 8] ∧ x p = true ∧ x l = true) ↔
    ((x 0 && (x 12 || x 14 || x 20 || x 24)) ||
     (x 2 && (x 12 || x 18 || x 22 || x 23)) ||
     (x 8 && (x 12 || x 16 || x 17 || x 19))) = true := by
  constructor
  · rintro ⟨p, l, h1, h2, h3, h4, hp, hl⟩
    fin_cases p <;> simp at h4 <;> fin_cases l <;> simp at h2 h3 <;> simp_all
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((⟨ha, ((hb | hb) | hb) | hb⟩ | ⟨ha, ((hb | hb) | hb) | hb⟩) |
        ⟨ha, ((hb | hb) | hb) | hb⟩) <;>
      exact ⟨_, _, by decide, by decide, by decide, by decide, ha, hb⟩

end PEqualNP.Outside.L_meta_2573_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2573_aux
theorem PEqualNP.Outside.L_meta_2573 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output < (25 : ℕ) + x1.size → x2 < (25 : ℕ) + x1.size → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x1.size + (16 : ℕ) ∧ x6.output < (25 : ℕ) + x6.size ∧ x7 < (25 : ℕ) + x6.size ∧ ∀ (x8 : Fin (25 : ℕ) → Bool), (x6.eval (List.ofFn x8) = Bool.true ↔ x1.eval (List.ofFn x8) = Bool.true ∨ ∃ (x9 : Fin (25 : ℕ)) (x10 : Fin (25 : ℕ)), ↑x9 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x10 ∧ (↑x9 + ↑x10 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x9 ∈ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) ∧ (x6.wires (List.ofFn x8)).getD x7 Bool.false = ((x1.wires (List.ofFn x8)).getD x2 Bool.false || x8 (12 : Fin (25 : ℕ))) := by
  intro C w hm ho hw
  refine ⟨⟨C.gates ++ gs (25 + C.gates.length) C.output w, 25 + C.gates.length + 14⟩,
    25 + C.gates.length + 15, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hm g h
    · exact gs_mono _ _ _ g h
  · simp [Circuit.size, gs_len]
  · simp [Circuit.size, gs_len]; omega
  · simp [Circuit.size, gs_len]; omega
  · intro x
    have hW : (wiresFrom C.gates (List.ofFn x)).length = 25 + C.gates.length := by
      rw [length_wiresFrom]; simp
    have hE := ext (wiresFrom C.gates (List.ofFn x)) (by omega) C.output w
      (by rw [hW]; exact ho) (by rw [hW]; exact hw)
    rw [hW] at hE
    obtain ⟨h1, h2⟩ := hE
    have i0 : (wiresFrom C.gates (List.ofFn x)).getD 0 false = x 0 :=
      inp C.gates x 0
    have i2 : (wiresFrom C.gates (List.ofFn x)).getD 2 false = x 2 :=
      inp C.gates x 2
    have i8 : (wiresFrom C.gates (List.ofFn x)).getD 8 false = x 8 :=
      inp C.gates x 8
    have i12 : (wiresFrom C.gates (List.ofFn x)).getD 12 false = x 12 :=
      inp C.gates x 12
    have i14 : (wiresFrom C.gates (List.ofFn x)).getD 14 false = x 14 :=
      inp C.gates x 14
    have i16 : (wiresFrom C.gates (List.ofFn x)).getD 16 false = x 16 :=
      inp C.gates x 16
    have i17 : (wiresFrom C.gates (List.ofFn x)).getD 17 false = x 17 :=
      inp C.gates x 17
    have i18 : (wiresFrom C.gates (List.ofFn x)).getD 18 false = x 18 :=
      inp C.gates x 18
    have i19 : (wiresFrom C.gates (List.ofFn x)).getD 19 false = x 19 :=
      inp C.gates x 19
    have i20 : (wiresFrom C.gates (List.ofFn x)).getD 20 false = x 20 :=
      inp C.gates x 20
    have i22 : (wiresFrom C.gates (List.ofFn x)).getD 22 false = x 22 :=
      inp C.gates x 22
    have i23 : (wiresFrom C.gates (List.ofFn x)).getD 23 false = x 23 :=
      inp C.gates x 23
    have i24 : (wiresFrom C.gates (List.ofFn x)).getD 24 false = x 24 :=
      inp C.gates x 24
    rw [i0, i2, i8, i12, i14, i16, i17, i18, i19, i20, i22, i23, i24] at h1
    rw [i12] at h2
    have hc : ∀ (D : Circuit), D.wires (List.ofFn x) = wiresFrom D.gates (List.ofFn x) :=
      fun _ => rfl
    refine ⟨?_, ?_⟩
    · rw [star x]
      show (wiresFrom (C.gates ++ gs (25 + C.gates.length) C.output w) (List.ofFn x)).getD
          (25 + C.gates.length + 14) false = true ↔
        (wiresFrom C.gates (List.ofFn x)).getD C.output false = true ∨ _
      rw [wiresFrom_append, h1, Bool.or_eq_true]
    · rw [hc, hc]
      show (wiresFrom (C.gates ++ gs (25 + C.gates.length) C.output w) (List.ofFn x)).getD
          (25 + C.gates.length + 15) false = _
      rw [wiresFrom_append, h2]

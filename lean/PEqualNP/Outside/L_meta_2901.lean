import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2901

open PEqualNP.CircuitLowerBounds

def bop (N : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.foldr (· &&& ·) (2 ^ N - 1)
  | _, l => l.foldr (· ||| ·) 0

def bw (N : ℕ) (gs : List Gate) (w : List ℕ) : List ℕ :=
  gs.foldl (fun w g => w ++ [bop N g.op (g.inputs.map fun i => w.getD i 0)]) w

lemma and_bit (N a : ℕ) (ha : a < N) : ∀ l : List ℕ,
    (l.foldr (· &&& ·) (2 ^ N - 1)).testBit a = (l.map fun m => m.testBit a).all id
  | [] => by simp [ha]
  | m :: l => by simp [Nat.testBit_and, and_bit N a ha l]

lemma or_bit (a : ℕ) : ∀ l : List ℕ,
    (l.foldr (· ||| ·) 0).testBit a = (l.map fun m => m.testBit a).any id
  | [] => by simp
  | m :: l => by simp [Nat.testBit_or, or_bit a l]

lemma bop_bit (N a : ℕ) (ha : a < N) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) : (bop N op l).testBit a = op.eval (l.map fun m => m.testBit a) := by
  rcases hop with rfl | rfl
  · exact and_bit N a ha l
  · exact or_bit a l

lemma key (N a : ℕ) (ha : a < N) : ∀ (gs : List Gate) (w : List ℕ) (wv : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → w.length = wv.length →
    (∀ i, (w.getD i 0).testBit a = wv.getD i false) →
    ∀ i, ((bw N gs w).getD i 0).testBit a =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wv).getD i false
  | [], w, wv, _, _, h => by simpa [bw] using h
  | g :: gs, w, wv, hops, hl, h => by
    have hg := hops g List.mem_cons_self
    have hstep : ∀ i, ((w ++ [bop N g.op (g.inputs.map fun i => w.getD i 0)]).getD i 0).testBit a =
        (wv ++ [g.op.eval (g.inputs.map fun i => wv.getD i false)]).getD i false := by
      intro i
      rcases lt_trichotomy i w.length with hi | rfl | hi
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi), h]
      · rw [List.getD_append_right _ _ _ _ le_rfl, hl, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        rw [bop_bit N a ha _ hg, List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact h j
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        simp
    exact key N a ha gs _ _ (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg')) (by simp [hl]) hstep

def mk (p : ℕ → Bool) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | k :: ks, acc => mk p ks (if p k then acc ||| 2 ^ k else acc)

lemma mk_bit (p : ℕ → Bool) (i : ℕ) : ∀ (ks : List ℕ) (acc : ℕ),
    (mk p ks acc).testBit i = (acc.testBit i || (decide (i ∈ ks) && p i))
  | [], acc => by simp [mk]
  | k :: ks, acc => by
    rw [mk, mk_bit p i ks]
    by_cases hk : p k <;> by_cases hik : i = k
    · subst hik; simp [hk, Nat.testBit_or]
    · simp [hk, hik, Nat.testBit_or, Ne.symm hik]
    · subst hik; simp [hk]
    · simp [hk, hik]

lemma enc_bit (v : List Bool) (i : ℕ) :
    (mk (fun k => v.getD k false) (List.range 7) 0).testBit i = (decide (i < 7) && v.getD i false) := by
  rw [mk_bit]; simp

lemma enc_lt (v : List Bool) : mk (fun k => v.getD k false) (List.range 7) 0 < 2 ^ 7 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [enc_bit]
  simp; omega

def YM : List ℕ := [226854911280625642308916404954512140970, 272225893536750770770699685945414569164, 320265757102059730318470218759311257840, 338958311018522360492699998064329424640, 340277174703306882242637262502835978240, 340282366841710300967557013907638845440, 340282366920938463444927863358058659840]

def E : List (ℕ × ℕ) := [(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)]

def XM (c : ℕ) : List ℕ := (List.range 7).map fun p => if c.testBit p then 2 ^ 128 - 1 else 0

def T (c : ℕ) : ℕ := E.foldr (fun e acc => ((XM c).getD e.1 0 &&& YM.getD e.2 0) ||| acc) 0

def gs : List Gate := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }]

lemma check : ∀ c < 128, (bw 128 gs (XM c ++ YM)).getD 44 0 = T c := by decide +kernel

lemma ybits : ∀ l < 7, ∀ a < 128, (YM.getD l 0).testBit a = a.testBit l := by decide +kernel

lemma ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
  simp [gs]

lemma lens : ∀ g ∈ gs, g.inputs.length ≤ 2 := by
  simp [gs]

lemma hE : ∀ e ∈ E, e.1 < 7 ∧ e.2 < 7 := by decide

lemma T_bit (c a : ℕ) : (T c).testBit a =
    E.any (fun e => ((XM c).getD e.1 0).testBit a && (YM.getD e.2 0).testBit a) := by
  unfold T
  generalize E = L
  induction L with
  | nil => simp
  | cons e L ih => simp only [List.foldr_cons, List.any_cons, Nat.testBit_or, Nat.testBit_and, ih]

lemma XM_get (c p : ℕ) (hp : p < 7) : (XM c).getD p 0 = if c.testBit p then 2 ^ 128 - 1 else 0 := by
  simp [XM, List.getD_eq_getElem?_getD, hp]

lemma main (x y : Fin 7 → Bool) : Circuit.eval ⟨gs, 44⟩ (List.ofFn x ++ List.ofFn y) =
    decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ E ∧ x p = true ∧ y l = true) := by
  set c := mk (fun k => (List.ofFn x).getD k false) (List.range 7) 0 with hc
  set a := mk (fun k => (List.ofFn y).getD k false) (List.range 7) 0 with ha
  have hc7 : c < 128 := enc_lt _
  have ha7 : a < 128 := enc_lt _
  have hxb : ∀ p : Fin 7, (List.ofFn x).getD p false = x p := by
    intro p; fin_cases p <;> rfl
  have hyb : ∀ p : Fin 7, (List.ofFn y).getD p false = y p := by
    intro p; fin_cases p <;> rfl
  have hX : ∀ p < 7, ((XM c).getD p 0).testBit a = (List.ofFn x).getD p false := by
    intro p hp
    rw [XM_get c p hp, hc, enc_bit]
    simp only [hp, decide_true, Bool.true_and]
    generalize (List.ofFn x).getD p false = b
    cases b
    · simp
    · simp only [ite_true, Nat.testBit_two_pow_sub_one, ha7, decide_true]
  have hY : ∀ l < 7, (YM.getD l 0).testBit a = (List.ofFn y).getD l false := by
    intro l hl
    rw [ybits l hl a ha7, ha, enc_bit]
    simp [hl]
  have hlenX : (XM c).length = 7 := by simp [XM]
  have hinit : ∀ i, ((XM c ++ YM).getD i 0).testBit a = (List.ofFn x ++ List.ofFn y).getD i false := by
    intro i
    by_cases h1 : i < 7
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by simp; omega), hX i h1]
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [hlenX, List.length_ofFn]
      by_cases h2 : i - 7 < 7
      · exact hY _ h2
      · rw [List.getD_eq_default _ _ (by simp [YM]; omega), List.getD_eq_default _ _ (by simp; omega)]
        simp
  have hk := key 128 a ha7 gs (XM c ++ YM) (List.ofFn x ++ List.ofFn y) ops
    (by simp [hlenX, YM]) hinit 44
  rw [check c hc7, T_bit] at hk
  unfold Circuit.eval Circuit.wires
  simp only
  rw [← hk, Bool.eq_iff_iff]
  simp only [List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨p, l⟩, he, h1, h2⟩
    have hb := hE (p, l) he
    rw [hX p hb.1] at h1
    rw [hY l hb.2] at h2
    exact ⟨⟨p, hb.1⟩, ⟨l, hb.2⟩, he, by rw [← hxb]; exact h1, by rw [← hyb]; exact h2⟩
  · rintro ⟨p, l, he, h1, h2⟩
    refine ⟨((p : ℕ), (l : ℕ)), he, ?_, ?_⟩
    · rw [hX p p.2, hxb]; exact h1
    · rw [hY l l.2, hyb]; exact h2

end PEqualNP.Outside.L_meta_2901

theorem PEqualNP.Outside.L_meta_2901 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 31 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C ∧
  (∀ x y : Fin 7 → Bool, C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true)) ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a : Fin 7 => decide (a ∈ ({3} : Finset (Fin 7)))) ++ List.ofFn (fun b : Fin 7 => decide (b ∈ ({1} : Finset (Fin 7))))) = false ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a2 : Fin 7 => decide (a2 ∈ ({5} : Finset (Fin 7)))) ++ List.ofFn (fun b2 : Fin 7 => decide (b2 ∈ ({2} : Finset (Fin 7))))) = false := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_, PEqualNP.Outside.L_meta_2901.main, ?_, ?_⟩
  · intro g hg
    have h := PEqualNP.Outside.L_meta_2901.ops g hg
    refine ⟨?_, ?_⟩
    · rcases h with h | h <;> simp [h]
    · exact PEqualNP.Outside.L_meta_2901.lens g hg
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack; decide
  · decide
  · decide

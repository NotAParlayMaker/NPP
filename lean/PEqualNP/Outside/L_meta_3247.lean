import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3247

open PEqualNP.CircuitLowerBounds

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wstep_len (w : List Bool) (g : Gate) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wstep_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD, List.getElem?_append_left hi]

lemma wstep_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (wstep w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [wstep, List.getD]

lemma tsnoc_lt (T : List (List (List ℕ))) (a : List (List ℕ)) (i : ℕ) (h : i < T.length) :
    (T ++ [a]).getD i [] = T.getD i [] := by
  simp [List.getD, List.getElem?_append_left h]

lemma tsnoc_eq (T : List (List (List ℕ))) (a : List (List ℕ)) (i : ℕ) (h : i = T.length) :
    (T ++ [a]).getD i [] = a := by
  subst h
  simp [List.getD]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  first
  | rw [List.getElem_ofFn]
  | simp

def evalD (v : ℕ → Bool) (D : List (List ℕ)) : Bool := D.any fun c => c.all v

def prodD (D1 D2 : List (List ℕ)) : List (List ℕ) :=
  D1.flatMap fun c1 => D2.map fun c2 => c1 ++ c2

lemma evalD_append (v : ℕ → Bool) (D1 D2 : List (List ℕ)) :
    evalD v (D1 ++ D2) = (evalD v D1 || evalD v D2) := by
  unfold evalD
  rw [List.any_append]

lemma evalD_prod (v : ℕ → Bool) (D1 D2 : List (List ℕ)) :
    evalD v (prodD D1 D2) = (evalD v D1 && evalD v D2) := by
  rw [Bool.eq_iff_iff]
  simp only [evalD, prodD, List.any_eq_true, List.mem_flatMap, List.mem_map, Bool.and_eq_true,
    List.all_eq_true]
  constructor
  · rintro ⟨c, ⟨c1, h1, c2, h2, rfl⟩, hc⟩
    exact ⟨⟨c1, h1, fun i hi => hc i (List.mem_append_left _ hi)⟩,
      ⟨c2, h2, fun i hi => hc i (List.mem_append_right _ hi)⟩⟩
  · rintro ⟨⟨c1, h1, a1⟩, ⟨c2, h2, a2⟩⟩
    refine ⟨c1 ++ c2, ⟨c1, h1, c2, h2, rfl⟩, fun i hi => ?_⟩
    rcases List.mem_append.mp hi with h | h
    · exact a1 i h
    · exact a2 i h

def gD (T : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.and => (g.inputs.map fun i => T.getD i []).foldr prodD [[]]
  | _ => (g.inputs.map fun i => T.getD i []).foldr (fun a b => a ++ b) []

def okb (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => decide (g.inputs.length ≤ 2)
  | GateOp.or => decide (g.inputs.length ≤ 2)
  | _ => false

def tstep (T : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) := T ++ [gD T g]

lemma all_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (l : List ℕ) :
    (l.map fun i => w.getD i false).all id
      = evalD v ((l.map fun i => T.getD i []).foldr prodD [[]]) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (id (w.getD a false) && (l.map fun i => w.getD i false).all id)
      = evalD v (prodD (T.getD a []) ((l.map fun i => T.getD i []).foldr prodD [[]]))
    rw [evalD_prod, ← ih, h a]
    rfl

lemma any_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (l : List ℕ) :
    (l.map fun i => w.getD i false).any id
      = evalD v ((l.map fun i => T.getD i []).foldr (fun a b => a ++ b) []) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (id (w.getD a false) || (l.map fun i => w.getD i false).any id)
      = evalD v (T.getD a [] ++ ((l.map fun i => T.getD i []).foldr (fun a b => a ++ b) []))
    rw [evalD_append, ← ih, h a]
    rfl

lemma gD_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (g : Gate) (hg : okb g = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = evalD v (gD T g) := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and => exact all_spec v w T h ins
  | or => exact any_spec v w T h ins
  | not => exact absurd hg Bool.false_ne_true
  | mod m => exact absurd hg Bool.false_ne_true
  | maj => exact absurd hg Bool.false_ne_true

def Good (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ))) : Prop :=
  w.length = T.length ∧ ∀ i, w.getD i false = evalD v (T.getD i [])

lemma good_step (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ))) (g : Gate)
    (hg : okb g = true) (h : Good v w T) : Good v (wstep w g) (tstep T g) := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨?_, fun i => ?_⟩
  · show (wstep w g).length = (T ++ [gD T g]).length
    rw [wstep_len, List.length_append, List.length_singleton, hl]
  · show (wstep w g).getD i false = evalD v ((T ++ [gD T g]).getD i [])
    by_cases hlt : i < T.length
    · rw [tsnoc_lt T _ i hlt, wstep_lt _ _ _ (by rw [hl]; exact hlt)]
      exact hv i
    · by_cases heq : i = T.length
      · rw [tsnoc_eq T _ i heq, wstep_last _ _ _ (by rw [hl]; exact heq)]
        exact gD_spec v w T hv g hg
      · have h1 : (T ++ [gD T g]).getD i [] = [] :=
          List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)
        have h2 : (wstep w g).getD i false = false :=
          List.getD_eq_default _ _ (by rw [wstep_len, hl]; omega)
        rw [h1, h2]
        rfl

lemma good_fold (v : ℕ → Bool) (gs : List Gate) (hg : ∀ g ∈ gs, okb g = true) :
    ∀ (w : List Bool) (T : List (List (List ℕ))), Good v w T →
      Good v (gs.foldl wstep w) (gs.foldl tstep T) := by
  induction gs with
  | nil =>
    intro w T h
    exact h
  | cons g gs ih =>
    intro w T h
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (good_step v w T g (hg g (List.mem_cons.mpr (Or.inl rfl))) h)

def T0 : List (List (List ℕ)) := (List.range 14).map fun i => [[i]]

lemma T0_len : T0.length = 14 := by decide +kernel

lemma T0_get : ∀ i < 14, T0.getD i [] = [[i]] := by decide +kernel

lemma good_init (x : Fin 14 → Bool) :
    Good (fun i => x (Fin.ofNat 14 i)) (List.ofFn x) T0 := by
  refine ⟨by rw [List.length_ofFn, T0_len], fun i => ?_⟩
  by_cases h : i < 14
  · rw [ofFn_getD x i h, T0_get i h]
    show x ⟨i, h⟩ = ((x (Fin.ofNat 14 i) && true) || false)
    rw [Bool.and_true, Bool.or_false]
    exact congrArg x (Fin.ext (Nat.mod_eq_of_lt h).symm)
  · have h1 : (List.ofFn x).getD i false = false :=
      List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)
    have h2 : T0.getD i [] = [] := List.getD_eq_default _ _ (by rw [T0_len]; omega)
    rw [h1, h2]
    rfl

lemma vp (p : Fin 7) : (Fin.ofNat 14 p.val : Fin 14) = Fin.castAdd 7 p :=
  Fin.ext (Nat.mod_eq_of_lt (Nat.lt_trans p.isLt (by decide)))

lemma vl (w : Fin 7) : (Fin.ofNat 14 (7 + w.val) : Fin 14) = Fin.natAdd 7 w :=
  Fin.ext (Nat.mod_eq_of_lt (by have := w.isLt; omega))

lemma below (x : Fin 14 → Bool) (D : List (List ℕ))
    (hD : ∀ c ∈ D, ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ p.val ∈ c ∧ 7 + l.val ∈ c)
    (h : evalD (fun i => x (Fin.ofNat 14 i)) D = true) :
    ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true
      ∧ x (Fin.natAdd 7 l) = true := by
  unfold evalD at h
  obtain ⟨c, hc, ha⟩ := List.any_eq_true.mp h
  obtain ⟨p, l, hi, hp, hl⟩ := hD c hc
  have ha' := List.all_eq_true.mp ha
  have e1 : x (Fin.ofNat 14 p.val) = true := ha' _ hp
  have e2 : x (Fin.ofNat 14 (7 + l.val)) = true := ha' _ hl
  exact ⟨p, l, hi, (congrArg x (vp p)).symm.trans e1, (congrArg x (vl l)).symm.trans e2⟩

lemma above (x : Fin 14 → Bool) (D : List (List ℕ)) (p l : Fin 7)
    (hc : ∃ c ∈ D, ∀ i ∈ c, i = p.val ∨ i = 7 + l.val)
    (hp : x (Fin.castAdd 7 p) = true) (hl : x (Fin.natAdd 7 l) = true) :
    evalD (fun i => x (Fin.ofNat 14 i)) D = true := by
  obtain ⟨c, hcD, hci⟩ := hc
  unfold evalD
  refine List.any_eq_true.mpr ⟨c, hcD, List.all_eq_true.mpr fun i hi => ?_⟩
  rcases hci i hi with rfl | rfl
  · exact (congrArg x (vp p)).trans hp
  · exact (congrArg x (vl l)).trans hl

def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

lemma isAO_spec (o : GateOp) (h : isAO o = true) : o = GateOp.and ∨ o = GateOp.or := by
  cases o with
  | and => exact Or.inl rfl
  | or => exact Or.inr rfl
  | not => exact absurd h Bool.false_ne_true
  | mod m => exact absurd h Bool.false_ne_true
  | maj => exact absurd h Bool.false_ne_true

def ins2 (k : ℕ) : List ℕ → Bool
  | [u, v] => decide (u ≠ v) && decide (u < 14 + k) && decide (v < 14 + k)
  | _ => false

lemma ins2_spec (k : ℕ) (l : List ℕ) (h : ins2 k l = true) :
    ∃ u v : ℕ, l = [u, v] ∧ u ≠ v ∧ u < 14 + k ∧ v < 14 + k := by
  match l, h with
  | [u, v], h =>
    simp only [ins2, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨u, v, rfl, h.1.1, h.1.2, h.2⟩
  | [], h => exact absurd h Bool.false_ne_true
  | [_], h => exact absurd h Bool.false_ne_true
  | _ :: _ :: _ :: _, h => exact absurd h Bool.false_ne_true

def shapeb (k : ℕ) (g : Gate) : Bool := isAO g.op && ins2 k g.inputs

def chk : ℕ → List Gate → Bool
  | _, [] => true
  | k, g :: gs => shapeb k g && chk (k + 1) gs

lemma chk_spec : ∀ (gs : List Gate) (k : ℕ), chk k gs = true →
    ∀ (i : ℕ) (g : Gate), gs[i]? = some g → shapeb (k + i) g = true := by
  intro gs
  induction gs with
  | nil =>
    intro k _ i g h
    simp at h
  | cons a gs ih =>
    intro k hc i g h
    simp only [chk, Bool.and_eq_true] at hc
    cases i with
    | zero =>
      simp at h
      subst h
      simpa using hc.1
    | succ i =>
      simp at h
      have := ih (k + 1) hc.2 i g h
      rwa [show k + 1 + i = k + (i + 1) by omega] at this

def GS : List Gate := [⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [14, 10]⟩, ⟨GateOp.and, [0, 15]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [17, 13]⟩, ⟨GateOp.and, [1, 18]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [20, 13]⟩, ⟨GateOp.and, [2, 21]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [23, 12]⟩, ⟨GateOp.and, [3, 24]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [26, 13]⟩, ⟨GateOp.and, [4, 27]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [29, 12]⟩, ⟨GateOp.and, [5, 30]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [32, 11]⟩, ⟨GateOp.and, [6, 33]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.or, [35, 22]⟩, ⟨GateOp.or, [36, 25]⟩, ⟨GateOp.or, [37, 28]⟩, ⟨GateOp.or, [38, 31]⟩, ⟨GateOp.or, [39, 34]⟩]

def Cw : Circuit := ⟨GS, 40⟩

def TF : List (List (List ℕ)) := GS.foldl tstep T0

lemma gs_ok : ∀ g ∈ GS, okb g = true := by decide +kernel

lemma gs_chk : chk 0 GS = true := by decide +kernel

lemma good_all (x : Fin 14 → Bool) :
    Good (fun i => x (Fin.ofNat 14 i)) (Cw.wires (List.ofFn x)) TF :=
  good_fold _ GS gs_ok _ _ (good_init x)

lemma clean_b : ∀ k < 26, GS.any (fun g => decide (14 + k ∈ g.inputs)) = true := by
  decide +kernel

lemma f2 : ∀ c ∈ TF.getD 40 [], ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3)
    ∧ p.val ∈ c ∧ 7 + l.val ∈ c := by
  decide +kernel

lemma f3 : ∀ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) →
    ∃ c ∈ TF.getD 40 [], ∀ i ∈ c, i = p.val ∨ i = 7 + l.val := by
  decide +kernel

lemma shape_all : ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), Cw.gates[k]? = some g →
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
    ∧ ∃ u v : ℕ, g.inputs = [u, v] ∧ u ≠ v ∧ u < 14 + k ∧ v < 14 + k := by
  intro k g h
  have hs := chk_spec GS 0 gs_chk k g h
  rw [Nat.zero_add] at hs
  simp only [shapeb, Bool.and_eq_true] at hs
  exact ⟨isAO_spec _ hs.1, ins2_spec k _ hs.2⟩

lemma clean_all : ∀ k : ℕ, k + 1 < Cw.size → ∃ (k' : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
    Cw.gates[k']? = some g ∧ 14 + k ∈ g.inputs := by
  intro k hk
  have hk' : k + 1 < 27 := hk
  obtain ⟨g, hg, hm⟩ := List.any_eq_true.mp (clean_b k (by omega))
  obtain ⟨k', hk''⟩ := List.mem_iff_getElem?.mp hg
  exact ⟨k', g, hk'', of_decide_eq_true hm⟩

lemma fun_all : ∀ x : Fin 14 → Bool, Cw.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
    (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true
      ∧ x (Fin.natAdd 7 l) = true := by
  intro x
  show (Cw.wires (List.ofFn x)).getD 40 false = true ↔ _
  rw [(good_all x).2 40]
  constructor
  · exact below x _ f2
  · rintro ⟨p, l, hi, hp, hl⟩
    exact above x _ p l (f3 p l hi) hp hl

def ohb (j : ℕ) : Bool := (List.finRange 14).any fun i =>
  (Cw.wires (List.ofFn (fun t : Fin 14 => decide (t = i)))).getD (14 + j) false

def belb (j : ℕ) : Bool := (TF.getD (14 + j) []).all fun c =>
  decide (∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ p.val ∈ c ∧ 7 + l.val ∈ c)

lemma clsb : (List.range 27).all (fun j => ohb j || belb j) = true := by
  decide +kernel

theorem main : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size = 27 ∧ (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ u v : ℕ, g.inputs = [u, v] ∧ u ≠ v ∧ u < 14 + k ∧ v < 14 + k) ∧ C.output + 1 = 14 + C.size ∧ (∀ k : ℕ, k + 1 < C.size → ∃ (k' : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k']? = some g ∧ 14 + k ∈ g.inputs) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧ ¬ (∃ j : ℕ, j < C.size ∧ (∀ i : Fin 14, (C.wires (List.ofFn (fun t : Fin 14 => decide (t = i)))).getD (14 + j) false = false) ∧ (∃ x : Fin 14 → Bool, (C.wires (List.ofFn x)).getD (14 + j) false = true ∧ ¬ ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧ ∃ (k k' : ℕ) (g g' : PEqualNP.CircuitLowerBounds.Gate), k ≠ k' ∧ C.gates[k]? = some g ∧ C.gates[k']? = some g' ∧ 14 + j ∈ g.inputs ∧ 14 + j ∈ g'.inputs) := by
  refine ⟨Cw, rfl, shape_all, rfl, clean_all, fun_all, ?_⟩
  rintro ⟨j, hj, h1, ⟨x, hx1, hx2⟩, -⟩
  have hj' : j < 27 := hj
  have hc := List.all_eq_true.mp clsb j (List.mem_range.mpr hj')
  rcases Bool.or_eq_true_iff.mp hc with ho | hb
  · obtain ⟨i, -, hi⟩ := List.any_eq_true.mp ho
    rw [h1 i] at hi
    exact Bool.false_ne_true hi
  · rw [(good_all x).2 (14 + j)] at hx1
    exact hx2 (below x _ (fun c hc => of_decide_eq_true (List.all_eq_true.mp hb c hc)) hx1)

end PEqualNP.Outside.L_meta_3247

theorem PEqualNP.Outside.L_meta_3247 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size = 27 ∧ (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ u v : ℕ, g.inputs = [u, v] ∧ u ≠ v ∧ u < 14 + k ∧ v < 14 + k) ∧ C.output + 1 = 14 + C.size ∧ (∀ k : ℕ, k + 1 < C.size → ∃ (k' : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k']? = some g ∧ 14 + k ∈ g.inputs) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧ ¬ (∃ j : ℕ, j < C.size ∧ (∀ i : Fin 14, (C.wires (List.ofFn (fun t : Fin 14 => decide (t = i)))).getD (14 + j) false = false) ∧ (∃ x : Fin 14 → Bool, (C.wires (List.ofFn x)).getD (14 + j) false = true ∧ ¬ ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧ ∃ (k k' : ℕ) (g g' : PEqualNP.CircuitLowerBounds.Gate), k ≠ k' ∧ C.gates[k]? = some g ∧ C.gates[k']? = some g' ∧ 14 + j ∈ g.inputs ∧ 14 + j ∈ g'.inputs) := by
  exact PEqualNP.Outside.L_meta_3247.main

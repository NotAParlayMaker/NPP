import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2738

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mu (j w : ℕ) : ℕ := if w < 10 then w else if w < 10 + j then w + 2 else 10

def normAO (isAnd : Bool) (op : GateOp) (j : ℕ) : List ℕ → Gate
  | [] => if isAnd then ⟨GateOp.not, [10]⟩ else ⟨GateOp.not, [11]⟩
  | [a] => ⟨GateOp.and, [mu j a, 11]⟩
  | a :: b :: _ => if mu j a = mu j b then ⟨GateOp.and, [mu j a, 11]⟩ else ⟨op, [mu j a, mu j b]⟩

def normNot (j : ℕ) : List ℕ → Gate
  | [] => ⟨GateOp.not, [10]⟩
  | a :: _ => ⟨GateOp.not, [mu j a]⟩

def norm (j : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => normAO true GateOp.and j g.inputs
  | GateOp.or => normAO false GateOp.or j g.inputs
  | GateOp.not => normNot j g.inputs
  | GateOp.mod _ => g
  | GateOp.maj => g

def normList : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs => norm j g :: normList (j + 1) gs

def Clean (k : ℕ) (g : Gate) : Prop :=
  (∀ w ∈ g.inputs, w < 12 + k) ∧ g.inputs.Nodup ∧
    (g.op = GateOp.not ∧ g.inputs.length = 1 ∨ g.op ≠ GateOp.not ∧ g.inputs.length = 2)

def AON (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

lemma mu_lt (j w : ℕ) : mu j w < 12 + j := by unfold mu; split_ifs <;> omega

lemma mu_ne (j w : ℕ) : mu j w ≠ 11 := by unfold mu; split_ifs <;> omega

lemma clean_norm (j : ℕ) (g : Gate) (h : AON g) : Clean j (norm j g) ∧ AON (norm j g) := by
  rcases g with ⟨op, ins⟩
  obtain ⟨hop, hlen⟩ := h
  simp only at hop hlen
  have h11 : 11 < 12 + j := by omega
  have h10 : 10 < 12 + j := by omega
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · simp [norm, normAO, Clean, AON, h10]
    · simp [norm, normAO, Clean, AON, mu_lt, mu_ne, h11]
    · by_cases hab : mu j a = mu j b
      · simp [norm, normAO, hab, Clean, AON, mu_lt, mu_ne, h11]
      · simp [norm, normAO, hab, Clean, AON, mu_lt]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · simp [norm, normAO, Clean, AON, h11]
    · simp [norm, normAO, Clean, AON, mu_lt, mu_ne, h11]
    · by_cases hab : mu j a = mu j b
      · simp [norm, normAO, hab, Clean, AON, mu_lt, mu_ne, h11]
      · simp [norm, normAO, hab, Clean, AON, mu_lt]
    · simp at hlen
  · rcases ins with _ | ⟨a, t⟩
    · simp [norm, normNot, Clean, AON, h10]
    · simp [norm, normNot, Clean, AON, mu_lt]

lemma val_eq (j : ℕ) (N O : List Bool) (g : Gate) (h : AON g)
    (hmu : ∀ w, N.getD (mu j w) false = O.getD w false)
    (h10 : N.getD 10 false = false) (h11 : N.getD 11 false = true) :
    (norm j g).op.eval ((norm j g).inputs.map fun i => N.getD i false) =
      g.op.eval (g.inputs.map fun i => O.getD i false) := by
  rcases g with ⟨op, ins⟩
  obtain ⟨hop, hlen⟩ := h
  simp only at hop hlen
  simp only [List.getD_eq_getElem?_getD] at hmu h10 h11
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · simp [norm, normAO, GateOp.eval, h10]
    · simp [norm, normAO, GateOp.eval, hmu, h11]
    · by_cases hab : mu j a = mu j b
      · have e : O[a]?.getD false = O[b]?.getD false := by rw [← hmu a, ← hmu b, hab]
        simp [norm, normAO, hab, GateOp.eval, h11, hmu, e]
      · simp [norm, normAO, hab, GateOp.eval, hmu]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · simp [norm, normAO, GateOp.eval, h11]
    · simp [norm, normAO, GateOp.eval, hmu, h11]
    · by_cases hab : mu j a = mu j b
      · have e : O[a]?.getD false = O[b]?.getD false := by rw [← hmu a, ← hmu b, hab]
        simp [norm, normAO, hab, GateOp.eval, h11, hmu, e]
      · simp [norm, normAO, hab, GateOp.eval, hmu]
    · simp at hlen
  · rcases ins with _ | ⟨a, t⟩
    · simp [norm, normNot, GateOp.eval, h10]
    · simp [norm, normNot, GateOp.eval, hmu]

lemma getD_N (X V : List Bool) (j : ℕ) (hX : X.length = 10) (hV : V.length = j) (w : ℕ) :
    (X ++ [false, true] ++ V).getD (mu j w) false = (X ++ V).getD w false := by
  have hXl : (X ++ [false, true]).length = 12 := by simp [hX]
  simp only [List.getD_eq_getElem?_getD]
  unfold mu
  split_ifs with h1 h2
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hXl, hX]
    congr 2
  · have hw : (X ++ V).length ≤ w := by simp only [List.length_append, hX, hV]; omega
    rw [List.getElem?_eq_none hw, List.getElem?_append_left (by omega),
      List.getElem?_append_right (by omega), hX]
    simp

lemma getD_N10 (X V : List Bool) (hX : X.length = 10) :
    (X ++ [false, true] ++ V).getD 10 false = false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [hX]), List.getElem?_append_right (by omega), hX]
  simp

lemma getD_N11 (X V : List Bool) (hX : X.length = 10) :
    (X ++ [false, true] ++ V).getD 11 false = true := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [hX]), List.getElem?_append_right (by omega), hX]
  simp

lemma run (gs : List Gate) : ∀ (j : ℕ) (X V : List Bool), X.length = 10 → V.length = j →
    (∀ g ∈ gs, AON g) →
    (normList j gs).foldl F (X ++ [false, true] ++ V) =
      X ++ [false, true] ++ (gs.foldl F (X ++ V)).drop 10 := by
  induction gs with
  | nil =>
    intro j X V hX _ _
    simp only [normList, List.foldl_nil]
    rw [List.drop_left' hX]
  | cons g gs ih =>
    intro j X V hX hV hg
    simp only [normList, List.foldl_cons]
    have hv := val_eq j (X ++ [false, true] ++ V) (X ++ V) g (hg g (by simp))
      (getD_N X V j hX hV) (getD_N10 X V hX) (getD_N11 X V hX)
    have e1 : F (X ++ [false, true] ++ V) (norm j g) = X ++ [false, true] ++
        (V ++ [g.op.eval (g.inputs.map fun i => (X ++ V).getD i false)]) := by
      simp only [F]
      rw [hv]
      simp only [List.append_assoc]
    have e2 : F (X ++ V) g =
        X ++ (V ++ [g.op.eval (g.inputs.map fun i => (X ++ V).getD i false)]) := by
      simp only [F, List.append_assoc]
    rw [e1, e2]
    exact ih (j + 1) X _ hX (by simp [hV]) (fun g' h' => hg g' (by simp [h']))

lemma normList_length (gs : List Gate) : ∀ j, (normList j gs).length = gs.length := by
  induction gs with
  | nil => intro j; rfl
  | cons g gs ih => intro j; simp [normList, ih]

lemma normList_aon (gs : List Gate) : ∀ j, (∀ g ∈ gs, AON g) → ∀ e ∈ normList j gs, AON e := by
  induction gs with
  | nil => intro j _ e he; simp [normList] at he
  | cons g gs ih =>
    intro j hg e he
    simp only [normList, List.mem_cons] at he
    rcases he with rfl | he
    · exact (clean_norm j g (hg g (by simp))).2
    · exact ih (j + 1) (fun g' h' => hg g' (by simp [h'])) e he

lemma normList_clean (gs : List Gate) : ∀ j, (∀ g ∈ gs, AON g) →
    ∀ (i : ℕ) (hi : i < (normList j gs).length), Clean (j + i) ((normList j gs)[i]) := by
  induction gs with
  | nil => intro j _ i hi; simp [normList] at hi
  | cons g gs ih =>
    intro j hg i hi
    rcases i with _ | i
    · simpa [normList] using (clean_norm j g (hg g (by simp))).1
    · have hi' : i < (normList (j + 1) gs).length := by
        simp only [normList, List.length_cons] at hi; omega
      have := ih (j + 1) (fun g' h' => hg g' (by simp [h'])) i hi'
      simp only [normList, List.getElem_cons_succ]
      rw [show j + (i + 1) = j + 1 + i by omega]
      exact this

lemma foldl_prefix (L : List Gate) : ∀ w : List Bool, w <+: L.foldl F w := by
  induction L with
  | nil => intro w; exact List.prefix_refl w
  | cons g L ih =>
    intro w
    simp only [List.foldl_cons]
    exact (List.prefix_append w _).trans (ih (F w g))

lemma foldl_F_length (L : List Gate) : ∀ w : List Bool,
    (L.foldl F w).length = w.length + L.length := by
  induction L with
  | nil => intro w; simp
  | cons g L ih => intro w; simp [ih, F]; omega

end PEqualNP.Outside.L_meta_2738

theorem PEqualNP.Outside.L_meta_2738 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     x2 < x3 →       x3 < (10 : ℕ) + x1.length →         ∃ (x7 : List PEqualNP.CircuitLowerBounds.Gate) (x8 : ℕ) (x9 : ℕ),           x7.length ≤ x1.length ∧             x8 < (12 : ℕ) + x7.length ∧               x9 < (12 : ℕ) + x7.length ∧                 PEqualNP.MetaComplexity.FanInTwo { gates := x7, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧                   (∀ (x10 : Fin x7.length),                       have x11 : PEqualNP.CircuitLowerBounds.Gate := x7.get x10;                       (∀ x12 ∈ x11.inputs, x12 < (12 : ℕ) + ↑x10) ∧ x11.inputs.Nodup ∧ (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x11.inputs.length = (1 : ℕ) ∨ x11.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x11.inputs.length = (2 : ℕ))) ∧                     ∀ (x10 : List Bool), x10.length = (10 : ℕ) → ({ gates := x7, output := x8 : PEqualNP.CircuitLowerBounds.Circuit }.eval (x10 ++ [Bool.false, Bool.true]) || { gates := x7, output := x9 : PEqualNP.CircuitLowerBounds.Circuit }.eval (x10 ++ [Bool.false, Bool.true])) = ({ gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval x10 || { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval x10) := by
  intro x1 x2 x3 hfan h23 h3
  have hAON : ∀ g ∈ x1, L_meta_2738.AON g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h1
  have hlen := L_meta_2738.normList_length x1 0
  refine ⟨L_meta_2738.normList 0 x1, L_meta_2738.mu x1.length x2, L_meta_2738.mu x1.length x3,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen]
  · rw [hlen]; exact L_meta_2738.mu_lt _ _
  · rw [hlen]; exact L_meta_2738.mu_lt _ _
  · intro e he
    obtain ⟨h1, h2⟩ := L_meta_2738.normList_aon x1 0 hAON e he
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · intro i
    have := L_meta_2738.normList_clean x1 0 hAON i.1 i.2
    rw [Nat.zero_add] at this
    exact this
  · intro x10 hx10
    show (((L_meta_2738.normList 0 x1).foldl L_meta_2738.F (x10 ++ [false, true])).getD
        (L_meta_2738.mu x1.length x2) false ||
      ((L_meta_2738.normList 0 x1).foldl L_meta_2738.F (x10 ++ [false, true])).getD
        (L_meta_2738.mu x1.length x3) false) =
      ((x1.foldl L_meta_2738.F x10).getD x2 false || (x1.foldl L_meta_2738.F x10).getD x3 false)
    have hr := L_meta_2738.run x1 0 x10 [] hx10 rfl hAON
    simp only [List.append_nil] at hr
    rw [hr]
    have hpre : x10 ++ (x1.foldl L_meta_2738.F x10).drop 10 = x1.foldl L_meta_2738.F x10 := by
      have := List.prefix_iff_eq_append.1 (L_meta_2738.foldl_prefix x1 x10)
      rw [hx10] at this
      exact this
    have hVlen : ((x1.foldl L_meta_2738.F x10).drop 10).length = x1.length := by
      rw [List.length_drop, L_meta_2738.foldl_F_length, hx10]; omega
    rw [L_meta_2738.getD_N x10 _ x1.length hx10 hVlen x2,
      L_meta_2738.getD_N x10 _ x1.length hx10 hVlen x3, hpre]

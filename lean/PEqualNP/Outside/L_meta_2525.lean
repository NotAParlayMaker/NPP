import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2525_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    set b := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hlen⟩ := ih (w ++ [b])
    refine ⟨b :: t, ?_, by simp [hlen]⟩
    change wiresFrom gs (w ++ [b]) = w ++ b :: t
    rw [ht, List.append_assoc]
    rfl

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wiresFrom_agree_except (k : ℕ) (gs : List Gate)
    (hno : ∀ g ∈ gs, k ∉ g.inputs) :
    ∀ w1 w2 : List Bool, w1.length = w2.length →
    (∀ i, i ≠ k → w1.getD i false = w2.getD i false) →
    ∀ i, i ≠ k → (wiresFrom gs w1).getD i false = (wiresFrom gs w2).getD i false := by
  induction gs with
  | nil =>
    intro w1 w2 _ hag i hi
    exact hag i hi
  | cons g gs ih =>
    intro w1 w2 hlen hag i hi
    have hgk : k ∉ g.inputs := hno g (by simp)
    have hmap : g.inputs.map (fun j => w1.getD j false) = g.inputs.map (fun j => w2.getD j false) := by
      apply List.map_congr_left
      intro j hj
      exact hag j (fun h => hgk (h ▸ hj))
    set b1 := g.op.eval (g.inputs.map fun j => w1.getD j false)
    set b2 := g.op.eval (g.inputs.map fun j => w2.getD j false)
    have hb : b1 = b2 := congrArg g.op.eval hmap
    change (wiresFrom gs (w1 ++ [b1])).getD i false = (wiresFrom gs (w2 ++ [b2])).getD i false
    apply ih (fun g' hg' => hno g' (by simp [hg'])) (w1 ++ [b1]) (w2 ++ [b2]) (by simp [hlen])
    · intro j hj
      by_cases hlt : j < w1.length
      · have hlt2 : j < w2.length := hlen ▸ hlt
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
          List.getElem?_append_left hlt2]
        simpa [List.getD_eq_getElem?_getD] using hag j hj
      · by_cases heq : j = w1.length
        · subst heq
          have h1 : (w1 ++ [b1]).getD w1.length false = b1 := by simp [List.getD_eq_getElem?_getD]
          have h2 : (w2 ++ [b2]).getD w1.length false = b2 := by
            rw [hlen]; simp [List.getD_eq_getElem?_getD]
          rw [h1, h2, hb]
        · have hge1 : (w1 ++ [b1]).length ≤ j := by simp; omega
          have hge2 : (w2 ++ [b2]).length ≤ j := by simp; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
    · exact hi

def p9 : (Fin 9 → Bool) → Bool :=
  fun x => [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
    ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
    ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
    ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
    fun e => x e.1 && x e.2

def x_0 : Fin 9 → Bool := fun i => decide (i = 0)
def x_4 : Fin 9 → Bool := fun i => decide (i = 4)
def x_04 : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4)

lemma p9_x0 : p9 x_0 = false := by decide
lemma p9_x4 : p9 x_4 = false := by decide
lemma p9_x04 : p9 x_04 = true := by decide

lemma main_proof (C : Circuit)
    (hw9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4))
    (hfun : circuitFun 9 C = p9) :
    (∃ g ∈ C.gates.drop 1, 0 ∈ g.inputs) ∧ (∃ g ∈ C.gates.drop 1, 4 ∈ g.inputs) := by
  have hnonempty : C.gates ≠ [] := by
    intro hemp
    have h := hw9 x_0
    simp [Circuit.wires, hemp, List.getD_eq_getElem?_getD, x_0] at h
  rcases hgs : C.gates with _ | ⟨g0, rest⟩
  · exact absurd hgs hnonempty
  have hdrop : C.gates.drop 1 = rest := by rw [hgs]; rfl
  have hstep1 : ∀ x : Fin 9 → Bool,
      let w1 := List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]
      C.wires (List.ofFn x) = wiresFrom rest w1 ∧ w1.getD 9 false = (x 0 || x 4) := by
    intro x
    dsimp only
    set b := g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)
    have hcw : C.wires (List.ofFn x) = wiresFrom rest (List.ofFn x ++ [b]) := by
      unfold Circuit.wires
      rw [hgs]
      rfl
    refine ⟨hcw, ?_⟩
    have h9 := hw9 x
    rw [hcw] at h9
    have hlt : 9 < (List.ofFn x ++ [b]).length := by simp
    rw [wiresFrom_getD_lt rest (List.ofFn x ++ [b]) hlt] at h9
    exact h9
  have hOut0 : C.output ≠ 0 := by
    intro h0
    have hev := congrFun hfun x_0
    simp only [circuitFun, Circuit.eval, h0] at hev
    rw [(hstep1 x_0).1] at hev
    have hlt : 0 < (List.ofFn x_0 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x_0).getD i false)]).length := by simp
    rw [wiresFrom_getD_lt rest _ hlt] at hev
    have hget : (List.ofFn x_0 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x_0).getD i false)]).getD 0 false = true := by
      simp [List.getD_eq_getElem?_getD, x_0]
    rw [hget, p9_x0] at hev
    cases hev
  have hOut4 : C.output ≠ 4 := by
    intro h4
    have hev := congrFun hfun x_4
    simp only [circuitFun, Circuit.eval, h4] at hev
    rw [(hstep1 x_4).1] at hev
    have hlt : 4 < (List.ofFn x_4 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x_4).getD i false)]).length := by simp
    rw [wiresFrom_getD_lt rest _ hlt] at hev
    have hget : (List.ofFn x_4 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x_4).getD i false)]).getD 4 false = true := by
      simp [List.getD_eq_getElem?_getD, x_4]
    rw [hget, p9_x4] at hev
    cases hev
  dsimp only [List.drop]
  constructor
  · by_contra hno
    push Not at hno
    set w1 := List.ofFn x_4 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x_4).getD i false)]
    set w2 := List.ofFn x_04 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x_04).getD i false)]
    have hag : ∀ i, i ≠ 0 → w1.getD i false = w2.getD i false := by
      intro i hi
      by_cases hlt : i < 9
      · simp only [w1, w2, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simp [hlt] : i < (List.ofFn x_4).length),
          List.getElem?_append_left (by simp [hlt] : i < (List.ofFn x_04).length),
          List.getElem?_ofFn, hlt, dite_true, Option.getD_some, x_4, x_04]
        have hne : (⟨i, hlt⟩ : Fin 9) ≠ 0 := fun h => hi (congrArg Fin.val h)
        simp only [hne, false_or]
      · by_cases h9 : i = 9
        · subst h9
          rw [(hstep1 x_4).2, (hstep1 x_04).2]
          decide
        · have hge1 : w1.length ≤ i := by simp [w1]; omega
          have hge2 : w2.length ≤ i := by simp [w2]; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
    have heq := wiresFrom_agree_except 0 rest hno w1 w2 (by simp [w1, w2]) hag C.output hOut0
    have h1 : C.eval (List.ofFn x_4) = (wiresFrom rest w1).getD C.output false := by
      simp only [Circuit.eval, (hstep1 x_4).1]; rfl
    have h2 : C.eval (List.ofFn x_04) = (wiresFrom rest w2).getD C.output false := by
      simp only [Circuit.eval, (hstep1 x_04).1]; rfl
    have hf1 := congrFun hfun x_4
    have hf2 := congrFun hfun x_04
    simp only [circuitFun] at hf1 hf2
    rw [h1, p9_x4] at hf1
    rw [h2, p9_x04] at hf2
    rw [hf1, hf2] at heq
    cases heq
  · by_contra hno
    push Not at hno
    set w1 := List.ofFn x_0 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x_0).getD i false)]
    set w2 := List.ofFn x_04 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x_04).getD i false)]
    have hag : ∀ i, i ≠ 4 → w1.getD i false = w2.getD i false := by
      intro i hi
      by_cases hlt : i < 9
      · simp only [w1, w2, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simp [hlt] : i < (List.ofFn x_0).length),
          List.getElem?_append_left (by simp [hlt] : i < (List.ofFn x_04).length),
          List.getElem?_ofFn, hlt, dite_true, Option.getD_some, x_0, x_04]
        have hne : (⟨i, hlt⟩ : Fin 9) ≠ 4 := fun h => hi (congrArg Fin.val h)
        simp only [hne, or_false]
      · by_cases h9 : i = 9
        · subst h9
          rw [(hstep1 x_0).2, (hstep1 x_04).2]
          decide
        · have hge1 : w1.length ≤ i := by simp [w1]; omega
          have hge2 : w2.length ≤ i := by simp [w2]; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
    have heq := wiresFrom_agree_except 4 rest hno w1 w2 (by simp [w1, w2]) hag C.output hOut4
    have h1 : C.eval (List.ofFn x_0) = (wiresFrom rest w1).getD C.output false := by
      simp only [Circuit.eval, (hstep1 x_0).1]; rfl
    have h2 : C.eval (List.ofFn x_04) = (wiresFrom rest w2).getD C.output false := by
      simp only [Circuit.eval, (hstep1 x_04).1]; rfl
    have hf1 := congrFun hfun x_0
    have hf2 := congrFun hfun x_04
    simp only [circuitFun] at hf1 hf2
    rw [h1, p9_x0] at hf1
    rw [h2, p9_x04] at hf2
    rw [hf1, hf2] at heq
    cases heq

end PEqualNP.Outside.L_meta_2525_aux

theorem PEqualNP.Outside.L_meta_2525 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → (∃ x5 ∈ List.drop (1 : ℕ) x2.gates, (0 : ℕ) ∈ x5.inputs) ∧ ∃ x5 ∈ List.drop (1 : ℕ) x2.gates, (4 : ℕ) ∈ x5.inputs := by
  dsimp only
  exact PEqualNP.Outside.L_meta_2525_aux.main_proof

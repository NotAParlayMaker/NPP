import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4063

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def runW (f : List Bool → Gate → Bool) (G : List Gate) (w : List Bool) : List Bool :=
  G.foldl (fun w g => w ++ [f w g]) w

lemma runW_cons (f : List Bool → Gate → Bool) (g : Gate) (G : List Gate) (w : List Bool) :
    runW f (g :: G) w = runW f G (w ++ [f w g]) := rfl

def fV (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = runW fV C.gates x := rfl

lemma getD_snoc_true (w : List Bool) (a : Bool) (i : ℕ) (h : (w ++ [a]).getD i false = true) :
    (i < w.length ∧ w.getD i false = true) ∨ (i = w.length ∧ a = true) := by
  by_cases hi : i < w.length
  · left; exact ⟨hi, by rwa [List.getD_append _ _ _ _ hi] at h⟩
  · right
    rw [List.getD_append_right _ _ _ _ (by omega)] at h
    rcases Nat.lt_or_ge (i - w.length) 1 with h1 | h1
    · have : i - w.length = 0 := by omega
      rw [this] at h
      exact ⟨by omega, by simpa using h⟩
    · rw [List.getD_eq_default _ _ (by simpa using h1)] at h
      cases h

lemma step_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) : fV w g = true → fV w' g = true := by
  unfold fV
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact h i (H _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨i, hi, rfl⟩, hv⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hv⟩

lemma run_mono (G : List Gate) (hG : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      ∀ i, (runW fV G w).getD i false = true → (runW fV G w').getD i false = true := by
  induction G with
  | nil => intro w w' _ h; exact h
  | cons g G ih =>
    intro w w' hl h
    rw [runW_cons, runW_cons]
    apply ih (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hl])
    intro i hi
    rcases getD_snoc_true w _ i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [List.getD_append _ _ _ _ (by omega)]; exact h i h2
    · subst h1
      rw [hl]
      simp only [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      simpa using step_mono g (hG g List.mem_cons_self) w w' h h2


def EL : List (Fin 11 × Fin 11) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
def NL : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]

def P (x : Fin 11 → Bool) : Bool :=
  EL.any (fun e => x e.1 && x e.2) || NL.any (fun r => (List.finRange 11).all fun i => !x i || r.testBit i.val)

set_option maxRecDepth 100000 in
lemma allP : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool, P ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] = true := by decide +kernel

lemma P_all (x : Fin 11 → Bool) : P x = true := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10] := by
    funext i; fin_cases i <;> rfl
  rw [hx]; exact allP _ _ _ _ _ _ _ _ _ _ _

end PEqualNP.Outside.L_meta_4063

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership in
theorem PEqualNP.Outside.L_meta_4063 : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ), PEqualNP.EdgeOwnership.AndOrOnly x3 → (∀ x6 ∈ x2, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x4 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false) → PEqualNP.TopForm.BelowF x1 x3 x4 := by
  intro G N C j hAO hq x hx
  cases hf : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
  swap; · rfl
  exfalso
  have hP := PEqualNP.Outside.L_meta_4063.P_all x
  unfold PEqualNP.Outside.L_meta_4063.P at hP
  rcases Bool.or_eq_true_iff.mp hP with hE | hN
  · obtain ⟨e, he, hv⟩ := List.any_eq_true.mp hE
    obtain ⟨hu, hv⟩ := Bool.and_eq_true_iff.mp hv
    have hadj : G.Adj e.1 e.2 := by
      revert he; simp only [PEqualNP.Outside.L_meta_4063.EL]
      intro he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
    have : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true := by
      unfold PEqualNP.MetaComplexity.NestedCover.graphFun
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨e.1, e.2, hadj, hu, hv⟩
    rw [hf] at this; cases this
  · obtain ⟨r, hr, hall⟩ := List.any_eq_true.mp hN
    have hsub : ∀ i : Fin 11, x i = true → r.testBit i.val = true := by
      intro i hi
      have := List.all_eq_true.mp hall i (List.mem_finRange i)
      simpa [hi] using this
    have hG : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hAO
    have base : ∀ i, (List.ofFn x).getD i false = true →
        (List.ofFn (fun i : Fin 11 => r.testBit i.val)).getD i false = true := by
      intro i hi
      by_cases hlt : i < 11
      · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hi ⊢
        simp only [List.getElem_ofFn] at hi ⊢
        exact hsub ⟨i, hlt⟩ hi
      · rw [List.getD_eq_default _ _ (by simpa using hlt)] at hi
        cases hi
    have hm := PEqualNP.Outside.L_meta_4063.run_mono C.gates hG _ _ (by simp) base (11 + j)
    rw [← PEqualNP.Outside.L_meta_4063.wires_eq, ← PEqualNP.Outside.L_meta_4063.wires_eq] at hm
    have h1 := hm hx
    have h2 := hq r hr
    unfold gateVal at h2
    rw [h1] at h2; cases h2

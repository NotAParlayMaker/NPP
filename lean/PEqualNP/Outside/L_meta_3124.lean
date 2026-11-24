import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3124

open PEqualNP.CircuitLowerBounds

def firstInputs (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [!x 0]

def input (pins : List ℕ) (x : Fin 9 → Bool) : List Bool :=
  firstInputs x ++ [GateOp.or.eval (pins.map fun w => (firstInputs x).getD w false)]

def Stable (i : Fin 9) (x y : Fin 9 → Bool) : Prop :=
  ∀ j, j ≠ i → x j = y j

lemma append_agree {a b z : List Bool} {w : ℕ}
    (hlen : a.length = b.length) (hw : a.getD w false = b.getD w false) :
    (a ++ z).getD w false = (b ++ z).getD w false := by
  by_cases h : w < a.length
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hlen ▸ h)]
    exact hw
  · have ha : a.length ≤ w := by omega
    have hb : b.length ≤ w := by omega
    rw [List.getD_append_right _ _ _ _ ha, List.getD_append_right _ _ _ _ hb, hlen]

lemma prefix_agree {i : Fin 9} {x y : Fin 9 → Bool}
    (h : Stable i x y) (hi : i.val ≠ 0) {w : ℕ} (hw : w ≠ i.val) :
    (firstInputs x).getD w false = (firstInputs y).getD w false := by
  have h0 : (0 : Fin 9) ≠ i := by
    intro he
    exact hi (congrArg Fin.val he).symm
  unfold firstInputs
  rw [h 0 h0]
  apply append_agree (by simp)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rename_i hbound
    have hne : (⟨w,hbound⟩ : Fin 9) ≠ i := fun he => hw (congrArg Fin.val he)
    rw [h _ hne]
  · rfl

lemma input_agree {i : Fin 9} {x y : Fin 9 → Bool} {pins : List ℕ}
    (h : Stable i x y) (hi : i.val ≠ 0) (hp : i.val ∉ pins)
    {w : ℕ} (hw : w ≠ i.val) :
    (input pins x).getD w false = (input pins y).getD w false := by
  have he : (pins.map fun j => (firstInputs x).getD j false) =
      (pins.map fun j => (firstInputs y).getD j false) := by
    apply List.map_congr_left
    intro j hj
    exact prefix_agree h hi (fun eq => hp (eq ▸ hj))
  unfold input
  rw [he]
  exact append_agree (by simp [firstInputs]) (prefix_agree h hi hw)

lemma eval_agree (pins : List ℕ) (C : Circuit) {i : Fin 9} {x y : Fin 9 → Bool}
    (h : Stable i x y) (hi : i.val ≠ 0) (hp : i.val ∉ pins)
    (ho : C.output ≠ i.val)
    (hg : ∀ g ∈ C.gates, i.val ∉ g.inputs)
    (hs : ¬ ∃ g, C.gates[1]? = some g) :
    C.eval (input pins x) = C.eval (input pins y) := by
  unfold Circuit.eval Circuit.wires
  cases e : C.gates with
  | nil =>
    simpa only [List.foldl_nil] using input_agree h hi hp ho
  | cons g gs =>
    cases gs with
    | nil =>
      have hm : (g.inputs.map fun j => (input pins x).getD j false) =
          (g.inputs.map fun j => (input pins y).getD j false) := by
        apply List.map_congr_left
        intro j hj
        apply input_agree h hi hp
        intro he
        exact hg g (by simp [e]) (he ▸ hj)
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hm]
      exact append_agree (by simp [input,firstInputs]) (input_agree h hi hp ho)
    | cons g' rest =>
      exact (hs ⟨g', by simp [e]⟩).elim

lemma unused (pins : List ℕ) (C : Circuit) (hp : pins.length ≤ 2)
    (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hs : ¬ ∃ g, C.gates[1]? = some g) :
    ∃ i : Fin 9, i.val ≠ 0 ∧ i.val ∉ pins ∧ C.output ≠ i.val ∧
      ∀ g ∈ C.gates, i.val ∉ g.inputs := by
  let used := pins ++ C.gates.flatMap Gate.inputs ++ [C.output, 0]
  have hg : (C.gates.flatMap Gate.inputs).length ≤ 2 := by
    cases e : C.gates with
    | nil => simp
    | cons g gs =>
      cases gs with
      | nil => simpa using (hf g (by simp [e])).2
      | cons a as => exact (hs ⟨a, by simp [e]⟩).elim
  have hl : used.length ≤ 6 := by
    simp only [used, List.length_append, List.length_cons, List.length_nil]
    omega
  have he : ∃ i : Fin 9, i.val ∉ used := by
    by_contra! hn
    let all := (Finset.univ : Finset (Fin 9)).image Fin.val
    have hsub : all ⊆ used.toFinset := by
      intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact List.mem_toFinset.mpr (hn i)
    have hc : all.card = 9 := by
      dsimp only [all]
      rw [Finset.card_image_of_injective _ Fin.val_injective]
      simp
    have hle := (Finset.card_le_card hsub).trans (List.toFinset_card_le used)
    omega
  obtain ⟨i, hn⟩ := he
  refine ⟨i, ?_, ?_, ?_, ?_⟩
  · intro hi
    exact hn (by simp [used, hi])
  · intro hi
    exact hn (by simp [used, hi])
  · intro hi
    exact hn (by simp [used, hi])
  · intro g hgc hi
    exact hn (by simp [used, List.mem_flatMap, hgc, hi, Exists.intro g])

def edge (x : Fin 9 → Bool) : Bool :=
  (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))

def one (j : Fin 9) (k : Fin 9) : Bool := decide (k = j)
def two (i j : Fin 9) (k : Fin 9) : Bool := decide (k = i ∨ k = j)

lemma one_false (j : Fin 9) : edge (one j) = false := by
  fin_cases j <;> decide

lemma some_two_true (i : Fin 9) : ∃ j : Fin 9, edge (two i j) = true := by
  fin_cases i <;> decide

end PEqualNP.Outside.L_meta_3124

theorem PEqualNP.Outside.L_meta_3124 : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (¬∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro pins hp C hf _ hs
  obtain ⟨i, hi, hpin, ho, hg⟩ := PEqualNP.Outside.L_meta_3124.unused pins C hp hf hs
  obtain ⟨j, ht⟩ := PEqualNP.Outside.L_meta_3124.some_two_true i
  let x := PEqualNP.Outside.L_meta_3124.one j
  let y := PEqualNP.Outside.L_meta_3124.two i j
  have hxy : PEqualNP.Outside.L_meta_3124.Stable i x y := by
    intro k hk
    simp [x, y, PEqualNP.Outside.L_meta_3124.one, PEqualNP.Outside.L_meta_3124.two, hk]
  have he := PEqualNP.Outside.L_meta_3124.eval_agree pins C hxy hi hpin ho hg hs
  by_contra! h
  change ∀ z, ¬ (C.eval (PEqualNP.Outside.L_meta_3124.input pins z) ≠
    PEqualNP.Outside.L_meta_3124.edge z) at h
  push Not at h
  rw [h x, h y] at he
  change PEqualNP.Outside.L_meta_3124.edge (PEqualNP.Outside.L_meta_3124.one j) =
    PEqualNP.Outside.L_meta_3124.edge (PEqualNP.Outside.L_meta_3124.two i j) at he
  rw [PEqualNP.Outside.L_meta_3124.one_false j, ht] at he
  contradiction

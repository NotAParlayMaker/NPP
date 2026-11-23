import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1334

def step (acc : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

lemma getD_append_singleton (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false = if i < l.length then l.getD i false else if i = l.length then v else false := by
  by_cases h1 : i < l.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, h1]
  · by_cases h2 : i = l.length
    · subst h2
      simp [List.getD_eq_getElem?_getD]
    · have hgt : l.length + 1 ≤ i := by omega
      have hlen : (l ++ [v]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, h1, h2]

lemma step_agree (acc₁ acc₂ : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) (t : ℕ)
    (hlen : acc₁.length = acc₂.length)
    (hagree : ∀ i, i ≠ t → acc₁.getD i false = acc₂.getD i false)
    (hno : t ∉ g.inputs) :
    (step acc₁ g).length = (step acc₂ g).length ∧
    ∀ i, i ≠ t → (step acc₁ g).getD i false = (step acc₂ g).getD i false := by
  have hmap : (g.inputs.map fun i => acc₁.getD i false) =
      (g.inputs.map fun i => acc₂.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact hagree i (fun heq => hno (heq ▸ hi))
  refine ⟨by simp [step, hlen], ?_⟩
  intro i hi
  simp only [step, getD_append_singleton, hlen, hmap]
  split_ifs with h1 h2
  · exact hagree i hi
  · rfl
  · rfl

lemma foldl_agree (gs : List PEqualNP.CircuitLowerBounds.Gate) (t : ℕ)
    (acc₁ acc₂ : List Bool)
    (hlen : acc₁.length = acc₂.length)
    (hagree : ∀ i, i ≠ t → acc₁.getD i false = acc₂.getD i false)
    (hno : ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), gs[k]? = some g → t ∉ g.inputs) :
    (gs.foldl step acc₁).length = (gs.foldl step acc₂).length ∧
    ∀ i, i ≠ t → (gs.foldl step acc₁).getD i false = (gs.foldl step acc₂).getD i false := by
  induction gs generalizing acc₁ acc₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g rest ih =>
    have hg : t ∉ g.inputs := hno 0 g rfl
    obtain ⟨hlen', hagree'⟩ := step_agree acc₁ acc₂ g t hlen hagree hg
    exact ih (step acc₁ g) (step acc₂ g) hlen' hagree' (fun k h hk => hno (k + 1) h hk)

lemma foldl_set_agree (gs : List PEqualNP.CircuitLowerBounds.Gate) (q t : ℕ)
    (g' : PEqualNP.CircuitLowerBounds.Gate) (acc₁ acc₂ : List Bool)
    (hlen : acc₁.length = acc₂.length)
    (ht : t = acc₁.length + q)
    (hagree : ∀ i, i ≠ t → acc₁.getD i false = acc₂.getD i false)
    (hno : ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), gs[k]? = some g → t ∉ g.inputs) :
    ((gs.set q g').foldl step acc₁).length = (gs.foldl step acc₂).length ∧
    ∀ i, i ≠ t → ((gs.set q g').foldl step acc₁).getD i false = (gs.foldl step acc₂).getD i false := by
  induction gs generalizing q acc₁ acc₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g rest ih =>
    cases q with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      have hlen' : (step acc₁ g').length = (step acc₂ g).length := by simp [step, hlen]
      have hagree' : ∀ i, i ≠ t → (step acc₁ g').getD i false = (step acc₂ g).getD i false := by
        intro i hi
        simp only [step, getD_append_singleton, hlen]
        have hne : i ≠ acc₂.length := by omega
        split_ifs with h1
        · exact hagree i hi
        · rfl
      exact foldl_agree rest t (step acc₁ g') (step acc₂ g) hlen' hagree'
        (fun k h hk => hno (k + 1) h hk)
    | succ q' =>
      simp only [List.set_cons_succ, List.foldl_cons]
      have hg : t ∉ g.inputs := hno 0 g rfl
      obtain ⟨hlen', hagree'⟩ := step_agree acc₁ acc₂ g t hlen hagree hg
      have ht' : t = (step acc₁ g).length + q' := by simp [step]; omega
      exact ih q' (step acc₁ g) (step acc₂ g) hlen' ht' hagree'
        (fun k h hk => hno (k + 1) h hk)

end PEqualNP.Outside.L_meta_1334

theorem PEqualNP.Outside.L_meta_1334 : ∀ (n q w : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (g' : PEqualNP.CircuitLowerBounds.Gate), (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), gates[k]? = some g → n + q ∉ g.inputs) → w ≠ n + q → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set q g', w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x) := by
  intro n q w gates g' hno hw x
  have hres := PEqualNP.Outside.L_meta_1334.foldl_set_agree gates q (n + q) g'
    (List.ofFn x) (List.ofFn x) rfl (by simp) (fun _ _ => rfl) hno
  exact hres.2 w hw

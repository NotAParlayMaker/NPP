import PEqualNP.Defs

namespace PEqualNP.MetaComplexity.DeadWire1334

open PEqualNP.CircuitLowerBounds

private def value (xs : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => xs.getD i false)

private def step (xs : List Bool) (g : Gate) := xs ++ [value xs g]

-- A suffix which never reads d propagates agreement everywhere else.
private theorem suffix (gs : List Gate) (d : ℕ) (a b : List Bool)
    (unused : ∀ g ∈ gs, d ∉ g.inputs)
    (lengths : a.length = b.length)
    (agree : ∀ i, i ≠ d → a[i]? = b[i]?) :
    ∀ i, i ≠ d → (gs.foldl step a)[i]? = (gs.foldl step b)[i]? := by
  induction gs generalizing a b with
  | nil => exact agree
  | cons g gs ih =>
    have same : value a g = value b g := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i hi
      have ne : i ≠ d := fun h => unused g (by simp) (h ▸ hi)
      simp only [List.getD_eq_getElem?_getD, agree i ne]
    apply ih (step a g) (step b g) (fun k hk => unused k (by simp [hk]))
    · simp [step, lengths]
    · intro i hi
      simp only [step, List.getElem?_append, lengths, same, agree i hi]

private theorem replaceGate (gs : List Gate) (xs : List Bool) (q : ℕ) (replacement : Gate)
    (unused : ∀ g ∈ gs, xs.length + q ∉ g.inputs) :
    ∀ w, w ≠ xs.length + q →
      ((gs.set q replacement).foldl step xs)[w]? = (gs.foldl step xs)[w]? := by
  induction gs generalizing xs q with
  | nil => simp
  | cons g gs ih =>
    cases q with
    | zero =>
      simp only [Nat.add_zero] at unused ⊢
      apply suffix gs xs.length (step xs replacement) (step xs g)
        (fun k hk => unused k (by simp [hk])) (by simp [step])
      intro i hi
      by_cases lt : i < xs.length
      · simp [step, List.getElem?_append_left lt]
      · have pos : 0 < i - xs.length := by omega
        simp [step, List.getElem?_append_right (Nat.le_of_not_gt lt),
          List.getElem?_eq_none (by exact pos : [value xs replacement].length ≤ i - xs.length),
          List.getElem?_eq_none (by exact pos : [value xs g].length ≤ i - xs.length)]
    | succ q =>
      have size : (step xs g).length + q = xs.length + (q + 1) := by
        simp [step]
        omega
      exact fun w hw => ih (step xs g) q
        (fun k hk => size ▸ unused k (by simp [hk])) w (size ▸ hw)

end PEqualNP.MetaComplexity.DeadWire1334

theorem PEqualNP.Outside.L_meta_1334 :
    ∀ (n q w : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (g' : PEqualNP.CircuitLowerBounds.Gate), (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), gates[k]? = some g → n + q ∉ g.inputs) → w ≠ n + q → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set q g', w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x) := by
  intro n q w gates replacement unused hw x
  have e := PEqualNP.MetaComplexity.DeadWire1334.replaceGate gates (List.ofFn x) q replacement
    (by
      intro g hg
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
      simpa using unused k g hk) w (by simpa using hw)
  exact congrArg (fun v : Option Bool => v.getD false) e

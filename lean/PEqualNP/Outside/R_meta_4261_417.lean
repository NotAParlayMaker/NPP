import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4261_417
    (h1 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)) 11)
    (h2 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         (¬∀ x5 ∈ x1, x5 = (0 : ℕ) ∨ x5 = (9 : ℕ)) ∧ (9 : ℕ) ∈ x1 →           (1 : ℕ) ∈ x1 ∨ (4 : ℕ) ∈ x1 ∨ (5 : ℕ) ∈ x1 →             ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),               PEqualNP.MetaComplexity.FanInTwo x7 →                 x7.size ≤ (13 : ℕ) →                   ∃ (x10 : Fin (9 : ℕ) → Bool),                     have x11 : List Bool := List.ofFn x10 ++ [!x10 (0 : Fin (9 : ℕ))];                     x7.eval (x11 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x12 : ℕ) => x11.getD x12 Bool.false) x1)]) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  classical
  -- wire bookkeeping
  have snoc_ne : ∀ (L : List Bool) (t : Bool) (j : ℕ), j ≠ L.length →
      (L ++ [t]).getD j false = L.getD j false := by
    intro L t j h
    by_cases hj : j < L.length
    · exact List.getD_append _ _ _ _ hj
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have snoc_eq : ∀ (L : List Bool) (t : Bool) (k : ℕ), L.length = k →
      (L ++ [t]).getD k false = t := by
    intro L t k h
    subst h; simp
  obtain ⟨val, hval⟩ : ∃ val : PEqualNP.CircuitLowerBounds.Gate → List Bool → Bool,
      val = fun g w => g.op.eval (g.inputs.map fun i => w.getD i false) := ⟨_, rfl⟩
  obtain ⟨wf, hwf⟩ : ∃ wf : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool,
      wf = fun gs w => gs.foldl (fun w g => w ++ [val g w]) w := ⟨_, rfl⟩
  have wf_cons : ∀ g gs w, wf (g :: gs) w = wf gs (w ++ [val g w]) := by
    intro g gs w; rw [hwf]; rfl
  have wf_nil : ∀ w, wf [] w = w := by intro w; rw [hwf]; rfl
  obtain ⟨ok, hok⟩ : ∃ ok : PEqualNP.CircuitLowerBounds.Gate → Prop, ok = fun g =>
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2 := ⟨_, rfl⟩
  have okand : ∀ l : List ℕ, l.length ≤ 2 → ok ⟨PEqualNP.CircuitLowerBounds.GateOp.and, l⟩ := by
    intro l h; rw [hok]; exact ⟨by simp, h⟩
  have okor : ∀ l : List ℕ, l.length ≤ 2 → ok ⟨PEqualNP.CircuitLowerBounds.GateOp.or, l⟩ := by
    intro l h; rw [hok]; exact ⟨by simp, h⟩
  have oknot : ∀ l : List ℕ, l.length ≤ 2 → ok ⟨PEqualNP.CircuitLowerBounds.GateOp.not, l⟩ := by
    intro l h; rw [hok]; exact ⟨by simp, h⟩
  have shape : ∀ g, ok g → (∃ l : List ℕ, l.length ≤ 2 ∧
      (g = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, l⟩ ∨ g = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, l⟩ ∨
        g = ⟨PEqualNP.CircuitLowerBounds.GateOp.not, l⟩)) := by
    intro g h
    rw [hok] at h
    obtain ⟨op, l⟩ := g
    refine ⟨l, h.2, ?_⟩
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with rfl | rfl | rfl <;> simp
  -- rd g i: the value of gate g uses wire i
  obtain ⟨rd, hrd⟩ : ∃ rd : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop, rd = fun g i =>
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.head? = some i) ∧ i ∈ g.inputs := ⟨_, rfl⟩
  have val_congr : ∀ g, ok g → ∀ (w w' : List Bool) (σ : ℕ → ℕ),
      (∀ i, rd g i → w.getD i false = w'.getD (σ i) false) →
      val g w = val ⟨g.op, g.inputs.map σ⟩ w' := by
    intro g hg w w' σ h
    obtain ⟨l, hl, rfl | rfl | rfl⟩ := shape g hg
    · rw [hval]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (by rw [hrd]; exact ⟨fun e => by simp at e, hi⟩)
    · rw [hval]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (by rw [hrd]; exact ⟨fun e => by simp at e, hi⟩)
    · cases l with
      | nil => rw [hval]; rfl
      | cons a l =>
        have := h a (by rw [hrd]; simp)
        rw [hval]
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.headD_cons, this]
  -- Elimination: wires 0, 9, 10 constant, every gate that uses one of them is saved.
  have elim : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, ok g) →
      ∀ (old new : (Fin 8 → Bool) → List Bool) (n m : ℕ),
      (∀ y, (old y).length = n) → (∀ y, (new y).length = m) → 11 ≤ n →
      (∀ i, i = 0 ∨ i = 9 ∨ i = 10 → ∃ b, ∀ y, (old y).getD i false = b) →
      (∀ i, (∃ b, ∀ y, (old y).getD i false = b) ∨
        ∃ j, j < m ∧ ∀ y, (old y).getD i false = (new y).getD j false) →
      ∃ gs' : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs', ok g) ∧
        gs'.length + gs.countP (fun g => decide (rd g 0 ∨ rd g 9 ∨ rd g 10)) ≤ gs.length ∧
        ∀ i, (∃ b, ∀ y, (wf gs (old y)).getD i false = b) ∨
          ∃ j, ∀ y, (wf gs (old y)).getD i false = (wf gs' (new y)).getD j false := by
    intro gs
    induction gs with
    | nil =>
      intro _ old new n m _ _ _ _ hrep
      refine ⟨[], by simp, by simp, ?_⟩
      intro i
      rcases hrep i with h | ⟨j, _, h⟩
      · exact Or.inl (by simpa only [wf_nil] using h)
      · exact Or.inr ⟨j, by simpa only [wf_nil] using h⟩
    | cons g gs ih =>
      intro hgs old new n m hn hm h11 hS hrep
      have hg : ok g := hgs g List.mem_cons_self
      have hgs' : ∀ g ∈ gs, ok g := fun g' h => hgs g' (List.mem_cons_of_mem _ h)
      -- one step
      have step : (∃ b, ∀ y, val g (old y) = b) ∨
          (∃ j, j < m ∧ ∀ y, val g (old y) = (new y).getD j false) ∨
          ((¬ (rd g 0 ∨ rd g 9 ∨ rd g 10)) ∧ ∃ g', ok g' ∧ ∀ y, val g (old y) = val g' (new y)) := by
        have nr : (∀ i, rd g i → ¬ ∃ b, ∀ y, (old y).getD i false = b) → ¬ (rd g 0 ∨ rd g 9 ∨ rd g 10) := by
          intro h
          rintro (h' | h' | h')
          · exact h _ h' (hS 0 (by simp))
          · exact h _ h' (hS 9 (by simp))
          · exact h _ h' (hS 10 (by simp))
        have wire : ∀ i, (¬ ∃ b, ∀ y, (old y).getD i false = b) →
            ∃ j, j < m ∧ ∀ y, (old y).getD i false = (new y).getD j false :=
          fun i h => (hrep i).resolve_left h
        obtain ⟨l, hl, rfl | rfl | rfl⟩ := shape g hg
        · match l, hl with
          | [], _ => exact Or.inl ⟨true, fun y => by rw [hval]; rfl⟩
          | [a], _ =>
            have e : ∀ y, val ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a]⟩ (old y) = (old y).getD a false := by
              intro y; rw [hval]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
            rcases hrep a with ⟨b, h⟩ | ⟨j, hj, h⟩
            · exact Or.inl ⟨b, fun y => (e y).trans (h y)⟩
            · exact Or.inr (Or.inl ⟨j, hj, fun y => (e y).trans (h y)⟩)
          | [a, c], _ =>
            have e : ∀ y, val ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩ (old y)
                = ((old y).getD a false && (old y).getD c false) := by
              intro y; rw [hval]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
            by_cases ha : ∃ b, ∀ y, (old y).getD a false = b
            · obtain ⟨b, ha⟩ := ha
              cases b
              · exact Or.inl ⟨false, fun y => by rw [e, ha, Bool.false_and]⟩
              · have e' : ∀ y, val ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩ (old y) = (old y).getD c false :=
                  fun y => by rw [e, ha, Bool.true_and]
                rcases hrep c with ⟨b, h⟩ | ⟨j, hj, h⟩
                · exact Or.inl ⟨b, fun y => (e' y).trans (h y)⟩
                · exact Or.inr (Or.inl ⟨j, hj, fun y => (e' y).trans (h y)⟩)
            · by_cases hc : ∃ b, ∀ y, (old y).getD c false = b
              · obtain ⟨b, hc⟩ := hc
                cases b
                · exact Or.inl ⟨false, fun y => by rw [e, hc, Bool.and_false]⟩
                · obtain ⟨j, hj, h⟩ := wire a ha
                  exact Or.inr (Or.inl ⟨j, hj, fun y => by rw [e, hc, Bool.and_true]; exact h y⟩)
              · refine Or.inr (Or.inr ⟨nr ?_, ?_⟩)
                · intro i hi
                  rw [hrd] at hi
                  have := hi.2
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
                  rcases this with rfl | rfl <;> assumption
                · obtain ⟨j, _, h⟩ := wire a ha
                  obtain ⟨k, _, h'⟩ := wire c hc
                  refine ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.and, [j, k]⟩, okand _ (by simp), fun y => ?_⟩
                  rw [e, h, h', hval]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          | _ :: _ :: _ :: _, hl => simp at hl
        · match l, hl with
          | [], _ => exact Or.inl ⟨false, fun y => by rw [hval]; rfl⟩
          | [a], _ =>
            have e : ∀ y, val ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ (old y) = (old y).getD a false := by
              intro y; rw [hval]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
            rcases hrep a with ⟨b, h⟩ | ⟨j, hj, h⟩
            · exact Or.inl ⟨b, fun y => (e y).trans (h y)⟩
            · exact Or.inr (Or.inl ⟨j, hj, fun y => (e y).trans (h y)⟩)
          | [a, c], _ =>
            have e : ∀ y, val ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, c]⟩ (old y)
                = ((old y).getD a false || (old y).getD c false) := by
              intro y; rw [hval]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
            by_cases ha : ∃ b, ∀ y, (old y).getD a false = b
            · obtain ⟨b, ha⟩ := ha
              cases b
              · have e' : ∀ y, val ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, c]⟩ (old y) = (old y).getD c false :=
                  fun y => by rw [e, ha, Bool.false_or]
                rcases hrep c with ⟨b, h⟩ | ⟨j, hj, h⟩
                · exact Or.inl ⟨b, fun y => (e' y).trans (h y)⟩
                · exact Or.inr (Or.inl ⟨j, hj, fun y => (e' y).trans (h y)⟩)
              · exact Or.inl ⟨true, fun y => by rw [e, ha, Bool.true_or]⟩
            · by_cases hc : ∃ b, ∀ y, (old y).getD c false = b
              · obtain ⟨b, hc⟩ := hc
                cases b
                · obtain ⟨j, hj, h⟩ := wire a ha
                  exact Or.inr (Or.inl ⟨j, hj, fun y => by rw [e, hc, Bool.or_false]; exact h y⟩)
                · exact Or.inl ⟨true, fun y => by rw [e, hc, Bool.or_true]⟩
              · refine Or.inr (Or.inr ⟨nr ?_, ?_⟩)
                · intro i hi
                  rw [hrd] at hi
                  have := hi.2
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
                  rcases this with rfl | rfl <;> assumption
                · obtain ⟨j, _, h⟩ := wire a ha
                  obtain ⟨k, _, h'⟩ := wire c hc
                  refine ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [j, k]⟩, okor _ (by simp), fun y => ?_⟩
                  rw [e, h, h', hval]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          | _ :: _ :: _ :: _, hl => simp at hl
        · cases l with
          | nil => exact Or.inl ⟨true, fun y => by rw [hval]; rfl⟩
          | cons a l =>
            have e : ∀ y, val ⟨PEqualNP.CircuitLowerBounds.GateOp.not, a :: l⟩ (old y) = !(old y).getD a false := by
              intro y; rw [hval]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
            by_cases ha : ∃ b, ∀ y, (old y).getD a false = b
            · obtain ⟨b, ha⟩ := ha
              exact Or.inl ⟨!b, fun y => by rw [e, ha]⟩
            · refine Or.inr (Or.inr ⟨nr ?_, ?_⟩)
              · intro i hi
                rw [hrd] at hi
                have := hi.1 rfl
                simp only [List.head?_cons, Option.some.injEq] at this
                rw [← this]; exact ha
              · obtain ⟨j, _, h⟩ := wire a ha
                refine ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.not, [j]⟩, oknot _ (by simp), fun y => ?_⟩
                rw [e, h, hval]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      have hn' : ∀ y, (old y ++ [val g (old y)]).length = n + 1 := fun y => by simp [hn]
      have hS' : ∀ i, i = 0 ∨ i = 9 ∨ i = 10 → ∃ b, ∀ y, (old y ++ [val g (old y)]).getD i false = b := by
        intro i hi
        obtain ⟨b, h⟩ := hS i hi
        exact ⟨b, fun y => by rw [snoc_ne _ _ _ (by rw [hn]; omega)]; exact h y⟩
      have cnt : (g :: gs).countP (fun g => decide (rd g 0 ∨ rd g 9 ∨ rd g 10))
          ≤ gs.countP (fun g => decide (rd g 0 ∨ rd g 9 ∨ rd g 10)) + 1 := by
        rw [List.countP_cons]; split <;> omega
      rcases step with ⟨b, hb⟩ | ⟨j, hj, hb⟩ | ⟨hno, g', hg', hb⟩
      · obtain ⟨gs', h1', h2', h3'⟩ := ih hgs' (fun y => old y ++ [val g (old y)]) new (n + 1) m hn' hm
          (by omega) hS' (by
            intro i
            by_cases hi : i = n
            · exact Or.inl ⟨b, fun y => by rw [snoc_eq _ _ _ ((hn y).trans hi.symm)]; exact hb y⟩
            · rcases hrep i with ⟨c, h⟩ | ⟨k, hk, h⟩
              · exact Or.inl ⟨c, fun y => by rw [snoc_ne _ _ _ (by rw [hn]; exact hi)]; exact h y⟩
              · exact Or.inr ⟨k, hk, fun y => by rw [snoc_ne _ _ _ (by rw [hn]; exact hi)]; exact h y⟩)
        refine ⟨gs', h1', by simp only [List.length_cons]; omega, ?_⟩
        simpa only [wf_cons] using h3'
      · obtain ⟨gs', h1', h2', h3'⟩ := ih hgs' (fun y => old y ++ [val g (old y)]) new (n + 1) m hn' hm
          (by omega) hS' (by
            intro i
            by_cases hi : i = n
            · exact Or.inr ⟨j, hj, fun y => by rw [snoc_eq _ _ _ ((hn y).trans hi.symm)]; exact hb y⟩
            · rcases hrep i with ⟨c, h⟩ | ⟨k, hk, h⟩
              · exact Or.inl ⟨c, fun y => by rw [snoc_ne _ _ _ (by rw [hn]; exact hi)]; exact h y⟩
              · exact Or.inr ⟨k, hk, fun y => by rw [snoc_ne _ _ _ (by rw [hn]; exact hi)]; exact h y⟩)
        refine ⟨gs', h1', by simp only [List.length_cons]; omega, ?_⟩
        simpa only [wf_cons] using h3'
      · obtain ⟨gs', h1', h2', h3'⟩ := ih hgs' (fun y => old y ++ [val g (old y)])
          (fun y => new y ++ [val g' (new y)]) (n + 1) (m + 1) hn' (fun y => by simp [hm]) (by omega) hS' (by
            intro i
            by_cases hi : i = n
            · refine Or.inr ⟨m, by omega, fun y => ?_⟩
              rw [snoc_eq _ _ _ ((hn y).trans hi.symm), snoc_eq _ _ _ (hm y)]; exact hb y
            · rcases hrep i with ⟨c, h⟩ | ⟨k, hk, h⟩
              · exact Or.inl ⟨c, fun y => by rw [snoc_ne _ _ _ (by rw [hn]; exact hi)]; exact h y⟩
              · refine Or.inr ⟨k, by omega, fun y => ?_⟩
                rw [snoc_ne _ _ _ (by rw [hn]; exact hi), snoc_ne _ _ _ (by rw [hm]; omega)]; exact h y)
        refine ⟨g' :: gs', ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hg'
          · exact h1' x hx
        · rw [List.countP_cons_of_neg (by simpa using hno)]
          simp only [List.length_cons]; omega
        · simpa only [wf_cons] using h3'
  -- The step itself.
  intro l hl hlt _ hl9 hla C hfan hsize
  obtain ⟨E, hE⟩ : ∃ E : (Fin 9 → Bool) → Bool, E = fun x => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 ||
      x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5) := ⟨_, rfl⟩
  obtain ⟨a, b, ha, hab, hb, hor⟩ : ∃ a b : Fin 9, a ≠ 0 ∧ a ≠ b ∧ E (fun i => decide (i = 0 ∨ i = a)) = true ∧
      ((E (fun i => decide (i = 0 ∨ i = b)) = true ∧ b ≠ 0) ∧ ∀ x : Fin 9 → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (l.map fun i => (List.ofFn x ++ [!x 0]).getD i false) = (!x 0 || x a)) := by
    have h9 : ∀ x : Fin 9 → Bool, (List.ofFn x ++ [!x 0]).getD 9 false = !x 0 := fun x => rfl
    have hj : ∀ (x : Fin 9 → Bool) (j : Fin 9), (List.ofFn x ++ [!x 0]).getD j.val false = x j := by
      intro x j; fin_cases j <;> rfl
    match l, hl with
    | [p, q], _ =>
      have key : ∃ c : Fin 9, (c = 1 ∨ c = 4 ∨ c = 5) ∧ ([p, q] = [9, c.val] ∨ [p, q] = [c.val, 9]) := by
        have m9 := hl9.2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m9 hla
        have hp : p = 1 ∨ q = 1 ∨ p = 4 ∨ q = 4 ∨ p = 5 ∨ q = 5 := by omega
        rcases m9 with rfl | rfl
        · rcases hp with h | h | h | h | h | h
          · omega
          · exact ⟨1, by simp, Or.inl (by rw [h]; rfl)⟩
          · omega
          · exact ⟨4, by simp, Or.inl (by rw [h]; rfl)⟩
          · omega
          · exact ⟨5, by simp, Or.inl (by rw [h]; rfl)⟩
        · rcases hp with h | h | h | h | h | h
          · exact ⟨1, by simp, Or.inr (by rw [h]; rfl)⟩
          · omega
          · exact ⟨4, by simp, Or.inr (by rw [h]; rfl)⟩
          · omega
          · exact ⟨5, by simp, Or.inr (by rw [h]; rfl)⟩
          · omega
      obtain ⟨c, hc, hpq⟩ := key
      have hev : ∀ x : Fin 9 → Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval
          ([p, q].map fun i => (List.ofFn x ++ [!x 0]).getD i false) = (!x 0 || x c) := by
        intro x
        rcases hpq with e | e
        · rw [e]
          simp only [List.map_cons, List.map_nil, h9, hj, PEqualNP.CircuitLowerBounds.GateOp.eval,
            List.any_cons, List.any_nil, id, Bool.or_false]
        · rw [e]
          simp only [List.map_cons, List.map_nil, h9, hj, PEqualNP.CircuitLowerBounds.GateOp.eval,
            List.any_cons, List.any_nil, id, Bool.or_false]
          exact Bool.or_comm _ _
      subst hE
      rcases hc with rfl | rfl | rfl
      · exact ⟨1, 4, by decide, by decide, by decide, ⟨by decide, by decide⟩, hev⟩
      · exact ⟨4, 1, by decide, by decide, by decide, ⟨by decide, by decide⟩, hev⟩
      · exact ⟨5, 1, by decide, by decide, by decide, ⟨by decide, by decide⟩, hev⟩
  by_contra hno
  have h : ∀ x : Fin 9 → Bool, (wf C.gates (List.ofFn x ++ [!x 0] ++ [!x 0 || x a])).getD C.output false = E x := by
    intro x
    by_contra hx
    refine hno ⟨x, ?_⟩
    intro _ e
    apply hx
    rw [← hor.2 x, hE, hwf, hval]
    exact e
  have okC : ∀ g ∈ C.gates, ok g := by
    intro g hg; rw [hok]; exact hfan g hg
  have hsz : C.gates.length ≤ 13 := hsize
  have b0 : ∀ x : Fin 9 → Bool, (List.ofFn x ++ [!x 0] ++ [!x 0 || x a]).getD 0 false = x 0 := fun x => rfl
  have b9 : ∀ x : Fin 9 → Bool, (List.ofFn x ++ [!x 0] ++ [!x 0 || x a]).getD 9 false = !x 0 := fun x => rfl
  have b10 : ∀ x : Fin 9 → Bool, (List.ofFn x ++ [!x 0] ++ [!x 0 || x a]).getD 10 false = (!x 0 || x a) := fun x => rfl
  have blen : ∀ x : Fin 9 → Bool, (List.ofFn x ++ [!x 0] ++ [!x 0 || x a]).length = 11 := fun x => by simp
  have bj : ∀ (x : Fin 9 → Bool) (j : Fin 9), (List.ofFn x ++ [!x 0] ++ [!x 0 || x a]).getD j.val false = x j := by
    intro x j; fin_cases j <;> rfl
  -- At most one gate uses wire 0, 9 or 10.
  have few : C.gates.countP (fun g => decide (rd g 0 ∨ rd g 9 ∨ rd g 10)) ≤ 1 := by
    by_contra hge
    obtain ⟨G, hG⟩ : ∃ G : (Fin 8 → Bool) → Fin 9 → Bool,
        G = fun y => ![false, y 0, y 1, y 2, y 6, y 7, y 4, y 5, y 3] := ⟨_, rfl⟩
    have G0 : ∀ y, G y 0 = false := fun y => by rw [hG]; rfl
    have hsucc : ∀ j : Fin 9, j ≠ 0 → ∃ k : Fin 8, ∀ y, G y j = y k := by
      intro j hj
      rw [hG]
      fin_cases j
      · exact absurd rfl hj
      · exact ⟨0, fun y => rfl⟩
      · exact ⟨1, fun y => rfl⟩
      · exact ⟨2, fun y => rfl⟩
      · exact ⟨6, fun y => rfl⟩
      · exact ⟨7, fun y => rfl⟩
      · exact ⟨4, fun y => rfl⟩
      · exact ⟨5, fun y => rfl⟩
      · exact ⟨3, fun y => rfl⟩
    obtain ⟨gs', o1, o2, o3⟩ := elim C.gates okC
      (fun y => List.ofFn (G y) ++ [!G y 0] ++ [!G y 0 || G y a]) (fun y => List.ofFn y) 11 8
      (fun y => blen (G y)) (fun y => by simp) (le_refl _)
      (by
        rintro i (rfl | rfl | rfl)
        · exact ⟨false, fun y => by rw [b0, G0]⟩
        · exact ⟨true, fun y => by rw [b9, G0]; rfl⟩
        · exact ⟨true, fun y => by rw [b10, G0]; rfl⟩)
      (by
        intro i
        by_cases hi9 : i < 9
        · by_cases hi0 : i = 0
          · subst hi0; exact Or.inl ⟨false, fun y => by rw [b0, G0]⟩
          · obtain ⟨k, hk⟩ := hsucc ⟨i, hi9⟩ (fun e => hi0 (congrArg Fin.val e))
            refine Or.inr ⟨k.val, k.isLt, fun y => ?_⟩
            have e1 := bj (G y) ⟨i, hi9⟩
            simp only at e1
            have e2 : ∀ k : Fin 8, (List.ofFn y).getD k.val false = y k := by
              intro k; fin_cases k <;> rfl
            rw [e1, hk y, e2]
        · by_cases hi99 : i = 9
          · subst hi99; exact Or.inl ⟨true, fun y => by rw [b9, G0]; rfl⟩
          · by_cases hi10 : i = 10
            · subst hi10; exact Or.inl ⟨true, fun y => by rw [b10, G0]; rfl⟩
            · exact Or.inl ⟨false, fun y => List.getD_eq_default _ _ (by rw [blen]; omega)⟩)
    have KE : ∀ y : Fin 8 → Bool, E (G y) = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) ||
        (y 4 && y 0) || (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 5 && y 7)) := by
      intro y
      rw [hE, hG]
      show (false && y 0 || y 0 && y 1 || y 1 && y 2 || y 2 && y 6 || y 6 && false || false && y 7 ||
        y 0 && y 4 || y 1 && y 5 || y 2 && y 3 || y 7 && y 5 || y 4 && y 3 || y 3 && y 7) = _
      generalize y 0 = c0
      generalize y 1 = c1
      generalize y 2 = c2
      generalize y 3 = c3
      generalize y 4 = c4
      generalize y 5 = c5
      generalize y 6 = c6
      generalize y 7 = c7
      revert c0 c1 c2 c3 c4 c5 c6 c7
      decide
    rcases o3 C.output with ⟨c, hc⟩ | ⟨j, hj⟩
    · have e1 := (hc fun _ => true).symm.trans (h _)
      have e2 := (hc fun _ => false).symm.trans (h _)
      rw [KE] at e1 e2
      rw [e1] at e2
      exact absurd e2 (by decide)
    · refine h1 ⟨⟨gs', j⟩, ?_, ?_, ?_⟩
      · intro g hg
        have := o1 g hg
        rw [hok] at this; exact this
      · show gs'.length ≤ 11
        omega
      · intro y
        have e := (hj y).symm.trans (h (G y))
        rw [KE] at e
        rw [hwf, hval] at e
        exact e
  -- If no gate uses wire 10 the second gate can go.
  have drop : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, ok g) → gs.length ≤ 13 →
      (∀ g ∈ gs, ¬ rd g 10) → ∀ o, o ≠ 10 →
      ¬ ∀ x : Fin 9 → Bool, (wf gs (List.ofFn x ++ [!x 0] ++ [!x 0 || x a])).getD o false = E x := by
    intro gs hgs hlen hnr o ho hall
    obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℕ, σ = fun i => if i < 10 then i else i - 1 := ⟨_, rfl⟩
    have sim : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, ok g) → (∀ g ∈ gs, ¬ rd g 10) →
        ∀ w w' : List Bool, 11 ≤ w.length → w.length = w'.length + 1 →
        (∀ i, i ≠ 10 → w.getD i false = w'.getD (σ i) false) →
        ∀ i, i ≠ 10 → (wf gs w).getD i false
          = (wf (gs.map fun g => ⟨g.op, g.inputs.map σ⟩) w').getD (σ i) false := by
      intro gs
      induction gs with
      | nil => intro _ _ w w' _ _ hh; simpa only [List.map_nil, wf_nil] using hh
      | cons g gs ih =>
        intro hgs hnr w w' h11 hl' hh
        rw [List.map_cons, wf_cons, wf_cons]
        have hv : val g w = val ⟨g.op, g.inputs.map σ⟩ w' :=
          val_congr g (hgs g List.mem_cons_self) w w' σ (fun i hi => hh i fun e =>
            hnr g List.mem_cons_self (e ▸ hi))
        rw [← hv]
        refine ih (fun g' h' => hgs g' (List.mem_cons_of_mem _ h'))
          (fun g' h' => hnr g' (List.mem_cons_of_mem _ h')) _ _ (by simp; omega) (by simp; omega) ?_
        intro i hi
        by_cases hin : i = w.length
        · have : w'.length = σ i := by rw [hσ]; show _ = if i < 10 then i else i - 1; split <;> omega
          rw [snoc_eq _ _ _ hin.symm, snoc_eq _ _ _ this]
        · have : σ i ≠ w'.length := by rw [hσ]; show (if i < 10 then i else i - 1) ≠ _; split <;> omega
          rw [snoc_ne _ _ _ hin, snoc_ne _ _ _ this]
          exact hh i hi
    refine h2 ⟨⟨⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ :: gs.map fun g => ⟨g.op, g.inputs.map σ⟩, σ o⟩,
      ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨by simp, by simp⟩
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
        have := hgs g' hg'
        rw [hok] at this
        exact ⟨this.1, by simpa using this.2⟩
    · show (_ :: gs.map _).length ≤ 14
      simp only [List.length_cons, List.length_map]; omega
    · intro x
      have e := sim gs hgs hnr (List.ofFn x ++ [!x 0] ++ [!x 0 || x a]) (List.ofFn x ++ [!x 0])
        (by rw [blen]) (by simp) (by
          intro i hi
          by_cases hlt : i < 10
          · have : σ i = i := by rw [hσ]; show (if i < 10 then i else i - 1) = i; split <;> omega
            rw [this]
            exact List.getD_append _ _ _ _ (by simp; omega)
          · rw [List.getD_eq_default _ _ (by rw [blen]; omega), List.getD_eq_default _ _ (by
              rw [hσ]; show _ ≤ if i < 10 then i else i - 1
              simp; split <;> omega)]) o ho
      have e2 : (wf (gs.map fun g => ⟨g.op, g.inputs.map σ⟩) (List.ofFn x ++ [!x 0])).getD (σ o) false = E x :=
        e.symm.trans (hall x)
      have e3 : E x = [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any
          fun (i : ℕ) => x (Fin.ofNat 9 (i / 10)) && x (Fin.ofNat 9 (i % 10)) := by
        rw [hE]
        simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
        rfl
      rw [hwf, hval] at e2
      exact e2.trans e3
  -- The output is not wire 0, 9 or 10.
  have pre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ), i < w.length →
      (wf gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rw [wf_nil]
    | cons g gs ih =>
      intro w i hi
      rw [wf_cons, ih _ _ (by simp; omega), snoc_ne _ _ _ (by omega)]
  have Ezero : E (fun _ => false) = false := by rw [hE]; rfl
  have out0 : C.output ≠ 0 := by
    intro e
    have := h (fun i => decide (i = 1 ∨ i = 2))
    rw [e, pre _ _ _ (by rw [blen]; omega), b0, hE] at this
    exact absurd this (by decide)
  have out9 : C.output ≠ 9 := by
    intro e
    have := h (fun _ => false)
    rw [e, pre _ _ _ (by rw [blen]; omega), b9, Ezero] at this
    exact absurd this (by decide)
  have out10 : C.output ≠ 10 := by
    intro e
    have := h (fun _ => false)
    rw [e, pre _ _ _ (by rw [blen]; omega), b10, Ezero] at this
    exact absurd this (by decide)
  -- Two inputs that differ only at 0 and agree through every gate give the same output.
  have indep : ∀ x x' : Fin 9 → Bool, (∀ j, j ≠ 0 → x j = x' j) →
      (∀ g ∈ C.gates, ∀ w w' : List Bool, (∀ i, i ≠ 0 → i ≠ 9 → i ≠ 10 → w.getD i false = w'.getD i false) →
        w.getD 0 false = x 0 → w'.getD 0 false = x' 0 → w.getD 9 false = (!x 0) → w'.getD 9 false = (!x' 0) →
        w.getD 10 false = (!x 0 || x a) → w'.getD 10 false = (!x' 0 || x' a) → val g w = val g w') →
      E x = E x' := by
    intro x x' hxx hgood
    have sim : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, g ∈ C.gates) →
        ∀ w w' : List Bool, w.length = w'.length → 11 ≤ w.length →
        (∀ i, i ≠ 0 → i ≠ 9 → i ≠ 10 → w.getD i false = w'.getD i false) →
        w.getD 0 false = x 0 → w'.getD 0 false = x' 0 → w.getD 9 false = (!x 0) → w'.getD 9 false = (!x' 0) →
        w.getD 10 false = (!x 0 || x a) → w'.getD 10 false = (!x' 0 || x' a) →
        ∀ i, i ≠ 0 → i ≠ 9 → i ≠ 10 → (wf gs w).getD i false = (wf gs w').getD i false := by
      intro gs
      induction gs with
      | nil => intro _ w w' _ _ hh _ _ _ _ _ _; simpa only [wf_nil] using hh
      | cons g gs ih =>
        intro hm w w' hl' h11 hh p1 p2 p3 p4 p5 p6
        rw [wf_cons, wf_cons]
        have hv := hgood g (hm g List.mem_cons_self) w w' hh p1 p2 p3 p4 p5 p6
        refine ih (fun g' h' => hm g' (List.mem_cons_of_mem _ h')) _ _ (by simp [hl']) (by simp; omega) ?_
          (by rw [snoc_ne _ _ _ (by omega)]; exact p1) (by rw [snoc_ne _ _ _ (by omega)]; exact p2)
          (by rw [snoc_ne _ _ _ (by omega)]; exact p3) (by rw [snoc_ne _ _ _ (by omega)]; exact p4)
          (by rw [snoc_ne _ _ _ (by omega)]; exact p5) (by rw [snoc_ne _ _ _ (by omega)]; exact p6)
        intro i i0 i9 i10
        by_cases hin : i = w.length
        · rw [snoc_eq _ _ _ hin.symm, snoc_eq _ _ _ (hl'.symm.trans hin.symm)]; exact hv
        · rw [snoc_ne _ _ _ hin, snoc_ne _ _ _ (by omega)]; exact hh i i0 i9 i10
    rw [← h x, ← h x']
    refine sim C.gates (fun g hg => hg) _ _ (by rw [blen, blen]) (by rw [blen]) ?_ (b0 x) (b0 x') (b9 x) (b9 x')
      (b10 x) (b10 x') _ out0 out9 out10
    intro i i0 i9 i10
    by_cases hi : i < 9
    · have e1 := bj x ⟨i, hi⟩
      have e2 := bj x' ⟨i, hi⟩
      simp only at e1 e2
      rw [e1, e2]
      exact hxx _ fun e => i0 (congrArg Fin.val e)
    · rw [List.getD_eq_default _ _ (by rw [blen]; omega), List.getD_eq_default _ _ (by rw [blen]; omega)]
  have agree : ∀ g, ok g → ¬ (rd g 0 ∨ rd g 9 ∨ rd g 10) → ∀ w w' : List Bool,
      (∀ i, i ≠ 0 → i ≠ 9 → i ≠ 10 → w.getD i false = w'.getD i false) → val g w = val g w' := by
    intro g hg hn w w' hh
    have := val_congr g hg w w' id (fun i hi => hh i (fun e => hn (Or.inl (e ▸ hi)))
      (fun e => hn (Or.inr (Or.inl (e ▸ hi)))) (fun e => hn (Or.inr (Or.inr (e ▸ hi)))))
    simpa using this
  -- Some gate uses wire 10, and it is the only one that uses 0, 9 or 10.
  by_cases hex : ∃ g ∈ C.gates, rd g 10
  · obtain ⟨g, hg, hg10⟩ := hex
    have only : ∀ g' ∈ C.gates, (rd g' 0 ∨ rd g' 9 ∨ rd g' 10) → g' = g := by
      intro g' hg' hr
      rw [List.countP_eq_length_filter] at few
      have m1 : g ∈ C.gates.filter (fun g => decide (rd g 0 ∨ rd g 9 ∨ rd g 10)) := by
        simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hg, Or.inr (Or.inr hg10)⟩
      have m2 : g' ∈ C.gates.filter (fun g => decide (rd g 0 ∨ rd g 9 ∨ rd g 10)) := by
        simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hg', hr⟩
      match hfil : C.gates.filter (fun g => decide (rd g 0 ∨ rd g 9 ∨ rd g 10)), few with
      | [], _ => rw [hfil] at m1; simp at m1
      | [z], _ =>
        rw [hfil, List.mem_singleton] at m1 m2
        rw [m1, m2]
      | _ :: _ :: _, few => simp at few
    -- From a property of g alone.
    have viaA : (∀ w w' : List Bool, (∀ i, i ≠ 0 → i ≠ 9 → i ≠ 10 → w.getD i false = w'.getD i false) →
        w.getD 10 false = true → w'.getD 10 false = true → val g w = val g w') → False := by
      intro hh
      have e := indep (fun i => decide (i = 0 ∨ i = a)) (fun i => decide (i = a)) (by
          intro j hj; simp [hj]) (by
        intro g' hg' w w' q p1 p2 p3 p4 p5 p6
        by_cases hr : rd g' 0 ∨ rd g' 9 ∨ rd g' 10
        · rw [only g' hg' hr]
          exact hh w w' q (by rw [p5]; simp) (by rw [p6]; simp)
        · exact agree g' (okC g' hg') hr w w' q)
      rw [hb] at e
      have e0 : ∀ a : Fin 9, E (fun i => decide (i = a)) = false := by rw [hE]; decide
      rw [e0] at e
      exact absurd e (by decide)
    have viaB : (∀ w w' : List Bool, (∀ i, i ≠ 0 → i ≠ 9 → i ≠ 10 → w.getD i false = w'.getD i false) →
        w.getD 0 false = true → w'.getD 0 false = false → w.getD 10 false = false → w'.getD 10 false = true →
        val g w = val g w') → False := by
      intro hh
      have e := indep (fun i => decide (i = 0 ∨ i = b)) (fun i => decide (i = b)) (by
          intro j hj; simp [hj]) (by
        intro g' hg' w w' q p1 p2 p3 p4 p5 p6
        by_cases hr : rd g' 0 ∨ rd g' 9 ∨ rd g' 10
        · rw [only g' hg' hr]
          refine hh w w' q (by rw [p1]; simp) (by rw [p2]; simp [Ne.symm hor.1.2]) (by rw [p5]; simp [ha, hab])
            (by rw [p6]; simp [Ne.symm hor.1.2])
        · exact agree g' (okC g' hg') hr w w' q)
      rw [hor.1.1] at e
      have e0 : ∀ b : Fin 9, E (fun i => decide (i = b)) = false := by rw [hE]; decide
      rw [e0] at e
      exact absurd e (by decide)
    obtain ⟨l', hl', hgl⟩ := shape g (okC g hg)
    have hmem : 10 ∈ l' := by
      rw [hrd] at hg10
      rcases hgl with e | e | e <;> · rw [e] at hg10; exact hg10.2
    rcases hgl with e | e | e
    · -- AND
      by_cases h9 : 9 ∈ l'
      · -- it equals wire 9
        have pairs : ∀ w : List Bool, val g w = (w.getD 10 false && w.getD 9 false) := by
          intro w
          rw [e, hval]
          match l', hl' with
          | [], _ => simp at hmem
          | [p], _ => simp only [List.mem_singleton] at hmem h9; omega
          | [p, q], _ =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem h9
            have : (p = 10 ∧ q = 9) ∨ (p = 9 ∧ q = 10) := by omega
            rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
            · simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.and_comm]
          | _ :: _ :: _ :: _, hl' => simp at hl'
        obtain ⟨φ, hφ⟩ : ∃ φ : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate,
            φ = fun g' => if rd g' 10 then ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9]⟩ else g' := ⟨_, rfl⟩
        have φok : ∀ g' ∈ C.gates, ok (φ g') := by
          intro g' hg'
          rw [hφ]
          show ok (if rd g' 10 then _ else g')
          split
          · exact okand _ (by simp)
          · exact okC g' hg'
        refine drop (C.gates.map φ) ?_ (by simpa using hsz) ?_ C.output out10 ?_
        · intro g1 h1'
          obtain ⟨g', hg', rfl⟩ := List.mem_map.1 h1'
          exact φok g' hg'
        · intro g1 h1'
          obtain ⟨g', hg', rfl⟩ := List.mem_map.1 h1'
          rw [hφ]
          show ¬ rd (if rd g' 10 then _ else g') 10
          split
          · rw [hrd]; simp
          · assumption
        · intro x
          rw [← h x]
          have sim : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, g ∈ C.gates) →
              ∀ w : List Bool, 11 ≤ w.length → w.getD 9 false = (!x 0) → w.getD 10 false = (!x 0 || x a) →
              wf (gs.map φ) w = wf gs w := by
            intro gs
            induction gs with
            | nil => intro _ w _ _ _; rfl
            | cons g1 gs ih =>
              intro hm w h11 p9 p10
              rw [List.map_cons, wf_cons, wf_cons]
              have hv : val (φ g1) w = val g1 w := by
                rw [hφ]
                show val (if rd g1 10 then _ else g1) w = _
                split
                · next hr =>
                  rw [only g1 (hm g1 List.mem_cons_self) (Or.inr (Or.inr hr)), pairs w, p9, p10, hval]
                  simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, p9]
                  cases x 0 <;> simp
                · rfl
              rw [hv]
              exact ih (fun g' h' => hm g' (List.mem_cons_of_mem _ h')) _ (by simp; omega)
                (by rw [snoc_ne _ _ _ (by omega)]; exact p9) (by rw [snoc_ne _ _ _ (by omega)]; exact p10)
          rw [sim C.gates (fun g hg => hg) _ (by rw [blen]) (b9 x) (b10 x)]
      · by_cases h0 : 0 ∈ l'
        · refine viaB ?_
          intro w w' _ p0 p0' p10 p10'
          have z : ∀ w : List Bool, (w.getD 0 false = false ∨ w.getD 10 false = false) → val g w = false := by
            intro w hz
            rw [e, hval]
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval]
            rw [Bool.eq_false_iff]
            intro hall
            rw [List.all_map, List.all_eq_true] at hall
            rcases hz with hz | hz
            · have := hall 0 h0
              simp only [Function.comp, id] at this
              rw [hz] at this; exact absurd this (by decide)
            · have := hall 10 hmem
              simp only [Function.comp, id] at this
              rw [hz] at this; exact absurd this (by decide)
          rw [z w (Or.inr p10), z w' (Or.inl p0')]
        · refine viaA ?_
          intro w w' q p10 p10'
          rw [e, hval]
          simp only
          congr 1
          apply List.map_congr_left
          intro i hi
          by_cases hi10 : i = 10
          · rw [hi10, p10, p10']
          · exact q i (fun e => h0 (e ▸ hi)) (fun e => h9 (e ▸ hi)) hi10
    · -- OR
      refine viaA ?_
      have t : ∀ w : List Bool, w.getD 10 false = true → val g w = true := by
        intro w hw
        rw [e, hval]
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true]
        exact ⟨10, hmem, hw⟩
      intro w w' _ p10 p10'
      rw [t w p10, t w' p10']
    · -- NOT
      refine viaA ?_
      have hh : l'.head? = some 10 := by
        rw [hrd, e] at hg10; exact hg10.1 rfl
      intro w w' _ p10 p10'
      rw [e, hval]
      cases l' with
      | nil => simp at hh
      | cons p l' =>
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.headD_cons]
        rw [p10, p10']
  · exact drop C.gates okC hsz (fun g hg hr => hex ⟨g, hg, hr⟩) C.output out10 h

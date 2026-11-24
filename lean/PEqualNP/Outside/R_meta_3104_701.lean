import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3104_701
    (hNorm : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧
        D.size = C.size ∧
        D.output = C.output ∧
        ∀ xs : List Bool, xs.length = n → D.wires xs = C.wires xs)
    (hAnd : let f : (Fin 8 → Bool) → Bool := fun x => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4);
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.FanInTwo x3 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 9 x2 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 + x2.size) x3 →
        x2.size + x3.size ≤ 13 →
        10 + x2.size ≤ x3.output → x3.output < 10 + x2.size + x3.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.output - (10 + x2.size))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        let x8 : Bool → (Fin 8 → Bool) → List Bool := fun b x => x2.wires (List.ofFn x ++ [x 1 || b]);
        (∀ x, x3.eval (x8 false x ++ [(x8 false x).getD x4 false]) = f x) →
        ∃ x, x3.eval (x8 true x ++ [true]) ≠ (f x || x 0 || x 3))
    (hOr : let f : (Fin 8 → Bool) → Bool := fun x => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4);
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.FanInTwo x3 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 9 x2 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 + x2.size) x3 →
        x2.size + x3.size ≤ 13 →
        10 + x2.size ≤ x3.output → x3.output < 10 + x2.size + x3.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.output - (10 + x2.size))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        let x8 : Bool → (Fin 8 → Bool) → List Bool := fun b x => x2.wires (List.ofFn x ++ [x 1 || b]);
        (∀ x, x3.eval (x8 false x ++ [(x8 false x).getD x4 false]) = f x) →
        ∃ x, x3.eval (x8 true x ++ [true]) ≠ (f x || x 0 || x 3))
    (hNot : let f : (Fin 8 → Bool) → Bool := fun x => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4);
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.FanInTwo x3 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 9 x2 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 + x2.size) x3 →
        x2.size + x3.size ≤ 13 →
        10 + x2.size ≤ x3.output → x3.output < 10 + x2.size + x3.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.output - (10 + x2.size))).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        let x8 : Bool → (Fin 8 → Bool) → List Bool := fun b x => x2.wires (List.ofFn x ++ [x 1 || b]);
        (∀ x, x3.eval (x8 false x ++ [(x8 false x).getD x4 false]) = f x) →
        ∃ x, x3.eval (x8 true x ++ [true]) ≠ (f x || x 0 || x 3)) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         have x8 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x8 : Bool) (x9 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x9 ++ [x9 (1 : Fin (8 : ℕ)) || x8]);         (∀ (x9 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.false x9 ++ [(x8 Bool.false x9).getD x4 Bool.false]) = x1 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.true x10 ++ [Bool.true]) ≠ (x1 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  intro f x2 x3 x4 hf2 hf3 hsz x8 hcomp
  obtain ⟨y2, hyf2, hyrb2, hysz2, -, hyw2⟩ := hNorm 9 x2 hf2
  obtain ⟨y3, hyf3, hyrb3, hysz3, hyo3, hyw3⟩ := hNorm (10 + y2.size) x3 hf3
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ t : List Bool, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      simp only [List.foldl_cons, ht, List.append_assoc, List.singleton_append]
  have hw2eq : ∀ (b : Bool) (x : Fin 8 → Bool), y2.wires (List.ofFn x ++ [x 1 || b]) = x8 b x := by
    intro b x
    exact hyw2 (List.ofFn x ++ [x 1 || b]) (by simp)
  have hw2len : ∀ (b : Bool) (x : Fin 8 → Bool), (y2.wires (List.ofFn x ++ [x 1 || b])).length = 9 + y2.size := by
    intro b x
    obtain ⟨t, ht, hl⟩ := hpre y2.gates (List.ofFn x ++ [x 1 || b])
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires PEqualNP.CircuitLowerBounds.Circuit.size at *
    rw [ht]
    simp [hl]
    omega
  have hy3eq : ∀ (b : Bool) (x : Fin 8 → Bool) (u : Bool),
      y3.eval (y2.wires (List.ofFn x ++ [x 1 || b]) ++ [u]) = x3.eval (x8 b x ++ [u]) := by
    intro b x u
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [hyo3, hw2eq]
    have hlen : (x8 b x ++ [u]).length = 10 + y2.size := by
      rw [← hw2eq b x, List.length_append, hw2len b x]
      simp
      omega
    rw [hyw3 _ hlen]
  have hycomp : ∀ x : Fin 8 → Bool,
      y3.eval (y2.wires (List.ofFn x ++ [x 1 || false]) ++ [(y2.wires (List.ofFn x ++ [x 1 || false])).getD x4 false]) = f x := by
    intro x
    rw [hy3eq, hw2eq]
    exact hcomp x
  by_cases hout : 10 + y2.size ≤ y3.output ∧ y3.output < 10 + y2.size + y3.size
  · obtain ⟨hlo, hhi⟩ := hout
    have hidx : y3.output - (10 + y2.size) < y3.gates.length := by
      have : y3.size = y3.gates.length := rfl
      omega
    have hmem := (hyf3 _ (List.getElem_mem hidx)).1
    have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt y3 (y3.output - (10 + y2.size)) = y3.gates[y3.output - (10 + y2.size)] := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hidx]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hop | hop | hop
    · obtain ⟨x, hx⟩ := hAnd y2 y3 x4 hyf2 hyf3 hyrb2 hyrb3 (by omega) hlo hhi (by rw [hgat]; exact hop) hycomp
      exact ⟨x, by rw [← hy3eq]; exact hx⟩
    · obtain ⟨x, hx⟩ := hOr y2 y3 x4 hyf2 hyf3 hyrb2 hyrb3 (by omega) hlo hhi (by rw [hgat]; exact hop) hycomp
      exact ⟨x, by rw [← hy3eq]; exact hx⟩
    · obtain ⟨x, hx⟩ := hNot y2 y3 x4 hyf2 hyf3 hyrb2 hyrb3 (by omega) hlo hhi (by rw [hgat]; exact hop) hycomp
      exact ⟨x, by rw [← hy3eq]; exact hx⟩
  · by_cases hlt : y3.output < 9 + y2.size
    · let a : Fin 8 → Bool := fun i => decide (i.val = 1 ∨ i.val = 3)
      refine ⟨a, ?_⟩
      rw [← hy3eq]
      have hsame : y2.wires (List.ofFn a ++ [a 1 || true]) = y2.wires (List.ofFn a ++ [a 1 || false]) := by
        have ha1 : a 1 = true := by decide
        simp [ha1]
      have heval_lt : ∀ (u : Bool) (xs : List Bool), xs.length = 9 + y2.size →
          y3.eval (xs ++ [u]) = xs.getD y3.output false := by
        intro u xs hxs
        obtain ⟨t, ht, _⟩ := hpre y3.gates (xs ++ [u])
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
        rw [ht, List.getD_append _ _ _ _ (by simp [hxs]; omega), List.getD_append _ _ _ _ (by omega)]
      rw [heval_lt true _ (hw2len true a), hsame, ← heval_lt _ _ (hw2len false a), hycomp a]
      decide
    · by_cases heq : y3.output = 9 + y2.size
      · let a : Fin 8 → Bool := fun _ => false
        refine ⟨a, ?_⟩
        rw [← hy3eq]
        obtain ⟨t, ht, _⟩ := hpre y3.gates (y2.wires (List.ofFn a ++ [a 1 || true]) ++ [true])
        change (y3.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (y2.wires (List.ofFn a ++ [a 1 || true]) ++ [true])).getD y3.output false ≠ _
        rw [ht]
        have hlen := hw2len true a
        rw [List.getD_append _ _ _ _ (by rw [List.length_append, hlen]; simp; omega)]
        rw [List.getD_append_right _ _ _ _ (by omega)]
        have hsub : y3.output - (y2.wires (List.ofFn a ++ [a 1 || true])).length = 0 := by omega
        rw [hsub]
        decide
      · have hbig : 10 + y2.size + y3.size ≤ y3.output := by omega
        let a : Fin 8 → Bool := fun i => decide (i.val = 0)
        refine ⟨a, ?_⟩
        rw [← hy3eq]
        obtain ⟨t, ht, hl⟩ := hpre y3.gates (y2.wires (List.ofFn a ++ [a 1 || true]) ++ [true])
        change (y3.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (y2.wires (List.ofFn a ++ [a 1 || true]) ++ [true])).getD y3.output false ≠ _
        rw [ht]
        have hlen := hw2len true a
        have hsz' : y3.size = y3.gates.length := rfl
        rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_append, hlen, hl]; simp; omega)]
        decide

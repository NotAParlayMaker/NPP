import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1674_2
    (h1 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ 14 →
      (∀ (a : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (t : List PEqualNP.CircuitLowerBounds.Gate),
        D.gates = a ++ g :: t → (t.flatMap (fun k => k.inputs)).count (10 + a.length) ≤ 1) →
      ∃ (r : ℕ) (b : Bool), r ∈ (if b then [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] else [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ) ∧
        let x := fun i : Fin 9 => r.testBit i.val
        let w := List.ofFn x ++ [x 0 || x 2]
        D.eval w ≠ b)
    (h2 : ∀ (P Q : PEqualNP.CircuitLowerBounds.Circuit) (g : PEqualNP.CircuitLowerBounds.Gate),
      PEqualNP.MetaComplexity.Monotone2 P → PEqualNP.MetaComplexity.Monotone2 Q →
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → g.inputs.length ≤ 2 →
      P.size + Q.size ≤ 13 → 2 ≤ (Q.gates.flatMap (fun k => k.inputs)).count (10 + P.size) →
      ∃ (r : ℕ) (b : Bool), r ∈ (if b then [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] else [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ) ∧
        let x := fun i : Fin 9 => r.testBit i.val
        let w := List.ofFn x ++ [x 0 || x 2]
        let v := P.wires w
        Q.eval (v ++ [g.op.eval (g.inputs.map (fun j => v.getD j false))]) ≠ b)
    (h3 : ∀ (P Q : PEqualNP.CircuitLowerBounds.Circuit) (i : Option ℕ),
      PEqualNP.MetaComplexity.FanInTwo P → PEqualNP.MetaComplexity.Monotone2 Q → P.size + Q.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let v := P.wires (List.ofFn x ++ [x 0 || x 2])
        Q.eval (v ++ [!((i.map (fun j => v.getD j false)).getD false)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  classical
  let F : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let init (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 2]
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) := w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]
  let marked (g : PEqualNP.CircuitLowerBounds.Gate) := g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  have preserved (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have border (r : ℕ) (b : Bool)
      (hr : r ∈ (if b then [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] else [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ)) :
      F (fun i : Fin 9 => r.testBit i.val) = b := by
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, List.mem_cons,
      List.not_mem_nil, or_false] at hr <;>
      rcases hr with h|h|h|h|h|h|h|h|h|h|h|h <;> subst r <;> decide
  have firstMark (s : List PEqualNP.CircuitLowerBounds.Gate) (ex : ∃ g ∈ s, marked g) :
      ∃ a g t, s = a ++ g :: t ∧ marked g ∧ ∀ z ∈ a, ¬ marked z := by
    induction s with
    | nil => simp at ex
    | cons k s ih =>
      by_cases hk : marked k
      · exact ⟨[], k, s, rfl, hk, by simp⟩
      · obtain ⟨z, hz, hm⟩ := ex
        obtain h | h := List.mem_cons.mp hz
        · exact (hk (h ▸ hm)).elim
        · obtain ⟨a, g, t, eq, hg, ha⟩ := ih ⟨z, h, hm⟩
          exact ⟨k :: a, g, t, by simp [eq], hg, by simpa using And.intro hk ha⟩
  have lastMark (s : List PEqualNP.CircuitLowerBounds.Gate) (ex : ∃ g ∈ s, marked g) :
      ∃ a g t, s = a ++ g :: t ∧ marked g ∧ ∀ z ∈ t, ¬ marked z := by
    obtain ⟨a, g, t, eq, hg, ha⟩ := firstMark s.reverse (by simpa using ex)
    refine ⟨t.reverse, g, a.reverse, ?_, hg, by simpa using ha⟩
    simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse eq
  have negstep (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) (hg : marked g) :
      step w g = w ++ [!((g.inputs.head?.map (fun j => w.getD j false)).getD false)] := by
    change g.op = PEqualNP.CircuitLowerBounds.GateOp.not at hg
    rcases g with ⟨op, ins⟩
    change op = PEqualNP.CircuitLowerBounds.GateOp.not at hg
    subst op
    cases ins <;> rfl
  intro C hc hpin hf
  by_contra short
  obtain ⟨gs, o⟩ := C
  cases gs with
  | nil =>
    have h := hpin (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
    simp [List.getD_eq_getElem?_getD] at h
  | cons f rest =>
    have limit : rest.length ≤ 14 := by
      change ¬ 16 ≤ (f :: rest).length at short
      simp only [List.length_cons] at short
      omega
    have agree (x : Fin 9 → Bool) : (rest.foldl step (init x)).getD o false = F x := by
      let w := List.ofFn x
      let y := f.op.eval (f.inputs.map (fun i => w.getD i false))
      have h := hpin x
      change (rest.foldl step (w ++ [y])).getD 9 false = (x 0 || x 2) at h
      rw [preserved rest (w ++ [y]) 9 (by simp [w])] at h
      have last : (w ++ [y]).getD 9 false = y := by
        simp [w, List.getD_eq_getElem?_getD]
      have val := last.symm.trans h
      have e := congrFun hf x
      change (rest.foldl step (w ++ [y])).getD o false = F x at e
      simpa only [val, w, init] using e
    have fanpart (ls : List PEqualNP.CircuitLowerBounds.Gate) (incl : ∀ g ∈ ls, g ∈ rest) :
        PEqualNP.MetaComplexity.FanInTwo ⟨ls, o⟩ := fun g hg => hc g (List.mem_cons_of_mem f (incl g hg))
    have monopart (ls : List PEqualNP.CircuitLowerBounds.Gate) (incl : ∀ g ∈ ls, g ∈ rest)
        (none : ∀ g ∈ ls, ¬ marked g) : PEqualNP.MetaComplexity.Monotone2 ⟨ls, o⟩ := by
      intro g hg
      obtain ⟨hop, hsize⟩ := fanpart ls incl g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
      refine ⟨?_, hsize⟩
      rcases hop with ok | ok | bad
      · exact Or.inl ok
      · exact Or.inr ok
      · exact (none g hg bad).elim
    by_cases some : ∃ g ∈ rest, marked g
    · obtain ⟨a, n, t, split, hn, clean⟩ := lastMark rest some
      have hA := fanpart a (by intro g hg; simp [split, hg])
      have hQ := monopart t (by intro g hg; simp [split, hg]) clean
      have sz : a.length + t.length ≤ 13 := by simp [split] at limit; omega
      obtain ⟨x, bad⟩ := h3 ⟨a, o⟩ ⟨t, o⟩ n.inputs.head? hA hQ sz
      apply bad
      have e := agree x
      rw [split, List.foldl_append, List.foldl_cons, negstep _ n hn] at e
      exact e
    · have clean : ∀ g ∈ rest, ¬ marked g := by simpa using some
      have allmono := monopart rest (fun _ h => h) clean
      by_cases shared : ∃ a g t, rest = a ++ g :: t ∧
          2 ≤ (t.flatMap (fun k => k.inputs)).count (10 + a.length)
      · obtain ⟨a, g, t, eq, repeated⟩ := shared
        have hA := monopart a (by intro k hk; simp [eq, hk]) (by intro k hk; exact clean k (by simp [eq, hk]))
        have hQ := monopart t (by intro k hk; simp [eq, hk]) (by intro k hk; exact clean k (by simp [eq, hk]))
        obtain ⟨hop, hlen⟩ := allmono g (by simp [eq])
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        have sz : a.length + t.length ≤ 13 := by simp [eq] at limit; omega
        obtain ⟨r, b, hr, bad⟩ := h2 ⟨a, o⟩ ⟨t, o⟩ g hA hQ hop hlen sz repeated
        apply bad
        have e := (agree (fun i => r.testBit i.val)).trans (border r b hr)
        rw [eq, List.foldl_append, List.foldl_cons] at e
        exact e
      · have single (a : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (t : List PEqualNP.CircuitLowerBounds.Gate)
            (e : rest = a ++ g :: t) :
            (t.flatMap (fun k => k.inputs)).count (10 + a.length) ≤ 1 := by
          by_contra! h
          exact shared ⟨a, g, t, e, by omega⟩
        obtain ⟨r, b, hr, bad⟩ := h1 ⟨rest, o⟩ allmono limit single
        exact bad ((agree _).trans (border r b hr))

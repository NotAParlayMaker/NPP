import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3250_4
    (hclass : let w := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6];
    let f := fun x : Fin 9 → Bool => (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit (tableIndex x);
    let allowed := fun (v : Fin 9) (m : (Fin 9 → Bool) → Bool) =>
      (∀ x, m x = true) ∨ ∃ t ∈ ([(1,2,9),(4,0,3),(4,3,9),(7,2,5)] : List (ℕ × ℕ × ℕ)),
        v.val = t.1 ∧ ∀ x, m x = ((w x).getD t.2.1 false || (w x).getD t.2.2 false);
    ∀ (v : Fin 9) (g : Gate), v ≠ 0 → v ≠ 6 → v.val ∉ g.inputs →
      FanInTwo ⟨[g],0⟩ →
      let m := fun x : Fin 9 → Bool => g.op.eval (g.inputs.map (fun j => (w x).getD j false));
      (∀ x, x v = false → f x ≠ f (Function.update x v true) → m x = true) →
      allowed v m)
    (hand : let w := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6];
    let f := fun x : Fin 9 → Bool => (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit (tableIndex x);
    let allowed := fun (v : Fin 9) (m : (Fin 9 → Bool) → Bool) =>
      (∀ x, m x = true) ∨ ∃ t ∈ ([(1,2,9),(4,0,3),(4,3,9),(7,2,5)] : List (ℕ × ℕ × ℕ)),
        v.val = t.1 ∧ ∀ x, m x = ((w x).getD t.2.1 false || (w x).getD t.2.2 false);
    ∀ (v : Fin 9) (C : Circuit), v ≠ 0 → v ≠ 6 → FanInTwo C → C.size ≤ 13 →
      let m := fun x => (C.wires (w x)).getD 10 false;
      allowed v m → ∃ x, C.eval ((w x).set v.val (x v && m x)) ≠ f x)
    (hor : let w := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6];
    let f := fun x : Fin 9 → Bool => (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit (tableIndex x);
    ∀ (v : Fin 9) (C : Circuit), v ≠ 0 → v ≠ 6 → FanInTwo C → C.size ≤ 13 →
      (∀ g ∈ C.gates.take 1, v.val ∉ g.inputs) →
      let m := fun x => (C.wires (w x)).getD 10 false;
      (∀ x, x v = false → f x ≠ f (Function.update x v true) → m x = false) →
      ∃ x, C.eval ((w x).set v.val (x v || m x)) ≠ f x)
    (hlater : let w := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6];
    let f := fun x : Fin 9 → Bool => (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit (tableIndex x);
    ∀ (v : Fin 9) (C : Circuit) (j : ℕ) (b : Bool), v ≠ 0 → v ≠ 6 → FanInTwo C →
      C.size ≤ 13 → 10 < j → j < 10 + C.size →
      (∀ g ∈ C.gates.take (j - 9), v.val ∉ g.inputs) →
      let m := fun x => (C.wires (w x)).getD j false;
      (∀ x, x v = false → f x ≠ f (Function.update x v true) → m x = !b) →
      ∃ x, C.eval ((w x).set v.val (if b then x v || m x else x v && m x)) ≠ f x)
    : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) (x6 : Bool),   x2 ≠ (0 : Fin (9 : ℕ)) →     x2 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < x4 →               x4 ≤ (10 : ℕ) + x3.size →                 (∀ x14 ∈ List.take (x4 - (10 : ℕ)) x3.gates, ↑x2 ∉ x14.inputs) →                   (∀ (x15 : Fin (9 : ℕ) → Bool),                       have x16 : Fin (9 : ℕ) → Bool := Function.update x15 x2 Bool.false;                       x1 x16 ≠ x1 (Function.update x15 x2 Bool.true) → (x3.wires (List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))])).getD x5 Bool.false = !x6) →                     ∃ (x16 : Fin (9 : ℕ) → Bool),                       have x17 : List Bool := List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))];                       have x18 : Bool := (x3.wires x17).getD x5 Bool.false;                       x3.eval (x17.set (↑x2) (if x6 = Bool.true then x16 x2 || x18 else x16 x2 && x18)) ≠ x1 x16 := by
  classical
  intro graph v C cut i b v0 v6 fan small lo lt cap avoid sens
  let w := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
  let f := fun x : Fin 9 → Bool => (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit (tableIndex x)
  have graph_eq : ∀ x, graph x = f x := by decide +kernel
  let m (x : Fin 9 → Bool) := (C.wires (w x)).getD i false
  have sensitive (x : Fin 9 → Bool) (hx : x v = false) (diff : f x ≠ f (Function.update x v true)) :
      m x = !b := by
    have upd : Function.update x v false = x := by
      funext j
      by_cases h : j = v
      · subst j; simp [hx]
      · simp [Function.update_of_ne h]
    have h := sens x
    dsimp only at h
    rw [upd] at h
    exact h (by simpa only [graph_eq] using diff)
  have noRead (j : ℕ) (hj : j ≤ cut - 10) : ∀ g ∈ C.gates.take j, v.val ∉ g.inputs := by
    intro g hg
    apply avoid g
    have sub := List.take_prefix j (C.gates.take (cut - 10))
    rw [List.take_take, Nat.min_eq_left hj] at sub
    exact sub.subset hg
  by_cases first : i = 10
  · obtain ⟨g,gs,gates⟩ : ∃ g gs, C.gates = g :: gs := by
      cases h : C.gates with
      | nil => change cut ≤ 10 + C.gates.length at cap; rw [h] at cap; simp at cap; omega
      | cons g gs => exact ⟨g,gs,rfl⟩
    have noFirst := noRead 1 (by omega)
    have av : v.val ∉ g.inputs := noFirst g (by simp [gates])
    have val (x : Fin 9 → Bool) : m x = g.op.eval (g.inputs.map (fun j => (w x).getD j false)) := by
      let step (u : List Bool) (z : Gate) := u ++ [z.op.eval (z.inputs.map (fun j => u.getD j false))]
      have stable (ls : List Gate) (u : List Bool) (j : ℕ) (h : j < u.length) :
          (ls.foldl step u).getD j false = u.getD j false := by
        induction ls generalizing u with
        | nil => rfl
        | cons z ls ih =>
          rw [List.foldl_cons, ih (step u z) (by simp [step]; omega)]
          exact List.getD_append _ _ _ _ h
      change (C.gates.foldl step (w x)).getD i false = _
      rw [first, gates, List.foldl_cons, stable _ _ _ (by simp [step, w])]
      have ten : (w x).length = 10 := by simp [w]
      simp [step, List.getD_eq_getElem?_getD, ten]
    cases mode : b with
    | false =>
      have one : FanInTwo ⟨[g],0⟩ := by
        intro z hz
        have eq : z = g := by simpa using hz
        subst z
        exact fan g (by simp [gates])
      have spec := hclass v g v0 v6 av one (fun x hx hd => by
        exact (val x).symm.trans (by simpa only [mode, Bool.not_false] using sensitive x hx hd))
      have tenVal (x : Fin 9 → Bool) : (C.wires (w x)).getD 10 false = g.op.eval (g.inputs.map (fun j => (w x).getD j false)) := by
        simpa only [m,first] using val x
      have result := hand v C v0 v6 fan small (by
        rcases spec with same | ⟨t,ht,hv,values⟩
        · exact Or.inl (fun x => (tenVal x).trans (same x))
        · exact Or.inr ⟨t,ht,hv,fun x => (tenVal x).trans (values x)⟩)
      simpa [graph_eq, f, first] using result
    | true =>
      have result := hor v C v0 v6 fan small noFirst (fun x hx hd => by
        simpa only [m, first, mode, Bool.not_true] using sensitive x hx hd)
      simpa [graph_eq, f, first] using result
  · have result := hlater v C i b v0 v6 fan small (by omega) (by omega) (noRead _ (by omega)) sensitive
    simpa only [graph_eq] using result

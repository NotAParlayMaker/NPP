import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3306

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def flip (X Y : Finset ℕ) (g : Gate) : Prop :=
  g.op = .and ∧ g.inputs.headD 0 ∈ X ∧ (g.inputs.drop 1).headD 0 ∈ Y

noncomputable def orient (X Y : Finset ℕ) (g : Gate) : Gate := by
  classical
  exact ⟨g.op, if flip X Y g then g.inputs.reverse else g.inputs⟩

noncomputable def normal (X Y : Finset ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (orient X Y), C.output⟩

lemma default_gate (X Y : Finset ℕ) : orient X Y ⟨.or, []⟩ = ⟨.or, []⟩ := by
  simp [orient,flip]

lemma gate_at (X Y : Finset ℕ) (C : Circuit) (j : ℕ) :
    gateAt (normal X Y C) j = orient X Y (gateAt C j) := by
  unfold gateAt normal
  simpa only [default_gate] using
    (List.getD_map (l := C.gates) (n := j) (d := ⟨.or, []⟩) (orient X Y))

lemma membership (X Y : Finset ℕ) (g : Gate) (i : ℕ) :
    i ∈ (orient X Y g).inputs ↔ i ∈ g.inputs := by
  classical
  by_cases h : flip X Y g <;> simp [orient,h]

lemma arity (X Y : Finset ℕ) (g : Gate) :
    (orient X Y g).inputs.length = g.inputs.length := by
  classical
  by_cases h : flip X Y g <;> simp [orient,h]

lemma ao {n C} (X Y : Finset ℕ) (h : IsAO2 n C) : IsAO2 n (normal X Y C) := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact h.1 a ha
  · intro j hj i hi
    rw [gate_at, membership] at hi
    exact h.2.1 j (by simpa [normal] using hj) i hi
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact (arity X Y a).trans (h.2.2 a ha)

lemma value (X Y : Finset ℕ) (g : Gate) (v : ℕ → Bool) :
    (orient X Y g).op.eval ((orient X Y g).inputs.map v) = g.op.eval (g.inputs.map v) := by
  classical
  by_cases h : flip X Y g
  · simp [orient,h,h.1,GateOp.eval,List.map_reverse]
  · simp [orient,h]

lemma wires_same (X Y : Finset ℕ) (C : Circuit) (w : List Bool) :
    (normal X Y C).wires w = C.wires w := by
  cases C with
  | mk gs out =>
    unfold Circuit.wires normal
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [value]
      exact ih _

lemma or_same {X Y : Finset ℕ} {g : Gate} (h : g.op = .or) : orient X Y g = g := by
  cases g
  simp_all [orient,flip]

lemma and_order {X Y : Finset ℕ} (g : Gate) (h : g.op = .and) {u v : ℕ}
    (ins : g.inputs = [u,v]) (sides : (u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)) :
    ∃ a b, (orient X Y g).inputs = [a,b] ∧ a ∈ Y ∧ b ∈ X := by
  classical
  by_cases hv : u ∈ X ∧ v ∈ Y
  · exact ⟨v,u,by simp [orient,flip,h,ins,hv.1,hv.2],hv.2,hv.1⟩
  · obtain ⟨hu,hv'⟩ := sides.resolve_left hv
    exact ⟨u,v,by simp [orient,flip,h,ins,hv],hu,hv'⟩

end PEqualNP.Outside.L_meta_3306

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.Outside.L_meta_3306

theorem PEqualNP.Outside.L_meta_3306 : ∀ (n : ℕ) (C : Circuit) (X Y : Finset ℕ),
    IsAO2 n C →
    (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ u v, (gateAt C j).inputs = [u,v] ∧ (u ∈ X ∧ v ∈ Y ∨ u ∈ Y ∧ v ∈ X)) →
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
      (∀ j, (gateAt D j).op = (gateAt C j).op) ∧
      (∀ j, (gateAt C j).op = GateOp.or → gateAt D j = gateAt C j) ∧
      ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∃ a b, (gateAt D j).inputs = [a,b] ∧ a ∈ Y ∧ b ∈ X := by
  intro n C X Y hc pairs
  refine ⟨normal X Y C, ao X Y hc, by simp [normal,Circuit.size], ?_, ?_, ?_, ?_⟩
  · funext x
    exact congrArg (fun w : List Bool => w.getD C.output false) (wires_same X Y C (List.ofFn x))
  · intro j
    rw [gate_at]
    rfl
  · intro j h
    rw [gate_at]
    exact or_same h
  · intro j hj h
    rw [gate_at] at h ⊢
    obtain ⟨u,v,ins,sides⟩ := pairs j (by simpa [normal] using hj) h
    exact and_order _ h ins sides

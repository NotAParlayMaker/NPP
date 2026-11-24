import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3626

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isNonNot : GateOp → Bool
  | GateOp.not => false
  | _ => true

lemma isNonNot_eq_rec (op : GateOp) :
    isNonNot op = GateOp.rec true true false (fun _ => true) true op := by
  cases op <;> rfl

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def IsUnaryOrConst (n : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ b : Bool, ∀ u, f u = b) ∨ (∃ (i : Fin n) (b : Bool), ∀ u, f u = xor (u i) b)

lemma isUnaryOrConst_const (n : ℕ) (b : Bool) :
    IsUnaryOrConst n (fun _ => b) :=
  Or.inl ⟨b, fun _ => rfl⟩

lemma isUnaryOrConst_not {n : ℕ} {f : (Fin n → Bool) → Bool} (h : IsUnaryOrConst n f) :
    IsUnaryOrConst n (fun u => !f u) := by
  rcases h with ⟨b, hb⟩ | ⟨i, b, hb⟩
  · exact Or.inl ⟨!b, fun u => by simp [hb u]⟩
  · refine Or.inr ⟨i, !b, fun u => ?_⟩
    dsimp only
    rw [hb u]
    cases u i <;> cases b <;> rfl

lemma foldl_stepW_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma all_not_wires_unary {n : ℕ} (gs : List Gate) (hnot : ∀ g ∈ gs, g.op = GateOp.not)
    (init : (Fin n → Bool) → List Bool) (L : ℕ) (hlen : ∀ u, (init u).length = L)
    (hinit : ∀ k, IsUnaryOrConst n (fun u => (init u).getD k false)) :
    ∀ k, IsUnaryOrConst n (fun u => (gs.foldl stepW (init u)).getD k false) := by
  induction gs generalizing init L with
  | nil =>
    simpa using hinit
  | cons g gs ih =>
    have hg : g.op = GateOp.not := hnot g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.not :=
      fun g' hg' => hnot g' (List.mem_cons_of_mem g hg')
    have hnext_unary : IsUnaryOrConst n (fun u =>
        g.op.eval (g.inputs.map fun i => (init u).getD i false)) := by
      rw [hg]
      cases hins : g.inputs with
      | nil =>
        simpa [GateOp.eval] using isUnaryOrConst_const n true
      | cons j js =>
        simpa [GateOp.eval] using isUnaryOrConst_not (hinit j)
    apply ih hgs (fun u => stepW (init u) g) (L + 1)
    · intro u
      simp [stepW, hlen u]
    · intro k
      by_cases hk : k < L
      · have heq : (fun u => (stepW (init u) g).getD k false) =
            (fun u => (init u).getD k false) := by
          funext u
          simp only [stepW]
          exact List.getD_append (init u) _ false k (by rw [hlen u]; exact hk)
        rw [heq]
        exact hinit k
      · by_cases hkeq : k = L
        · have heq : (fun u => (stepW (init u) g).getD k false) =
              (fun u => g.op.eval (g.inputs.map fun i => (init u).getD i false)) := by
            funext u
            rw [hkeq]
            simp only [stepW]
            rw [← hlen u]
            simp
          rw [heq]
          exact hnext_unary
        · have heq : (fun u => (stepW (init u) g).getD k false) = (fun _ => false) := by
            funext u
            simp only [stepW, List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by simp [hlen u]; omega)]
            rfl
          rw [heq]
          exact isUnaryOrConst_const n false

lemma init_map_unary {n : ℕ} (xs : List (Fin n)) (k : ℕ) :
    IsUnaryOrConst n (fun u => (xs.map u).getD k false) := by
  by_cases hk : k < xs.length
  · refine Or.inr ⟨xs[k], false, fun u => ?_⟩
    simp [List.getD_eq_getElem?_getD, hk]
  · have heq : (fun u : Fin n → Bool => (xs.map u).getD k false) = (fun _ => false) := by
      funext u
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [heq]
    exact isUnaryOrConst_const n false

lemma op_eq_not_of_isNonNot_false {op : GateOp} (h : isNonNot op = false) :
    op = GateOp.not := by
  cases op <;> simp [isNonNot] at h ⊢

end PEqualNP.Outside.L_meta_3626

theorem PEqualNP.Outside.L_meta_3626 : have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates := by
  intro x1 x2 x3 x4 x5 _hfan x7 hdep hnonconst
  dsimp only [x7] at hdep hnonconst
  have hpos : 1 ≤ List.countP (fun g => PEqualNP.Outside.L_meta_3626.isNonNot g.op) x4.gates := by
    by_contra hlt
    have hzero : List.countP (fun g => PEqualNP.Outside.L_meta_3626.isNonNot g.op) x4.gates = 0 := by
      omega
    rw [List.countP_eq_zero] at hzero
    have hnot : ∀ g ∈ x4.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro g hg
      have hfalse : PEqualNP.Outside.L_meta_3626.isNonNot g.op = false := by
        cases hval : PEqualNP.Outside.L_meta_3626.isNonNot g.op
        · rfl
        · exact absurd hval (hzero g hg)
      exact PEqualNP.Outside.L_meta_3626.op_eq_not_of_isNonNot_false hfalse
    have hunary : PEqualNP.Outside.L_meta_3626.IsUnaryOrConst (x2 + 1)
        (fun u => x4.eval (List.map u x5)) := by
      exact PEqualNP.Outside.L_meta_3626.all_not_wires_unary x4.gates hnot
        (fun u => List.map u x5) x5.length (fun u => by simp)
        (PEqualNP.Outside.L_meta_3626.init_map_unary x5) x4.output
    rcases hunary with ⟨b, hb⟩ | ⟨i, b, hb⟩
    · dsimp only at hb
      obtain ⟨x8, hx8⟩ := hdep
      exact hx8 (by rw [hb, hb])
    · dsimp only at hb
      by_cases hi : i = x3
      · subst hi
        obtain ⟨x9, x10, hne⟩ := hnonconst
        apply hne
        rw [hb, hb, Fin.insertNth_apply_same, Fin.insertNth_apply_same]
      · obtain ⟨x8, hx8⟩ := hdep
        apply hx8
        rw [hb, hb, Function.update_of_ne hi, Function.update_of_ne hi]
  refine ⟨{ gates := [], output := 0 }, ?_, ?_⟩
  · intro g hg
    cases hg
  · dsimp only [x1]
    have heq : (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun _ => Bool.true) Bool.true g.op) =
        (fun g => PEqualNP.Outside.L_meta_3626.isNonNot g.op) := by
      funext g
      exact (PEqualNP.Outside.L_meta_3626.isNonNot_eq_rec g.op).symm
    simpa [heq] using hpos

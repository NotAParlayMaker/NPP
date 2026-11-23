import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_216

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def pre (C : Circuit) (j : ℕ) (x : List Bool) : List Bool :=
  (C.gates.take j).foldl step x

def bit (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) : Bool :=
  match C.gates[j]? with
  | some g => (pre C j (List.ofFn x)).getD (g.inputs.headD 0) false
  | none => false

def Inv (a b c : List Bool) : Prop :=
  ∀ i, a.getD i false = false → b.getD i false = false → c.getD i false = false

lemma length_foldl (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step]; omega

lemma getD_snoc (a : List Bool) (v : Bool) (i : ℕ) :
    (a ++ [v]).getD i false =
      if i < a.length then a.getD i false else if i = a.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp

lemma inv_snoc (a b c : List Bool) (hab : a.length = b.length) (hac : a.length = c.length)
    (h : Inv a b c) (va vb vc : Bool) (hv : va = false → vb = false → vc = false) :
    Inv (a ++ [va]) (b ++ [vb]) (c ++ [vc]) := by
  intro i
  rw [getD_snoc, getD_snoc, getD_snoc, ← hab, ← hac]
  split_ifs
  · exact h i
  · exact hv
  · intro _ _; rfl

lemma gate_ok (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hl : g.inputs.length ≤ 2) (a b c : List Bool) (h : Inv a b c)
    (hbit : g.op = GateOp.and → a.getD (g.inputs.headD 0) false = b.getD (g.inputs.headD 0) false) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = false →
      g.op.eval (g.inputs.map fun i => b.getD i false) = false →
        g.op.eval (g.inputs.map fun i => c.getD i false) = false := by
  obtain ⟨op, l⟩ := g
  simp only at hg hl hbit ⊢
  rcases hg with h1 | h1
  · subst h1
    simp only [forall_const] at hbit
    rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · simp [GateOp.eval]
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, id] at *
      exact h i
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, id, List.headD_cons] at *
      intro ha hb
      cases hai : a.getD i false
      · rw [hai] at hbit
        rw [h i hai hbit.symm]; rfl
      · rw [hai] at hbit ha
        rw [← hbit] at hb
        simp only [Bool.true_and] at ha hb
        rw [h j ha hb]; simp
    · simp at hl
  · subst h1
    simp only [GateOp.eval, List.any_eq_false, List.mem_map, id] at *
    intro ha hb x hx
    obtain ⟨i, hi, rfl⟩ := hx
    simpa using h i (by simpa using ha _ ⟨i, hi, rfl⟩) (by simpa using hb _ ⟨i, hi, rfl⟩)

lemma pre_succ (C : Circuit) (m : ℕ) (g : Gate) (hg : C.gates[m]? = some g) (x : List Bool) :
    pre C (m + 1) x = step (pre C m x) g := by
  unfold pre
  rw [List.take_add_one, hg]
  simp

lemma pre_length (C : Circuit) (m : ℕ) (hm : m ≤ C.gates.length) (x : List Bool) :
    (pre C m x).length = x.length + m := by
  unfold pre
  rw [length_foldl]
  simp [hm]

lemma main (n : ℕ) (C : Circuit)
    (hmono : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool)
    (hbits : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
      bit C n x j = bit C n x' j) :
    ∀ m, m ≤ C.gates.length →
      Inv (pre C m (List.ofFn x)) (pre C m (List.ofFn x'))
        (pre C m (List.ofFn (fun i => x i || x' i))) := by
  intro m
  induction m with
  | zero =>
    intro _ i
    simp only [pre, List.take_zero, List.foldl_nil]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases hi : i < n
    · simp [hi]
      intro h1 h2
      simp [h1, h2]
    · simp [hi]
  | succ m ih =>
    intro hm
    have hlt : m < C.gates.length := by omega
    have hg : C.gates[m]? = some C.gates[m] := List.getElem?_eq_getElem hlt
    rw [pre_succ C m _ hg, pre_succ C m _ hg, pre_succ C m _ hg]
    have hI := ih (by omega)
    have hmem : C.gates[m] ∈ C.gates := List.getElem_mem hlt
    obtain ⟨hop, hl⟩ := hmono _ hmem
    have hop' : C.gates[m].op = GateOp.and ∨ C.gates[m].op = GateOp.or := by
      simpa using hop
    apply inv_snoc
    · rw [pre_length C m (by omega), pre_length C m (by omega)]; simp
    · rw [pre_length C m (by omega), pre_length C m (by omega)]; simp
    · exact hI
    · apply gate_ok _ hop' hl _ _ _ hI
      intro hand
      have := hbits m _ hg hand
      simp only [bit, hg] at this
      exact this

end PEqualNP.Outside.L_meta_216

theorem PEqualNP.Outside.L_meta_216 : ∀ (n k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → (∃ A : Finset ℕ, A.card ≤ k ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → {x : Fin n → Bool | C.eval (List.ofFn x) = false ∧ ∀ y : Fin n → Bool, (∀ i : Fin n, x i = true → y i = true) → C.eval (List.ofFn y) = false → y = x}.ncard ≤ 2 ^ k := by
  intro n k C hmono hA
  obtain ⟨A, hAk, hAnd⟩ := hA
  let φ : (Fin n → Bool) → (A → Bool) := fun x j => PEqualNP.Outside.L_meta_216.bit C n x j
  have key : ∀ x x' : Fin n → Bool, φ x = φ x' →
      C.eval (List.ofFn x) = false → C.eval (List.ofFn x') = false →
        C.eval (List.ofFn (fun i => x i || x' i)) = false := by
    intro x x' hφ h1 h2
    have hbits : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.Outside.L_meta_216.bit C n x j = PEqualNP.Outside.L_meta_216.bit C n x' j := by
      intro j g hg hand
      exact congrFun hφ ⟨j, hAnd j g hg hand⟩
    have hI := PEqualNP.Outside.L_meta_216.main n C hmono x x' hbits C.gates.length le_rfl
    have hw : ∀ z : List Bool,
        PEqualNP.Outside.L_meta_216.pre C C.gates.length z = C.wires z := by
      intro z
      simp only [PEqualNP.Outside.L_meta_216.pre, List.take_length]
      rfl
    rw [hw, hw, hw] at hI
    exact hI C.output h1 h2
  calc _ ≤ (Set.univ : Set (A → Bool)).ncard := by
        apply Set.ncard_le_ncard_of_injOn φ (fun _ _ => Set.mem_univ _) _ (Set.toFinite _)
        intro x hx x' hx' hxx
        simp only [Set.mem_ofPred_eq] at hx hx'
        have hy := key x x' hxx hx.1 hx'.1
        have e1 := hx.2 _ (fun i h => by simp [h]) hy
        have e2 := hx'.2 _ (fun i h => by simp [h]) hy
        exact e1.symm.trans e2
    _ = 2 ^ A.card := by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_coe]
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hAk

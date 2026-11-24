import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4968_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wire values of a gate list, as in Circuit.wires.
def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp only [W, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc_lt {α : Type} (l : List α) (v d : α) (i : ℕ) (h : i < l.length) :
    (l ++ [v]).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq {α : Type} (l : List α) (v d : α) (i : ℕ) (h : i = l.length) :
    (l ++ [v]).getD i d = v := by
  subst h
  simp [List.getD_eq_getElem?_getD]

theorem W_prefix (gs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, getD_snoc_lt _ _ _ _ (by rw [W_length]; omega), ih]

theorem key {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    (W gs (List.ofFn x)).getD (p : ℕ) false = x p := by
  have h := p.isLt
  rw [W_prefix _ _ _ (by simp), List.getD_eq_getElem?_getD]
  simp [h]

theorem or2 (u v : Bool) : GateOp.or.eval [u, v] = (u || v) := by simp [GateOp.eval]

theorem and2 (u v : Bool) : GateOp.and.eval [u, v] = (u && v) := by simp [GateOp.eval]

theorem base (n : ℕ) (C : Circuit) (a b : ℕ) (hC : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.gates.length = C.gates.length + 1 ∧
      D.output + 1 = n + D.gates.length ∧
      ∀ x : List Bool, x.length = n →
        (∀ i < n + C.gates.length, (W D.gates x).getD i false = (W C.gates x).getD i false) ∧
        (W D.gates x).getD D.output false =
          ((W C.gates x).getD a false && (W C.gates x).getD b false) := by
  refine ⟨⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.gates.length⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC g hg
    · constructor <;> simp
  · simp
  · simp
    omega
  · intro x hx
    have hlen : (W C.gates x).length = n + C.gates.length := by rw [W_length, hx]
    constructor
    · intro i hi
      show (W (C.gates ++ [⟨GateOp.and, [a, b]⟩]) x).getD i false = _
      rw [W_snoc, getD_snoc_lt _ _ _ _ (by rw [hlen]; exact hi)]
    · show (W (C.gates ++ [⟨GateOp.and, [a, b]⟩]) x).getD (n + C.gates.length) false = _
      rw [W_snoc, getD_snoc_eq _ _ _ _ hlen.symm]
      simp only [List.map_cons, List.map_nil, and2]

theorem step (n : ℕ) (C : Circuit) (a b : ℕ) (hC : Monotone2 C)
    (hout : C.output + 1 = n + C.gates.length) :
    ∃ D : Circuit, Monotone2 D ∧ D.gates.length = C.gates.length + 2 ∧
      D.output + 1 = n + D.gates.length ∧
      ∀ x : List Bool, x.length = n →
        (∀ i < n + C.gates.length, (W D.gates x).getD i false = (W C.gates x).getD i false) ∧
        (W D.gates x).getD D.output false =
          ((W C.gates x).getD C.output false ||
            ((W C.gates x).getD a false && (W C.gates x).getD b false)) := by
  refine ⟨⟨C.gates ++ [⟨GateOp.and, [a, b]⟩] ++ [⟨GateOp.or, [C.output, n + C.gates.length]⟩],
    n + C.gates.length + 1⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | rfl) | rfl
    · exact hC g hg
    · constructor <;> simp
    · constructor <;> simp
  · simp
  · simp
    omega
  · intro x hx
    have hlen : (W C.gates x).length = n + C.gates.length := by rw [W_length, hx]
    constructor
    · intro i hi
      show (W (C.gates ++ [⟨GateOp.and, [a, b]⟩] ++
        [⟨GateOp.or, [C.output, n + C.gates.length]⟩]) x).getD i false = _
      rw [W_snoc, W_snoc, getD_snoc_lt _ _ _ _ (by simp [hlen]; omega),
        getD_snoc_lt _ _ _ _ (by rw [hlen]; exact hi)]
    · show (W (C.gates ++ [⟨GateOp.and, [a, b]⟩] ++
        [⟨GateOp.or, [C.output, n + C.gates.length]⟩]) x).getD (n + C.gates.length + 1) false = _
      rw [W_snoc, W_snoc, getD_snoc_eq _ _ _ _ (by simp [hlen])]
      simp only [List.map_cons, List.map_nil, and2, or2]
      rw [getD_snoc_lt _ _ _ _ (by rw [hlen]; omega), getD_snoc_eq _ _ _ _ hlen.symm]

theorem main (n : ℕ) (C : Circuit) (hC : Monotone2 C) :
    ∀ (m : ℕ) (a b : Fin (m + 1) → ℕ), (∀ k, a k < n + C.gates.length) →
      (∀ k, b k < n + C.gates.length) →
      ∃ D : Circuit, Monotone2 D ∧ D.gates.length = C.gates.length + 2 * m + 1 ∧
        D.output + 1 = n + D.gates.length ∧
        ∀ x : List Bool, x.length = n →
          (∀ i < n + C.gates.length, (W D.gates x).getD i false = (W C.gates x).getD i false) ∧
          ((W D.gates x).getD D.output false = true ↔
            ∃ k, (W C.gates x).getD (a k) false = true ∧ (W C.gates x).getD (b k) false = true) := by
  intro m
  induction m with
  | zero =>
    intro a b _ _
    obtain ⟨D, hDm, hDs, hDo, hD⟩ := base n C (a 0) (b 0) hC
    refine ⟨D, hDm, by omega, hDo, ?_⟩
    intro x hx
    obtain ⟨h1, h2⟩ := hD x hx
    refine ⟨h1, ?_⟩
    rw [h2, Bool.and_eq_true]
    constructor
    · intro h
      exact ⟨0, h⟩
    · rintro ⟨⟨k, hk'⟩, hk⟩
      have hk0 : k = 0 := by omega
      subst hk0
      exact hk
  | succ m ih =>
    intro a b ha hb
    obtain ⟨D, hDm, hDs, hDo, hD⟩ :=
      ih (fun k => a k.castSucc) (fun k => b k.castSucc) (fun k => ha _) (fun k => hb _)
    obtain ⟨E, hEm, hEs, hEo, hE⟩ := step n D (a (Fin.last _)) (b (Fin.last _)) hDm hDo
    refine ⟨E, hEm, by omega, hEo, ?_⟩
    intro x hx
    obtain ⟨hD1, hD2⟩ := hD x hx
    obtain ⟨hE1, hE2⟩ := hE x hx
    constructor
    · intro i hi
      rw [hE1 i (by omega), hD1 i hi]
    · rw [hE2, Bool.or_eq_true, Bool.and_eq_true, hD1 (a (Fin.last _)) (ha _),
        hD1 (b (Fin.last _)) (hb _)]
      constructor
      · rintro (h | h)
        · obtain ⟨k, hk⟩ := hD2.mp h
          exact ⟨k.castSucc, hk⟩
        · exact ⟨Fin.last _, h⟩
      · rintro ⟨k, hk⟩
        rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
        · exact Or.inl (hD2.mpr ⟨j, hk⟩)
        · exact Or.inr hk

end PEqualNP.Outside.L_meta_4968_aux

theorem PEqualNP.Outside.L_meta_4968 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (x2 + (1 : ℕ)) → Fin x1) (x5 : Fin (x2 + (1 : ℕ)) → ℕ), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin (x2 + (1 : ℕ))), x5 x7 < x1 + x3.size) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size = x3.size + (2 : ℕ) * x2 + (1 : ℕ) ∧ x8.output < x1 + x8.size ∧ (∀ (x9 : Fin x1 → Bool), ∀ x10 < x1 + x3.size, (x8.wires (List.ofFn x9)).getD x10 Bool.false = (x3.wires (List.ofFn x9)).getD x10 Bool.false) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin (x2 + (1 : ℕ))), x9 (x4 x10) = Bool.true ∧ (x3.wires (List.ofFn x9)).getD (x5 x10) Bool.false = Bool.true := by
  intro n m C x4 x5 hC hb
  obtain ⟨D, hDm, hDs, hDo, hD⟩ := PEqualNP.Outside.L_meta_4968_aux.main n C hC m
    (fun k => (x4 k : ℕ)) x5 (fun k => by have := (x4 k).isLt; omega) hb
  refine ⟨D, hDm, hDs, ?_, ?_, ?_⟩
  · show D.output < n + D.gates.length
    omega
  · intro x9 i hi
    exact (hD (List.ofFn x9) (by simp)).1 i hi
  · intro x9
    obtain ⟨h1, h2⟩ := hD (List.ofFn x9) (by simp)
    constructor
    · intro h
      obtain ⟨k, hk1, hk2⟩ := h2.mp h
      have hk1' : (PEqualNP.Outside.L_meta_4968_aux.W C.gates (List.ofFn x9)).getD (x4 k : ℕ) false
          = true := hk1
      rw [PEqualNP.Outside.L_meta_4968_aux.key] at hk1'
      exact ⟨k, hk1', hk2⟩
    · rintro ⟨k, hk1, hk2⟩
      refine h2.mpr ⟨k, ?_, hk2⟩
      show (PEqualNP.Outside.L_meta_4968_aux.W C.gates (List.ofFn x9)).getD (x4 k : ℕ) false = true
      rw [PEqualNP.Outside.L_meta_4968_aux.key]
      exact hk1

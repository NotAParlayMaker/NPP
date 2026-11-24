import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4671_aux

open PEqualNP.CircuitLowerBounds

def rm (n m : ℕ) (f : Fin n → Fin m) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i, h⟩ : ℕ) else m + (i - n)

def mg (n m : ℕ) (f : Fin n → Fin m) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rm n m f)⟩

def st (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Inv (n m : ℕ) (f : Fin n → Fin m) (k : ℕ) (w4 w9 : List Bool) : Prop :=
  w4.length = n + k ∧ w9.length = m + k ∧ ∀ i, w9.getD (rm n m f i) false = w4.getD i false

theorem rm_lt {n m : ℕ} (f : Fin n → Fin m) {k i : ℕ} (h : i < n + k) : rm n m f i < m + k := by
  unfold rm
  split
  · have := (f ⟨i, by assumption⟩).isLt
    omega
  · omega

theorem rm_eq {n m : ℕ} (f : Fin n → Fin m) (k : ℕ) : rm n m f (n + k) = m + k := by
  unfold rm
  split
  · omega
  · omega

theorem rm_ge {n m : ℕ} (f : Fin n → Fin m) {k i : ℕ} (h : n + k < i) : m + k < rm n m f i := by
  unfold rm
  split
  · omega
  · omega

theorem inv_step {n m : ℕ} (f : Fin n → Fin m) {k : ℕ} {w4 w9 : List Bool}
    (h : Inv n m f k w4 w9) (g : Gate) : Inv n m f (k + 1) (st w4 g) (st w9 (mg n m f g)) := by
  obtain ⟨h4, h9, hv⟩ := h
  have hval : (mg n m f g).op.eval ((mg n m f g).inputs.map fun i => w9.getD i false) =
      g.op.eval (g.inputs.map fun i => w4.getD i false) := by
    simp only [mg, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hv i
  refine ⟨by simp [st, h4]; omega, by simp [st, h9]; omega, ?_⟩
  intro i
  unfold st
  rw [hval]
  rcases lt_trichotomy i (n + k) with hi | hi | hi
  · have hr := rm_lt f hi
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    exact hv i
  · subst hi
    rw [rm_eq f k, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    simp [h4, h9]
  · have hr := rm_ge f hi
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem inv_fold {n m : ℕ} (f : Fin n → Fin m) :
    ∀ (gs : List Gate) (k : ℕ) (w4 w9 : List Bool), Inv n m f k w4 w9 →
      Inv n m f (k + gs.length) (gs.foldl st w4) ((gs.map (mg n m f)).foldl st w9)
  | [], k, w4, w9, h => by simpa using h
  | g :: gs, k, w4, w9, h => by
    have := inv_fold f gs (k + 1) (st w4 g) (st w9 (mg n m f g)) (inv_step f h g)
    simp only [List.foldl_cons, List.map_cons, List.length_cons]
    rw [show k + (gs.length + 1) = k + 1 + gs.length by omega]
    exact this

theorem inv_init {n m : ℕ} (f : Fin n → Fin m) (x : Fin m → Bool) :
    Inv n m f 0 (List.ofFn (x ∘ f)) (List.ofFn x) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases hi : i < n
  · have hr : rm n m f i = (f ⟨i, hi⟩ : ℕ) := by simp [rm, hi]
    rw [hr]
    simp [List.getD_eq_getElem?_getD, hi]
  · have hr : rm n m f i = m + (i - n) := by simp [rm, hi]
    rw [hr, List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_4671_aux

open PEqualNP.Outside.L_meta_4671_aux

theorem PEqualNP.Outside.L_meta_4671 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 + x4.size → x5 < x1 + x4.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size = x4.size ∧ x9.output < x2 + x9.size ∧ x10 < x2 + x9.size ∧ ∀ (x11 : Fin x2 → Bool), x9.eval (List.ofFn x11) = x4.eval (List.ofFn (x11 ∘ x3)) ∧ (x9.wires (List.ofFn x11)).getD x10 Bool.false = (x4.wires (List.ofFn (x11 ∘ x3))).getD x5 Bool.false := by
  intro n m f C x5 hC hout hx5
  refine ⟨⟨C.gates.map (mg n m f), rm n m f C.output⟩, rm n m f x5, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2⟩ := hC g0 hg0
    exact ⟨h1, by simpa [mg] using h2⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · have := rm_lt f (k := C.gates.length) hout
    simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using this
  · have := rm_lt f (k := C.gates.length) hx5
    simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using this
  · intro x
    have hI := inv_fold f C.gates 0 _ _ (inv_init f x)
    have hw : ∀ i, ((⟨C.gates.map (mg n m f), rm n m f C.output⟩ :
        PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (rm n m f i) false =
        (C.wires (List.ofFn (x ∘ f))).getD i false := by
      intro i
      exact hI.2.2 i
    exact ⟨hw C.output, hw x5⟩

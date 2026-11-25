import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9018
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

def rhoW (N p c L : ℕ) (w : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < L then (if w i < N + p then w i else N + p + c) else i - L + (N + p)

def rgW (N p c L : ℕ) (w : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rhoW N p c L w)⟩

theorem keyW (N p c L : ℕ) (w : ℕ → ℕ) (u xa G : List Bool) (hu : u.length = L) (hxa : xa.length = N + p)
    (hG : G.length ≤ c) (hw : ∀ i, i < L → xa.getD (w i) false = u.getD i false) (i : ℕ) :
    (u ++ G).getD i false = (xa ++ G).getD (rhoW N p c L w i) false := by
  unfold rhoW
  by_cases hi : i < L
  · rw [if_pos hi, List.getD_append _ _ _ _ (by omega)]
    by_cases hwi : w i < N + p
    · rw [if_pos hwi, List.getD_append _ _ _ _ (by omega)]
      exact (hw i hi).symm
    · rw [if_neg hwi, ← hw i hi, List.getD_eq_default xa _ (by omega),
        List.getD_eq_default (xa ++ G) _ (by rw [List.length_append]; omega)]
  · rw [if_neg hi, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

theorem simW (N p c L : ℕ) (w : ℕ → ℕ) (u xa : List Bool) (hu : u.length = L) (hxa : xa.length = N + p)
    (hw : ∀ i, i < L → xa.getD (w i) false = u.getD i false) : ∀ (gs : List Gate) (G : List Bool),
    G.length + gs.length ≤ c →
    ∃ G' : List Bool, G'.length = G.length + gs.length ∧ wf gs (u ++ G) = u ++ G' ∧
      wf (gs.map (rgW N p c L w)) (xa ++ G) = xa ++ G' := by
  intro gs
  induction gs with
  | nil => intro G _; exact ⟨G, rfl, rfl, rfl⟩
  | cons g gs ih =>
    intro G hG
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : (rgW N p c L w g).op.eval ((rgW N p c L w g).inputs.map fun i => (xa ++ G).getD i false)
        = g.op.eval (g.inputs.map fun i => (u ++ G).getD i false) := by
      show g.op.eval ((g.inputs.map (rhoW N p c L w)).map fun i => (xa ++ G).getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact (keyW N p c L w u xa G hu hxa (by simp at hG; omega) hw a).symm
    rw [hv, List.append_assoc u G, List.append_assoc xa G]
    obtain ⟨G', h1, h2, h3⟩ := ih (G ++ [g.op.eval (g.inputs.map fun i => (u ++ G).getD i false)])
      (by simp at hG ⊢; omega)
    exact ⟨G', by simp at h1 ⊢; omega, h2, h3⟩

theorem wf_ext : ∀ (gs : List Gate) (U : List Bool), ∃ A : List Bool, wf gs U = U ++ A ∧ A.length = gs.length := by
  intro gs
  induction gs with
  | nil => intro U; exact ⟨[], by simp [wf], rfl⟩
  | cons g gs ih =>
    intro U
    rw [wf_cons]
    obtain ⟨A, h1, h2⟩ := ih (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
    exact ⟨g.op.eval (g.inputs.map fun i => U.getD i false) :: A,
      by rw [h1, List.append_assoc]; rfl, by simp [h2]⟩

end PEqualNP.Outside.L_meta_9018

open PEqualNP.Outside.L_meta_9018 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9018 : ∀ (N L : ℕ) (D : Set (List Bool)) (P : List PEqualNP.CircuitLowerBounds.Gate) (w : Fin L → ℕ) (g : Fin L → List Bool → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ x ∈ D, x.length = N) → PEqualNP.MetaComplexity.Monotone2 (⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x ∈ D, ∀ j, ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (w j) false = g j x) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size ≤ P.length + C.size ∧ ∀ x ∈ D, C'.eval x = C.eval (List.ofFn fun j => g j x) := by
  intro N L D P w g C hD hP hC hg
  refine ⟨⟨P ++ C.gates.map (rgW N P.length C.gates.length L (fun i => if h : i < L then w ⟨i, h⟩ else 0)),
    rhoW N P.length C.gates.length L (fun i => if h : i < L then w ⟨i, h⟩ else 0) C.output⟩, ?_, ?_, fun x hx => ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hP g' h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hC g0 hg0
      exact ⟨this.1, by simpa [rgW] using this.2⟩
  · show (P ++ C.gates.map _).length ≤ P.length + C.gates.length
    simp
  · have hxl := hD x hx
    obtain ⟨A, hA1, hA2⟩ := wf_ext P x
    have hu : (List.ofFn fun j => g j x).length = L := by simp
    have hwv : ∀ i, i < L → (x ++ A).getD ((fun i => if h : i < L then w ⟨i, h⟩ else 0) i) false
        = (List.ofFn fun j => g j x).getD i false := by
      intro i hi
      have e := getD_ofFn (fun j => g j x) ⟨i, hi⟩
      simp only at e
      rw [e]
      simp only [dif_pos hi]
      rw [← hA1]
      exact hg x hx ⟨i, hi⟩
    obtain ⟨G', h1, h2, h3⟩ := simW N P.length C.gates.length L _ (List.ofFn fun j => g j x) (x ++ A) hu
      (by simp; omega) hwv C.gates [] (by simp)
    rw [List.append_nil] at h2 h3
    show (wf (P ++ C.gates.map _) x).getD _ false = (wf C.gates (List.ofFn fun j => g j x)).getD C.output false
    rw [wf_append, hA1, h3, h2]
    exact (keyW N P.length C.gates.length L _ (List.ofFn fun j => g j x) (x ++ A) G' hu (by simp; omega)
      (by simp at h1; omega) hwv C.output).symm

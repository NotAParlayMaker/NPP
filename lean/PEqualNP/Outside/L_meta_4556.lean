import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4556_aux

-- The omitted input is sent to an unavailable wire. All subsequent wires shift down one.
def rho (i : ℕ) : ℕ := if i < 9 then i else if i = 9 then 100 else i - 1

def rename (g : Gate) : Gate := ⟨g.op, g.inputs.map rho⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma lookup_append (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : i = w.length
    · simp [he]
    · rw [ite_eq_right he, List.getD_eq_default _ false (by simp; omega),
        List.getD_eq_default _ false (by omega)]

lemma extend (v w : List Bool) (b : Bool)
    (hlen : w.length = v.length + 1) (hlo : 10 ≤ v.length) (hhi : v.length < 100)
    (h : ∀ i, v.getD (rho i) false = w.getD i false) :
    ∀ i, (v ++ [b]).getD (rho i) false = (w ++ [b]).getD i false := by
  intro i
  rw [lookup_append, lookup_append, h]
  have he : rho i = v.length ↔ i = w.length := by
    unfold rho
    split_ifs <;> omega
  simp only [he]

lemma simulate (gs : List Gate) (v w : List Bool)
    (hlen : w.length = v.length + 1) (hlo : 10 ≤ v.length)
    (hhi : v.length + gs.length < 100)
    (h : ∀ i, v.getD (rho i) false = w.getD i false) :
    ∀ i, (run (gs.map rename) v).getD (rho i) false = (run gs w).getD i false := by
  induction gs generalizing v w with
  | nil => exact h
  | cons g gs ih =>
    have hv : (rename g).op.eval ((rename g).inputs.map fun i => v.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [rename, List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => h i)
    simp only [List.map_cons, run, List.foldl_cons]
    rw [hv]
    apply ih
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_cons] at hhi
      simp only [List.length_append, List.length_singleton]; omega
    · exact extend v w _ hlen hlo (by omega) h

lemma initial (x : Fin 10 → Bool) :
    ∀ i, (List.ofFn x).getD (rho i) false =
      (List.ofFn (Fin.init x) ++ [false, x 9]).getD i false := by
  intro i
  by_cases hi : i < 11
  · interval_cases i <;> simp [rho, List.ofFn_succ, Fin.init]
  · have hr : 10 ≤ rho i := by
      unfold rho
      split_ifs <;> omega
    rw [List.getD_eq_default _ false (by simpa using hr),
      List.getD_eq_default _ false (by simp; omega)]

end PEqualNP.Outside.L_meta_4556_aux

open PEqualNP.Outside.L_meta_4556_aux

theorem PEqualNP.Outside.L_meta_4556 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) (fun (x4 : Fin (10 : ℕ) → Bool) => x1.eval (List.ofFn (Fin.init x4) ++ [Bool.false, x4 (9 : Fin (10 : ℕ))])) (13 : ℕ) := by
  intro C hf hs
  refine ⟨⟨C.gates.map rename, rho C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa [rename] using hf g' hg'
  · simpa [Circuit.size] using hs
  · intro x
    apply simulate C.gates (List.ofFn x) (List.ofFn (Fin.init x) ++ [false, x 9])
    · simp
    · simp
    · have hh : C.gates.length ≤ 13 := hs
      simp only [List.length_ofFn]; omega
    · exact initial x

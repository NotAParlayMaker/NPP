import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1354_aux

open PEqualNP.CircuitLowerBounds

def renameWire (n total i : ℕ) : ℕ :=
  if i < n then i else if i = n then n + total else i - 1

def renameGate (n total : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renameWire n total)⟩

def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [gateValue w g]) w

lemma renamed_read (n total : ℕ) (x v : List Bool) (hx : x.length = n)
    (hv : v.length ≤ total) (i : ℕ) :
    (x ++ v).getD (renameWire n total i) false = (x ++ false :: v).getD i false := by
  by_cases hi : i < n
  · simp only [renameWire, ite_eq_left hi]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · by_cases he : i = n
    · subst i
      simp only [renameWire, Nat.lt_irrefl, ite_false, ite_true]
      rw [List.getD_eq_default _ _ (by simp; omega)]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [hx]
    · simp only [renameWire, ite_eq_right hi, ite_eq_right he]
      rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      have hidx : i - x.length = (i - 1 - x.length) + 1 := by omega
      rw [hidx, List.getD_cons_succ]

lemma renamed_value (n total : ℕ) (x v : List Bool) (hx : x.length = n)
    (hv : v.length ≤ total) (g : Gate) :
    gateValue (x ++ v) (renameGate n total g) = gateValue (x ++ false :: v) g := by
  unfold gateValue renameGate
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact renamed_read n total x v hx hv i

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [gateValue w g]) := rfl

lemma run_rename (n total : ℕ) (gs : List Gate) (x v : List Bool)
    (hx : x.length = n) (hlen : v.length + gs.length ≤ total) :
    ∃ r : List Bool, r.length = v.length + gs.length ∧
      run (gs.map (renameGate n total)) (x ++ v) = x ++ r ∧
      run gs (x ++ false :: v) = x ++ false :: r := by
  induction gs generalizing v with
  | nil => exact ⟨v, by simp, rfl, rfl⟩
  | cons g gs ih =>
    let z := gateValue (x ++ false :: v) g
    obtain ⟨r, hrlen, hrnew, hrold⟩ := ih (v ++ [z]) (by simp at hlen ⊢; omega)
    refine ⟨r, ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrlen
    · rw [List.map_cons, run_cons, renamed_value n total x v hx (by simp at hlen; omega)]
      simpa only [List.append_assoc] using hrnew
    · rw [run_cons]
      simpa only [List.append_assoc, List.cons_append] using hrold

theorem restriction (n : ℕ) (gates : List Gate) :
    ∃ gates' : List Gate,
      gates'.map Gate.op = gates.map Gate.op ∧
      gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧
      ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length →
        Circuit.eval ⟨gates', n+j⟩ (List.ofFn x) =
          Circuit.eval ⟨gates, n+1+j⟩ (List.ofFn x ++ [false]) := by
  refine ⟨gates.map (renameGate n gates.length), ?_, ?_, ?_⟩
  · simp [renameGate, List.map_map, Function.comp_def]
  · simp [renameGate, List.map_map, Function.comp_def]
  · intro j x hj
    obtain ⟨r, hrlen, hrnew, hrold⟩ :=
      run_rename n gates.length gates (List.ofFn x) [] (by simp) (by simp)
    simp only [List.append_nil] at hrnew hrold
    change (run (gates.map (renameGate n gates.length)) (List.ofFn x)).getD (n+j) false =
      (run gates (List.ofFn x ++ [false])).getD (n+1+j) false
    rw [hrnew, hrold]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega),
      List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    simp only [List.length_ofFn]
    have h1 : n+j-n = j := by omega
    have h2 : n+1+j-n = j+1 := by omega
    rw [h1, h2, List.getD_cons_succ]

end PEqualNP.Outside.L_meta_1354_aux

theorem PEqualNP.Outside.L_meta_1354 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) :=
  PEqualNP.Outside.L_meta_1354_aux.restriction

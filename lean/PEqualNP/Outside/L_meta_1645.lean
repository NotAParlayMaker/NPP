import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1645

open PEqualNP.CircuitLowerBounds

def Allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def gateValue (values : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun w => values.getD w false)

def appendGate (values : List Bool) (g : Gate) : List Bool :=
  values ++ [gateValue values g]

def run (gates : List Gate) (values : List Bool) : List Bool :=
  gates.foldl appendGate values

def Below (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ w, x.getD w false = true → y.getD w false = true

theorem gateValue_pos (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (a b : List Bool) (h : Below a b) :
    gateValue a g = true → gateValue b g = true := by
  unfold gateValue
  rcases hop with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro ha w hw
    exact h.2 w (ha w hw)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨w, hw, ha⟩
    exact ⟨w, hw, h.2 w ha⟩

theorem appendGate_below {a b : List Bool} (h : Below a b) (g : Gate)
    (hg : gateValue a g = true → gateValue b g = true) :
    Below (appendGate a g) (appendGate b g) := by
  refine ⟨by simp [appendGate, h.1], ?_⟩
  intro w
  unfold appendGate
  by_cases hw : w < a.length
  · have hwb : w < b.length := h.1 ▸ hw
    rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hwb]
    exact h.2 w
  · have ha := Nat.le_of_not_gt hw
    have hb : b.length ≤ w := h.1 ▸ ha
    rw [List.getD_append_right _ _ _ _ ha, List.getD_append_right _ _ _ _ hb, h.1]
    cases he : w - b.length with
    | zero => simpa using hg
    | succ k => simp

theorem initial_below {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    Below (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro w
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rename_i hw
    simpa using h ⟨w, hw⟩
  · simp

theorem run_cons (g : Gate) (gs : List Gate) (a : List Bool) :
    run (g :: gs) a = run gs (appendGate a g) := rfl

theorem run_keeps (gs : List Gate) (a : List Bool) {w : ℕ} (h : w < a.length) :
    (run gs a).getD w false = a.getD w false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp [appendGate]; omega), appendGate, List.getD_append _ _ _ _ h]

theorem run_length (gs : List Gate) (a : List Bool) :
    (run gs a).length = a.length + gs.length := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih]
    simp [appendGate]
    omega

theorem run_append (l1 l2 : List Gate) (a : List Bool) :
    run (l1 ++ l2) a = run l2 (run l1 a) := by
  simp [run, List.foldl_append]

theorem next_index (g : Gate) (gs : List Gate) (a : List Bool) (j : ℕ) :
    (run gs (appendGate a g)).getD ((appendGate a g).length + j) false =
      (run (g :: gs) a).getD (a.length + (j + 1)) false := by
  congr 1
  simp [appendGate]
  omega

theorem value_first (g : Gate) (gs : List Gate) (a : List Bool) :
    (run (g :: gs) a).getD a.length false = gateValue a g := by
  rw [run_cons, run_keeps _ _ (by simp [appendGate]), appendGate]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl a.length)]
  simp

def AgreesNot (gs : List Gate) (a b : List Bool) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = .not →
    (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false

theorem AgreesNot.tail {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) :
    AgreesNot gs (appendGate a g) (appendGate b g) := by
  intro j q hj hq
  rw [next_index, next_index]
  exact h (j+1) q (by simpa using hj) hq

theorem AgreesNot.first {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) (hg : g.op = .not) :
    gateValue a g = gateValue b g := by
  have h0 := h 0 g rfl hg
  simpa only [Nat.add_zero, value_first] using h0

theorem run_below (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (hnot : AgreesNot gs a b) :
    Below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    rw [run_cons, run_cons]
    apply ih _ _ (appendGate_below h g ?_)
      (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    rcases (hops _ List.mem_cons_self).1 with ha | ho | hn
    · exact gateValue_pos g (Or.inl ha) a b h
    · exact gateValue_pos g (Or.inr ho) a b h
    · rw [hnot.first hn]
      exact id

theorem eval_eq (gates : List Gate) (w : ℕ) (x : List Bool) :
    Circuit.eval ⟨gates, w⟩ x = (run gates x).getD w false := rfl

theorem prefix_mono (gates : List Gate) (j : ℕ) (hj : j < gates.length)
    (hops : ∀ g ∈ gates, Allowed g)
    (hnot : ∀ k : ℕ, ∀ hk : k < gates.length, (gates[k]'hk).op = .not → k = j)
    (a b : List Bool) (hab : Below a b) (w : ℕ) (hw : w < a.length + j) :
    (run gates a).getD w false = true → (run gates b).getD w false = true := by
  have key : Below (run (gates.take j) a) (run (gates.take j) b) := by
    apply run_below _ _ _ hab (fun g hg => hops g (List.mem_of_mem_take hg))
    intro k g hk hg
    exfalso
    rw [List.getElem?_take] at hk
    split_ifs at hk with hkj
    · obtain ⟨hk', hkg⟩ := List.getElem?_eq_some_iff.mp hk
      have := hnot k hk' (by rw [hkg]; exact hg)
      omega
  have hla : w < (run (gates.take j) a).length := by
    rw [run_length, List.length_take]
    omega
  have hlb : w < (run (gates.take j) b).length := by
    rw [run_length, List.length_take, ← hab.1]
    omega
  rw [← List.take_append_drop j gates, run_append, run_append, run_keeps _ _ hla,
    run_keeps _ _ hlb]
  exact key.2 w

theorem not_value (gates : List Gate) (j h : ℕ) (hj : j < gates.length) (r : List ℕ)
    (a : List Bool) (hop : (gates[j]'hj).op = .not)
    (hin : (gates[j]'hj).inputs = (a.length + h) :: r) (hh : h < j) :
    (run gates a).getD (a.length + j) false = !((run gates a).getD (a.length + h) false) := by
  have hR : (run (gates.take j) a).length = a.length + j := by
    rw [run_length, List.length_take]
    omega
  have hsplit : gates = gates.take j ++ (gates[j]'hj :: gates.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  rw [hsplit, run_append]
  rw [run_keeps _ _ (show a.length + h < (run (gates.take j) a).length by omega)]
  rw [← hR, value_first]
  unfold gateValue
  rw [hop, hin]
  simp [GateOp.eval]

end PEqualNP.Outside.L_meta_1645

theorem PEqualNP.Outside.L_meta_1645 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    (∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev (N + (h : ℕ)) x = false ∧ ev (N + (j : ℕ)) x = true) ∧
    (∀ w ∈ L i0, w ≠ p0 → w ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = w)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = w)) = true) ∧
    ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)) = false ∧
    ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v : Fin N, x v = true → v ∉ L i0) → (∀ v : Fin N, y v = true → v ∉ L i0) → (∀ v : Fin N, x v = true → y v = true) → ev w x = true → ev w y = true := by
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _ gates o j h hops _ hjop hnot hhj hin _ ev hev hp0 hp1 hoth hcomp
  obtain ⟨r, hr⟩ := hin
  have hops' : ∀ g ∈ gates, PEqualNP.Outside.L_meta_1645.Allowed g := hops
  have hnot' : ∀ k : ℕ, ∀ hk : k < gates.length,
      (gates[k]'hk).op = PEqualNP.CircuitLowerBounds.GateOp.not → k = j.val := by
    intro k hk hkop
    have := hnot ⟨k, hk⟩ (by simpa [List.get_eq_getElem] using hkop)
    rw [← this]
  have hlen : ∀ x : Fin N → Bool, (List.ofFn x).length = N := fun x => List.length_ofFn
  have hevr : ∀ (w : ℕ) (x : Fin N → Bool),
      ev w x = (PEqualNP.Outside.L_meta_1645.run gates (List.ofFn x)).getD w false := by
    intro w x
    rw [hev]
    rfl
  have mono : ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) →
      ev (N + (h : ℕ)) x = true → ev (N + (h : ℕ)) y = true := by
    intro x y hxy
    rw [hevr, hevr]
    apply PEqualNP.Outside.L_meta_1645.prefix_mono gates j.val j.isLt hops' hnot'
      _ _ (PEqualNP.Outside.L_meta_1645.initial_below x y hxy)
    rw [hlen]
    omega
  have notv : ∀ x : Fin N → Bool, ev (N + (j : ℕ)) x = !(ev (N + (h : ℕ)) x) := by
    intro x
    rw [hevr, hevr]
    have := PEqualNP.Outside.L_meta_1645.not_value gates j.val h.val j.isLt r (List.ofFn x)
      (by simpa [List.get_eq_getElem] using hjop)
      (by rw [hlen]; simpa [List.get_eq_getElem] using hr) hhj
    rw [hlen] at this
    exact this
  have off : ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) →
      ev (N + (h : ℕ)) x = false := by
    intro x hx
    cases hg : ev (N + (h : ℕ)) x with
    | false => rfl
    | true =>
      have := mono x (fun v : Fin N => decide (v ∉ L i0))
        (fun v hv => by simpa using hx v hv) hg
      rw [hcomp] at this
      exact absurd this Bool.false_ne_true
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨off x hx, ?_⟩
    rw [notv, off x hx]
    rfl
  · intro w _ hw0 hw1
    refine ⟨hoth w hw0 hw1, ?_⟩
    rw [notv, hoth w hw0 hw1]
    rfl
  · rw [notv, hp0]
    rfl
  · rw [notv, hp1]
    rfl
  · intro w x y hx hy hxy
    rw [hevr, hevr]
    apply (PEqualNP.Outside.L_meta_1645.run_below gates (List.ofFn x) (List.ofFn y)
      (PEqualNP.Outside.L_meta_1645.initial_below x y hxy) hops' ?_).2 w
    intro k g hk hg
    obtain ⟨hk', hkg⟩ := List.getElem?_eq_some_iff.mp hk
    have hkj : k = j.val := hnot' k hk' (by rw [hkg]; exact hg)
    subst hkj
    have ex := notv x
    have ey := notv y
    rw [off x hx] at ex
    rw [off y hy] at ey
    rw [hevr] at ex ey
    rw [hlen, hlen, ex, ey]

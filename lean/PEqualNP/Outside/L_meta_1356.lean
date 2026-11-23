import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1356_aux

open PEqualNP.CircuitLowerBounds

def Allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def Positive (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

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

theorem gateValue_neg (g : Gate) (hop : g.op = .not) (a b : List Bool) (h : Below a b) :
    gateValue b g = true → gateValue a g = true := by
  unfold gateValue
  rw [hop]
  cases hi : g.inputs with
  | nil => simp [GateOp.eval]
  | cons w ws =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true']
    intro hf
    cases ha : a.getD w false
    · rfl
    · exact (Bool.false_ne_true (hf.symm.trans (h.2 w ha))).elim

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

theorem value_first (g : Gate) (gs : List Gate) (a : List Bool) :
    (run (g :: gs) a).getD a.length false = gateValue a g := by
  rw [run_cons, run_keeps _ _ (by simp [appendGate]), appendGate]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl a.length)]
  simp

theorem next_index (g : Gate) (gs : List Gate) (a : List Bool) (j : ℕ) :
    (run gs (appendGate a g)).getD ((appendGate a g).length + j) false =
      (run (g :: gs) a).getD (a.length + (j + 1)) false := by
  congr 1
  simp [appendGate]
  omega

theorem note_antitone (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (i : ℕ) (g : Gate) (hi : gs[i]? = some g)
    (hg : g.op = .not)
    (hprev : ∀ (j : ℕ) (q : Gate), j < i → gs[j]? = some q → q.op = .not →
      (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false) :
    (run gs b).getD (b.length + i) false = true →
      (run gs a).getD (a.length + i) false = true := by
  induction gs generalizing a b i g with
  | nil => simp at hi
  | cons q gs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst g
      simpa only [Nat.add_zero, value_first] using gateValue_neg q hg a b h
    | succ i =>
      have hb : Below (appendGate a q) (appendGate b q) := by
        apply appendGate_below h
        rcases (hops q (List.mem_cons_self ..)).1 with ha | ho | hn
        · exact gateValue_pos q (Or.inl ha) a b h
        · exact gateValue_pos q (Or.inr ho) a b h
        · have he := hprev 0 q (Nat.zero_lt_succ i) rfl hn
          simp only [Nat.add_zero, value_first] at he
          rw [he]
          exact id
      have hpre (j : ℕ) (r : Gate) (hji : j < i) (hj : gs[j]? = some r)
          (hr : r.op = .not) :
          (run gs (appendGate a q)).getD ((appendGate a q).length + j) false =
          (run gs (appendGate b q)).getD ((appendGate b q).length + j) false := by
        rw [next_index, next_index]
        exact hprev (j+1) r (by omega) (by simpa using hj) hr
      have got := ih _ _ hb (fun r hr => hops r (List.mem_cons_of_mem _ hr))
        i g (by simpa using hi) hg hpre
      rwa [next_index, next_index] at got

def BelowExcept (p : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ w, w ≠ p → a.getD w false = true → b.getD w false = true

theorem gateValue_pos_except (p : ℕ) (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (hp : p ∉ g.inputs) (a b : List Bool) (h : BelowExcept p a b) :
    gateValue a g = true → gateValue b g = true := by
  unfold gateValue
  have hne : ∀ w ∈ g.inputs, w ≠ p := by
    intro w hw he
    subst w
    exact hp hw
  rcases hop with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro ha w hw
    exact h.2 w (hne w hw) (ha w hw)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨w, hw, ha⟩
    exact ⟨w, hw, h.2 w (hne w hw) ha⟩

theorem appendGate_belowExcept {p : ℕ} {a b : List Bool} (h : BelowExcept p a b)
    (g : Gate) (hg : gateValue a g = true → gateValue b g = true) :
    BelowExcept p (appendGate a g) (appendGate b g) := by
  refine ⟨by simp [appendGate, h.1], ?_⟩
  intro w hwp
  unfold appendGate
  by_cases hw : w < a.length
  · have hwb : w < b.length := h.1 ▸ hw
    rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hwb]
    exact h.2 w hwp
  · have ha := Nat.le_of_not_gt hw
    have hb : b.length ≤ w := h.1 ▸ ha
    rw [List.getD_append_right _ _ _ _ ha, List.getD_append_right _ _ _ _ hb, h.1]
    cases he : w - b.length with
    | zero => simpa using hg
    | succ k => simp

def NotBelow (gs : List Gate) (a b : List Bool) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = .not →
    (run gs a).getD (a.length + j) false = true →
      (run gs b).getD (b.length + j) false = true

theorem NotBelow.tail {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : NotBelow (g :: gs) a b) :
    NotBelow gs (appendGate a g) (appendGate b g) := by
  intro j q hj hq
  rw [next_index, next_index]
  exact h (j+1) q (by simpa using hj) hq

theorem NotBelow.first {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : NotBelow (g :: gs) a b) (hg : g.op = .not) :
    gateValue a g = true → gateValue b g = true := by
  have h0 := h 0 g rfl hg
  simpa only [Nat.add_zero, value_first] using h0

theorem run_belowExcept (p : ℕ) (gs : List Gate) (a b : List Bool)
    (h : BelowExcept p a b) (hops : ∀ g ∈ gs, Allowed g)
    (hno : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) → p ∉ g.inputs)
    (hnot : NotBelow gs a b) : BelowExcept p (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    rw [run_cons, run_cons]
    apply ih _ _ (appendGate_belowExcept h g ?_)
      (fun q hq => hops q (List.mem_cons_of_mem _ hq))
      (fun q hq => hno q (List.mem_cons_of_mem _ hq)) hnot.tail
    rcases (hops g (List.mem_cons_self ..)).1 with ha | ho | hn
    · exact gateValue_pos_except p g (Or.inl ha)
        (hno g (List.mem_cons_self ..) (Or.inl ha)) a b h
    · exact gateValue_pos_except p g (Or.inr ho)
        (hno g (List.mem_cons_self ..) (Or.inr ho)) a b h
    · exact hnot.first hn

theorem initial_belowExcept {n : ℕ} (p : Fin n) (x y : Fin n → Bool)
    (heq : ∀ v, v ≠ p → x v = y v) :
    BelowExcept p.val (List.ofFn y) (List.ofFn x) := by
  refine ⟨by simp, ?_⟩
  intro w hwp
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rename_i hw
    have hne : (⟨w,hw⟩ : Fin n) ≠ p := by
      intro h
      exact hwp (congrArg Fin.val h)
    simpa only [Option.getD_some, heq _ hne] using (id : y ⟨w,hw⟩ = true → y ⟨w,hw⟩ = true)
  · simp

theorem circuit_antitone_except (n : ℕ) (gs : List Gate) (p : Fin n)
    (k : Fin gs.length) (hops : ∀ g ∈ gs, Allowed g)
    (hnot : ∀ q : Fin gs.length, (gs.get q).op = .not → q = k)
    (hno : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) → p.val ∉ g.inputs)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true)
    (heq : ∀ v, v ≠ p → x v = y v) :
    ∀ o, o ≠ p.val → Circuit.eval ⟨gs,o⟩ (List.ofFn y) = true →
      Circuit.eval ⟨gs,o⟩ (List.ofFn x) = true := by
  have hnb : NotBelow gs (List.ofFn y) (List.ofFn x) := by
    intro j g hj hg
    apply note_antitone gs (List.ofFn x) (List.ofFn y) (initial_below x y hxy) hops j g hj hg
    intro i q hij hi hq
    obtain ⟨hjl, hjg⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hil, hiq⟩ := List.getElem?_eq_some_iff.mp hi
    have hjk : (⟨j,hjl⟩ : Fin gs.length) = k := hnot _ (by
      change gs[j].op = .not
      rw [hjg]
      exact hg)
    have hik : (⟨i,hil⟩ : Fin gs.length) = k := hnot _ (by
      change gs[i].op = .not
      rw [hiq]
      exact hq)
    have he := congrArg Fin.val (hik.trans hjk.symm)
    simp only [Fin.val_mk] at he
    omega
  have h := run_belowExcept p.val gs _ _ (initial_belowExcept p x y heq) hops hno hnb
  intro o ho
  exact h.2 o ho

end PEqualNP.Outside.L_meta_1356_aux

namespace PEqualNP.Outside.L_meta_1356_aux.Output

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_keeps (gs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (gs.foldl step x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem eval_input (n : Nat) (gs : List Gate) (p : Fin n) (x : Fin n → Bool) :
    (Circuit.mk gs p.val).eval (List.ofFn x) = x p := by
  unfold Circuit.eval Circuit.wires
  change (gs.foldl step (List.ofFn x)).getD p.val false = x p
  rw [fold_keeps _ _ _ (by simpa using p.isLt)]
  simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,p.isLt]

theorem output_ne_member (n : Nat) (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (gs : List Gate) (o : Nat)
    (hc : ∀ x : Fin n → Bool, (Circuit.mk gs o).eval (List.ofFn x) =
      decide (∃ v ∈ S, x v = true)) (p : Fin n) : o ≠ p.val := by
  classical
  have hn : ¬ S ⊆ {p} := by
    intro h
    have hle := Finset.card_le_card h
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨q,hq,hqp⟩ := Finset.not_subset.mp hn
  have hne : q ≠ p := by simpa using hqp
  intro ho
  let x : Fin n → Bool := fun v => decide (v = q)
  have h := hc x
  rw [ho,eval_input] at h
  have hx : x p = false := by simp [x,Ne.symm hne]
  have hy : decide (∃ v ∈ S, x v = true) = true := by
    apply decide_eq_true
    exact ⟨q,hq,by simp [x]⟩
  rw [hx,hy] at h
  exact Bool.false_ne_true h

end PEqualNP.Outside.L_meta_1356_aux.Output

theorem PEqualNP.Outside.L_meta_1356 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i9 : Fin m, 2 ≤ (S i9).card) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → ∀ (p : Fin n) (i0 : Fin m), p ∈ S i0 → ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ p.val ∈ (gates.get a).inputs := by
  classical
  intro n m S hS gs out hops hc iota hn p i hp
  by_contra missing
  have hno : ∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → p.val ∉ g.inputs := by
    intro g hg hop hmem
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
    apply missing
    refine ⟨j,?_,?_⟩
    · simpa only [hj] using hop
    · simpa only [hj] using hmem
  have honce : ∀ q : Fin gs.length, (gs.get q).op =
      PEqualNP.CircuitLowerBounds.GateOp.not → q = iota 0 := by
    intro q hq
    obtain ⟨r,hr⟩ := hn q hq
    have hr0 : r = 0 := Subsingleton.elim _ _
    rw [hr0] at hr
    exact hr.symm
  let x : Fin n → Bool := fun _ => false
  let y : Fin n → Bool := fun v => decide (v = p)
  have hxy : ∀ v, x v = true → y v = true := by simp [x]
  have heq : ∀ v, v ≠ p → x v = y v := by
    intro v hv
    simp [x,y,hv]
  have hy : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,out i⟩ (List.ofFn y) = true := by
    rw [hc i y]
    apply decide_eq_true
    exact ⟨p,hp,by simp [y]⟩
  have hneq := PEqualNP.Outside.L_meta_1356_aux.Output.output_ne_member
    n (S i) (hS i) gs (out i) (hc i) p
  have hx := PEqualNP.Outside.L_meta_1356_aux.circuit_antitone_except
    n gs p (iota 0) hops honce hno x y hxy heq (out i) hneq hy
  rw [hc i x] at hx
  simpa [x] using hx

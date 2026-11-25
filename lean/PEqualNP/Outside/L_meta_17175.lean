import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_17175

def cost (g : Gate) : ℕ := match g.op with
  | .not => 0
  | _ => 1

def uses (g : Gate) : Finset ℕ := match g.op with
  | .not => (g.inputs.take 1).toFinset
  | _ => g.inputs.toFinset

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rel (m a b : Bool) : Prop := if m then (a = true → b = true) else a = b

def agrees (m : Bool) (s : Finset ℕ) (x y : List Bool) :=
  ∀ i ∈ s, rel m (x.getD i false) (y.getD i false)

theorem gate_card (g : Gate) (h : g.inputs.length ≤ 2) : (uses g).card ≤ cost g + 1 := by
  cases g with | mk op l =>
    cases op <;> simp [uses, cost] <;> first | exact (List.toFinset_card_le _).trans h | exact (List.toFinset_card_le _).trans (by simp)

theorem gate_rel (g : Gate) (m : Bool) (x y : List Bool)
    (hb : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hm : m = true → cost g = 1) (h : agrees m (uses g) x y) :
    rel m (g.op.eval (g.inputs.map fun i => x.getD i false)) (g.op.eval (g.inputs.map fun i => y.getD i false)) := by
  obtain ⟨op, l⟩ := g
  change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hb
  change l.length ≤ 2 at hl
  rcases hb with rfl | rfl | rfl <;> cases m <;> cases l with
  | nil => simp_all [rel, GateOp.eval, cost]
  | cons a t => cases t with
    | nil => simp_all [agrees, uses, rel, cost, GateOp.eval]
    | cons b t =>
      cases t <;> simp_all [agrees, uses, rel, cost, GateOp.eval, List.length_cons] <;> grind

theorem read_push (x : List Bool) (b : Bool) (i : ℕ) :
    (x ++ [b]).getD i false = if i = x.length then b else x.getD i false := by
  by_cases h : i < x.length
  · rw [ite_eq_right (Nat.ne_of_lt h), List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    split <;> rename_i hh
    · simp [hh]
    · rw [List.getD_eq_default x false (by omega), List.getD_eq_default [b] false (by simp; omega)]

def pull (n : ℕ) (g : Gate) (s : Finset ℕ) := if n ∈ s then s.erase n ∪ uses g else s

theorem pull_card (n : ℕ) (g : Gate) (s : Finset ℕ) (hl : g.inputs.length ≤ 2) :
    (pull n g s).card ≤ s.card + cost g := by
  unfold pull
  split <;> rename_i h
  · have ha := Finset.card_union_le (s.erase n) (uses g)
    have hb := Finset.card_erase_add_one h
    have hc := gate_card g hl
    omega
  · omega

theorem pull_sound (n : ℕ) (g : Gate) (s : Finset ℕ) (m : Bool) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (hb : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hm : m = true → cost g = 1)
    (h : agrees m (pull n g s) x y) : agrees m s (step x g) (step y g) := by
  intro i hi
  simp only [step, read_push, hx, hy]
  split <;> rename_i he
  · subst i
    exact gate_rel g m x y hb hl hm (fun j hj => h j (by simp [pull, hi, hj]))
  · apply h
    by_cases hn : n ∈ s <;> simp [pull, hn, hi, he]

theorem support (gs : List Gate) (n : ℕ) (s : Finset ℕ) (m : Bool)
    (hb : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hm : ∀ g ∈ gs, m = true → cost g = 1) :
    ∃ t : Finset ℕ, t.card ≤ s.card + (gs.map cost).sum ∧ ∀ x y : List Bool,
      x.length = n → y.length = n → agrees m t x y → agrees m s (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing n s with
  | nil => exact ⟨s, by simp, fun _ _ _ _ h => h⟩
  | cons g gs ih =>
    obtain ⟨t, ht, h⟩ := ih (n+1) s (fun j hj => hb j (by simp [hj])) (fun j hj => hm j (by simp [hj]))
    obtain ⟨ha, hc⟩ := hb g (by simp)
    refine ⟨pull n g t, ?_, ?_⟩
    · have := pull_card n g t hc
      simp only [List.map_cons, List.sum_cons]; omega
    · intro x y hx hy hxy
      exact h _ _ (by simp [step, hx]) (by simp [step, hy]) (pull_sound n g t m x y hx hy ha hc (hm g (by simp)) hxy)

theorem wire {N : ℕ} (u v : Fin N) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = N + v.val) := by
  unfold oneEach
  by_cases h : i < N
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h, Fin.ext_iff, show i ≠ N + v.val by omega]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    have hu : i ≠ u.val := by omega
    by_cases hk : i - N < N
    · simp [hk, hu, Fin.ext_iff, show i - N = v.val ↔ i = N + v.val by omega]
    · simp [hk, hu, show i ≠ N + v.val by omega]

def recognizes {N : ℕ} (m : Bool) (s : Finset ℕ) := ∀ a b c d : Fin N,
  agrees m s (oneEach a b) (oneEach c d) → rel m (decide (a = b)) (decide (c = d))

theorem row {N : ℕ} {m : Bool} {s : Finset ℕ} (hr : recognizes (N := N) m s)
    {a b : Fin N} (ha : a.val ∉ s) (hb : m = true ∨ b.val ∉ s) : a = b := by
  by_contra hab
  have h := hr a a b a (by
    intro i hi
    rw [wire, wire]
    have hia : i ≠ a.val := by grind
    cases m <;> simp_all [rel]; grind)
  cases m <;> simp_all [rel, Ne.symm hab]

theorem col {N : ℕ} {m : Bool} {s : Finset ℕ} (hr : recognizes (N := N) m s)
    {a b : Fin N} (ha : N+a.val ∉ s) (hb : N+b.val ∉ s) : a = b := by
  by_contra hab
  have h := hr a a a b (by
    intro i hi
    rw [wire, wire]
    have hia : i ≠ N+a.val := by grind
    have hib : i ≠ N+b.val := by grind
    cases m <;> simp [rel, hia, hib])
  cases m <;> simp_all [rel]

theorem size_bound {N : ℕ} (hn : 2 ≤ N) {m : Bool} {s : Finset ℕ} (hr : recognizes (N := N) m s) :
    2*N ≤ s.card + (if m then 1 else 2) := by
  let L := Finset.range N
  let R := Finset.Ico N (N+N)
  have left : (L \ s).card ≤ (if m then 0 else 1) := by
    cases m with
    | false =>
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp [L] at ha hb
      exact congrArg Fin.val (row hr (a := ⟨a, ha.1⟩) (b := ⟨b, hb.1⟩) ha.2 (Or.inr hb.2))
    | true =>
      simp only [ite_true, Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro a ha
      simp [L] at ha
      let u : Fin N := ⟨a, ha.1⟩
      let v : Fin N := ⟨if a = 0 then 1 else 0, by split <;> omega⟩
      have h := congrArg Fin.val (row hr (a := u) (b := v) ha.2 (Or.inl rfl))
      change a = (if a = 0 then 1 else 0) at h
      split at h <;> omega
  have right : (R \ s).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp [R] at ha hb
    let u : Fin N := ⟨a-N, by omega⟩
    let v : Fin N := ⟨b-N, by omega⟩
    have h := congrArg Fin.val (col hr (a := u) (b := v) (by simpa [u, Nat.add_sub_of_le ha.1.1] using ha.2) (by simpa [v, Nat.add_sub_of_le hb.1.1] using hb.2))
    change a-N = b-N at h
    omega
  have hL := Finset.card_sdiff_add_card_inter L s
  have hR := Finset.card_sdiff_add_card_inter R s
  have hdis : Disjoint (L ∩ s) (R ∩ s) := by
    rw [Finset.disjoint_left]; intro i hi hj; simp [L] at hi; simp [R] at hj; omega
  have hu : (L ∩ s ∪ R ∩ s) ⊆ s := by intro i hi; rcases Finset.mem_union.mp hi with h | h <;> exact (Finset.mem_inter.mp h).2
  have hcard := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint hdis] at hcard
  have hcL : L.card = N := by simp [L]
  have hcR : R.card = N := by simp [R]
  cases m <;> simp only [Bool.false_eq_true, ite_false, ite_true] at left ⊢ <;> omega

theorem cost_bound (gs : List Gate) : (gs.map cost).sum ≤ gs.length ∧
    ((gs.map cost).sum = gs.length → ∀ g ∈ gs, cost g = 1) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hb : cost g ≤ 1 := by unfold cost; split <;> decide
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.mem_cons]
    exact ⟨by omega, fun h a ha => ha.elim (fun e => by subst a; omega) (ih.2 (by omega) a)⟩

end PEqualNP.Outside.L_meta_17175

theorem PEqualNP.Outside.L_meta_17175 : (∀ (N : ℕ), 2 ≤ N → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents (fun u v : Fin N => decide (u = v)) C → 2 * N - 2 ≤ C.size) := by
  intro N hn C hf hr
  let m := decide ((C.gates.map L_meta_17175.cost).sum = C.gates.length)
  obtain ⟨hsum, hall⟩ := L_meta_17175.cost_bound C.gates
  obtain ⟨s, hsize, hsem⟩ := L_meta_17175.support C.gates (N+N) {C.output} m hf (fun g hg h => hall (by simpa [m] using h) g hg)
  have hs : L_meta_17175.recognizes (N := N) m s := by
    intro a b c d h
    have hab : C.eval (oneEach a b) = decide (a = b) := hr a b
    have hcd : C.eval (oneEach c d) = decide (c = d) := hr c d
    rw [← hab, ← hcd]
    exact hsem _ _ (by simp [PEqualNP.Represents.oneEach]) (by simp [PEqualNP.Represents.oneEach]) h C.output (by simp)
  have hb := L_meta_17175.size_bound hn hs
  simp only [Finset.card_singleton] at hsize
  unfold PEqualNP.CircuitLowerBounds.Circuit.size
  by_cases h : (C.gates.map L_meta_17175.cost).sum = C.gates.length <;> simp [m, h] at hb <;> omega

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def key (a b c d : ℕ) : ℕ :=
  (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

def renameWire (s : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ :=
  if hi : i < 14 then (s ⟨i, hi⟩).val else i

def renamePin (s : Equiv.Perm (Fin 14)) (i : Fin 15) : Fin 15 :=
  ⟨renameWire s i.val, by
    unfold renameWire
    split
    · have := (s ⟨i.val, by assumption⟩).isLt; omega
    · exact i.isLt⟩

lemma renameWire_injective (s : Equiv.Perm (Fin 14)) : Function.Injective (renameWire s) := by
  intro i j he
  by_cases hi : i < 14 <;> by_cases hj : j < 14
  · have eq : s ⟨i, hi⟩ = s ⟨j, hj⟩ := Fin.ext (by simpa [renameWire, hi, hj] using he)
    exact congrArg Fin.val (s.injective eq)
  · simp only [renameWire, hi, hj, dite_true, dite_false] at he
    have := (s ⟨i, hi⟩).isLt
    omega
  · simp only [renameWire, hi, hj, dite_true, dite_false] at he
    have := (s ⟨j, hj⟩).isLt
    omega
  · simpa [renameWire, hi, hj] using he

lemma renamePin_value (s : Equiv.Perm (Fin 14)) (i : Fin 15) :
    (renamePin s i).val = (if i.val < 14 then (s (Fin.ofNat 14 i.val)).val else 14) := by
  by_cases h : i.val < 14
  · have eq : (⟨i.val, h⟩ : Fin 14) = Fin.ofNat 14 i.val := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt h]
    change renameWire s i.val = _
    simp [renameWire, h, eq]
  · have eq : i.val = 14 := by have := i.isLt; omega
    change renameWire s i.val = _
    simp [renameWire, eq]

def renameGate (s : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renameWire s)⟩

def renameCircuit (s : Equiv.Perm (Fin 14)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate s), renameWire s C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Related (s : Equiv.Perm (Fin 14)) (w v : List Bool) : Prop :=
  14 ≤ w.length ∧ w.length = v.length ∧
    ∀ i, v.getD (renameWire s i) false = w.getD i false

lemma primary_value {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]

lemma related_start (s : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool) :
    Related s (List.ofFn (x ∘ s)) (List.ofFn x) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases h : i < 14
  · simp only [renameWire, dite_eq_left h]
    exact (primary_value x (s ⟨i, h⟩)).trans (primary_value (x ∘ s) ⟨i, h⟩).symm
  · simp only [renameWire, h, dite_false]
    rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]

lemma related_snoc {s : Equiv.Perm (Fin 14)} {w v : List Bool}
    (h : Related s w v) (b : Bool) : Related s (w ++ [b]) (v ++ [b]) := by
  obtain ⟨hn, hlen, hp⟩ := h
  refine ⟨by simp; omega, by simp [hlen], ?_⟩
  intro i
  have hi : i < w.length → renameWire s i < v.length := by
    intro hl
    unfold renameWire
    split
    · have := (s ⟨i, by assumption⟩).isLt; omega
    · omega
  rcases Nat.lt_trichotomy i w.length with hl | he | hh
  · rw [List.getD_append _ _ _ _ (hi hl), List.getD_append _ _ _ _ hl]
    exact hp i
  · have hmap : renameWire s i = v.length := by
      rw [renameWire, dite_eq_right (by omega), he, hlen]
    rw [hmap, he]
    simp
  · have hmap : renameWire s i = i := by rw [renameWire, dite_eq_right (by omega)]
    rw [hmap, List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma related_step {s : Equiv.Perm (Fin 14)} {w v : List Bool}
    (h : Related s w v) (g : Gate) : Related s (step w g) (step v (renameGate s g)) := by
  have he : (renameGate s g).op.eval ((renameGate s g).inputs.map fun i => v.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [renameGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact h.2.2 i
  unfold step
  rw [he]
  exact related_snoc h _

lemma related_fold (s : Equiv.Perm (Fin 14)) (gs : List Gate) :
    ∀ w v, Related s w v → Related s (gs.foldl step w) ((gs.map (renameGate s)).foldl step v) := by
  induction gs with
  | nil => intro w v h; exact h
  | cons g gs ih => intro w v h; exact ih _ _ (related_step h g)

lemma rename_eval {s : Equiv.Perm (Fin 14)} {w v : List Bool} (h : Related s w v) (C : Circuit) :
    (renameCircuit s C).eval v = C.eval w :=
  (related_fold s C.gates w v h).2.2 C.output

lemma rename_mono (s : Equiv.Perm (Fin 14)) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (renameCircuit s C) := by
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
  exact ⟨(h g₀ hg₀).1, by simpa [renameGate] using (h g₀ hg₀).2⟩

def AO (op : GateOp) : Prop := op = .and ∨ op = .or

lemma eval_swap {op : GateOp} (h : AO op) (a b : Bool) :
    op.eval [a, b] = op.eval [b, a] := by
  rcases h with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

def OrderedAs {n : ℕ} (a b x y : Fin n) : Prop :=
  x < y ∧ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))

lemma order_pair {n : ℕ} (a b : Fin n) (h : a ≠ b) : ∃ x y, OrderedAs a b x y := by
  rcases lt_or_gt_of_ne h with hl | hr
  · exact ⟨a, b, hl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨b, a, hr, Or.inr ⟨rfl, rfl⟩⟩

lemma ordered_eval {n : ℕ} {a b x y : Fin n} (h : OrderedAs a b x y)
    {op : GateOp} (hop : AO op) (v : Fin n → Bool) :
    op.eval [v x, v y] = op.eval [v a, v b] := by
  rcases h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact eval_swap hop _ _

lemma ordered_minmax {n : ℕ} {a b x y : Fin n} (h : OrderedAs a b x y) :
    min x.val y.val = min a.val b.val ∧ max x.val y.val = max a.val b.val := by
  rcases h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨min_comm _ _, max_comm _ _⟩

def prefixInputs (x : Fin 14 → Bool) (a b : Fin 14) (c d : Fin 15) (p q : GateOp) : List Bool :=
  let w := List.ofFn x ++ [p.eval [x a, x b]]
  w ++ [q.eval [w.getD c.val false, w.getD d.val false]]

def Witness (f : (Fin 14 → Bool) → Bool) (a b : Fin 14) (c d : Fin 15)
    (p q : GateOp) (T : Circuit) : Prop :=
  a < b ∧ c < d ∧ AO p ∧ AO q ∧ Monotone2 T ∧ T.size ≤ 24 ∧
    ∀ x, T.eval (prefixInputs x a b c d p q) = f x

lemma rename_witness {f : (Fin 14 → Bool) → Bool} {a b : Fin 14} {c d : Fin 15}
    {p q : GateOp} {T : Circuit} (h : Witness f a b c d p q T)
    (s : Equiv.Perm (Fin 14)) (symm : ∀ x, f (x ∘ s) = f x) :
    ∃ (a' b' : Fin 14) (c' d' : Fin 15), Witness f a' b' c' d' p q (renameCircuit s T) ∧
      key a'.val b'.val c'.val d'.val = key (s a).val (s b).val (renamePin s c).val (renamePin s d).val := by
  obtain ⟨hab, hcd, hp, hq, hm, hs, he⟩ := h
  obtain ⟨a', b', h₁⟩ := order_pair (s a) (s b) (s.injective.ne (ne_of_lt hab))
  have hcne : renamePin s c ≠ renamePin s d := fun e =>
    (ne_of_lt hcd) (Fin.ext (renameWire_injective s (congrArg Fin.val e)))
  obtain ⟨c', d', h₂⟩ := order_pair (renamePin s c) (renamePin s d) hcne
  refine ⟨a', b', c', d', ⟨h₁.1, h₂.1, hp, hq, rename_mono s T hm, ?_, ?_⟩, ?_⟩
  · simpa [Circuit.size, renameCircuit] using hs
  · intro x
    let u := List.ofFn (x ∘ s) ++ [p.eval [(x ∘ s) a, (x ∘ s) b]]
    let v := List.ofFn x ++ [p.eval [x a', x b']]
    have hv : Related s u v := by
      dsimp only [u, v]
      rw [ordered_eval h₁ hp x]
      exact related_snoc (related_start s x) _
    have he₂ : q.eval [v.getD c'.val false, v.getD d'.val false] =
        q.eval [u.getD c.val false, u.getD d.val false] := by
      rw [ordered_eval h₂ hq (fun i => v.getD i.val false)]
      change q.eval [v.getD (renameWire s c.val) false, v.getD (renameWire s d.val) false] = _
      rw [hv.2.2 c.val, hv.2.2 d.val]
    have hrel : Related s (prefixInputs (x ∘ s) a b c d p q) (prefixInputs x a' b' c' d' p q) := by
      change Related s (u ++ [_]) (v ++ [_])
      rw [he₂]
      exact related_snoc hv _
    exact (rename_eval hrel T).trans ((he (x ∘ s)).trans (symm x))
  · obtain ⟨ha, hb⟩ := ordered_minmax h₁
    obtain ⟨hc, hd⟩ := ordered_minmax h₂
    simp only [key, ha, hb, hc, hd]

lemma split_prefix (f : (Fin 14 → Bool) → Bool) (C : Circuit)
    (basis : IsAO2 14 C) (noDup : ∀ g ∈ C.gates, g.inputs.Nodup)
    (small : 2 ≤ C.size) (big : C.size ≤ 26) (eval : ∀ x, C.eval (List.ofFn x) = f x) :
    ∃ (a b : Fin 14) (c d : Fin 15) (p q : GateOp) (T : Circuit), Witness f a b c d p q T := by
  obtain ⟨ops, back, arity⟩ := basis
  cases hc : C.gates with
  | nil => simp [Circuit.size, hc] at small
  | cons g rem =>
    cases hr : rem with
    | nil => simp [Circuit.size, hc, hr] at small
    | cons h tail =>
      have hgates : C.gates = g :: h :: tail := by simpa only [hr] using hc
      have hg : g ∈ C.gates := by simp [hgates]
      have hh : h ∈ C.gates := by simp [hgates]
      obtain ⟨a₀, b₀, hab⟩ := List.length_eq_two.mp (arity g hg)
      obtain ⟨c₀, d₀, hcd⟩ := List.length_eq_two.mp (arity h hh)
      have at0 : PEqualNP.MetaComplexity.NestedCover.gateAt C 0 = g := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hgates]
      have at1 : PEqualNP.MetaComplexity.NestedCover.gateAt C 1 = h := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hgates]
      have first (i : ℕ) (hi : i ∈ g.inputs) : i < 14 := by
        have := back 0 (by simp [hgates]) i (at0 ▸ hi)
        simpa using this
      have second (i : ℕ) (hi : i ∈ h.inputs) : i < 15 :=
        back 1 (by simp [hgates]) i (at1 ▸ hi)
      let a : Fin 14 := ⟨a₀, first a₀ (by simp [hab])⟩
      let b : Fin 14 := ⟨b₀, first b₀ (by simp [hab])⟩
      let c : Fin 15 := ⟨c₀, second c₀ (by simp [hcd])⟩
      let d : Fin 15 := ⟨d₀, second d₀ (by simp [hcd])⟩
      have nab : a ≠ b := by
        have hne : a₀ ≠ b₀ := by simpa [hab] using noDup g hg
        exact fun e => hne (congrArg Fin.val e)
      have ncd : c ≠ d := by
        have hne : c₀ ≠ d₀ := by simpa [hcd] using noDup h hh
        exact fun e => hne (congrArg Fin.val e)
      obtain ⟨a', b', h₁⟩ := order_pair a b nab
      obtain ⟨c', d', h₂⟩ := order_pair c d ncd
      let T : Circuit := ⟨tail, C.output⟩
      have hp : AO g.op := ops g hg
      have hq : AO h.op := ops h hh
      refine ⟨a', b', c', d', g.op, h.op, T, h₁.1, h₂.1, hp, hq, ?_, ?_, ?_⟩
      · intro k hk
        have hmem : k ∈ C.gates := by
          have ht : k ∈ tail := hk
          simp [hgates, ht]
        refine ⟨?_, (arity k hmem).le⟩
        rcases ops k hmem with eq | eq <;> simp [eq]
      · simp [Circuit.size, hgates] at big
        change tail.length ≤ 24
        omega
      · intro x
        have firstEval : step (List.ofFn x) g = List.ofFn x ++ [g.op.eval [x a', x b']] := by
          unfold step
          rw [ordered_eval h₁ hp x, hab]
          have ha : (List.ofFn x).getD a₀ false = x a := primary_value x a
          have hb : (List.ofFn x).getD b₀ false = x b := primary_value x b
          simp only [List.map_cons, List.map_nil, ha, hb]
        have prefixEq : prefixInputs x a' b' c' d' g.op h.op = step (step (List.ofFn x) g) h := by
          rw [firstEval]
          dsimp only [prefixInputs, step]
          rw [ordered_eval h₂ hq (fun i => (List.ofFn x ++ [g.op.eval [x a', x b']]).getD i.val false), hcd] <;> rfl
        rw [prefixEq]
        have main := eval x
        unfold Circuit.eval Circuit.wires at main
        rw [hgates] at main
        exact main

end PEqualNP.Outside.L_meta_3010

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3010 in
theorem PEqualNP.Outside.L_meta_3010 :
    ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  classical
  intro f C basis hnodup hmin hmax computes
  let P (k : Nat) := ∃ (a b : Fin 14) (c d : Fin 15) (p q : GateOp) (T : Circuit),
    Witness f a b c d p q T ∧ key a.val b.val c.val d.val = k
  have existsWitness : ∃ k, P k := by
    obtain ⟨a, b, c, d, p, q, T, h⟩ := split_prefix f C basis hnodup hmin hmax computes
    exact ⟨_, a, b, c, d, p, q, T, h, rfl⟩
  obtain ⟨a, b, c, d, p, q, T, hw, hk⟩ := Nat.find_spec existsWitness
  obtain ⟨hab, hcd, hp, hq, hfan, hsize, hcompute⟩ := hw
  refine ⟨a, b, c, d, p, q, T, hab, hcd, hp, hq, ?_, hfan, hsize, hcompute⟩
  intro s hsymm
  obtain ⟨a', b', c', d', h', heq⟩ := rename_witness (show Witness f a b c d p q T from
    ⟨hab, hcd, hp, hq, hfan, hsize, hcompute⟩) s hsymm
  have p' : P (key (s a).val (s b).val (renamePin s c).val (renamePin s d).val) :=
    ⟨a', b', c', d', p, q, renameCircuit s T, h', heq⟩
  have hleast := Nat.find_min' existsWitness p'
  rw [← hk] at hleast
  simpa only [key, renamePin_value] using hleast

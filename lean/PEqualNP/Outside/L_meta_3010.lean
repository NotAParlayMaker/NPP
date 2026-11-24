import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private abbrev AO (op : GateOp) := op = GateOp.and ∨ op = GateOp.or

-- A sorted pair of distinct wires together with an allowed operation.
private abbrev Head (n : ℕ) :=
  { indices : Fin n × Fin n // indices.1 < indices.2 } × { op : GateOp // AO op }

private abbrev Head.a {n : ℕ} (g : Head n) : Fin n := g.1.val.1
private abbrev Head.b {n : ℕ} (g : Head n) : Fin n := g.1.val.2
private theorem Head.lt {n : ℕ} (g : Head n) : g.a < g.b := g.1.property
private abbrev Head.op {n : ℕ} (g : Head n) : GateOp := g.2.val
private theorem Head.good {n : ℕ} (g : Head n) : AO g.op := g.2.property

private def ordered {n : ℕ} (i j : Fin n) (h : i ≠ j) (op : GateOp) (good : AO op) :
    Head n :=
  ⟨⟨(min i j, max i j), min_lt_max.mpr h⟩, ⟨op, good⟩⟩

private def readHead {n : ℕ} (g : Head n) (w : Fin n → Bool) :=
  g.op.eval [w g.a, w g.b]

private theorem read_ordered {n : ℕ} (i j : Fin n) (h : i ≠ j) (op : GateOp)
    (good : AO op) (w : Fin n → Bool) :
    readHead (ordered i j h op good) w = op.eval [w i, w j] := by
  rcases lt_or_gt_of_ne h with hij | hji
  · simp [readHead, ordered, min_eq_left hij.le, max_eq_right hij.le]
  · simp only [readHead, ordered, min_eq_right hji.le, max_eq_left hji.le]
    rcases good with rfl | rfl <;> cases w i <;> cases w j <;> rfl

-- Input permutations fix every gate wire and every index beyond the circuit.
private def wire (p : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ :=
  if h : i < 14 then (p ⟨i,h⟩).val else i

private theorem wire_injective (p : Equiv.Perm (Fin 14)) : Function.Injective (wire p) := by
  intro i j hij
  by_cases hi : i < 14 <;> by_cases hj : j < 14
  · simp only [wire, dite_eq_left hi, dite_eq_left hj] at hij
    exact congrArg Fin.val (p.injective (Fin.ext hij))
  · simp only [wire, dite_eq_left hi, dite_eq_right hj] at hij
    have := (p ⟨i,hi⟩).isLt
    omega
  · simp only [wire, dite_eq_right hi, dite_eq_left hj] at hij
    have := (p ⟨j,hj⟩).isLt
    omega
  · simpa only [wire, dite_eq_right hi, dite_eq_right hj] using hij

private def lifted (p : Equiv.Perm (Fin 14)) (i : Fin 15) : Fin 15 :=
  ⟨wire p i.val, by
    by_cases h : i.val < 14
    · simp only [wire, dite_eq_left h]
      exact Nat.lt_trans (p ⟨i,h⟩).isLt (by decide)
    · simpa only [wire, dite_eq_right h] using i.isLt⟩

private theorem lifted_injective (p : Equiv.Perm (Fin 14)) : Function.Injective (lifted p) := by
  intro i j hij
  exact Fin.ext (wire_injective p (congrArg Fin.val hij))

private def transported {n : ℕ} (g : Head n) (f : Fin n → Fin n)
    (hinj : Function.Injective f) : Head n :=
  ordered (f g.a) (f g.b) (hinj.ne g.lt.ne) g.op g.good

private theorem transported_lo {n : ℕ} (g : Head n) (f : Fin n → Fin n)
    (hinj : Function.Injective f) :
    (transported g f hinj).a.val = min (f g.a).val (f g.b).val :=
  Fin.val_min _ _

private theorem transported_hi {n : ℕ} (g : Head n) (f : Fin n → Fin n)
    (hinj : Function.Injective f) :
    (transported g f hinj).b.val = max (f g.a).val (f g.b).val :=
  Fin.val_max _ _

private theorem read_transported {n : ℕ} (g : Head n) (f : Fin n → Fin n)
    (hinj : Function.Injective f) (x : Fin n → Bool) :
    readHead (transported g f hinj) x = readHead g (x ∘ f) :=
  read_ordered _ _ _ _ _ _

private def renamedGate (p : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire p)⟩

private def renamed (p : Equiv.Perm (Fin 14)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renamedGate p), wire p C.output⟩

private theorem renamed_mono (p : Equiv.Perm (Fin 14)) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (renamed p C) := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨g', hg', rfl⟩
  simpa [renamedGate] using h g' hg'

private theorem lookup (p : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool)
    (extra : List Bool) (i : ℕ) :
    (List.ofFn x ++ extra).getD (wire p i) false =
      (List.ofFn (x ∘ p) ++ extra).getD i false := by
  by_cases h : i < 14
  · simp only [wire, dite_eq_left h, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp only [List.length_ofFn]; exact (p ⟨i,h⟩).isLt),
        List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn, dite_eq_left h, dite_eq_left (p ⟨i,h⟩).isLt,
      Option.getD_some, Function.comp_apply]
  · simp only [wire, dite_eq_right h, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h),
        List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)]
    simp

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- Both evaluations append the same gate value at each step.
private theorem eval_renamed (p : Equiv.Perm (Fin 14)) (C : Circuit) (x : Fin 14 → Bool)
    (t : List Bool) :
    (renamed p C).eval (List.ofFn x ++ t) = C.eval (List.ofFn (x ∘ p) ++ t) := by
  suffices aux : ∀ (gs : List Gate) (s : List Bool),
    ((gs.map (renamedGate p)).foldl step (List.ofFn x ++ s)).getD (wire p C.output) false =
      (gs.foldl step (List.ofFn (x ∘ p) ++ s)).getD C.output false by
    exact aux C.gates t
  intro gs
  induction gs with
  | nil => exact fun s => lookup p x s _
  | cons g gs ih =>
    intro s
    let v := g.op.eval (g.inputs.map fun i => (List.ofFn (x ∘ p) ++ s).getD i false)
    simpa only [List.map_cons, List.foldl_cons, step, renamedGate, List.map_map,
      Function.comp_def, lookup, List.append_assoc, v] using ih (s ++ [v])

private def extra (g : Head 14) (q : Head 15) (x : Fin 14 → Bool) : List Bool :=
  let v := readHead g x
  let w := List.ofFn x ++ [v]
  [v, readHead q (fun i => w.getD i.val false)]

private def realizes (F : (Fin 14 → Bool) → Bool) (g : Head 14) (q : Head 15) (C : Circuit) :=
  Monotone2 C ∧ C.size ≤ 24 ∧ ∀ x, C.eval (List.ofFn x ++ extra g q x) = F x

private def rank (g : Head 14) (q : Head 15) : ℕ :=
  (15 * g.a.val + g.b.val) * 225 + (15 * q.a.val + q.b.val)

private theorem transport_realizes (F : (Fin 14 → Bool) → Bool) (g : Head 14)
    (q : Head 15) (C : Circuit) (h : realizes F g q C) (p : Equiv.Perm (Fin 14))
    (hF : ∀ x, F (x ∘ p) = F x) :
    realizes F (transported g p p.injective) (transported q (lifted p) (lifted_injective p))
      (renamed p C) := by
  refine ⟨renamed_mono p C h.1, ?_, ?_⟩
  · simpa [renamed, Circuit.size] using h.2.1
  · intro x
    have he : extra (transported g p p.injective)
        (transported q (lifted p) (lifted_injective p)) x = extra g q (x ∘ p) := by
      simp only [extra, read_transported]
      simp only [readHead, Function.comp_apply, lifted, lookup]
    rw [he, eval_renamed, h.2.2, hF]


-- Removing the first two gates makes their values additional inputs to the tail.
private theorem initial (F : (Fin 14 → Bool) → Bool) (C : Circuit)
    (hao : PEqualNP.TopForm.IsAO2 14 C) (hnd : ∀ g ∈ C.gates, g.inputs.Nodup)
    (hlo : 2 ≤ C.size) (hhi : C.size ≤ 26)
    (hs : ∀ x, C.eval (List.ofFn x) = F x) :
    ∃ (u : Head 14) (v : Head 15) (D : Circuit), realizes F u v D := by
  rcases C with ⟨gs, o⟩
  cases gs with
  | nil => simp [Circuit.size] at hlo
  | cons A tail =>
    cases tail with
    | nil => simp [Circuit.size] at hlo
    | cons B gs =>
      have hA : A ∈ (A :: B :: gs) := by simp
      have hB : B ∈ (A :: B :: gs) := by simp
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hao.2.2 A hA)
      obtain ⟨c, d, hcd⟩ := List.length_eq_two.mp (hao.2.2 B hB)
      have rbA := hao.2.1 0 (by simp)
      have rbB := hao.2.1 1 (by simp)
      change ∀ i ∈ A.inputs, i < 14 at rbA
      change ∀ i ∈ B.inputs, i < 15 at rbB
      rw [hab] at rbA
      rw [hcd] at rbB
      have ha := rbA a (by simp)
      have hb := rbA b (by simp)
      have hc := rbB c (by simp)
      have hd := rbB d (by simp)
      have nab : a ≠ b := by simpa [hab] using hnd A hA
      have ncd : c ≠ d := by simpa [hcd] using hnd B hB
      let u := ordered (⟨a,ha⟩ : Fin 14) ⟨b,hb⟩ (by simpa using nab) A.op (hao.1 A hA)
      let v := ordered (⟨c,hc⟩ : Fin 15) ⟨d,hd⟩ (by simpa using ncd) B.op (hao.1 B hB)
      refine ⟨u, v, ⟨gs,o⟩, ?_, ?_, ?_⟩
      · intro g hg
        have hm : g ∈ A :: B :: gs := by simp [hg]
        have ho := hao.1 g hm
        exact ⟨ho, (hao.2.2 g hm).le⟩
      · simp only [Circuit.size, List.length_cons] at hhi ⊢
        omega
      · intro x
        have get_input (i : ℕ) (hi : i < 14) : (List.ofFn x).getD i false = x ⟨i,hi⟩ :=
          (List.getD_eq_getElem (List.ofFn x) false (n := i)
            (by simpa only [List.length_ofFn] using hi)).trans (List.getElem_ofFn (f := x) _)
        have hw : List.ofFn x ++ extra u v x = step (step (List.ofFn x) A) B := by
          simp only [extra, u, v, read_ordered, step, hab, hcd,
            List.map_cons, List.map_nil, get_input a ha, get_input b hb, List.append_assoc, List.cons_append,
            List.nil_append]
        change (gs.foldl step (List.ofFn x ++ extra u v x)).getD o false = F x
        rw [hw]
        exact hs x

private theorem lifted_val_post (p : Equiv.Perm (Fin 14)) (i : Fin 15) :
    (lifted p i).val =
      if i.val < 14 then (p (Fin.ofNat 14 i.val)).val else 14 := by
  by_cases h : i.val < 14
  · have he : Fin.ofNat 14 i.val = ⟨i.val,h⟩ := by
      apply Fin.ext
      exact (Fin.val_ofNat 14 i.val).trans (Nat.mod_eq_of_lt h)
    simp only [lifted, wire, dite_eq_left h, ite_eq_left h, he]
  · have h14 : i.val = 14 := by have := i.isLt; omega
    simp [lifted, wire, h14]

end PEqualNP.Outside.L_meta_3010

open PEqualNP.Outside.L_meta_3010

theorem PEqualNP.Outside.L_meta_3010 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  intro F C hao hnd hlo hhi hs
  classical
  obtain ⟨u₀, v₀, D₀, h₀⟩ := initial F C hao hnd hlo hhi hs
  -- Minimize over all realizations. Every symmetry gives another realization.
  let P : ℕ → Prop := fun k =>
    ∃ (u : Head 14) (v : Head 15) (D : PEqualNP.CircuitLowerBounds.Circuit),
      realizes F u v D ∧ rank u v = k
  have hex : ∃ k, P k := ⟨_, u₀, v₀, D₀, h₀, rfl⟩
  obtain ⟨u, v, D, h, hk⟩ := Nat.find_spec hex
  refine ⟨u.a, u.b, v.a, v.b, u.op, v.op, D, u.lt, v.lt, u.good, v.good, ?_, h.1, h.2.1, ?_⟩
  · intro p hp
    let u' := transported u p p.injective
    let v' := transported v (lifted p) (lifted_injective p)
    have hit : P (rank u' v') :=
      ⟨u', v', renamed p D, transport_realizes F u v D h p hp, rfl⟩
    have hmin := Nat.find_min' hex hit
    rw [←hk] at hmin
    have hu : u.a.val ≤ u.b.val := u.lt.le
    have hv : v.a.val ≤ v.b.val := v.lt.le
    simpa only [min_eq_left hu, max_eq_right hu, min_eq_left hv, max_eq_right hv,
      rank, u', v', transported_lo, transported_hi, lifted_val_post] using hmin
  · intro x
    simpa [extra, readHead, List.append_assoc] using h.2.2 x

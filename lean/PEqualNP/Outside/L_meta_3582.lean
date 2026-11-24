import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3582

open PEqualNP.CircuitLowerBounds

def edge (m : ℕ) : Bool :=
  (m.testBit 0 && m.testBit 1) || (m.testBit 1 && m.testBit 2) || (m.testBit 2 && m.testBit 3) || (m.testBit 3 && m.testBit 4) || (m.testBit 4 && m.testBit 0) || (m.testBit 0 && m.testBit 5) || (m.testBit 1 && m.testBit 6) || (m.testBit 2 && m.testBit 7) || (m.testBit 3 && m.testBit 8) || (m.testBit 5 && m.testBit 7) || (m.testBit 6 && m.testBit 8) || (m.testBit 8 && m.testBit 5)

def signal (m : ℕ) (w : Fin 10) : Bool :=
  if w.val < 9 then m.testBit w.val else m.testBit 0 || m.testBit 2

def table : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 4, 1, 9, 1, 20, 1, 36, 1, 64, 1, 129, 1, 257, 1, 1, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 4, 18, 4, 4, 16, 0, 0, 16, 4, 36, 4, 68, 4, 144, 4, 256, 4, 4, 16, 1, 8, 10, 1, 5, 1, 8, 1, 0, 0, 40, 1, 65, 1, 129, 1, 257, 1, 1, 8, 1, 128, 130, 1, 5, 1, 9, 1, 144, 1, 0, 0, 65, 1, 128, 1, 256, 1, 1, 128, 257, 2, 2, 256, 260, 2, 10, 2, 18, 2, 34, 2, 0, 0, 130, 2, 256, 2, 257, 2, 5, 4, 34, 4, 4, 32, 40, 4, 20, 4, 32, 4, 68, 4, 0, 0, 260, 4, 4, 32, 9, 8, 10, 8, 36, 8, 8, 32, 48, 8, 32, 8, 64, 8, 136, 8, 0, 0, 9, 8]

def base (v : Fin 9) (w : Fin 10) (isAnd : Bool) : ℕ :=
  table.getD (2 * (10 * v.val + w.val) + (bif isAnd then 1 else 0)) 0

def gadget (isAnd : Bool) (m : ℕ) (v : Fin 9) (w : Fin 10) : Bool :=
  bif isAnd then m.testBit v.val && signal m w
  else m.testBit v.val || signal m w

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
lemma collision_table :
    ∀ v : Fin 9, v ≠ 0 → v ≠ 2 → ∀ w : Fin 10, v.castSucc ≠ w →
    ∀ isAnd : Bool,
      let m := base v w isAnd
      let m' := m + 2 ^ v.val
      m < 512 ∧ m.testBit v.val = false ∧ m'.testBit v.val = true ∧
      edge m = false ∧ edge m' = true ∧
      (∀ i : Fin 10, i.val ≠ v.val → signal m i = signal m' i) ∧
      gadget isAnd m v w = gadget isAnd m' v w := by
  decide

def input (m : ℕ) (v : Fin 9) : Bool := m.testBit v.val

def augmented (m : ℕ) : List Bool :=
  List.ofFn (input m) ++ [input m 0 || input m 2]

lemma signal_encoding (m : ℕ) (w : Fin 10) :
    (augmented m).getD w.val false = signal m w := by
  fin_cases w <;> rfl

lemma raw_encoding (m : ℕ) (v : Fin 9) :
    (augmented m).getD v.val false = m.testBit v.val := by
  have h := signal_encoding m v.castSucc
  simpa [signal, v.isLt] using h

def rawGate (isAnd : Bool) (v : Fin 9) (w : Fin 10) :
    PEqualNP.CircuitLowerBounds.Gate :=
  ⟨bif isAnd then PEqualNP.CircuitLowerBounds.GateOp.and
    else PEqualNP.CircuitLowerBounds.GateOp.or, [v.val, w.val]⟩

lemma gate_encoding (isAnd : Bool) (m : ℕ) (v : Fin 9) (w : Fin 10) :
    (rawGate isAnd v w).op.eval
      ((rawGate isAnd v w).inputs.map fun i => (augmented m).getD i false) =
      gadget isAnd m v w := by
  cases isAnd <;>
    simp only [rawGate, gadget, Bool.cond_false, Bool.cond_true,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, Bool.or_false, List.all_cons, List.all_nil,
      Bool.and_true, id_eq] <;>
    rw [raw_encoding, signal_encoding]

lemma collision_real_inputs :
    ∀ v : Fin 9, v ≠ 0 → v ≠ 2 → ∀ w : Fin 10, v.castSucc ≠ w →
    ∀ isAnd : Bool,
      let m := base v w isAnd
      let m' := m + 2 ^ v.val
      edge m = false ∧ edge m' = true ∧
      (∀ i : Fin 10, i ≠ v.castSucc →
        (augmented m).getD i.val false = (augmented m').getD i.val false) ∧
      (rawGate isAnd v w).op.eval
          ((rawGate isAnd v w).inputs.map fun i => (augmented m).getD i false) =
        (rawGate isAnd v w).op.eval
          ((rawGate isAnd v w).inputs.map fun i => (augmented m').getD i false) := by
  intro v hv0 hv2 w hvw isAnd
  have h := collision_table v hv0 hv2 w hvw isAnd
  dsimp only at h ⊢
  refine ⟨h.2.2.2.1, h.2.2.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [signal_encoding, signal_encoding]
    apply h.2.2.2.2.2.1 i
    intro heq
    apply hi
    exact Fin.ext heq
  · rw [gate_encoding, gate_encoding]
    exact h.2.2.2.2.2.2

def effRead (v : ℕ) (g : Gate) : Bool :=
  (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v

lemma gate_ignores_eq (v : ℕ) (g : Gate) (a b : List Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (hread : effRead v g = false)
    (hab : ∀ i : ℕ, i ≠ v → a.getD i false = b.getD i false) :
    g.op.eval (g.inputs.map fun i => a.getD i false) =
      g.op.eval (g.inputs.map fun i => b.getD i false) := by
  have htake : g.inputs.take 2 = g.inputs := List.take_of_length_le hlen
  rcases hop with hand | hor | hnot
  · have hnotmem : v ∉ g.inputs := by
      simpa [effRead, hand, GateOp.eval, htake] using hread
    have hm : g.inputs.map (fun i => a.getD i false) =
        g.inputs.map (fun i => b.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hab i
      intro heq
      subst i
      exact hnotmem hi
    rw [hm]
  · have hnotmem : v ∉ g.inputs := by
      simpa [effRead, hor, GateOp.eval, htake] using hread
    have hm : g.inputs.map (fun i => a.getD i false) =
        g.inputs.map (fun i => b.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hab i
      intro heq
      subst i
      exact hnotmem hi
    rw [hm]
  · cases hin : g.inputs with
    | nil => simp [hnot, GateOp.eval]
    | cons i tail =>
      have hi : i ≠ v := by
        intro heq
        subst i
        simp [effRead, hnot, hin, GateOp.eval] at hread
      simpa [hnot, hin, GateOp.eval] using congrArg Bool.not (hab i hi)

lemma filter_unique_value {α : Type} (p : α → Bool) (l : List α) (g : α)
    (hg : g ∈ l) (hpg : p g = true) (hlen : (l.filter p).length ≤ 1) :
    ∀ h ∈ l, p h = true → h = g := by
  have hg' : g ∈ l.filter p := by simp [hg, hpg]
  intro h hh hph
  have hh' : h ∈ l.filter p := by simp [hh, hph]
  have heq : l.filter p = [g] := by
    cases hlist : l.filter p with
    | nil => simp [hlist] at hg'
    | cons x xs =>
      have hxs : xs = [] := by
        have hlength : xs.length = 0 := by simpa [hlist] using hlen
        exact List.length_eq_zero_iff.mp hlength
      subst xs
      have hx : x = g := by
        have hx' : g = x := by simpa [hlist] using hg'
        exact hx'.symm
      simp [hx]
  simpa [heq] using hh'

def Except (v : ℕ) (a b : List Bool) : Prop :=
  ∀ i : ℕ, i ≠ v → a.getD i false = b.getD i false

def value (g : Gate) (a : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => a.getD i false)

def step (a : List Bool) (g : Gate) : List Bool := a ++ [value g a]

lemma append_eq_except (v : ℕ) (a b : List Bool) (hlen : a.length = b.length)
    (hab : Except v a b) (x y : Bool) (hxy : x = y) :
    Except v (a ++ [x]) (b ++ [y]) := by
  intro i hi
  by_cases hia : i < a.length
  · rw [List.getD_append a [x] false i hia,
      List.getD_append b [y] false i (by omega)]
    exact hab i hi
  · rw [List.getD_append_right a [x] false i (by omega),
      List.getD_append_right b [y] false i (by omega)]
    rw [hlen, hxy]

lemma gate_prefix_eq (g : Gate) (a suffix : List Bool)
    (hraw : ∀ i ∈ g.inputs, i < a.length) :
    value g (a ++ suffix) = value g a := by
  unfold value
  congr 1
  apply List.map_congr_left
  intro i hi
  exact List.getD_append a suffix false i (hraw i hi)

lemma fold_eq_except (v : ℕ) (A B : List Bool) :
    ∀ gs : List Gate,
    (∀ g ∈ gs, ∀ a b : List Bool,
      (∃ sa, a = A ++ sa) → (∃ sb, b = B ++ sb) →
      Except v a b → value g a = value g b) →
    ∀ a b : List Bool,
      (∃ sa, a = A ++ sa) → (∃ sb, b = B ++ sb) →
      a.length = b.length → Except v a b →
      Except v (gs.foldl step a) (gs.foldl step b) := by
  intro gs
  induction gs with
  | nil =>
    intro hstep a b ha hb hlen hab
    exact hab
  | cons g gs ih =>
    intro hstep a b ha hb hlen hab
    have hv := hstep g (by simp) a b ha hb hab
    simp only [List.foldl_cons]
    apply ih
    · intro g' hg' a' b' ha' hb' hab'
      exact hstep g' (by simp [hg']) a' b' ha' hb' hab'
    · rcases ha with ⟨sa, rfl⟩
      exact ⟨sa ++ [value g (A ++ sa)], by simp [step, List.append_assoc]⟩
    · rcases hb with ⟨sb, rfl⟩
      exact ⟨sb ++ [value g (B ++ sb)], by simp [step, List.append_assoc]⟩
    · simpa [step] using hlen
    · exact append_eq_except v a b hlen hab _ _ hv

lemma circuit_eq_of_only_reader (C : Circuit) (v : ℕ) (A B : List Bool) (g : Gate)
    (hFan : PEqualNP.MetaComplexity.FanInTwo C)
    (hraw : ∀ i ∈ g.inputs, i < A.length) (hlen : A.length = B.length)
    (hinput : Except v A B) (hgvalue : value g A = value g B)
    (honly : ∀ h ∈ C.gates, effRead v h = true → h = g)
    (hout : C.output ≠ v) : C.eval A = C.eval B := by
  have hfold : Except v (C.gates.foldl step A) (C.gates.foldl step B) := by
    apply fold_eq_except v A B C.gates
    · intro h hh a b ha hb hab
      by_cases hr : effRead v h = true
      · have heq := honly h hh hr
        subst h
        rcases ha with ⟨sa, rfl⟩
        rcases hb with ⟨sb, rfl⟩
        rw [gate_prefix_eq g A sa hraw,
          gate_prefix_eq g B sb (by
            intro i hi
            rw [← hlen]
            exact hraw i hi)]
        exact hgvalue
      · have hspec := hFan h hh
        have hop : h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hspec.1
        have hread : effRead v h = false := by
          cases heff : effRead v h <;> simp_all
        exact gate_ignores_eq v h a b hop hspec.2 hread hab
    · exact ⟨[], by simp⟩
    · exact ⟨[], by simp⟩
    · exact hlen
    · exact hinput
  change (C.gates.foldl step A).getD C.output false =
    (C.gates.foldl step B).getD C.output false
  exact hfold C.output hout

lemma fold_prefix (gs : List Gate) (A : List Bool) :
    ∃ suffix, gs.foldl step A = A ++ suffix := by
  induction gs generalizing A with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    rcases ih (step A g) with ⟨suffix, h⟩
    refine ⟨[value g A] ++ suffix, ?_⟩
    simpa [step, List.append_assoc] using h

lemma wires_input (C : Circuit) (A : List Bool) (i : ℕ) (hi : i < A.length) :
    (C.wires A).getD i false = A.getD i false := by
  obtain ⟨suffix, h⟩ := fold_prefix C.gates A
  change (C.gates.foldl step A).getD i false = _
  rw [h]
  exact List.getD_append A suffix false i hi

lemma singleton_test : ∀ v : Fin 9,
    edge (2 ^ v.val) = false ∧
      (augmented (2 ^ v.val)).getD v.val false = true := by
  decide

lemma mixed_value (g : Gate) (v : Fin 9) (w : Fin 10)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hinp : g.inputs = [v.val, w.val] ∨ g.inputs = [w.val, v.val]) (m : ℕ) :
    value g (augmented m) = gadget (!(g.op.eval [true, false])) m v w := by
  rcases hop with hop | hop <;> rcases hinp with hin | hin
  all_goals
    simp only [value, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, Bool.or_false, List.all_cons, List.all_nil,
      Bool.and_true, id_eq]
    rw [raw_encoding, signal_encoding]
    simp [gadget, Bool.and_comm, Bool.or_comm]

end PEqualNP.Outside.L_meta_3582

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3582

theorem PEqualNP.Outside.L_meta_3582 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = x1 x4) → ∀ (x5 : Fin (9 : ℕ)) (x6 : Fin (10 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) → x5 ≠ (2 : Fin (9 : ℕ)) → x5.castSucc ≠ x6 → ∀ x10 ∈ x2.gates, x10.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10.inputs = [↑x5, ↑x6] ∨ x10.inputs = [↑x6, ↑x5] → (2 : ℕ) ≤ (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x5) x2.gates).length := by
  dsimp only
  intro C hFan hcomp v w hv0 hv2 hvw g hg hop hinp
  by_contra hcount
  have hlow : (C.gates.filter (effRead v.val)).length ≤ 1 := by
    change ¬ 2 ≤ (C.gates.filter (effRead v.val)).length at hcount
    omega
  have hpg : effRead v.val g = true := by
    rcases hop with hop | hop <;> rcases hinp with hin | hin <;>
      simp [effRead, hop, hin, GateOp.eval]
  have honly : ∀ h ∈ C.gates, effRead v.val h = true → h = g :=
    filter_unique_value (effRead v.val) C.gates g hg hpg hlow
  have hcompNat (m : ℕ) : C.eval (augmented m) = edge m := by
    simpa [augmented, input, edge] using hcomp (input m)
  have hout : C.output ≠ v.val := by
    intro hbad
    have h := hcompNat (2 ^ v.val)
    unfold Circuit.eval at h
    rw [hbad, wires_input C _ v.val (by simp [augmented]; omega)] at h
    have hs := singleton_test v
    rw [hs.2, hs.1] at h
    cases h
  let isAnd := !(g.op.eval [true, false])
  let m := base v w isAnd
  let m' := m + 2 ^ v.val
  have hc := collision_table v hv0 hv2 w hvw isAnd
  have hr := collision_real_inputs v hv0 hv2 w hvw isAnd
  have hinput : Except v.val (augmented m) (augmented m') := by
    intro i hi
    by_cases hi10 : i < 10
    · exact hr.2.2.1 ⟨i, hi10⟩ (by
        intro heq
        apply hi
        exact congrArg Fin.val heq)
    · exact (List.getD_eq_default (l := augmented m) (d := false) (n := i) (by simp [augmented]; omega)).trans
        (List.getD_eq_default (l := augmented m') (d := false) (n := i) (by simp [augmented]; omega)).symm
  have hraw : ∀ i ∈ g.inputs, i < (augmented m).length := by
    intro i hi
    rcases hinp with hin | hin <;> rw [hin] at hi <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
      rcases hi with rfl | rfl
    all_goals simp [augmented] <;> omega
  have hvalue : value g (augmented m) = value g (augmented m') := by
    rw [mixed_value g v w hop hinp m, mixed_value g v w hop hinp m']
    exact hc.2.2.2.2.2.2
  have hflow := circuit_eq_of_only_reader C v.val (augmented m) (augmented m') g
    hFan hraw (by simp [augmented]) hinput hvalue honly hout
  rw [hcompNat m, hcompNat m', hc.2.2.2.1, hc.2.2.2.2.1] at hflow
  cases hflow

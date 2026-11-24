import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3604_aux

def W1 : List (ℕ × ℕ) := [(20, 21), (1, 3), (9, 13), (4, 12), (1, 17), (1, 33), (2, 66), (4, 132), (8, 264)]

def W2 : List (ℕ × ℕ) :=
  [(0, 0), (0, 0), (4, 6), (1, 3), (9, 12), (9, 12), (4, 12), (5, 12), (8, 24), (1, 17), (20, 21), (1, 33), (2, 66), (21, 84), (4, 132), (5, 132), (8, 264), (9, 265), (4, 6), (1, 3), (0, 0), (0, 0), (1, 3), (3, 5), (1, 3), (3, 9), (1, 3), (6, 20), (1, 3), (6, 36), (1, 3), (2, 66), (1, 3), (3, 129), (1, 3), (3, 257), (9, 12), (9, 12), (1, 3), (3, 5), (0, 0), (0, 0), (16, 24), (4, 12), (1, 17), (5, 17), (1, 33), (5, 33), (2, 66), (13, 73), (9, 13), (4, 132), (8, 264), (36, 292), (4, 12), (5, 12), (1, 3), (3, 9), (16, 24), (4, 12), (0, 0), (0, 0), (1, 17), (8, 24), (1, 33), (9, 33), (2, 66), (10, 66), (4, 12), (24, 144), (4, 12), (8, 264), (8, 24), (1, 17), (1, 3), (6, 20), (1, 17), (5, 17), (1, 17), (8, 24), (0, 0), (0, 0), (1, 17), (24, 40), (1, 17), (17, 65), (1, 17), (17, 129), (1, 17), (17, 257), (20, 21), (1, 33), (1, 3), (6, 36), (1, 33), (5, 33), (1, 33), (9, 33), (1, 17), (24, 40), (0, 0), (0, 0), (1, 33), (33, 65), (1, 33), (32, 160), (1, 33), (32, 288), (2, 66), (21, 84), (1, 3), (2, 66), (2, 66), (13, 73), (2, 66), (10, 66), (1, 17), (17, 65), (1, 33), (33, 65), (0, 0), (0, 0), (2, 66), (66, 130), (2, 66), (64, 320), (4, 132), (5, 132), (1, 3), (3, 129), (9, 13), (4, 132), (4, 12), (24, 144), (1, 17), (17, 129), (1, 33), (32, 160), (2, 66), (66, 130), (0, 0), (0, 0), (4, 132), (132, 260), (8, 264), (9, 265), (1, 3), (3, 257), (8, 264), (36, 292), (4, 12), (8, 264), (1, 17), (17, 257), (1, 33), (32, 288), (2, 66), (64, 320), (4, 132), (132, 260), (0, 0), (0, 0)]

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma drun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma drun_single (g : Gate) (x : List Bool) :
    drun [g] x = x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)] :=
  rfl

lemma drun_append (A B : List Gate) (x : List Bool) : drun (A ++ B) x = drun B (drun A x) := by
  simp [drun, List.foldl_append]

lemma drun_length (gs : List Gate) (x : List Bool) :
    (drun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [drun]
  | cons g gs ih => rw [drun_cons, ih]; simp; omega

lemma drun_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (drun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [drun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

-- Two runs that agree off a set of input wires agree off it at the end, when no gate reads it.
lemma indepB (B : ℕ → Prop) : ∀ (gs : List Gate) (Y0 Y1 : List Bool), Y0.length = Y1.length →
    (∀ i, Y0.length ≤ i → ¬ B i) →
    (∀ i, ¬ B i → Y0.getD i false = Y1.getD i false) →
    (∀ g ∈ gs, ∀ r ∈ g.inputs, ¬ B r) →
    ∀ i, ¬ B i → (drun gs Y0).getD i false = (drun gs Y1).getD i false := by
  intro gs
  induction gs with
  | nil => intro Y0 Y1 _ _ h _; simpa [drun] using h
  | cons g gs ih =>
    intro Y0 Y1 hl hB hY hg
    rw [drun_cons, drun_cons]
    have hv : g.op.eval (g.inputs.map fun i => Y0.getD i false) =
        g.op.eval (g.inputs.map fun i => Y1.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro r hr
      exact hY r (hg g (by simp) r hr)
    apply ih
    · simp [hl]
    · intro i hi
      exact hB i (by simp at hi; omega)
    · intro i hi
      rcases lt_trichotomy i Y0.length with h1 | h1 | h1
      · rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ (by omega)]
        exact hY i hi
      · subst h1
        rw [List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (by omega)]
        rw [Nat.sub_self, hl, Nat.sub_self, List.getD_cons_zero, List.getD_cons_zero]
        exact hv
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg' r hr
      exact hg g' (by simp [hg']) r hr

def fP (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 ||
    x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def tb (n : ℕ) : Fin 9 → Bool := fun i => n.testBit i

def inp (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 2]

lemma inp_len (x : Fin 9 → Bool) : (inp x).length = 10 := by simp [inp]

lemma inp_getD (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) : (inp x).getD i false = x ⟨i, hi⟩ := by
  unfold inp
  rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_ofFn]

lemma inp_getD9 (x : Fin 9 → Bool) : (inp x).getD 9 false = (x 0 || x 2) := by
  unfold inp
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma w1_ok : ∀ v : Fin 9,
    (∀ i : Fin 9, i ≠ v → (W1.getD v (0, 0)).1.testBit i = (W1.getD v (0, 0)).2.testBit i) ∧
    ((W1.getD v (0, 0)).1.testBit 0 || (W1.getD v (0, 0)).1.testBit 2) =
      ((W1.getD v (0, 0)).2.testBit 0 || (W1.getD v (0, 0)).2.testBit 2) ∧
    fP (tb (W1.getD v (0, 0)).1) ≠ fP (tb (W1.getD v (0, 0)).2) := by
  decide +kernel

lemma w2_ok : ∀ a b : Fin 9, a ≠ b → ∀ c : Fin 2,
    (∀ i : Fin 9, i ≠ a → i ≠ b →
      (W2.getD (18 * a + 2 * b + c) (0, 0)).1.testBit i = (W2.getD (18 * a + 2 * b + c) (0, 0)).2.testBit i) ∧
    ((W2.getD (18 * a + 2 * b + c) (0, 0)).1.testBit 0 || (W2.getD (18 * a + 2 * b + c) (0, 0)).1.testBit 2) =
      ((W2.getD (18 * a + 2 * b + c) (0, 0)).2.testBit 0 || (W2.getD (18 * a + 2 * b + c) (0, 0)).2.testBit 2) ∧
    (if (c : ℕ) = 0 then
      ((W2.getD (18 * a + 2 * b + c) (0, 0)).1.testBit a && (W2.getD (18 * a + 2 * b + c) (0, 0)).1.testBit b) =
        ((W2.getD (18 * a + 2 * b + c) (0, 0)).2.testBit a && (W2.getD (18 * a + 2 * b + c) (0, 0)).2.testBit b)
    else
      ((W2.getD (18 * a + 2 * b + c) (0, 0)).1.testBit a || (W2.getD (18 * a + 2 * b + c) (0, 0)).1.testBit b) =
        ((W2.getD (18 * a + 2 * b + c) (0, 0)).2.testBit a || (W2.getD (18 * a + 2 * b + c) (0, 0)).2.testBit b)) ∧
    fP (tb (W2.getD (18 * a + 2 * b + c) (0, 0)).1) ≠ fP (tb (W2.getD (18 * a + 2 * b + c) (0, 0)).2) := by
  decide +kernel

-- The two input lists of a witness pair agree off a set of variables.
lemma agree_off (n n' : ℕ) (B : ℕ → Prop) (hB : ∀ i, 9 ≤ i → ¬ B i)
    (hbits : ∀ i : Fin 9, ¬ B i → n.testBit i = n'.testBit i)
    (h9 : (n.testBit 0 || n.testBit 2) = (n'.testBit 0 || n'.testBit 2)) :
    ∀ i, ¬ B i → (inp (tb n)).getD i false = (inp (tb n')).getD i false := by
  intro i hi
  by_cases hlt : i < 9
  · rw [inp_getD _ _ hlt, inp_getD _ _ hlt]
    exact hbits ⟨i, hlt⟩ hi
  · by_cases he : i = 9
    · subst he
      rw [inp_getD9, inp_getD9]
      exact h9
    · rw [List.getD_eq_default _ _ (by rw [inp_len]; omega), List.getD_eq_default _ _ (by rw [inp_len]; omega)]

theorem m04 (C : Circuit) (ho : 10 ≤ C.output) (hcomp : ∀ x : Fin 9 → Bool, C.eval (inp x) = fP x) :
    (∀ v : Fin 9, (v : ℕ) ∈ C.gates.flatMap Gate.inputs) ∧
    ∀ g ∈ C.gates, ∀ a b : Fin 9, a ≠ b → (g.op = GateOp.and ∨ g.op = GateOp.or) →
      g.inputs = [(a : ℕ), (b : ℕ)] →
      2 ≤ (C.gates.flatMap Gate.inputs).count (a : ℕ) ∨ 2 ≤ (C.gates.flatMap Gate.inputs).count (b : ℕ) := by
  have hval : ∀ x, (drun C.gates (inp x)).getD C.output false = fP x := fun x => hcomp x
  constructor
  · intro v
    by_contra hv
    have hno : ∀ g ∈ C.gates, ∀ r ∈ g.inputs, ¬ (r = (v : ℕ)) := by
      intro g hg r hr hrv
      apply hv
      rw [List.mem_flatMap]
      exact ⟨g, hg, hrv ▸ hr⟩
    obtain ⟨hbits, hw9, hf⟩ := w1_ok v
    have key := indepB (fun i => i = (v : ℕ)) C.gates (inp (tb (W1.getD v (0, 0)).1))
      (inp (tb (W1.getD v (0, 0)).2)) (by simp [inp_len])
      (by intro i hi; rw [inp_len] at hi; omega)
      (agree_off _ _ (fun i => i = (v : ℕ)) (by intro i hi; omega)
        (fun i hi => hbits i (fun e => hi (by rw [e]))) hw9)
      hno C.output (by omega)
    rw [hval, hval] at key
    exact hf key
  · intro g hg a b hab hop hin
    by_contra hc
    push_neg at hc
    obtain ⟨k0, hk0, rfl⟩ := List.getElem_of_mem hg
    have hsplit : C.gates = C.gates.take k0 ++ C.gates[k0] :: C.gates.drop (k0 + 1) := by
      conv_lhs => rw [← List.take_append_drop k0 C.gates, List.drop_eq_getElem_cons hk0]
    have hab' : (a : ℕ) ≠ (b : ℕ) := fun e => hab (Fin.ext e)
    have hcnt : ∀ c : ℕ, (C.gates.flatMap Gate.inputs).count c =
        ((C.gates.take k0).flatMap Gate.inputs).count c + (C.gates[k0]).inputs.count c +
          ((C.gates.drop (k0 + 1)).flatMap Gate.inputs).count c := by
      intro c
      conv_lhs => rw [hsplit]
      simp only [List.flatMap_append, List.flatMap_cons, List.count_append]
      omega
    have ca : (C.gates[k0]).inputs.count (a : ℕ) = 1 := by rw [hin]; simp [hab', hab'.symm]
    have cb : (C.gates[k0]).inputs.count (b : ℕ) = 1 := by rw [hin]; simp [hab', hab'.symm]
    have h1 := hcnt a
    have h2 := hcnt b
    have zpre : ∀ c : ℕ, ((C.gates.take k0).flatMap Gate.inputs).count c = 0 →
        ∀ g' ∈ C.gates.take k0, ∀ r ∈ g'.inputs, r ≠ c := by
      intro c hz g' hg' r hr hrc
      have : c ∈ (C.gates.take k0).flatMap Gate.inputs := List.mem_flatMap.mpr ⟨g', hg', hrc ▸ hr⟩
      rw [List.count_eq_zero] at hz
      exact hz this
    have zpost : ∀ c : ℕ, ((C.gates.drop (k0 + 1)).flatMap Gate.inputs).count c = 0 →
        ∀ g' ∈ C.gates.drop (k0 + 1), ∀ r ∈ g'.inputs, r ≠ c := by
      intro c hz g' hg' r hr hrc
      have : c ∈ (C.gates.drop (k0 + 1)).flatMap Gate.inputs := List.mem_flatMap.mpr ⟨g', hg', hrc ▸ hr⟩
      rw [List.count_eq_zero] at hz
      exact hz this
    have pa := zpre a (by omega)
    have pb := zpre b (by omega)
    have qa := zpost a (by omega)
    have qb := zpost b (by omega)
    let B : ℕ → Prop := fun i => i = (a : ℕ) ∨ i = (b : ℕ)
    -- the witness pair for this gate
    obtain ⟨c, hc⟩ : ∃ c : Fin 2, (C.gates[k0].op = GateOp.and ∧ (c : ℕ) = 0) ∨
        (C.gates[k0].op = GateOp.or ∧ (c : ℕ) = 1) := by
      rcases hop with h | h
      · exact ⟨0, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨1, Or.inr ⟨h, rfl⟩⟩
    obtain ⟨hbits, hw9, hopv, hf⟩ := w2_ok a b hab c
    set p := W2.getD (18 * a + 2 * b + c) (0, 0) with hp
    have hagree := agree_off p.1 p.2 B (by intro i hi; simp only [B]; omega)
      (fun i hi => hbits i (fun e => hi (Or.inl (by rw [e]))) (fun e => hi (Or.inr (by rw [e])))) hw9
    have hB10 : ∀ i, 10 ≤ i → ¬ B i := by intro i hi; simp only [B]; omega
    -- the runs before the gate
    have r1 := indepB B (C.gates.take k0) (inp (tb p.1)) (inp (tb p.2)) (by simp [inp_len])
      (by intro i hi; rw [inp_len] at hi; exact hB10 i hi) hagree
      (fun g' hg' r hr hb => by rcases hb with hb | hb; exact pa g' hg' r hr hb; exact pb g' hg' r hr hb)
    -- the gate's value is the same in both runs
    have hlen0 : ∀ n, (drun (C.gates.take k0) (inp (tb n))).length = 10 + (C.gates.take k0).length := by
      intro n; rw [drun_length, inp_len]
    have getA : ∀ n, (drun (C.gates.take k0) (inp (tb n))).getD a false = n.testBit a := by
      intro n
      rw [drun_getD _ _ _ (by rw [inp_len]; omega), inp_getD _ _ a.2]
      rfl
    have getB : ∀ n, (drun (C.gates.take k0) (inp (tb n))).getD b false = n.testBit b := by
      intro n
      rw [drun_getD _ _ _ (by rw [inp_len]; omega), inp_getD _ _ b.2]
      rfl
    have hgv : C.gates[k0].op.eval (C.gates[k0].inputs.map fun i => (drun (C.gates.take k0) (inp (tb p.1))).getD i false) =
        C.gates[k0].op.eval (C.gates[k0].inputs.map fun i => (drun (C.gates.take k0) (inp (tb p.2))).getD i false) := by
      rw [hin]
      simp only [List.map_cons, List.map_nil, getA, getB]
      rcases hc with ⟨h, hc0⟩ | ⟨h, hc1⟩
      · rw [h]
        simp only [hc0, ↓reduceIte] at hopv
        simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
        exact hopv
      · rw [h]
        simp only [hc1, one_ne_zero, ↓reduceIte] at hopv
        simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
        exact hopv
    -- after the gate, then the rest
    have r2 := indepB B (C.gates.drop (k0 + 1))
      (drun [C.gates[k0]] (drun (C.gates.take k0) (inp (tb p.1))))
      (drun [C.gates[k0]] (drun (C.gates.take k0) (inp (tb p.2))))
      (by simp only [drun_length, inp_len])
      (by intro i hi; rw [drun_length, hlen0] at hi; exact hB10 i (by omega))
      (by
        intro i hi
        rw [drun_single, drun_single]
        rcases lt_trichotomy i (10 + (C.gates.take k0).length) with h1 | h1 | h1
        · rw [List.getD_append _ _ _ _ (by rw [hlen0]; exact h1), List.getD_append _ _ _ _ (by rw [hlen0]; exact h1)]
          exact r1 i hi
        · subst h1
          rw [List.getD_append_right _ _ _ _ (by rw [hlen0]), List.getD_append_right _ _ _ _ (by rw [hlen0])]
          simp only [hlen0, Nat.sub_self, List.getD_cons_zero]
          exact hgv
        · rw [List.getD_eq_default _ _ (by simp only [List.length_append, hlen0, List.length_singleton]; omega),
            List.getD_eq_default _ _ (by simp only [List.length_append, hlen0, List.length_singleton]; omega)])
      (fun g' hg' r hr hb => by rcases hb with hb | hb; exact qa g' hg' r hr hb; exact qb g' hg' r hr hb)
      C.output (by simp only [B]; omega)
    have e1 : drun C.gates (inp (tb p.1)) = drun (C.gates.drop (k0 + 1)) (drun [C.gates[k0]] (drun (C.gates.take k0) (inp (tb p.1)))) := by
      conv_lhs => rw [hsplit]
      rw [show C.gates.take k0 ++ C.gates[k0] :: C.gates.drop (k0 + 1) =
        C.gates.take k0 ++ ([C.gates[k0]] ++ C.gates.drop (k0 + 1)) from rfl, drun_append, drun_append]
    have e2 : drun C.gates (inp (tb p.2)) = drun (C.gates.drop (k0 + 1)) (drun [C.gates[k0]] (drun (C.gates.take k0) (inp (tb p.2)))) := by
      conv_lhs => rw [hsplit]
      rw [show C.gates.take k0 ++ C.gates[k0] :: C.gates.drop (k0 + 1) =
        C.gates.take k0 ++ ([C.gates[k0]] ++ C.gates.drop (k0 + 1)) from rfl, drun_append, drun_append]
    rw [← e1, ← e2, hval, hval] at r2
    exact hf r2

end PEqualNP.Outside.L_meta_3604_aux

theorem PEqualNP.Outside.L_meta_3604 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (10 : ℕ) ≤ x1.output →     (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ))]) = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) x3) →       have x4 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates;       (∀ (x5 : Fin (9 : ℕ)), ↑x5 ∈ x4) ∧ ∀ x5 ∈ x1.gates, ∀ (x7 x8 : Fin (9 : ℕ)), x7 ≠ x8 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5.inputs = [↑x7, ↑x8] → (2 : ℕ) ≤ List.count (↑x7) x4 ∨ (2 : ℕ) ≤ List.count (↑x8) x4 := by
  intro x1 ho hcomp
  exact PEqualNP.Outside.L_meta_3604_aux.m04 x1 ho hcomp

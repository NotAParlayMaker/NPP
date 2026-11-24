import Mathlib.Data.List.Forall2
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2768_1
    (early : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.gates.length = 15 → C.output = 23 →
      C.gates[0]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0,3] } →
      List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [false]) C.gates = 1 →
      (∃ pre g post, C.gates = pre ++ g :: post ∧ pre.length < 8 ∧
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      PEqualNP.MetaComplexity.circuitFun 9 C ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))
    (middle : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.gates.length = 15 → C.output = 23 →
      C.gates[0]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0,3] } →
      List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [false]) C.gates = 1 →
      (∃ pre g post, C.gates = pre ++ g :: post ∧ 8 ≤ pre.length ∧ pre.length < 14 ∧
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      PEqualNP.MetaComplexity.circuitFun 9 C ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C shape count computes
  obtain ⟨hlen, hout, hfirst, hslots⟩ := shape
  have hfan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg
    have hs := hslots i hi
    rw [hgi] at hs
    rcases hs with rfl | ⟨a, _, rfl⟩ | ⟨a, b, _, _, _, rfl | rfl⟩ <;>
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  by_cases hearly : ∃ pre g post, C.gates = pre ++ g :: post ∧
      pre.length < 8 ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact early C hfan hlen hout hfirst count hearly computes
  by_cases hmiddle : ∃ pre g post, C.gates = pre ++ g :: post ∧
      8 ≤ pre.length ∧ pre.length < 14 ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact middle C hfan hlen hout hfirst count hmiddle computes
  have hnonempty : C.gates ≠ [] := by intro h; simp [h] at hlen
  obtain ⟨pre, g, hgates⟩ : ∃ pre g, C.gates = pre ++ [g] := by
    cases hr : C.gates.reverse with
    | nil =>
      have he := congrArg List.reverse hr
      have he' : C.gates = [] := by simpa using he
      exact (hnonempty he').elim
    | cons g tail =>
      refine ⟨tail.reverse, g, ?_⟩
      have he := congrArg List.reverse hr
      simpa using he
  have hprelen : pre.length = 14 := by rw [hgates] at hlen; simp at hlen; omega
  have split_member : ∀ (a : PEqualNP.CircuitLowerBounds.Gate) (l : List PEqualNP.CircuitLowerBounds.Gate),
      a ∈ l → ∃ before after, l = before ++ a :: after := by
    intro a l
    induction l with
    | nil => simp
    | cons b tail ih =>
      intro ha
      rcases List.mem_cons.mp ha with heq | ht
      · subst b; exact ⟨[], tail, rfl⟩
      · obtain ⟨before, after, heq⟩ := ih ht
        exact ⟨b :: before, after, by simp [heq]⟩
  have hpre : ∀ a ∈ pre, a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      a.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro a ha
    have haC : a ∈ C.gates := by rw [hgates]; simp [ha]
    have hb := (hfan a haC).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with hb | hb | hb
    · exact Or.inl hb
    · exact Or.inr hb
    · exfalso
      obtain ⟨before, after, hsplit⟩ := split_member a pre ha
      have hbefore : before.length < 14 := by rw [hsplit] at hprelen; simp at hprelen; omega
      have hsplitC : C.gates = before ++ a :: (after ++ [g]) := by
        rw [hgates, hsplit]; simp [List.append_assoc]
      by_cases hb8 : before.length < 8
      · exact hearly ⟨before, a, after ++ [g], hsplitC, hb8, hb⟩
      · exact hmiddle ⟨before, a, after ++ [g], hsplitC, by omega, hbefore, hb⟩
  have hprecount : List.countP (fun a : PEqualNP.CircuitLowerBounds.Gate =>
      a.op.eval [false]) pre = 0 := by
    apply List.countP_eq_zero.mpr
    intro a ha
    rcases hpre a ha with h | h <;> simp [h, PEqualNP.CircuitLowerBounds.GateOp.eval]
  have hgnot : g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    have hgC : g ∈ C.gates := by rw [hgates]; simp
    have hb := (hfan g hgC).1
    rw [hgates, List.countP_append, hprecount] at count
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with hb | hb | hb
    · simp [hb, PEqualNP.CircuitLowerBounds.GateOp.eval] at count
    · simp [hb, PEqualNP.CircuitLowerBounds.GateOp.eval] at count
    · exact hb
  let rel : Bool → Bool → Prop := fun a b => a = true → b = true
  have get_mono : ∀ {a b : List Bool}, List.Forall₂ rel a b →
      ∀ i, rel (a.getD i false) (b.getD i false) := by
    intro a b h
    induction h with
    | nil => intro i; simp [rel]
    | @cons a b as bs hab htail ih =>
      intro i
      cases i with
      | zero => simpa using hab
      | succ i => simpa using ih i
  have append_rel : ∀ {a b : List Bool}, List.Forall₂ rel a b →
      ∀ {c d : List Bool}, List.Forall₂ rel c d → List.Forall₂ rel (a ++ c) (b ++ d) := by
    intro a b h
    induction h with
    | nil => intro c d hcd; exact hcd
    | cons hab htail ih =>
      intro c d hcd
      exact List.Forall₂.cons hab (ih hcd)
  let run := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) =>
    gs.foldl (fun w a => w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]) w
  have run_mono : ∀ gs, (∀ a ∈ gs,
      a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      a.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∀ w v, List.Forall₂ rel w v → List.Forall₂ rel (run gs w) (run gs v) := by
    intro gs
    induction gs with
    | nil => intro _ w v h; exact h
    | cons a gs ih =>
      intro h w v hw
      apply ih (fun b hb => h b (by simp [hb]))
      apply append_rel hw
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      change a.op.eval (a.inputs.map fun i => w.getD i false) = true →
        a.op.eval (a.inputs.map fun i => v.getD i false) = true
      rcases h a (by simp) with hop | hop
      · rw [hop]
        change (a.inputs.map fun i => w.getD i false).all id = true →
          (a.inputs.map fun i => v.getD i false).all id = true
        intro hall
        apply List.all_eq_true.mpr
        intro b hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
        apply get_mono hw i
        exact List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
      · rw [hop]
        change (a.inputs.map fun i => w.getD i false).any id = true →
          (a.inputs.map fun i => v.getD i false).any id = true
        intro hany
        obtain ⟨b, hb, hbt⟩ := List.any_eq_true.mp hany
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
        apply List.any_eq_true.mpr
        exact ⟨v.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, get_mono hw i hbt⟩
  have run_length : ∀ gs w, (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [run]
    | cons a gs ih =>
      intro w
      change (run gs (w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)])).length = _
      rw [ih]
      simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]
      omega
  let w0 := run pre (List.ofFn fun _ : Fin 9 => false)
  let w1 := run pre (List.ofFn fun _ : Fin 9 => true)
  have hw : List.Forall₂ rel w0 w1 := run_mono pre hpre _ _ (by decide)
  have hl0 : w0.length = 23 := by rw [run_length]; simp [hprelen]
  have hl1 : w1.length = 23 := by rw [run_length]; simp [hprelen]
  have hinput : (g.inputs.map fun i => w0.getD i false).headD false = true →
      (g.inputs.map fun i => w1.getD i false).headD false = true := by
    cases g.inputs with
    | nil => simp
    | cons i rest => simpa using get_mono hw i
  have hzero : C.eval (List.ofFn fun _ : Fin 9 => false) = false := by
    have h := congrFun computes (fun _ => false)
    simpa [PEqualNP.MetaComplexity.circuitFun] using h
  have hone : C.eval (List.ofFn fun _ : Fin 9 => true) = true := by
    have h := congrFun computes (fun _ => true)
    simpa [PEqualNP.MetaComplexity.circuitFun] using h
  have hz : Bool.not ((g.inputs.map fun i => w0.getD i false).headD false) = false := by
    simpa [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hgates, hout,
      List.foldl_append, hgnot, PEqualNP.CircuitLowerBounds.GateOp.eval,
      ← hl0, w0, run] using hzero
  have ho : Bool.not ((g.inputs.map fun i => w1.getD i false).headD false) = true := by
    simpa [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hgates, hout,
      List.foldl_append, hgnot, PEqualNP.CircuitLowerBounds.GateOp.eval,
      ← hl1, w1, run] using hone
  have hzt : (g.inputs.map fun i => w0.getD i false).headD false = true := by simpa using hz
  have hot := hinput hzt
  rw [hot] at ho
  contradiction

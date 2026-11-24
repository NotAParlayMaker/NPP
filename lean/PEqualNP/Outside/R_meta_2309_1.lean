import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2309_1
    (h1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !x 0) →
      (PEqualNP.MetaComplexity.circuitFun 9 C = fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      C.size ≤ 15 →
      ∀ g : PEqualNP.CircuitLowerBounds.Gate,
      List.filter (fun h : PEqualNP.CircuitLowerBounds.Gate => [0, 9].any fun i => h.inputs.contains i)
        (List.map (fun h : PEqualNP.CircuitLowerBounds.Gate =>
          ({ op := h.op, inputs := if h.op.eval [false] = true then List.take 1 h.inputs else h.inputs } :
            PEqualNP.CircuitLowerBounds.Gate)) (List.drop 1 C.gates)) = [g] →
      0 ∈ g.inputs → 9 ∉ g.inputs → False)
    (h2 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !x 0) →
      (PEqualNP.MetaComplexity.circuitFun 9 C = fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      C.size ≤ 15 →
      ∀ g : PEqualNP.CircuitLowerBounds.Gate,
      List.filter (fun h : PEqualNP.CircuitLowerBounds.Gate => [0, 9].any fun i => h.inputs.contains i)
        (List.map (fun h : PEqualNP.CircuitLowerBounds.Gate =>
          ({ op := h.op, inputs := if h.op.eval [false] = true then List.take 1 h.inputs else h.inputs } :
            PEqualNP.CircuitLowerBounds.Gate)) (List.drop 1 C.gates)) = [g] →
      9 ∈ g.inputs → 0 ∉ g.inputs → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => { op := x3.op, inputs := if x3.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x2.gates);   have x4 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5;   have x5 : ℕ := (List.filter x4 x3).length;   PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → x5 ≤ (1 : ℕ) → False := by
  intro F C L R n5 hfan hnot hfun hsize h5
  simp only [F] at hfun
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool), ∃ r : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l = l ++ r := by
    intro gs
    induction gs with
    | nil => intro l; exact ⟨[], by simp⟩
    | cons g gs ih =>
      intro l
      obtain ⟨r, hr⟩ := ih (l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)])
      exact ⟨g.op.eval (g.inputs.map fun i => l.getD i false) :: r, by rw [List.foldl_cons, hr]; simp⟩
  have hlen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).length =
        l.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro l; simp
    | cons g gs ih =>
      intro l
      rw [List.foldl_cons, ih]
      simp
      omega
  have hval : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).getD
          (l.length + j) false =
        gs[j].op.eval (gs[j].inputs.map fun i => if i < l.length + j then
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).getD i false
          else false) := by
    intro gs l j hj
    obtain ⟨r, hr⟩ := hpre (gs.drop (j + 1))
      ((gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l ++
        [gs[j].op.eval (gs[j].inputs.map fun i =>
          ((gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).getD
            i false)])
    have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
      rw [List.getElem_cons_drop, List.take_append_drop]
    have hW : gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l =
        (gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l ++
        [gs[j].op.eval (gs[j].inputs.map fun i =>
          ((gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).getD
            i false)] ++ r := by
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
      exact hr
    have hAl : ((gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        l).length = l.length + j := by
      rw [hlen, List.length_take]
      omega
    rw [hW]
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega), hAl,
      Nat.sub_self]
    simp only [List.cons_append, List.getElem?_cons_zero, Option.getD_some]
    congr 1
    apply List.map_congr_left
    intro i _
    split_ifs with hi
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  have hwires : ∀ x : List Bool, C.wires x =
      C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := by
    intro x
    rfl
  have hin : ∀ (x : Fin 9 → Bool) (k : ℕ) (hk : k < 9), (C.wires (List.ofFn x)).getD k false = x ⟨k, hk⟩ := by
    intro x k hk
    obtain ⟨r, hr⟩ := hpre C.gates (List.ofFn x)
    rw [hwires, hr, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hk),
      List.getElem?_ofFn]
    simp [hk]
  have hgate : ∀ (x : Fin 9 → Bool) (j : ℕ) (hj : j < C.gates.length),
      (C.wires (List.ofFn x)).getD (9 + j) false =
        C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < 9 + j then
          (C.wires (List.ofFn x)).getD i false else false) := by
    intro x j hj
    have := hval C.gates (List.ofFn x) j hj
    simp only [List.length_ofFn] at this
    rw [hwires]
    exact this
  have hwlen : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).length = 9 + C.gates.length := by
    intro x
    rw [hwires, hlen, List.length_ofFn]
  have indep : (∀ g ∈ C.gates.drop 1,
      ((0 ∉ (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs) ∧
          9 ∉ (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs)) ∨
        (0 ∈ (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs) ∧
          9 ∈ (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs)))) → False := by
    intro hP
    have key : ∀ (x x' : Fin 9 → Bool), (∀ i : Fin 9, i ≠ 0 → x i = x' i) →
        ∀ k, k ≠ 0 → k ≠ 9 →
          (C.wires (List.ofFn x)).getD k false = (C.wires (List.ofFn x')).getD k false := by
      intro x x' hxx' k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
      intro hk0 hk9
      by_cases hk : k < 9
      · rw [hin x k hk, hin x' k hk]
        apply hxx'
        intro h
        apply hk0
        have := congrArg Fin.val h
        simpa using this
      · obtain ⟨j, rfl⟩ : ∃ j, k = 9 + j := ⟨k - 9, by omega⟩
        by_cases hj : j < C.gates.length
        · have hj1 : 1 ≤ j := by omega
          rw [hgate x j hj, hgate x' j hj]
          have hmem : C.gates[j] ∈ C.gates.drop 1 := by
            have h0 : j - 1 < (C.gates.drop 1).length := by simp; omega
            have e : (C.gates.drop 1)[j - 1] = C.gates[j] := by
              rw [List.getElem_drop]
              congr 1
              omega
            rw [← e]
            exact List.getElem_mem h0
          have hf := hfan _ (List.getElem_mem hj)
          have hag : ∀ i, i ≠ 0 → i ≠ 9 →
              (if i < 9 + j then (C.wires (List.ofFn x)).getD i false else false) =
                (if i < 9 + j then (C.wires (List.ofFn x')).getD i false else false) := by
            intro i hi0 hi9
            split_ifs with hi
            · exact ih i hi hi0 hi9
            · rfl
          have h0x : ∀ y : Fin 9 → Bool,
              (if (0 : ℕ) < 9 + j then (C.wires (List.ofFn y)).getD 0 false else false) = y 0 := by
            intro y
            rw [if_pos (by omega), hin y 0 (by norm_num)]
            rfl
          have h9x : ∀ y : Fin 9 → Bool,
              (if (9 : ℕ) < 9 + j then (C.wires (List.ofFn y)).getD 9 false else false) = !y 0 := by
            intro y
            rw [if_pos (by omega), hnot y]
          rcases hf with ⟨hop, hlen2⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop | hop | hop
          · have hE : (if C.gates[j].op.eval [false] = true then C.gates[j].inputs.take 1
                else C.gates[j].inputs) = C.gates[j].inputs := by
              rw [hop]
              simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
            rcases hP _ hmem with ⟨ha0, ha9⟩ | ⟨hb0, hb9⟩
            · rw [hE] at ha0 ha9
              congr 1
              apply List.map_congr_left
              intro i hi
              exact hag i (fun h => ha0 (h ▸ hi)) (fun h => ha9 (h ▸ hi))
            · rw [hE] at hb0 hb9
              rw [hop]
              match hin2 : C.gates[j].inputs, hlen2, hb0, hb9 with
              | [], _, hb0, _ => simp at hb0
              | [a], _, hb0, hb9 =>
                simp at hb0 hb9
                omega
              | [a, b], _, hb0, hb9 =>
                simp at hb0 hb9
                rcases hb0 with rfl | rfl <;> rcases hb9 with h | h <;> (try omega) <;> subst h <;>
                  simp only [List.map_cons, List.map_nil, h0x, h9x,
                    PEqualNP.CircuitLowerBounds.GateOp.eval] <;> simp
              | _ :: _ :: _ :: _, hl, _, _ => simp at hl
          · have hE : (if C.gates[j].op.eval [false] = true then C.gates[j].inputs.take 1
                else C.gates[j].inputs) = C.gates[j].inputs := by
              rw [hop]
              simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
            rcases hP _ hmem with ⟨ha0, ha9⟩ | ⟨hb0, hb9⟩
            · rw [hE] at ha0 ha9
              congr 1
              apply List.map_congr_left
              intro i hi
              exact hag i (fun h => ha0 (h ▸ hi)) (fun h => ha9 (h ▸ hi))
            · rw [hE] at hb0 hb9
              rw [hop]
              match hin2 : C.gates[j].inputs, hlen2, hb0, hb9 with
              | [], _, hb0, _ => simp at hb0
              | [a], _, hb0, hb9 =>
                simp at hb0 hb9
                omega
              | [a, b], _, hb0, hb9 =>
                simp at hb0 hb9
                rcases hb0 with rfl | rfl <;> rcases hb9 with h | h <;> (try omega) <;> subst h <;>
                  simp only [List.map_cons, List.map_nil, h0x, h9x,
                    PEqualNP.CircuitLowerBounds.GateOp.eval] <;> simp
              | _ :: _ :: _ :: _, hl, _, _ => simp at hl
          · have hE : (if C.gates[j].op.eval [false] = true then C.gates[j].inputs.take 1
                else C.gates[j].inputs) = C.gates[j].inputs.take 1 := by
              rw [hop]
              simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
            rw [hop]
            rcases hP _ hmem with ⟨ha0, ha9⟩ | ⟨hb0, hb9⟩
            · rw [hE] at ha0 ha9
              match hin2 : C.gates[j].inputs, ha0, ha9 with
              | [], _, _ => rfl
              | a :: rest, ha0, ha9 =>
                simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at ha0 ha9
                simp only [List.map_cons, PEqualNP.CircuitLowerBounds.GateOp.eval, List.headD_cons]
                rw [hag a (fun h => ha0 h.symm) (fun h => ha9 h.symm)]
            · rw [hE] at hb0 hb9
              match hin2 : C.gates[j].inputs, hb0, hb9 with
              | [], hb0, _ => simp at hb0
              | a :: rest, hb0, hb9 =>
                simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hb0 hb9
                omega
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by rw [hwlen]; omega), List.getElem?_eq_none (by rw [hwlen]; omega)]
    have hf : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD C.output false =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      intro x
      have := congrFun hfun x
      simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval] using this
    by_cases ho0 : C.output = 0
    · have e := hf ![true, false, false, false, false, false, false, false, false]
      rw [ho0, hin _ 0 (by norm_num)] at e
      revert e
      decide
    · by_cases ho9 : C.output = 9
      · have e := hf ![false, false, false, false, false, false, false, false, false]
        rw [ho9, hnot] at e
        revert e
        decide
      · have e1 := hf ![true, true, false, false, false, false, false, false, false]
        have e2 := hf ![false, true, false, false, false, false, false, false, false]
        rw [key ![true, true, false, false, false, false, false, false, false]
          ![false, true, false, false, false, false, false, false, false] (by decide) C.output ho0 ho9,
          e2] at e1
        revert e1
        decide
  have hT : ∀ g : PEqualNP.CircuitLowerBounds.Gate,
      ({ op := g.op, inputs := if g.op.eval [false] = true then List.take 1 g.inputs else g.inputs } :
        PEqualNP.CircuitLowerBounds.Gate).inputs =
      (if g.op.eval [false] = true then List.take 1 g.inputs else g.inputs) := fun g => rfl
  have hRiff : ∀ g : PEqualNP.CircuitLowerBounds.Gate, R g = true ↔ (0 ∈ g.inputs ∨ 9 ∈ g.inputs) := by
    intro g
    simp [R]
  have hlen1 : (List.filter R L).length ≤ 1 := h5
  match hfl : List.filter R L, hlen1 with
  | [], _ =>
    apply indep
    intro g hg
    left
    have hgL : ({ op := g.op, inputs := if g.op.eval [false] = true then List.take 1 g.inputs
        else g.inputs } : PEqualNP.CircuitLowerBounds.Gate) ∈ L := by
      simp only [L]
      exact List.mem_map_of_mem hg
    have hno : R ({ op := g.op, inputs := if g.op.eval [false] = true then List.take 1 g.inputs
        else g.inputs } : PEqualNP.CircuitLowerBounds.Gate) = false := by
      by_contra hc
      have : ({ op := g.op, inputs := if g.op.eval [false] = true then List.take 1 g.inputs
          else g.inputs } : PEqualNP.CircuitLowerBounds.Gate) ∈ List.filter R L :=
        List.mem_filter.2 ⟨hgL, by simpa using hc⟩
      rw [hfl] at this
      simp at this
    have := (hRiff ({ op := g.op, inputs := if g.op.eval [false] = true then List.take 1 g.inputs
        else g.inputs } : PEqualNP.CircuitLowerBounds.Gate)).not.1 (by rw [hno]; simp)
    rw [hT] at this
    exact not_or.1 this
  | [g'], _ =>
    by_cases hg0 : 0 ∈ g'.inputs <;> by_cases hg9 : 9 ∈ g'.inputs
    · apply indep
      intro g hg
      have hgL : ({ op := g.op, inputs := if g.op.eval [false] = true then List.take 1 g.inputs
          else g.inputs } : PEqualNP.CircuitLowerBounds.Gate) ∈ L := by
        simp only [L]
        exact List.mem_map_of_mem hg
      by_cases hr : R ({ op := g.op, inputs := if g.op.eval [false] = true then List.take 1 g.inputs
          else g.inputs } : PEqualNP.CircuitLowerBounds.Gate) = true
      · right
        have : ({ op := g.op, inputs := if g.op.eval [false] = true then List.take 1 g.inputs
            else g.inputs } : PEqualNP.CircuitLowerBounds.Gate) ∈ List.filter R L :=
          List.mem_filter.2 ⟨hgL, hr⟩
        rw [hfl, List.mem_singleton] at this
        rw [← hT, this]
        exact ⟨hg0, hg9⟩
      · left
        have := (hRiff _).not.1 hr
        rw [hT] at this
        exact not_or.1 this
    · exact h1 C hfan hnot hfun hsize g' hfl hg0 hg9
    · exact h2 C hfan hnot hfun hsize g' hfl hg9 hg0
    · have : g' ∈ List.filter R L := by rw [hfl]; simp
      have hr := (List.mem_filter.1 this).2
      exact (not_or.2 ⟨hg0, hg9⟩) ((hRiff g').1 hr)
  | _ :: _ :: _, hl => simp at hl

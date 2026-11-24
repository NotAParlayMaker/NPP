import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3130_486
    (floor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) 14)
    (remaining : have reads : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun g i => g.inputs[0]? = some i ∨ g.op ≠ .not ∧ i ∈ g.inputs;
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size = 14 → C.output = 23 → (∀ v ∈ [4,6,9], ∃! j : Fin C.gates.length, reads (C.gates.get j) v) →
      (∀ (j : Fin C.gates.length) i, reads (C.gates.get j) i → i < 10+j.val) →
      ∀ K : Finset (Fin C.gates.length), K.card = 3 →
      (∀ j ∈ K, (C.gates.get j).op = .or ∧ ∃ v ∈ [4,6,9], reads (C.gates.get j) v) →
      (∀ j ∉ K, ∀ i ∈ (C.gates.get j).inputs, reads (C.gates.get j) i →
        ∃ y z : Fin 7 → Bool,
          ((⟨C.gates.take j.val,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires [y 4,y 3,y 0,y 5,false,y 1,false,y 2,y 6,false]).getD i false ≠
          ((⟨C.gates.take j.val,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires [z 4,z 3,z 0,z 5,false,z 1,false,z 2,z 6,false]).getD i false) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 || x 6]) ≠ (([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (14 : ℕ) →       have x4 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) => x4.inputs[(0 : ℕ)]? = Option.some x5 ∨ x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x4.inputs;       (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)], ∃! x7 : Fin x1.gates.length, x4 (x1.gates.get x7) x5) →         ∀ (x6 : Finset (Fin x1.gates.length)),           x6.card + (11 : ℕ) ≤ x1.size →             (∀ x8 ∉ x6, ∀ x10 ∈ [(4 : ℕ), (6 : ℕ), (9 : ℕ)], ¬x4 (x1.gates.get x8) x10) →               (∀ x9 ∉ x6,                   ∀ x11 ∈ (x1.gates.get x9).inputs,                     x4 (x1.gates.get x9) x11 →                       have x14 : (Fin (7 : ℕ) → Bool) → Bool := fun (x14 : Fin (7 : ℕ) → Bool) => ({ gates := List.take (↑x9) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires [x14 (4 : Fin (7 : ℕ)), x14 (3 : Fin (7 : ℕ)), x14 (0 : Fin (7 : ℕ)), x14 (5 : Fin (7 : ℕ)), Bool.false, x14 (1 : Fin (7 : ℕ)), Bool.false, x14 (2 : Fin (7 : ℕ)), x14 (6 : Fin (7 : ℕ)), Bool.false]).getD x11 Bool.false;                       ∃ (x15 : Fin (7 : ℕ) → Bool) (x16 : Fin (7 : ℕ) → Bool), x14 x15 ≠ x14 x16) →                 ∃ (x10 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x10 ++ [x10 (4 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ))]) ≠ (fun (x11 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x12 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x12 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x12 % (10 : ℕ)))) x10 := by
  classical
  let read (g : PEqualNP.CircuitLowerBounds.Gate) (i : ℕ) : Prop :=
    g.inputs[0]? = some i ∨ g.op ≠ .not ∧ i ∈ g.inputs

  let value (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : Bool :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool := w ++ [value w g]

  let run (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool := gs.foldl step w

  let rename (k i j : ℕ) : ℕ := if j < k then j else if j = k then i else j - 1

  let mapGate (f : ℕ → ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨g.op, g.inputs.map f⟩

  have evalAnd (xs : List Bool) :
      PEqualNP.CircuitLowerBounds.GateOp.and.eval xs = xs.all id := rfl
  have evalOr (xs : List Bool) :
      PEqualNP.CircuitLowerBounds.GateOp.or.eval xs = xs.any id := rfl
  have evalNot (xs : List Bool) :
      PEqualNP.CircuitLowerBounds.GateOp.not.eval xs = !(xs.headD false) := rfl

  have head_read {g : PEqualNP.CircuitLowerBounds.Gate} {i : ℕ} (h : g.inputs.head? = some i) : read g i :=
    Or.inl (by simpa only [List.head?_eq_getElem?] using h)

  have not_read {g : PEqualNP.CircuitLowerBounds.Gate} {i : ℕ} (h : g.op = .not) :
      read g i ↔ g.inputs.head? = some i := by
    simp [read, h, List.head?_eq_getElem?]

  have read_mem {g : PEqualNP.CircuitLowerBounds.Gate} {i : ℕ} (h : read g i) : i ∈ g.inputs :=
    h.elim List.mem_of_getElem? And.right

  have read_nonnot {g : PEqualNP.CircuitLowerBounds.Gate} {i : ℕ} (h : g.op ≠ .not) : read g i ↔ i ∈ g.inputs :=
    ⟨read_mem, fun hi => Or.inr ⟨h, hi⟩⟩

  have value_map (f : ℕ → ℕ) (w v : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate)
      (h : ∀ i, read g i → w.getD (f i) false = v.getD i false) :
      value w (mapGate f g) = value v g := by
    by_cases hn : g.op = .not
    · cases hi : g.inputs with
      | nil => simp [value, mapGate, hn, hi, evalNot]
      | cons i rest =>
        have hr : read g i := head_read (by simp [hi])
        have he := h i hr
        simp only [value, mapGate, hn, hi, List.map_cons, evalNot, List.headD_cons, he]
    · unfold value mapGate
      simp only [List.map_map]
      congr 1
      exact List.map_congr_left (fun i hi => h i ((read_nonnot hn).2 hi))

  have gate_map_fan (f : ℕ → ℕ) {g : PEqualNP.CircuitLowerBounds.Gate}
      (h : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) :
      (mapGate f g).op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
        (mapGate f g).inputs.length ≤ 2 := by simpa [mapGate] using h

  have run_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (step w g)).length = _
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega

  have run_read (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step w g)).getD i false = _
      have h : i < (step w g).length := by simp [step]; omega
      exact (ih _ h).trans (List.getD_append _ _ _ _ hi)

  have run_snoc (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      run (gs ++ [g]) w = step (run gs w) g := by simp [run]

  have read_snoc (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simp

  have insert_read (p q : List Bool) (b : Bool) (r j : ℕ) (hr : r < p.length)
      (h : j = p.length → p.getD r false = b) :
      (p ++ q).getD (rename p.length r j) false = (p ++ b :: q).getD j false := by
    by_cases hlt : j < p.length
    · simp only [rename, ite_eq_left hlt]
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
    · by_cases he : j = p.length
      · subst j
        simp only [rename, lt_self_iff_false, ite_false, ite_true]
        rw [List.getD_append _ _ _ _ hr, List.getD_append_right _ _ _ _ le_rfl]
        simpa using h rfl
      · have hj : p.length < j := by omega
        simp only [rename, ite_eq_right hlt, ite_eq_right he]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        have hdiff : j - p.length = (j - 1 - p.length) + 1 := by omega
        rw [hdiff, List.getD_cons_succ]

  have erase_run (s : List PEqualNP.CircuitLowerBounds.Gate) (p q : List Bool) (b : Bool) (r : ℕ) (hr : r < p.length)
      (h : (∃ g ∈ s, read g p.length) → p.getD r false = b) :
      ∃ Q, run (s.map (mapGate (rename p.length r))) (p ++ q) = p ++ Q ∧
        run s (p ++ b :: q) = p ++ b :: Q := by
    induction s generalizing q with
    | nil => exact ⟨q, rfl, rfl⟩
    | cons g s ih =>
      have hv := value_map (rename p.length r) (p ++ q) (p ++ b :: q) g (by
        intro i hi
        exact insert_read p q b r i hr (fun e => h ⟨g, List.mem_cons_self, e ▸ hi⟩))
      let q' := q ++ [value (p ++ b :: q) g]
      have hleft : step (p ++ q) (mapGate (rename p.length r) g) = p ++ q' := by
        simp only [step, hv, q', List.append_assoc]
      have hright : step (p ++ b :: q) g = p ++ b :: q' := by
        simp only [step, q', List.append_assoc, List.cons_append]
      obtain ⟨Q, hQ, hQ'⟩ := ih q' (by
        rintro ⟨g',hg',hg''⟩
        exact h ⟨g',List.mem_cons_of_mem _ hg',hg''⟩)
      exact ⟨Q, by simpa only [run, List.map_cons, List.foldl_cons, hleft] using hQ,
        by simpa only [run, List.foldl_cons, hright] using hQ'⟩

  have erase_gate (t s : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (out r n : ℕ)
      (fan : PEqualNP.MetaComplexity.FanInTwo (⟨t ++ g :: s,out⟩ : PEqualNP.CircuitLowerBounds.Circuit)) (hr : r < n + t.length) :
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 1 = (t ++ g :: s).length ∧
        ∀ w : List Bool, w.length = n →
          ((out = n + t.length ∨ ∃ a ∈ s, read a (n + t.length)) →
            (run t w).getD r false = value (run t w) g) →
          D.eval w = (⟨t ++ g :: s,out⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval w := by
    let k := n + t.length
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨t ++ s.map (mapGate (rename k r)), rename k r out⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro a ha
      change a ∈ t ++ s.map (mapGate (rename k r)) at ha
      rcases List.mem_append.mp ha with ht | hs
      · exact fan a (List.mem_append_left _ ht)
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hs
        exact gate_map_fan _ (fan b (List.mem_append_right _ (List.mem_cons_of_mem _ hb)))
    · change (t ++ s.map (mapGate (rename k r))).length + 1 = _
      simp
      omega
    · intro w hw h
      let p := run t w
      let b := value p g
      have hp : p.length = k := by rw [run_length, hw]
      have hh : r < p.length := hp ▸ hr
      obtain ⟨Q, hQ, hQ'⟩ := erase_run s p [] b r hh (fun hs => h (Or.inr (by rwa [hp] at hs)))
      change (run (t ++ s.map (mapGate (rename k r))) w).getD (rename k r out) false =
        (run (t ++ g :: s) w).getD out false
      simp only [run, List.foldl_append, List.foldl_cons]
      change (run (s.map (mapGate (rename k r))) p).getD (rename k r out) false =
        (run s (p ++ [b])).getD out false
      rw [← hp]
      rw [List.append_nil] at hQ
      rw [hQ, hQ']
      exact insert_read p Q b r out hh (fun he => h (Or.inl (he.trans hp)))


  let target (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))

  let seed (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 4 || x 6]

  let slice (x : Fin 7 → Bool) : List Bool :=
    [x 4,x 3,x 0,x 5,false,x 1,false,x 2,x 6,false]

  let extendSlice (x : Fin 7 → Bool) : Fin 9 → Bool :=
    ![x 4,x 3,x 0,x 5,false,x 1,false,x 2,x 6]

  have seed_of (x : Fin 9 → Bool) (i : Fin 9) :
      (seed x).getD i false = x i := by
    simp only [seed]
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using i.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]

  have seed_nine (x : Fin 9 → Bool) : (seed x).getD 9 false = (x 4 || x 6) := by
    unfold seed
    simpa only [List.length_ofFn] using read_snoc (List.ofFn x) (x 4 || x 6)

  have full_eval (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 9 → Bool) :
      (⟨⟨.or,[4,6]⟩ :: D.gates,D.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = D.eval (seed x) := by
    have h (i : Fin 9) : (List.ofFn x).getD i false = x i := by
      simpa only [seed, List.getD_append _ _ _ _ (show i.val < (List.ofFn x).length by simp)] using seed_of x i
    change D.eval (step (List.ofFn x) ⟨.or,[4,6]⟩) = D.eval (seed x)
    have h4 : (List.ofFn x).getD 4 false = x 4 := h 4
    have h6 : (List.ofFn x).getD 6 false = x 6 := h 6
    simp only [step, value, h4, h6, seed, List.map_cons, List.map_nil, evalOr,
      List.any_cons, List.any_nil, id_eq, Bool.or_false]

  have tail_lower (floor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 target 14) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (fan : PEqualNP.MetaComplexity.FanInTwo C) (computes : ∀ x, C.eval (seed x) = target x) : 14 ≤ C.size := by
    by_contra! h
    let E : PEqualNP.CircuitLowerBounds.Circuit := ⟨⟨.or,[4,6]⟩ :: C.gates,C.output⟩
    apply floor
    refine ⟨E, ?_, ?_, fun x => (full_eval C x).trans (computes x)⟩
    · intro g hg
      change g ∈ ⟨.or,[4,6]⟩ :: C.gates at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp
      · exact fan g hg
    · change (⟨.or,[4,6]⟩ :: C.gates).length ≤ 14
      change C.gates.length < 14 at h
      simp
      omega

  have gate_parts (C : PEqualNP.CircuitLowerBounds.Circuit) (j : Fin C.gates.length) :
      C.gates = C.gates.take j.val ++ C.gates.get j :: C.gates.drop (j.val+1) := by
    conv_lhs => rw [← List.take_append_drop j.val C.gates]
    rw [List.drop_eq_getElem_cons j.isLt]
    rfl

  have prefix_value (C : PEqualNP.CircuitLowerBounds.Circuit) (j : Fin C.gates.length) (w : List Bool) :
      (C.wires w).getD (w.length + j.val) false =
        value (run (C.gates.take j.val) w) (C.gates.get j) := by
    have hpre : (run (C.gates.take j.val) w).length = w.length + j.val := by
      rw [run_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
    change (run C.gates w).getD _ false = _
    rw [congrArg (fun gs => run gs w) (gate_parts C j)]
    simp only [run, List.foldl_append, List.foldl_cons]
    change (run (C.gates.drop (j.val+1)) (step (run (C.gates.take j.val) w) (C.gates.get j))).getD _ false = _
    rw [← hpre, run_read _ _ _ (by simp [step])]
    exact read_snoc _ _

  have prefix_read (C : PEqualNP.CircuitLowerBounds.Circuit) (j : Fin C.gates.length) (w : List Bool) (i : ℕ)
      (hi : i < w.length + j.val) :
      (run (C.gates.take j.val) w).getD i false = (C.wires w).getD i false := by
    have hpre : (run (C.gates.take j.val) w).length = w.length + j.val := by
      rw [run_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
    change _ = (run C.gates w).getD i false
    conv_rhs => rw [← List.take_append_drop j.val C.gates]
    simpa only [run, List.foldl_append] using
      (run_read (C.gates.drop j.val) (run (C.gates.take j.val) w) i (hpre ▸ hi)).symm

  have prefix_input (C : PEqualNP.CircuitLowerBounds.Circuit) (j : Fin C.gates.length) (w : List Bool) (i : ℕ)
      (hi : i < w.length) :
      (run (C.gates.take j.val) w).getD i false = w.getD i false := run_read _ _ _ hi

  have eraseAt (C : PEqualNP.CircuitLowerBounds.Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) (j : Fin C.gates.length) (n r : ℕ)
      (hr : r < n + j.val) :
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 1 = C.size ∧
        ∀ w : List Bool, w.length = n →
          ((C.output = n + j.val ∨ ∃ k : Fin C.gates.length, j < k ∧ read (C.gates.get k) (n+j.val)) →
            (run (C.gates.take j.val) w).getD r false =
              value (run (C.gates.take j.val) w) (C.gates.get j)) → D.eval w = C.eval w := by
    let t := C.gates.take j.val
    let s := C.gates.drop (j.val+1)
    let g := C.gates.get j
    have ht : t.length = j.val := by simp [t]
    have he : C.gates = t ++ g :: s := gate_parts C j
    have Ceq : (⟨t ++ g :: s, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = C := by cases C; simp_all
    obtain ⟨D, hf, hd, heval⟩ := erase_gate t s g C.output r n (Ceq.symm ▸ fan) (by rwa [ht])
    refine ⟨D,hf,by rw [hd, ← he]; rfl,?_⟩
    intro w hw h
    rw [← Ceq]
    apply heval w hw
    rw [ht]
    intro hh
    apply h
    rcases hh with hh | ⟨a,ha,hr⟩
    · exact Or.inl hh
    · obtain ⟨k, hk⟩ := List.mem_iff_get.mp ha
      have hidx : j.val+1+k.val < C.gates.length := by
        have hh := k.isLt
        change k.val < (C.gates.drop (j.val+1)).length at hh
        simp only [List.length_drop] at hh
        omega
      let i : Fin C.gates.length := ⟨j.val+1+k.val,hidx⟩
      have hget : C.gates.get i = a := by
        simpa only [s,List.get_eq_getElem,List.getElem_drop,i] using hk
      exact Or.inr ⟨i,by change j.val < j.val+1+k.val; omega,hget ▸ hr⟩

  have used_by (floor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 target 14) (C : PEqualNP.CircuitLowerBounds.Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
      (hs : C.size ≤ 14) (computes : ∀ x, C.eval (seed x) = target x)
      (j : Fin C.gates.length) :
      C.output = 10+j.val ∨
        ∃ k : Fin C.gates.length, j < k ∧ read (C.gates.get k) (10+j.val) := by
    by_contra hu
    obtain ⟨D,hf,hd,he⟩ := eraseAt C fan j 10 0 (by omega)
    have computes' (x : Fin 9 → Bool) : D.eval (seed x) = target x :=
      (he (seed x) (by simp [seed]) (fun h => (hu h).elim)).trans (computes x)
    have := tail_lower floor D hf computes'
    omega

  have used_seed (floor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 target 14) (C : PEqualNP.CircuitLowerBounds.Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
      (hs : C.size ≤ 14) (computes : ∀ x, C.eval (seed x) = target x) :
      C.output = 9 ∨ ∃ j : Fin C.gates.length, read (C.gates.get j) 9 := by
    by_contra hu
    let g : PEqualNP.CircuitLowerBounds.Gate := ⟨.or,[4,6]⟩
    have hf : PEqualNP.MetaComplexity.FanInTwo (⟨[] ++ g :: C.gates,C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) := by
      intro z hz
      change z ∈ g :: C.gates at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simp [g]
      · exact fan z hz
    obtain ⟨D,hD,hsize,he⟩ := erase_gate [] C.gates g C.output 0 9 hf (by decide)
    apply floor
    refine ⟨D,hD,by simp at hsize; exact hsize ▸ hs,?_⟩
    intro x
    have hcalc := he (List.ofFn x) (by simp) (by
      simp only [List.length_nil, Nat.add_zero]
      intro hd
      apply (hu ?_).elim
      rcases hd with h | ⟨z,hz,hr⟩
      · exact Or.inl h
      · obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hz
        exact Or.inr ⟨j,hr⟩)
    exact hcalc.trans ((full_eval C x).trans (computes x))

  have pair_inputs {g : PEqualNP.CircuitLowerBounds.Gate} {a b : ℕ} (hab : a ≠ b)
      (ha : read g a) (hb : read g b) (hlen : g.inputs.length ≤ 2) :
      g.op ≠ .not ∧ (g.inputs = [a,b] ∨ g.inputs = [b,a]) := by
    have hn : g.op ≠ .not := by
      intro h
      exact hab (Option.some.inj (((not_read h).mp ha).symm.trans ((not_read h).mp hb)))
    refine ⟨hn,?_⟩
    have ha := read_mem ha
    have hb := read_mem hb
    cases e : g.inputs with
    | nil => simp [e] at ha
    | cons i l =>
      rw [e] at ha hb hlen
      cases l with
      | nil =>
        have h1 : a = i := by simpa using ha
        have h2 : b = i := by simpa using hb
        exact (hab (h1.trans h2.symm)).elim
      | cons j rest =>
        have hz : rest = [] := by simpa using hlen
        subst rest
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with h | h <;> rcases hb with e | e
        · exact (hab (h.trans e.symm)).elim
        · exact Or.inl (by rw [h,e])
        · exact Or.inr (by rw [h,e])
        · exact (hab (h.trans e.symm)).elim


  let marked (i : Fin 9) : Fin 9 → Bool := fun j => decide (i = j)

  have no_raw_output (C : PEqualNP.CircuitLowerBounds.Circuit) (computes : ∀ x, C.eval (seed x) = target x)
      (i : Fin 9) : C.output ≠ i.val := by
    intro h
    have hh := computes (marked i)
    change (run C.gates (seed (marked i))).getD C.output false = _ at hh
    rw [h, run_read _ _ _ (by simpa [seed] using i.isLt.trans (by decide : 9 < 10)), seed_of] at hh
    have ht : ∀ i : Fin 9, target (marked i) = false := by decide +kernel
    rw [ht] at hh
    simp [marked] at hh

  have no_seed_output (C : PEqualNP.CircuitLowerBounds.Circuit) (computes : ∀ x, C.eval (seed x) = target x) :
      C.output ≠ 9 := by
    intro h
    have hh := computes (marked 4)
    change (run C.gates (seed (marked 4))).getD C.output false = _ at hh
    rw [h, run_read _ _ _ (by simp [seed]), seed_nine] at hh
    exact Bool.noConfusion hh

  have absorbs (x : Fin 9 → Bool) (u : Fin 9) (hu : u = 4 ∨ u = 6) :
      ((x u && (x 4 || x 6)) = x u) ∧ ((x u || (x 4 || x 6)) = (x 4 || x 6)) := by
    rcases hu with rfl | rfl <;> cases x 4 <;> cases x 6 <;> decide

  have no_shared_seed (floor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 target 14) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (fan : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 14) (computes : ∀ x, C.eval (seed x) = target x)
      (j : Fin C.gates.length) (u : Fin 9) (hu : u = 4 ∨ u = 6)
      (hr : read (C.gates.get j) u) : ¬ read (C.gates.get j) 9 := by
    classical
    intro h9
    let g := C.gates.get j
    have hg := fan g (List.get_mem _ j)
    obtain ⟨hn, hp⟩ := pair_inputs (show u.val ≠ 9 by omega) hr h9 hg.2
    change g.inputs = [u.val,9] ∨ g.inputs = [9,u.val] at hp
    have hor : g.op = .and ∨ g.op = .or := by
      rcases hg.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hn h).elim
    let r := if g.op = .and then u.val else 9
    have hrlt : r < 10 := by unfold r; split <;> omega
    obtain ⟨D,hf,hd,he⟩ := eraseAt C fan j 10 r (by omega)
    have heq (x : Fin 9 → Bool) :
        (run (C.gates.take j.val) (seed x)).getD r false =
          value (run (C.gates.take j.val) (seed x)) g := by
      let w := run (C.gates.take j.val) (seed x)
      have hlt : u.val < 10 := Nat.lt_trans u.isLt (by decide)
      have huval : w.getD u false = x u := (prefix_input _ _ _ _ (by simpa [seed] using hlt)).trans (seed_of x u)
      have h9val : w.getD 9 false = (x 4 || x 6) := (prefix_input _ _ _ _ (by simp [seed])).trans (seed_nine x)
      change w.getD r false = value w g
      have diff : PEqualNP.CircuitLowerBounds.GateOp.or ≠ PEqualNP.CircuitLowerBounds.GateOp.and := by intro h; cases h
      rcases hor with hg | hg <;> rcases hp with h | h
      · simp only [r, hg, ite_true, value, h, List.map_cons, List.map_nil, evalAnd,
          List.all_cons, List.all_nil, id_eq, Bool.and_true, huval, h9val]
        exact (absorbs x u hu).1.symm
      · simp only [r, hg, ite_true, value, h, List.map_cons, List.map_nil, evalAnd,
          List.all_cons, List.all_nil, id_eq, huval, h9val, Bool.and_comm]
        exact (absorbs x u hu).1.symm
      · simp only [r, hg, diff, ite_false, value, h, List.map_cons,
          List.map_nil, evalOr, List.any_cons, List.any_nil, id_eq, Bool.or_false, huval, h9val]
        exact (absorbs x u hu).2.symm
      · simp only [r, hg, diff, ite_false, value, h, List.map_cons,
          List.map_nil, evalOr, List.any_cons, List.any_nil, id_eq, huval, h9val, Bool.or_comm]
        exact (absorbs x u hu).2.symm
    have computes' (x : Fin 9 → Bool) : D.eval (seed x) = target x :=
      (he (seed x) (by simp [seed]) (fun _ => heq x)).trans (computes x)
    have := tail_lower floor D hf computes'
    omega

  have same_off (gs : List PEqualNP.CircuitLowerBounds.Gate) (w v : List Bool) (a b : ℕ)
      (hqa : a < w.length) (hqb : b < w.length) (hlen : w.length = v.length)
      (hne : a ≠ b)
      (same : ∀ i, i ≠ a → i ≠ b → w.getD i false = v.getD i false)
      (swapA : w.getD a false = v.getD b false) (swapB : w.getD b false = v.getD a false)
      (pair : ∀ g ∈ gs, read g a ↔ read g b)
      (fan : PEqualNP.MetaComplexity.FanInTwo (⟨gs,0⟩ : PEqualNP.CircuitLowerBounds.Circuit)) :
      ∀ i, i ≠ a → i ≠ b → (run gs w).getD i false = (run gs v).getD i false := by
    induction gs generalizing w v with
    | nil => exact same
    | cons g gs ih =>
      have hval : value w g = value v g := by
        by_cases ha : read g a
        · have hf := fan g List.mem_cons_self
          have hb := (pair g List.mem_cons_self).mp ha
          obtain ⟨hn, hp⟩ := pair_inputs hne ha hb hf.2
          rcases hf.1 with hg | hg | hg
          · rcases hp with h | h <;>
              simp [value, hg, h, evalAnd, Bool.and_comm,
                -List.getD_eq_getElem?_getD, swapA, swapB]
          · rcases hp with h | h <;>
              simp [value, hg, h, evalOr, Bool.or_comm,
                -List.getD_eq_getElem?_getD, swapA, swapB]
          · exact (hn hg).elim
        · have hb : ¬ read g b := fun hb => ha ((pair g List.mem_cons_self).mpr hb)
          have hv := value_map id w v g (fun i hi =>
            same i (fun e => ha (e ▸ hi)) (fun e => hb (e ▸ hi)))
          simpa [mapGate] using hv
      intro i hi hj
      change (run gs (step w g)).getD i false = (run gs (step v g)).getD i false
      apply ih
      · simp [step]; omega
      · simp [step]; omega
      · simp [step, hlen]
      · intro k hka hkb
        by_cases hk : k < w.length
        · exact (List.getD_append _ _ _ _ hk).trans
            ((same k hka hkb).trans (List.getD_append _ _ _ _ (hlen ▸ hk)).symm)
        · change (w ++ [value w g]).getD k false = (v ++ [value v g]).getD k false
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          rw [hval, hlen]
      · exact (List.getD_append _ _ _ _ hqa).trans
          (swapA.trans (List.getD_append _ _ _ _ (hlen ▸ hqb)).symm)
      · exact (List.getD_append _ _ _ _ hqb).trans
          (swapB.trans (List.getD_append _ _ _ _ (hlen ▸ hqa)).symm)
      · exact fun g hg => pair g (List.mem_cons_of_mem _ hg)
      · exact fun g hg => fan g (List.mem_cons_of_mem _ hg)
      · exact hi
      · exact hj

  have no_shared_raw (C : PEqualNP.CircuitLowerBounds.Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) (computes : ∀ x, C.eval (seed x) = target x)
      (j : Fin C.gates.length) (hr4 : ∀ k, read (C.gates.get k) 4 ↔ k = j)
      (hr6 : ∀ k, read (C.gates.get k) 6 ↔ k = j) : False := by
    let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4)
    let y : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 6)
    have h5 : ∀ (i : ℕ), i ≠ 4 → i ≠ 6 → (seed x).getD i false = (seed y).getD i false := by
      intro i hi hj
      by_cases raw : i < 9
      · let k : Fin 9 := ⟨i,raw⟩
        change (seed x).getD k false = (seed y).getD k false
        rw [seed_of, seed_of]
        have ne4 : k ≠ 4 := fun h => hi (congrArg Fin.val h)
        have ne6 : k ≠ 6 := fun h => hj (congrArg Fin.val h)
        simp [x,y,ne4,ne6]
      · by_cases he : i = 9
        · subst i; rw [seed_nine,seed_nine]; decide
        · rw [List.getD_eq_default _ _ (by simp [seed]; omega),
            List.getD_eq_default _ _ (by simp [seed]; omega)]
    have branch (g : PEqualNP.CircuitLowerBounds.Gate) (hg : g ∈ C.gates) : read g 4 ↔ read g 6 := by
      obtain ⟨k,rfl⟩ := List.mem_iff_get.mp hg
      exact (hr4 k).trans (hr6 k).symm
    have same := same_off C.gates (seed x) (seed y) 4 6 (by simp [seed]) (by simp [seed])
      (by simp [seed]) (by decide) h5 (by decide) (by decide) branch fan C.output
      (no_raw_output C computes 4) (no_raw_output C computes 6)
    change C.eval (seed x) = C.eval (seed y) at same
    rw [computes, computes] at same
    exact Bool.noConfusion same


  let active (C : PEqualNP.CircuitLowerBounds.Circuit) (j : Fin C.gates.length) : Prop :=
    ∀ i ∈ (C.gates.get j).inputs, read (C.gates.get j) i →
      ∃ y z : Fin 7 → Bool,
        (run (C.gates.take j.val) (slice y)).getD i false ≠
        (run (C.gates.take j.val) (slice z)).getD i false

  have special_bound {v : ℕ} (hv : v ∈ [4,6,9]) : v < 10 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> decide

  have special_false (C : PEqualNP.CircuitLowerBounds.Circuit) (j : Fin C.gates.length) (x : Fin 7 → Bool)
      {v : ℕ} (hv : v ∈ [4,6,9]) :
      (run (C.gates.take j.val) (slice x)).getD v false = false := by
    rw [prefix_input _ _ _ _ (special_bound hv)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> rfl

  have value_eq (w v : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate)
      (h : ∀ i, read g i → w.getD i false = v.getD i false) : value w g = value v g := by
    simpa [mapGate] using value_map id w v g h

  have and_false (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) (hop : g.op = .and) {i : ℕ}
      (hr : read g i) (hw : w.getD i false = false) : value w g = false := by
    cases e : value w g with
    | false => rfl
    | true =>
      have hm : false ∈ g.inputs.map (fun j => w.getD j false) :=
        List.mem_map.mpr ⟨i,read_mem hr,hw⟩
      simp only [value,hop,evalAnd,List.all_eq_true] at e
      exact (Bool.noConfusion (e false hm))

  have inv_true (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) (hop : g.op = .not) {i : ℕ}
      (hr : read g i) (hw : w.getD i false = false) : value w g = true := by
    have h := (not_read hop).1 hr
    cases e : g.inputs with
    | nil => simp [e] at h
    | cons a rest =>
      have ha : a = i := by simpa [e] using h
      subst a
      simp only [value,hop,e,List.map_cons,evalNot,List.headD_cons,hw,Bool.not_false]

  have shape (floor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 target 14) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (fan : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 14) (computes : ∀ x, C.eval (seed x) = target x)
      (unique : ∀ v ∈ [4,6], ∃! j : Fin C.gates.length, read (C.gates.get j) v)
      (K : Finset (Fin C.gates.length)) (budget : K.card + 11 ≤ C.size)
      (outside : ∀ j ∉ K, ∀ v ∈ [4,6,9], ¬ read (C.gates.get j) v)
      (varies : ∀ j ∉ K, active C j) :
      C.size = 14 ∧ K.card = 3 ∧
        (∀ v ∈ [4,6,9], ∃! j : Fin C.gates.length, read (C.gates.get j) v) ∧
        (∀ j ∈ K, (C.gates.get j).op = .or ∧ ∃ v ∈ [4,6,9], read (C.gates.get j) v) ∧
        (∀ (j : Fin C.gates.length) i, read (C.gates.get j) i → i < 10+j.val) ∧ C.output = 23 := by
    classical
    obtain ⟨a,ha,hua⟩ := unique 4 (by simp)
    obtain ⟨b,hb,hub⟩ := unique 6 (by simp)
    obtain ⟨c,hc⟩ := (used_seed floor C fan hs computes).resolve_left (no_seed_output C computes)
    have hab : a ≠ b := by
      rintro rfl
      apply no_shared_raw C fan computes a
      · exact fun k => ⟨hua k, fun h => h.symm ▸ ha⟩
      · exact fun k => ⟨hub k, fun h => h.symm ▸ hb⟩
    have hac : a ≠ c := by
      rintro rfl
      exact no_shared_seed floor C fan hs computes a 4 (Or.inl rfl) ha hc
    have hbc : b ≠ c := by
      rintro rfl
      exact no_shared_seed floor C fan hs computes b 6 (Or.inr rfl) hb hc
    have hmem (j : Fin C.gates.length) (v : ℕ) (hv : v ∈ [4,6,9])
        (hr : read (C.gates.get j) v) : j ∈ K := by
      by_contra hn
      exact outside j hn v hv hr
    have haK := hmem a 4 (by simp) ha
    have hbK := hmem b 6 (by simp) hb
    have hcK := hmem c 9 (by simp) hc
    have sub : ({a,b,c} : Finset _) ⊆ K := by
      intro j hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl <;> assumption
    have cardThree : ({a,b,c} : Finset _).card = 3 := by simp [hab,hac,hbc]
    have hcmin := Finset.card_le_card sub
    rw [cardThree] at hcmin
    have cardK : K.card = 3 := by omega
    have Keq : K = {a,b,c} :=
      (Finset.eq_of_subset_of_card_le sub (by rw [cardK,cardThree])).symm
    have Kread (j : Fin C.gates.length) (hj : j ∈ K) :
        ∃ v ∈ [4,6,9], read (C.gates.get j) v := by
      rw [Keq] at hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · exact ⟨4,by simp,ha⟩
      · exact ⟨6,by simp,hb⟩
      · exact ⟨9,by simp,hc⟩
    have unique9 : ∃! j : Fin C.gates.length, read (C.gates.get j) 9 := by
      refine ⟨c,hc,?_⟩
      intro j hj
      have hx := hmem j 9 (by simp) hj
      rw [Keq] at hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact (no_shared_seed floor C fan hs computes _ 4 (Or.inl rfl) ha hj).elim
      · exact (no_shared_seed floor C fan hs computes _ 6 (Or.inr rfl) hb hj).elim
      · rfl
    have hUnique : ∀ v ∈ [4,6,9], ∃! j : Fin C.gates.length, read (C.gates.get j) v := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨a,ha,hua⟩
      · exact ⟨b,hb,hub⟩
      · exact unique9

    let constant (q : ℕ) : Prop := ∀ y z : Fin 7 → Bool,
      (C.wires (slice y)).getD q false = (C.wires (slice z)).getD q false
    have hout : ¬ constant C.output := by
      intro h
      have hh := h (fun _ => false) (fun _ => true)
      change C.eval (seed (extendSlice fun _ => false)) =
        C.eval (seed (extendSlice fun _ => true)) at hh
      rw [computes,computes] at hh
      exact Bool.noConfusion hh
    have none_constant (j : Fin C.gates.length) : ¬ constant (10+j.val) := by
      intro hj
      let bad := Finset.univ.filter (fun k : Fin C.gates.length => constant (10+k.val))
      have hne : bad.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
      let r := bad.max' hne
      have hbad : r ∈ bad := Finset.max'_mem _ _
      have hr := (Finset.mem_filter.mp hbad).2
      obtain e | ⟨k,hlt,hread⟩ := used_by floor C fan hs computes r
      · exact hout (e.symm ▸ hr)
      have earlier : 10+r.val < 10+k.val := by exact Nat.add_lt_add_left hlt _
      have earlier_constant (y z : Fin 7 → Bool) :
          (run (C.gates.take k.val) (slice y)).getD (10+r.val) false =
          (run (C.gates.take k.val) (slice z)).getD (10+r.val) false := by
        rw [prefix_read _ _ _ _ earlier, prefix_read _ _ _ _ earlier]
        exact hr y z
      have hK : k ∈ K := by
        by_contra hk
        obtain ⟨y,z,hyz⟩ := varies k hk _ (read_mem hread) hread
        exact hyz (earlier_constant y z)
      obtain ⟨v,hv,hvread⟩ := Kread k hK
      have hn : 10+r.val ≠ v := by have := special_bound hv; omega
      have hPair := (pair_inputs hn hread hvread (fan _ (List.get_mem _ k)).2).2
      have hconst : constant (10+k.val) := by
        intro y z
        have py := prefix_value C k (slice y)
        have pz := prefix_value C k (slice z)
        change (C.wires (slice y)).getD (10+k.val) false = _ at py
        change (C.wires (slice z)).getD (10+k.val) false = _ at pz
        rw [py,pz]
        apply value_eq
        intro i hi
        have hm := read_mem hi
        rcases hPair with h | h <;> rw [h] at hm <;>
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
        all_goals
          first
          | rcases hm with rfl | rfl
            · exact earlier_constant y z
            · exact (special_false C k y hv).trans (special_false C k z hv).symm
          | rcases hm with rfl | rfl
            · exact (special_false C k y hv).trans (special_false C k z hv).symm
            · exact earlier_constant y z
      have hk : k ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hconst⟩
      exact Nat.not_le_of_lt (show r.val < k.val from hlt) (show k.val ≤ r.val from Finset.le_max' _ _ hk)


    refine ⟨by omega,cardK,hUnique,?_,?_,?_⟩
    · intro j hj
      refine ⟨?_,Kread j hj⟩
      obtain ⟨v,hv,hvr⟩ := Kread j hj
      have hf := (fan (C.gates.get j) (List.get_mem _ j)).1
      rcases hf with he | he | he
      · exfalso
        apply none_constant j
        intro y z
        have py := prefix_value C j (slice y)
        have pz := prefix_value C j (slice z)
        change (C.wires (slice y)).getD (10+j.val) false = _ at py
        change (C.wires (slice z)).getD (10+j.val) false = _ at pz
        exact py.trans ((and_false _ _ he hvr (special_false C j y hv)).trans
          ((and_false _ _ he hvr (special_false C j z hv)).symm.trans pz.symm))
      · exact he
      · exfalso
        apply none_constant j
        intro y z
        have py := prefix_value C j (slice y)
        have pz := prefix_value C j (slice z)
        change (C.wires (slice y)).getD (10+j.val) false = _ at py
        change (C.wires (slice z)).getD (10+j.val) false = _ at pz
        exact py.trans ((inv_true _ _ he hvr (special_false C j y hv)).trans
          ((inv_true _ _ he hvr (special_false C j z hv)).symm.trans pz.symm))
    · intro j i hi
      by_contra! hbad
      have defval (x : Fin 7 → Bool) :
          (run (C.gates.take j.val) (slice x)).getD i false = false := by
        apply List.getD_eq_default
        rw [run_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
        exact hbad
      by_cases hj : j ∈ K
      · obtain ⟨v,hv,hr⟩ := Kread j hj
        have hne : i ≠ v := fun he => Nat.not_lt_of_ge hbad (he ▸ (special_bound hv).trans_le (by omega))
        have hp := (pair_inputs hne hi hr (fan _ (List.get_mem _ j)).2).2
        apply none_constant j
        intro y z
        have py := prefix_value C j (slice y)
        have pz := prefix_value C j (slice z)
        change (C.wires (slice y)).getD (10+j.val) false = _ at py
        change (C.wires (slice z)).getD (10+j.val) false = _ at pz
        rw [py,pz]
        apply value_eq
        intro q hq
        have hm := read_mem hq
        have e : q = i ∨ q = v := by
          rcases hp with h | h
          · rw [h] at hm
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using hm
          · rw [h] at hm
            exact (show q = v ∨ q = i from by
              simpa only [List.mem_cons, List.not_mem_nil, or_false] using hm).symm
        rcases e with rfl | rfl
        · exact (defval y).trans (defval z).symm
        · exact (special_false C j y hv).trans (special_false C j z hv).symm
      · obtain ⟨y,z,hn⟩ := varies j hj i (read_mem hi) hi
        exact hn ((defval y).trans (defval z).symm)
    · have hsize : C.gates.length = 14 := by change C.size = 14; omega
      let j : Fin C.gates.length := ⟨13,by omega⟩
      rcases used_by floor C fan hs computes j with he | ⟨k,hjk,_⟩
      · exact he
      · have hh : 13 < k.val := hjk
        have hk := k.isLt
        omega

  intro C fan small _ unique K budget outside varies
  by_contra failed
  have computes (x : Fin 9 → Bool) : C.eval (seed x) = target x := by
    by_contra wrong
    exact failed ⟨x,wrong⟩
  obtain ⟨hs,hK,hu,hOr,hback,hout⟩ :=
    shape floor C fan small computes unique K budget outside varies
  obtain ⟨x,hx⟩ := remaining C fan hs hout hu hback K hK hOr varies
  exact hx (computes x)

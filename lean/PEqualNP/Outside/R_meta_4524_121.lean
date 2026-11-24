import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Remove NOT gates from the instruction list and charge each complemented source separately.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_4524_121
    (one : let A : List (BitVec 256) := 0 :: BitVec.allOnes 256 ::
    [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
     0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
     0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
     0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
     0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
     0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
     0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
     0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
    let lit := fun (D P : List (BitVec 256)) (x : BitVec 256) => x ∈ P ∨ ∃ a ∈ P, a ∈ D ∧ x = ~~~a
    let valid := fun (D B : List (BitVec 256)) => ∀ i : Fin B.length,
      ∃ a, lit D (A ++ B.take i.val) a ∧ ∃ b, lit D (A ++ B.take i.val) b ∧
        (B.get i = a &&& b ∨ B.get i = a ||| b)
    ∀ D B : List (BitVec 256), B.length = 12 → D.length ≤ 1 → D ⊆ A ++ B → valid D B →
      ¬ lit D (A ++ B) 0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8)
    (many : let A : List (BitVec 256) := 0 :: BitVec.allOnes 256 ::
    [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
     0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
     0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
     0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
     0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
     0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
     0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
     0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
    let lit := fun (D P : List (BitVec 256)) (x : BitVec 256) => x ∈ P ∨ ∃ a ∈ P, a ∈ D ∧ x = ~~~a
    let valid := fun (D B : List (BitVec 256)) => ∀ i : Fin B.length,
      ∃ a, lit D (A ++ B.take i.val) a ∧ ∃ b, lit D (A ++ B.take i.val) b ∧
        (B.get i = a &&& b ∨ B.get i = a ||| b)
    ∀ D B : List (BitVec 256), B.length ≤ 11 → B.length+D.length ≤ 13 → D ⊆ A ++ B → valid D B →
      ¬ lit D (A ++ B) 0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (13 : ℕ) → (∀ (x4 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (8 : ℕ) → Bool) => x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ))) x4) → ∀ x5 ∈ x1.gates, x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
  have and_eval (l : List Bool) : GateOp.and.eval l = l.all id := rfl

  have or_eval (l : List Bool) : GateOp.or.eval l = l.any id := rfl

  have not_eval (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl

  -- Bit i of a column is its input value on the assignment numbered i.
  let cols : List (BitVec 256) :=
    [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
     0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
     0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
     0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
     0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
     0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
     0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
     0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

  let raw : List (BitVec 256) := 0 :: BitVec.allOnes 256 :: cols

  let lit (D P : List (BitVec 256)) (x : (BitVec 256)) : Prop := x ∈ P ∨ ∃ a ∈ P, a ∈ D ∧ x = ~~~a

  let step (D P : List (BitVec 256)) (x : (BitVec 256)) : Prop :=
    ∃ a, lit D P a ∧ ∃ b, lit D P b ∧ (x = a &&& b ∨ x = a ||| b)

  let program (D B : List (BitVec 256)) : Prop :=
    ∀ i : Fin B.length, step D (raw ++ B.take i.val) (B.get i)

  have lit_mono {D P D' P' : List (BitVec 256)} {x : (BitVec 256)} (hd : D ⊆ D') (hp : P ⊆ P') :
      lit D P x → lit D' P' x := by
    rintro (h | ⟨a,hp',hd',rfl⟩)
    · exact Or.inl (hp h)
    · exact Or.inr ⟨a,hp hp',hd hd',rfl⟩

  have prog_mono {D D' B : List (BitVec 256)} (h : D ⊆ D') (hp : program D B) : program D' B := by
    intro i
    obtain ⟨a,ha,b,hb,e⟩ := hp i
    exact ⟨a,lit_mono h (fun _ hx => hx) ha,b,lit_mono h (fun _ hx => hx) hb,e⟩

  have prog_add {D B : List (BitVec 256)} {x : (BitVec 256)} (h : program D B) (hx : step D (raw ++ B) x) :
      program D (B ++ [x]) := by
    intro i
    by_cases hi : i.val < B.length
    · have hh := h ⟨i.val,hi⟩
      simpa [List.take_append_of_le_length (Nat.le_of_lt hi), List.get_eq_getElem,
        List.getElem_append_left hi] using hh
    · have hi' := i.isLt
      simp at hi'
      have he : i.val = B.length := by omega
      simpa [List.get_eq_getElem, he, List.take_append_of_le_length] using hx

  -- The defaults agree with GateOp.eval on a gate with missing operands.
  let gv (w : List (BitVec 256)) (g : Gate) : (BitVec 256) :=
    let a := (g.inputs[0]?).map (fun i => w.getD i 0)
    let b := (g.inputs[1]?).map (fun i => w.getD i 0)
    GateOp.rec (motive := fun _ => BitVec 256)
      ((a.getD (BitVec.allOnes 256)) &&& (b.getD (BitVec.allOnes 256)))
      ((a.getD 0) ||| (b.getD 0)) (~~~(a.getD 0)) (fun _ => 0) 0 g.op

  let run (gs : List Gate) (w : List (BitVec 256)) := gs.foldl (fun w g => w ++ [gv w g]) w

  have read_bit (i : Fin 256) (w : List (BitVec 256)) (j : Nat) :
      ((w.getD j 0).getLsbD i.val) = (w.map (fun x => x.getLsbD i.val)).getD j false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[j]? <;> simp

  have gate_bit (i : Fin 256) (w : List (BitVec 256)) (g : Gate)
      (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      (gv w g).getLsbD i.val = g.op.eval (g.inputs.map (fun j => (w.getD j 0).getLsbD i.val)) := by
    have allBits : ∀ k : Fin 256, (BitVec.allOnes 256).getLsbD k.val = true := by
      intro k
      simp only [BitVec.getLsbD_allOnes, k.isLt, decide_true]
    obtain ⟨op,is⟩ := g
    rcases hg with ⟨ho,hl⟩
    change is.length ≤ 2 at hl
    rcases ho with ho | ho | ho
    all_goals change op = _ at ho
    all_goals subst op
    all_goals rcases is with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩ <;>
      simp [gv, and_eval, or_eval, not_eval, i.isLt] at hl ⊢
    all_goals try intro h
    all_goals exact allBits i

  have wires_def (C : Circuit) (input : List Bool) :
      C.wires input = C.gates.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) input := rfl
  have run_bit (i : Fin 256) (gs : List Gate) (w : List (BitVec 256)) (hg : FanInTwo ⟨gs,0⟩) :
      (run gs w).map (fun x => x.getLsbD i.val) =
        (Circuit.mk gs 0).wires (w.map (fun x => x.getLsbD i.val)) := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (w ++ [gv w g])).map _ = _
      rw [ih _ (fun a ha => hg a (by simp [ha]))]
      have eq := gate_bit i w g (hg g (by simp))
      simp only [List.map_append, List.map_singleton, eq, read_bit, wires_def, List.foldl_cons]

  let covered (D B w : List (BitVec 256)) : Prop := ∀ x ∈ w, lit D (raw ++ B) x

  -- A NOT introduces one complemented source or cancels a prior complement.
  have compile (gs : List Gate) (w D B : List (BitVec 256)) (prog : program D B) (hw : covered D B w)
      (legal : FanInTwo ⟨gs,0⟩) :
      ∃ D' B' : List (BitVec 256), program D' B' ∧ covered D' B' (run gs w) ∧
        B'.length ≤ B.length + gs.countP (fun g => !g.op.eval [false]) ∧
        D'.length ≤ D.length + gs.countP (fun g => g.op.eval [false]) := by
    induction gs generalizing w D B with
    | nil => exact ⟨D,B,prog,hw,by simp,by simp⟩
    | cons g gs ih =>
      have hg := legal g (List.mem_cons_self ..)
      have rest : FanInTwo ⟨gs,0⟩ := fun q hq => legal q (List.mem_cons_of_mem _ hq)
      let x := gv w g
      let P := raw ++ B
      have hz : lit D P 0 := Or.inl (by simp [P,raw])
      have ht : lit D P (BitVec.allOnes 256) := Or.inl (by simp [P,raw])
      have read (j : Nat) : lit D P (w.getD j 0) := by
        rw [List.getD_eq_getElem?_getD]
        cases he : w[j]? with
        | none => exact hz
        | some a => exact hw a (List.mem_of_getElem? he)
      have source (k : Nat) (d : (BitVec 256)) (hd : lit D P d) :
          lit D P (((g.inputs[k]?).map (fun j => w.getD j 0)).getD d) := by
        cases he : g.inputs[k]? with
        | none => exact hd
        | some j => exact read j
      have extend (D' B' : List (BitVec 256)) (hp : program D' B') (hold : ∀ z ∈ w, lit D' (raw ++ B') z)
          (hx : lit D' (raw ++ B') x)
          (hb : B'.length ≤ B.length + (if !g.op.eval [false] then 1 else 0))
          (hd : D'.length ≤ D.length + (if g.op.eval [false] then 1 else 0)) :
          ∃ Ds Bs : List (BitVec 256), program Ds Bs ∧ covered Ds Bs (run (g :: gs) w) ∧
            Bs.length ≤ B.length + (g::gs).countP (fun q => !q.op.eval [false]) ∧
            Ds.length ≤ D.length + (g::gs).countP (fun q => q.op.eval [false]) := by
        have hcov : covered D' B' (w ++ [x]) := by
          intro z h
          rcases List.mem_append.mp h with hh | hh
          · exact hold z hh
          · simpa only [List.mem_singleton.mp hh] using hx
        obtain ⟨Ds,Bs,p,c,hb',hd'⟩ := ih (w ++ [x]) D' B' hp hcov rest
        refine ⟨Ds,Bs,p,c,?_,?_⟩ <;> simp only [List.countP_cons]
        all_goals split_ifs at * <;> omega
      rcases hg.1 with ho | ho | ho
      case inl | inr.inl =>
        have hnew : step D P x := by
          first
          | change g.op = GateOp.and at ho
            refine ⟨_,source 0 _ ht,_,source 1 _ ht,Or.inl ?_⟩
            simp [x,gv,ho]
          | change g.op = GateOp.or at ho
            refine ⟨_,source 0 _ hz,_,source 1 _ hz,Or.inr ?_⟩
            simp [x,gv,ho]
        apply extend D (B ++ [x]) (prog_add prog hnew)
        · exact fun z h => lit_mono (fun _ h => h) (by simp) (hw z h)
        · exact Or.inl (by simp)
        · simp [ho,and_eval,or_eval]
        · simp
      case inr.inr =>
        change g.op = GateOp.not at ho
        let a := ((g.inputs[0]?).map (fun j => w.getD j 0)).getD 0
        have eq : x = ~~~a := by simp [x,gv,ho,a]
        rcases (source 0 0 hz) with hm | ⟨s,hs,hd,ha⟩
        · apply extend (a :: D) B (prog_mono (by simp) prog)
          · exact fun z h => lit_mono (by simp) (fun _ h => h) (hw z h)
          · exact Or.inr ⟨a,hm,by simp,eq⟩
          · simp
          · simp [ho,not_eval]
        · apply extend D B prog hw
          · exact Or.inl (by simpa [P,eq,show a = ~~~s from ha] using hs)
          · simp
          · simp

  have encode (C : Circuit) (legal : FanInTwo C) :
      ∃ D B : List (BitVec 256), program D B ∧
        B.length ≤ C.gates.countP (fun g => !g.op.eval [false]) ∧
        D.length ≤ C.gates.countP (fun g => g.op.eval [false]) ∧
        ∃ y, lit D (raw ++ B) y ∧ ∀ r : Fin 256,
          y.getLsbD r.val = C.eval (List.ofFn fun i : Fin 8 => r.val.testBit i.val) := by
    have empty : program [] [] := by intro i; exact Fin.elim0 i
    have init : covered [] [] cols := by
      intro x hx
      exact Or.inl (by simp [raw,hx])
    obtain ⟨D,B,prog,cov,hB,hD⟩ := compile C.gates cols [] [] empty init legal
    let y := (run C.gates cols).getD C.output 0
    refine ⟨D,B,prog,by simpa using hB,by simpa using hD,y,?_,?_⟩
    · dsimp only [y]
      rw [List.getD_eq_getElem?_getD]
      cases e : (run C.gates cols)[C.output]? with
      | none => exact Or.inl (by simp [raw])
      | some a => exact cov a (List.mem_of_getElem? e)
    · intro r
      change ((run C.gates cols).getD C.output 0).getLsbD r.val = _
      rw [read_bit,run_bit r _ _ legal]
      have initial : cols.map (fun x => x.getLsbD r.val) = List.ofFn (fun i : Fin 8 => r.val.testBit i.val) := by
        have allRows : ∀ s : Fin 256, cols.map (fun x => x.getLsbD s.val) =
            List.ofFn (fun i : Fin 8 => s.val.testBit i.val) := by
          dsimp only [cols]
          decide +kernel
        exact allRows r
      rw [initial]
      rfl
  intro C legal size computes g hg hnot
  obtain ⟨D,B,valid,hB,hD,y,hy,hvalue⟩ := encode C legal
  -- On the three legal gate operations, evaluating [false] detects exactly NOT.
  have negCount : 0 < C.gates.countP (fun q => q.op.eval [false]) := by
    apply List.countP_pos_iff.mpr
    exact ⟨g,hg,by simp [hnot,not_eval]⟩
  have partition (l : List Gate) : l.countP (fun q => q.op.eval [false]) +
      l.countP (fun q => !q.op.eval [false]) = l.length := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      cases h : a.op.eval [false] <;> simp [h] <;> omega
  have total := partition C.gates
  change C.gates.length = 13 at size
  have hit : y = 0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have graph : ∀ r : Fin 256,
        (0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8 : BitVec 256).getLsbD r.val = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
          (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) (fun i : Fin 8 => r.val.testBit i.val) := by decide +kernel
    exact (hvalue ⟨k,hk⟩).trans ((computes _).trans (graph ⟨k,hk⟩).symm)
  rw [hit] at hy
  -- Only truth tables that occur as sources can contribute a complemented literal.
  let E := D.filter (fun a => (raw ++ B).contains a)
  have bounded : E.length ≤ D.length := List.length_filter_le _ _
  have sources : E ⊆ raw ++ B := by
    intro a ha
    simpa using (List.mem_filter.mp ha).2
  have restrict {P : List (BitVec 256)} {x : BitVec 256} (sub : P ⊆ raw ++ B) :
      lit D P x → lit E P x := by
    rintro (ha | ⟨a, ha, hd, rfl⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨a, ha, List.mem_filter.mpr ⟨hd, by simpa using sub ha⟩, rfl⟩
  have valid' : program E B := by
    intro i
    have sub : raw ++ B.take i.val ⊆ raw ++ B := by
      intro x hx
      rcases List.mem_append.mp hx with ha | hb
      · exact List.mem_append_left _ ha
      · exact List.mem_append_right _ ((List.take_sublist i.val B).subset hb)
    obtain ⟨a,ha,b,hb,gate⟩ := valid i
    exact ⟨a,restrict sub ha,b,restrict sub hb,gate⟩
  have out := restrict (List.Subset.refl (raw ++ B)) hy
  by_cases full : B.length = 12
  · exact one E B full (by omega) sources valid' out
  · exact many E B (by omega) (by omega) sources valid' out

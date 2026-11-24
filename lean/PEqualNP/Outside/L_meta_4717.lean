import Mathlib.Tactic.Tauto
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- Normalize all wires at once, keeping a Boolean sign on each wire.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_4717 : 
    ∀ (n m : ℕ) (C : Circuit) (inputs : Fin n → Fin m → Bool),
      PEqualNP.MetaComplexity.FanInTwo C →
        have initial : List (Fin m → Bool) := (fun (_ : Fin m) => false) :: List.ofFn inputs
        ∃ ys : List (Fin m → Bool),
          ys.length ≤ List.countP (fun (g : Gate) => !g.op.eval [false]) C.gates ∧
          (∀ (i : ℕ) (hi : i < ys.length),
            ∃ p ∈ initial ++ List.take i ys, ∃ q ∈ initial ++ List.take i ys,
              ∃ b c : Bool, ys[i] = fun r : Fin m => (p r ^^ b) && (q r ^^ c)) ∧
          ∃ p ∈ initial ++ ys, ∃ b : Bool, ∀ r : Fin m,
            C.eval (List.ofFn fun i : Fin n => inputs i r) = (p r ^^ b) := by
  intro n m C inputs hC
  let S := Fin m → Bool
  let zeroS : S := fun _ => false
  let base : List S := zeroS :: List.ofFn inputs
  let Rep (pool : List S) (f : S) : Prop :=
    ∃ p ∈ pool, ∃ b : Bool, ∀ r, f r = (p r ^^ b)
  let Good (ys : List S) : Prop :=
    ∀ i, ∀ hi : i < ys.length,
      ∃ p ∈ base ++ ys.take i, ∃ q ∈ base ++ ys.take i, ∃ b c : Bool,
        ys[i] = fun r => (p r ^^ b) && (q r ^^ c)
  let cost (g : Gate) := !g.op.eval [false]
  let step (ws : List S) (g : Gate) :=
    ws ++ [fun r => g.op.eval (g.inputs.map fun i => ws.getD i zeroS r)]
  -- Negation changes a sign. A binary AND or OR needs at most one new AND.
  have gateForm (g : Gate) (ops : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (hlen : g.inputs.length ≤ 2) (pool : List S) (zero_mem : zeroS ∈ pool)
      (wire : ℕ → S) (hw : ∀ i, Rep pool (wire i)) :
      Rep pool (fun r => g.op.eval (g.inputs.map fun i => wire i r)) ∨
        ((!g.op.eval [false]) = true ∧
          ∃ p ∈ pool, ∃ q ∈ pool, ∃ b c d : Bool, ∀ r,
            g.op.eval (g.inputs.map fun i => wire i r) = (((p r ^^ b) && (q r ^^ c)) ^^ d)) := by
    rcases g with ⟨op, inputs⟩
    change op = .and ∨ op = .or ∨ op = .not at ops
    change inputs.length ≤ 2 at hlen
    cases inputs with
    | nil =>
      left
      refine ⟨zeroS,zero_mem,op.eval [],?_⟩
      intro r
      change op.eval [] = (false ^^ op.eval [])
      cases op.eval [] <;> rfl
    | cons i tail =>
      obtain ⟨p,hp,b,hb⟩ := hw i
      cases tail with
      | nil =>
        left
        refine ⟨p,hp,b ^^ op.eval [false],?_⟩
        intro r
        change op.eval [wire i r] = (p r ^^ (b ^^ op.eval [false]))
        rw [hb r]
        rcases ops with rfl | rfl | rfl <;> cases b <;> cases p r <;> rfl
      | cons j tail =>
        cases tail with
        | cons k tail => simp at hlen
        | nil =>
          obtain ⟨q,hq,c,hc⟩ := hw j
          rcases ops with rfl | rfl | rfl
          · right
            refine ⟨rfl,p,hp,q,hq,b,c,false,?_⟩
            intro r
            change GateOp.and.eval [wire i r, wire j r] = (((p r ^^ b) && (q r ^^ c)) ^^ false)
            rw [hb r,hc r]
            cases b <;> cases c <;> cases p r <;> cases q r <;> rfl
          · right
            refine ⟨rfl,p,hp,q,hq,!b,!c,true,?_⟩
            intro r
            change GateOp.or.eval [wire i r, wire j r] = (((p r ^^ !b) && (q r ^^ !c)) ^^ true)
            rw [hb r,hc r]
            cases b <;> cases c <;> cases p r <;> cases q r <;> rfl
          · left
            refine ⟨p,hp,!b,?_⟩
            intro r
            change GateOp.not.eval [wire i r, wire j r] = (p r ^^ !b)
            rw [hb r]
            cases b <;> cases p r <;> rfl
  have snocRead (ws : List S) (f : S) (i : ℕ) :
      (ws ++ [f]).getD i zeroS = if i = ws.length then f else ws.getD i zeroS := by
    induction ws generalizing i with
    | nil => cases i <;> rfl
    | cons a ws ih =>
      cases i with
      | zero => rfl
      | succ i => simpa using ih i
  have inputMem (ws : List S) (i : ℕ) : ws.getD i zeroS ∈ zeroS :: ws := by
    induction ws generalizing i with
    | nil => cases i <;> simp [List.getD]
    | cons a ws ih =>
      cases i with
      | zero => simp [List.getD]
      | succ i =>
        have mem := ih i
        change ws.getD i zeroS ∈ zeroS :: a :: ws
        simp only [List.mem_cons] at mem ⊢
        tauto
  have grow (ys : List S) (f : S) (old : Good ys)
      (newGate : ∃ p ∈ base ++ ys, ∃ q ∈ base ++ ys, ∃ b c : Bool,
        f = fun r => (p r ^^ b) && (q r ^^ c)) : Good (ys ++ [f]) := by
    intro i hi
    have bound : i < ys.length + 1 := by simpa using hi
    by_cases earlier : i < ys.length
    · have ht : (ys ++ [f]).take i = ys.take i :=
        List.take_append_of_le_length (by omega)
      simpa only [ht, List.getElem_append_left earlier] using old i earlier
    · have eq : i = ys.length := by omega
      subst i
      simpa using newGate
  have promote {ys : List S} {f p : S} (h : Rep (base ++ ys) f) :
      Rep (base ++ (ys ++ [p])) f := by
    obtain ⟨a, ha, b, hb⟩ := h
    exact ⟨a, by rw [← List.append_assoc]; exact List.mem_append_left _ ha, b, hb⟩
  -- At each step every original wire has a signed representative.
  have build (gs : List Gate) (ws ys : List S)
      (allowed : ∀ g ∈ gs,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (valid : Good ys) (reps : ∀ i, Rep (base ++ ys) (ws.getD i zeroS)) :
      ∃ out : List S, out.length ≤ ys.length + gs.countP cost ∧ Good out ∧
        ∀ i, Rep (base ++ out) ((gs.foldl step ws).getD i zeroS) := by
    induction gs generalizing ws ys with
    | nil => exact ⟨ys, by simp, valid, reps⟩
    | cons g gs ih =>
      let value : S := fun r => g.op.eval (g.inputs.map fun i => ws.getD i zeroS r)
      have tailOk : ∀ t ∈ gs,
          t.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ t.inputs.length ≤ 2 :=
        fun t ht => allowed t (List.mem_cons_of_mem g ht)
      have next (ys' : List S)
          (size : ys'.length ≤ ys.length + (if cost g then 1 else 0)) (good : Good ys')
          (previous : ∀ i, Rep (base ++ ys') (ws.getD i zeroS))
          (last : Rep (base ++ ys') value) :
          ∃ out : List S, out.length ≤ ys.length + (g :: gs).countP cost ∧ Good out ∧
            ∀ i, Rep (base ++ out) (((g :: gs).foldl step ws).getD i zeroS) := by
        have wires : ∀ i, Rep (base ++ ys') ((step ws g).getD i zeroS) := by
          intro i
          change Rep _ ((ws ++ [value]).getD i zeroS)
          rw [snocRead]
          split
          · exact last
          · exact previous i
        obtain ⟨out, hout, hg, hr⟩ := ih (ws := step ws g) (ys := ys') tailOk good wires
        refine ⟨out, ?_, hg, hr⟩
        rw [List.countP_cons]
        split <;> rename_i h <;> simp [h] at size ⊢ <;> omega
      obtain ⟨hops, hlen⟩ := allowed g (by simp)
      have hz : zeroS ∈ base ++ ys := List.mem_append_left _ (by simp [base])
      rcases gateForm g hops hlen (base ++ ys) hz (fun i => ws.getD i zeroS) reps with free | charged
      · exact next ys (by omega) valid reps free
      · obtain ⟨hcost, p, hp, q, hq, b, c, d, heval⟩ := charged
        let a : S := fun r => (p r ^^ b) && (q r ^^ c)
        apply next (ys ++ [a])
        · simp [cost, hcost]
        · exact grow ys a valid ⟨p, hp, q, hq, b, c, rfl⟩
        · exact fun i => promote (reps i)
        · exact ⟨a, by simp, d, heval⟩
  -- Evaluating the list of Boolean functions at a row commutes with the circuit.
  have readMap (ws : List S) (r : Fin m) (i : ℕ) :
      (ws.map (fun f => f r)).getD i false = ws.getD i zeroS r := by
    induction ws generalizing i with
    | nil => cases i <;> rfl
    | cons a ws ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i
  have simulate (gs : List Gate) (ws : List S) (r : Fin m) :
      (gs.foldl step ws).map (fun f => f r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws.map fun f => f r) := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons, ih]
      simp only [step, List.map_append, List.map_cons, List.map_nil, readMap]
  let start : List S := List.ofFn inputs
  have initReps : ∀ i, Rep (base ++ []) (start.getD i zeroS) := by
    intro i
    refine ⟨start.getD i zeroS, ?_, false, ?_⟩
    · exact List.mem_append_left _ (inputMem start i)
    · intro r
      simp
  obtain ⟨out, bound, good, represents⟩ :=
    build C.gates start [] hC (by intro i hi; simp at hi) initReps
  change ∃ ys : List S, ys.length ≤ C.gates.countP cost ∧ Good ys ∧
    Rep (base ++ ys) (fun r => C.eval (List.ofFn fun i => inputs i r))
  obtain ⟨p, hp, b, hb⟩ := represents C.output
  refine ⟨out, by simpa using bound, good, p, hp, b, ?_⟩
  intro r
  have same := simulate C.gates start r
  have startMap : start.map (fun f => f r) = List.ofFn (fun i => inputs i r) := by
    simp [start, List.map_ofFn, Function.comp_def]
  rw [startMap] at same
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    (List.ofFn fun i => inputs i r)).getD C.output false = (p r ^^ b)
  rw [← same, readMap]
  exact hb r

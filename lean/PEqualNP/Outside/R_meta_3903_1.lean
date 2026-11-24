import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- Reduction of L-meta-3903 by removing every NOT gate. Each wire becomes a pin: a wire of a
-- signed program with a polarity. The inputs keep their wires, NOT x_0 is x_0 complemented,
-- the OR wire is one node (none when it reads fewer than two pins), an AND or OR gate is one
-- node, and a NOT gate flips a pin and pays for the wire it complements unless that wire is x_0
-- or the constant wire nine. Nodes and paid wires number at most fourteen. The first hypothesis
-- rules out signed programs of at most thirteen nodes, so fourteen nodes remain, nothing is
-- paid, and the OR node comes first: only x_0 and the constant are ever complemented, which
-- the second hypothesis rules out. The compilation of gates into signed nodes is the one of
-- R_meta_1665_41.lean (Gan Tu, pull request 4493), started here from the OR wire.
theorem PEqualNP.Outside.R_meta_3903_1
    (h1 : ∀ (b : ℕ) (op : Fin b → Bool) (left right : Fin b → ℕ × Bool)
      (out : ℕ × Bool) (w : (Fin 9 → Bool) → ℕ → Bool), b ≤ 13 →
      (∀ j, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val) → out.1 < 10 + b →
      (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
      (∀ x j, let val := fun p : ℕ × Bool => Bool.xor (w x p.1) p.2
        w x (10 + j.val) = if op j then (val (left j) && val (right j))
          else (val (left j) || val (right j))) →
      ∃ x : Fin 9 → Bool, Bool.xor (w x out.1) out.2 ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h2 : ∀ (b : ℕ) (op : Fin b → Bool) (left right : Fin b → ℕ × Bool)
      (out : ℕ × Bool) (w : (Fin 9 → Bool) → ℕ → Bool), b ≤ 14 →
      (∀ j, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val) → out.1 < 10 + b →
      (let ok := fun p : ℕ × Bool => p.2 = true → p.1 = 0 ∨ p.1 = 9
       ok out ∧ ∀ j, ok (left j) ∧ ok (right j)) →
      (∀ j : Fin b, j.val = 0 → op j = false) →
      (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
      (∀ x j, let val := fun p : ℕ × Bool => Bool.xor (w x p.1) p.2
        w x (10 + j.val) = if op j then (val (left j) && val (right j))
          else (val (left j) || val (right j))) →
      ∃ x : Fin 9 → Bool, Bool.xor (w x out.1) out.2 ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size = (13 : ℕ) →           (∃ x6 ∈ x3.gates, (10 : ℕ) ∈ x6.inputs) ∨ x3.output = (10 : ℕ) →             (∃ x7 ∈ x3.gates, (9 : ℕ) ∈ x7.inputs) ∨ (9 : ℕ) ∈ x1 ∨ x3.output = (9 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x3.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro pins npins D fan size _ _
  classical
  dsimp only
  by_contra hall
  push Not at hall
  let target := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  -- Signed programs: a pin is a wire with a polarity, a node an AND (true) or OR (false) of two
  -- pins. Wires 0 to 8 are the inputs, wire 9 is the constant false, node j is wire 10 + j.
  let Pin := ℕ × Bool
  let Node := Bool × Pin × Pin
  let neg := fun (p : Pin) => (p.1,!p.2)
  let c0 : Pin := (9,false)
  let takePin := fun (w : List Bool) (p : Pin) => Bool.xor (w.getD p.1 false) p.2
  let bindGate := fun (w : List Bool) (g : Node) =>
    w ++ [if g.1 then (takePin w g.2.1 && takePin w g.2.2)
          else (takePin w g.2.1 || takePin w g.2.2)]
  let run := fun (P : List Node) (x : Fin 9 → Bool) => P.foldl bindGate (List.ofFn x ++ [false])
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let base := fun x : Fin 9 → Bool => List.ofFn x ++ [!(x 0)]
  let allowed := fun (S : Finset ℕ) (p : Pin) => p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ S
  let ordered := fun (P : List Node) => ∀ j : Fin P.length,
    (P.get j).2.1.1 < 10 + j.val ∧ (P.get j).2.2.1 < 10 + j.val
  -- the pins of the ten base wires: the inputs and the complement of x_0
  let m : List Pin := [(0,false),(1,false),(2,false),(3,false),(4,false),
    (5,false),(6,false),(7,false),(8,false),(0,true)]
  let src := fun i : ℕ => m.getD i c0
  have more {α : Type} (op : List Bool → α → Bool) (gs : List α) (w : List Bool) :
      ∃ t, gs.foldl (fun v g => v ++ [op v g]) w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp,rfl⟩
    | cons g gs ih =>
      obtain ⟨t,he,hl⟩ := ih (w ++ [op w g])
      exact ⟨op w g :: t, by simp only [List.foldl_cons, he, List.append_assoc,
        List.cons_append, List.nil_append], by simp [hl]⟩
  have shape (P : List Node) (x : Fin 9 → Bool) :
      ∃ t, run P x = (List.ofFn x ++ [false]) ++ t ∧ t.length = P.length := by
    exact more (fun w (g : Node) => if g.1 then (takePin w g.2.1 && takePin w g.2.2)
      else (takePin w g.2.1 || takePin w g.2.2)) P _
  have width (P : List Node) (x : Fin 9 → Bool) : (run P x).length = 10 + P.length := by
    obtain ⟨t,he,hl⟩ := shape P x
    simp [he,hl]
    omega
  have constZero (P : List Node) (x : Fin 9 → Bool) : (run P x).getD 9 false = false := by
    obtain ⟨t,he,_⟩ := shape P x
    rw [he, List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp
  have falsePin (P : List Node) (x : Fin 9 → Bool) : takePin (run P x) c0 = false := by
    change ((run P x).getD 9 false ^^ false) = false
    rw [constZero]
    rfl
  have complemented (w : List Bool) (p : Pin) : takePin w (neg p) = !(takePin w p) := by
    simp only [takePin,neg]
    cases w.getD p.1 false <;> cases p.2 <;> rfl
  have keepAllowed {S T : Finset ℕ} (h : S ⊆ T) {p : Pin} (a : allowed S p) : allowed T p := by
    intro on
    obtain z | k | mem := a on
    · exact Or.inl z
    · exact Or.inr (Or.inl k)
    · exact Or.inr (Or.inr (h mem))
  have getOK (P : List Node) (S : Finset ℕ) (M : List Pin)
      (hm : ∀ p ∈ M, p.1 < 10 + P.length ∧ allowed S p) (i : ℕ) :
      (M.getD i c0).1 < 10 + P.length ∧ allowed S (M.getD i c0) := by
    by_cases hi : i < M.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hm _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact ⟨by simp [c0]; omega, by simp [allowed,c0]⟩
  have longer {P : List Node} (hP : ordered P) (g : Node)
      (ha : g.2.1.1 < 10 + P.length) (hb : g.2.2.1 < 10 + P.length) :
      ordered (P ++ [g]) := by
    intro j
    change (P ++ [g])[j.val].2.1.1 < 10 + j.val ∧ (P ++ [g])[j.val].2.2.1 < 10 + j.val
    by_cases hi : j.val < P.length
    · rw [List.getElem_append_left hi]
      exact hP ⟨j.val,hi⟩
    · have eq : j.val = P.length := by have hj := j.isLt; simp at hj; omega
      simp only [eq]
      rw [List.getElem_append_right (Nat.le_refl P.length)]
      simp only [Nat.sub_self,List.getElem_cons_zero]
      exact ⟨ha,hb⟩
  -- the base wires read the same through their pins in every signed program
  have mOK : ∀ p ∈ m, p.1 < 10 ∧ allowed ∅ p := by simp [m,allowed]
  have baseMap (P : List Node) (x : Fin 9 → Bool) : base x = m.map (takePin (run P x)) := by
    obtain ⟨t,he,_⟩ := shape P x
    rw [he]
    simp [base,m,takePin]
  have srcRead (P : List Node) (x : Fin 9 → Bool) (i : ℕ) :
      (base x).getD i false = takePin (run P x) (src i) := by
    rw [baseMap P x, ← falsePin P x]
    exact List.getD_map m c0 (takePin (run P x))
  have srcOK (i : ℕ) : (src i).1 < 10 ∧ allowed ∅ (src i) := getOK [] ∅ m mOK i
  -- the state after the OR wire, whose values are orv: no node when the OR reads at most one
  -- pin, else one OR node
  let start := fun (orv : (Fin 9 → Bool) → Bool) (P1 : List Node) (M1 : List Pin) =>
    P1.length ≤ 1 ∧ (∀ g ∈ P1, g.1 = false) ∧ ordered P1 ∧
    (∀ g ∈ P1, allowed ∅ g.2.1 ∧ allowed ∅ g.2.2) ∧
    (∀ p ∈ M1, p.1 < 10 + P1.length ∧ allowed ∅ p) ∧
    ∀ x, base x ++ [orv x] = M1.map (takePin (run P1 x))
  have asPin (orv : (Fin 9 → Bool) → Bool) (p : Pin) (hp : p.1 < 10) (legal : allowed ∅ p)
      (value : ∀ x, orv x = takePin (run [] x) p) : ∃ P1 M1, start orv P1 M1 := by
    refine ⟨[],m ++ [p],by simp,by simp,fun j => Fin.elim0 j,by simp,?_,?_⟩
    · intro q hq
      obtain h | h := List.mem_append.mp hq
      · exact mOK q h
      · rw [List.mem_singleton.mp h]
        exact ⟨hp,legal⟩
    · intro x
      rw [value x, List.map_append, ← baseMap [] x]
      rfl
  have init : ∃ P1 M1,
      start (fun x => GateOp.or.eval (pins.map fun i => (base x).getD i false)) P1 M1 := by
    rcases pins with _ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩
    · exact asPin _ c0 (by decide) (by simp [allowed,c0]) (fun x => (falsePin [] x).symm)
    · refine asPin _ (src a) (srcOK a).1 (srcOK a).2 (fun x => ?_)
      have unary (u : Bool) : GateOp.or.eval [u] = u := by cases u <;> rfl
      rw [← srcRead [] x a, List.map_cons, List.map_nil, unary]
    · let g : Node := (false,src a,src b)
      refine ⟨[g],m ++ [(10,false)],by simp,by simp [g],?_,?_,?_,?_⟩
      · intro j
        have j0 : j.val = 0 := by have := j.isLt; change j.val < 1 at this; omega
        simp only [j0]
        exact ⟨by simpa [g] using (srcOK a).1,by simpa [g] using (srcOK b).1⟩
      · simp only [List.mem_singleton]
        rintro _ rfl
        exact ⟨(srcOK a).2,(srcOK b).2⟩
      · intro q hq
        obtain h | h := List.mem_append.mp hq
        · exact ⟨Nat.lt_of_lt_of_le (mOK q h).1 (by simp),(mOK q h).2⟩
        · rw [List.mem_singleton.mp h]
          exact ⟨by simp,by simp [allowed]⟩
      · intro x
        have pair (u w : Bool) : GateOp.or.eval [u,w] = (u || w) := by cases u <;> cases w <;> rfl
        have tip : takePin (run [g] x) (10,false) =
            (takePin (run [] x) (src a) || takePin (run [] x) (src b)) := by
          change ((run [] x ++ [takePin (run [] x) (src a) || takePin (run [] x) (src b)]).getD
            10 false ^^ false) = _
          rw [Bool.xor_false, List.getD_append_right _ _ _ _ (by rw [width]; rfl)]
          simp [width]
        rw [List.map_append, ← baseMap [g] x]
        congr 1
        simp only [List.map_cons, List.map_nil, pair, tip, srcRead [] x a, srcRead [] x b]
    · simp at npins
  obtain ⟨P1,M1,len1,or1,order1,nodes1,alias1,sem1⟩ := init
  let seed := fun x : Fin 9 → Bool =>
    base x ++ [GateOp.or.eval (pins.map fun i => (base x).getD i false)]
  let old := fun (gs : List Gate) (x : Fin 9 → Bool) => gs.foldl step (seed x)
  let state := fun (gs : List Gate) (P : List Node) (S : Finset ℕ) (M : List Pin) =>
    P1 <+: P ∧ P.length + S.card ≤ P1.length + gs.length ∧ ordered P ∧
    (∀ g ∈ P, allowed S g.2.1 ∧ allowed S g.2.2) ∧
    (∀ p ∈ M, p.1 < 10 + P.length ∧ allowed S p) ∧
    ∀ x, old gs x = M.map (takePin (run P x))
  -- compile the gates one by one; a gate costs at most one node or one paid wire
  have compile (gs : List Gate)
      (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
      ∃ P S M, state gs P S M := by
    induction gs using List.reverseRecOn with
    | nil => exact ⟨P1,∅,M1,List.prefix_refl _,by simp,order1,nodes1,alias1,sem1⟩
    | append_singleton gs gate ih =>
      obtain ⟨P,S,M,pre,budget,order,paid,aliases,sem⟩ := ih (fun g hg => ok g (by simp [hg]))
      obtain ⟨hop,short⟩ := ok gate (by simp)
      let source := fun i => M.getD i c0
      have sourceOK := getOK P S M aliases
      have reads (x : Fin 9 → Bool) (i : ℕ) :
          (old gs x).getD i false = takePin (run P x) (source i) := by
        rw [sem x, ← falsePin P x]
        exact List.getD_map M c0 (takePin (run P x))
      let v := fun x => gate.op.eval (gate.inputs.map fun i => (old gs x).getD i false)
      have appendOld (x : Fin 9 → Bool) : old (gs ++ [gate]) x = old gs x ++ [v x] := by
        simp only [old, List.foldl_append, List.foldl_cons, List.foldl_nil, step, v]
      have wire (p : Pin) (T : Finset ℕ) (subset : S ⊆ T) (cost : T.card ≤ S.card + 1)
          (hp : p.1 < 10 + P.length) (legal : allowed T p)
          (value : ∀ x, v x = takePin (run P x) p) :
          ∃ P S M, state (gs ++ [gate]) P S M := by
        refine ⟨P,T,M ++ [p],pre,?_,order,?_,?_,?_⟩
        · simp only [List.length_append, List.length_singleton]
          omega
        · intro g hg
          exact ⟨keepAllowed subset (paid g hg).1, keepAllowed subset (paid g hg).2⟩
        · intro a ha
          obtain oldmem | last := List.mem_append.mp ha
          · exact ⟨(aliases a oldmem).1,keepAllowed subset (aliases a oldmem).2⟩
          · simpa only [List.mem_singleton.mp last] using And.intro hp legal
        · intro x
          rw [appendOld,sem,value]
          simp
      have binary (b : Bool) (i j : ℕ)
          (value : ∀ x, v x =
            if b then (takePin (run P x) (source i) && takePin (run P x) (source j))
            else (takePin (run P x) (source i) || takePin (run P x) (source j))) :
          ∃ P S M, state (gs ++ [gate]) P S M := by
        let g : Node := (b,source i,source j)
        let nextPin : Pin := (10 + P.length,false)
        have appendVals (x) : run (P ++ [g]) x = run P x ++ [v x] := by
          simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil,bindGate,g]
          rw [value]
        refine ⟨P ++ [g],S,M ++ [nextPin],pre.trans (List.prefix_append P [g]),?_,
          longer order g (sourceOK i).1 (sourceOK j).1,?_,?_,?_⟩
        · simp only [List.length_append,List.length_singleton]
          omega
        · intro k hk
          obtain h | h := List.mem_append.mp hk
          · exact paid k h
          · have e : k = g := List.mem_singleton.mp h
            exact e ▸ ⟨(sourceOK i).2,(sourceOK j).2⟩
        · intro a ha
          obtain h | h := List.mem_append.mp ha
          · exact ⟨by have z := (aliases a h).1; simp; omega, (aliases a h).2⟩
          · have e : a = nextPin := List.mem_singleton.mp h
            subst a
            exact ⟨by simp [nextPin],by simp [allowed,nextPin]⟩
        · intro x
          rw [appendOld,sem,List.map_append]
          have kept : M.map (takePin (run P x)) = M.map (takePin (run (P ++ [g]) x)) := by
            apply List.map_congr_left
            intro a ha
            have lt := (aliases a ha).1
            rw [appendVals]
            have bound : a.1 < (run P x).length := by rw [width]; exact lt
            exact congrArg (fun z => Bool.xor z a.2)
              (List.getD_append (run P x) [v x] false a.1 bound).symm
          rw [kept]
          have tip : takePin (run (P ++ [g]) x) nextPin = v x := by
            rw [appendVals]
            simp only [nextPin,takePin,Bool.xor_false]
            rw [List.getD_append_right _ _ _ _ (by rw [width])]
            simp [width]
          simp [tip]
      have cBound : c0.1 < 10 + P.length := by dsimp [c0]; omega
      rcases hop with ha | ho | hn
      · cases he : gate.inputs with
        | nil =>
          apply wire (neg c0) S (fun _ h => h) (by omega) cBound (by simp [allowed,neg,c0])
          intro x
          change gate.op.eval _ = _
          rw [ha,he,complemented,falsePin]
          rfl
        | cons i is =>
          cases is with
          | nil =>
            apply wire (source i) S (fun _ h => h) (by omega) (sourceOK i).1 (sourceOK i).2
            intro x
            change gate.op.eval _ = _
            rw [ha,he]
            have unary (u : Bool) : GateOp.and.eval [u] = u := by cases u <;> rfl
            simpa only [List.map_cons,List.map_nil,unary] using reads x i
          | cons j rest =>
            have none : rest = [] := by simpa [he] using short
            subst rest
            apply binary true i j
            intro x
            have pair (u w : Bool) : GateOp.and.eval [u,w] = (u && w) := by cases u <;> cases w <;> rfl
            simp only [v,ha,he,List.map_cons,List.map_nil,pair,reads,ite_true]
      · cases he : gate.inputs with
        | nil =>
          apply wire c0 S (fun _ h => h) (by omega) cBound (by simp [allowed,c0])
          intro x
          change gate.op.eval _ = _
          rw [ho,he,falsePin]
          rfl
        | cons i is =>
          cases is with
          | nil =>
            apply wire (source i) S (fun _ h => h) (by omega) (sourceOK i).1 (sourceOK i).2
            intro x
            have unary (u : Bool) : GateOp.or.eval [u] = u := by cases u <;> rfl
            simpa only [v,ho,he,List.map_cons,List.map_nil,unary] using reads x i
          | cons j rest =>
            have none : rest = [] := by simpa [he] using short
            subst rest
            apply binary false i j
            intro x
            have pair (u w : Bool) : GateOp.or.eval [u,w] = (u || w) := by cases u <;> cases w <;> rfl
            simp only [v,ho,he,List.map_cons,List.map_nil,pair,reads,Bool.false_eq_true,ite_false]
      · cases he : gate.inputs with
        | nil =>
          apply wire (neg c0) S (fun _ h => h) (by omega) cBound (by simp [allowed,neg,c0])
          intro x
          change gate.op.eval _ = _
          rw [hn,he,complemented,falsePin]
          rfl
        | cons i is =>
          let a := source i
          apply wire (neg a) (insert a.1 S) (Finset.subset_insert _ _) (Finset.card_insert_le _ _)
            (sourceOK i).1 (by intro _; exact Or.inr (Or.inr (Finset.mem_insert_self _ _)))
          intro x
          have flip (u : Bool) (xs : List Bool) : GateOp.not.eval (u::xs) = !u := rfl
          simp only [v,hn,he,List.map_cons,flip,reads,complemented,a]
  have ok : ∀ a ∈ D.gates, (a.op = .and ∨ a.op = .or ∨ a.op = .not) ∧ a.inputs.length ≤ 2 := by
    intro a ha
    have h := fan a ha
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h.1,h.2⟩
  obtain ⟨P,S,M,pre,budget,back,paid,aliases,sem⟩ := compile D.gates ok
  have count : D.gates.length = 13 := size
  let out := M.getD D.output c0
  have outOK := getOK P S M aliases D.output
  have agrees (x : Fin 9 → Bool) : takePin (run P x) out = target x := by
    have hx := hall x
    change (old D.gates x).getD D.output false = target x at hx
    rw [sem,← falsePin P x] at hx
    exact (List.getD_map M c0 (takePin (run P x))).symm.trans hx
  let left := fun j : Fin P.length => (P.get j).2.1
  let right := fun j : Fin P.length => (P.get j).2.2
  let op := fun j : Fin P.length => (P.get j).1
  let table := fun (x : Fin 9 → Bool) (i : ℕ) => (run P x).getD i false
  have inputBits (x : Fin 9 → Bool) (i : Fin 9) : table x i.val = x i := by
    obtain ⟨t,h,_⟩ := shape P x
    change (run P x).getD i.val false = _
    rw [h, List.getD_append _ _ false _ (by simp; omega),
      List.getD_append _ _ false _ (by simp),
      List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn _
  have gateTable (x : Fin 9 → Bool) (j : Fin P.length) :
      table x (10 + j.val) =
        if op j then (takePin (run P x) (left j) && takePin (run P x) (right j))
        else (takePin (run P x) (left j) || takePin (run P x) (right j)) := by
    let before := run (P.take j.val) x
    let g := P.get j
    let v := if g.1 then (takePin before g.2.1 && takePin before g.2.2)
             else (takePin before g.2.1 || takePin before g.2.2)
    have preLength : before.length = 10 + j.val := by
      rw [show before = run (P.take j.val) x from rfl, width, List.length_take,
        Nat.min_eq_left j.isLt.le]
    have decomposition : P = P.take j.val ++ g :: P.drop (j.val + 1) := by
      simpa only [g, List.get_eq_getElem, List.drop_eq_getElem_cons j.isLt]
        using (List.take_append_drop j.val P).symm
    obtain ⟨extra,he,_⟩ := more (fun a (k : Node) =>
      if k.1 then (takePin a k.2.1 && takePin a k.2.2) else (takePin a k.2.1 || takePin a k.2.2))
      (P.drop (j.val + 1)) (before ++ [v])
    have full : run P x = (before ++ [v]) ++ extra := by
      calc
        run P x = run (P.take j.val ++ g :: P.drop (j.val + 1)) x :=
          congrArg (fun t => run t x) decomposition
        _ = (before ++ [v]) ++ extra := by
          simp only [run,List.foldl_append,List.foldl_cons]
          exact he
    have early (p : Pin) (lt : p.1 < 10 + j.val) : takePin (run P x) p = takePin before p := by
      have lb : p.1 < before.length := by omega
      have lb' : p.1 < (before ++ [v]).length := by simp; omega
      rw [full]
      simp only [takePin,List.getD_append _ _ false _ lb',List.getD_append _ _ false _ lb]
    change (run P x).getD (10 + j.val) false =
      if g.1 then (takePin (run P x) g.2.1 && takePin (run P x) g.2.2)
      else (takePin (run P x) g.2.1 || takePin (run P x) g.2.2)
    rw [early _ (back j).1,early _ (back j).2,full,
      List.getD_append _ _ false _ (by simp [preLength]),
      List.getD_append_right _ _ false _ (by rw [preLength])]
    simp only [preLength,Nat.sub_self,List.getD_cons_zero,v,g]
  by_cases small : P.length ≤ 13
  · obtain ⟨x,hx⟩ := h1 P.length op left right out table small back outOK.1
      inputBits (constZero P) gateTable
    exact hx (agrees x)
  -- fourteen nodes: the OR node comes first and no wire is paid for
  have first : P1.length = 1 := by omega
  have unpaid : S = ∅ := Finset.card_eq_zero.mp (by omega)
  have strip (p : Pin) (a : allowed S p) : p.2 = true → p.1 = 0 ∨ p.1 = 9 := by
    intro on
    rcases a on with z | k | mem
    · exact Or.inl z
    · exact Or.inr k
    · simp [unpaid] at mem
  have firstOr (j : Fin P.length) (j0 : j.val = 0) : op j = false := by
    have lt : j.val < P1.length := by omega
    have e : P.get j = P1[j.val] := (List.IsPrefix.getElem pre lt).symm
    exact or1 _ (e ▸ List.getElem_mem lt)
  obtain ⟨x,hx⟩ := h2 P.length op left right out table (by omega) back outOK.1
    ⟨strip _ outOK.2,fun j => ⟨strip _ (paid _ (List.get_mem P j)).1,
      strip _ (paid _ (List.get_mem P j)).2⟩⟩
    firstOr inputBits (constZero P) gateTable
  exact hx (agrees x)

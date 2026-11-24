import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2527_37
    (checkedLower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [Bool.false]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (15 : ℕ) ≤ x1.size)
    (hard : ∀ a b : Fin 10, (737869833953814245454 : Nat).testBit (10*a.val+b.val) = true →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        let wires := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 4]
        let read := fun (i : Fin 10) (x : Fin 9 → Bool) => (wires x).getD i.val false
        (∀ j ∈ [a,b], ∃ x : Fin 9 → Bool, read j x = false ∧ (read a x || read b x) = true ∧
          C.eval (wires x ++ [false]) ≠ C.eval (wires x ++ [true])) →
        ∃ x : Fin 9 → Bool, C.eval (wires x ++ [read a x || read b x]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
           x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x2.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (∃ x7 ∈ List.drop (1 : ℕ) x2.gates, (0 : ℕ) ∈ x7.inputs) → (∃ x8 ∈ List.drop (1 : ℕ) x2.gates, (4 : ℕ) ∈ x8.inputs) → (16 : ℕ) ≤ x2.size := by
  let target (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
      x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

  let inp (x : Fin 9 → Bool) (b c : Bool) := List.ofFn x ++ [b,c]
  let run (gs : List Gate) (w : List Bool) := gs.foldl (fun v g =>
    v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w
  let ren (s t i : Nat) := if i = 9 then s else if i = 10 then t else i
  let rg (s t : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (ren s t)⟩
  let embed (g : Gate) (s t : Nat) (C : Circuit) : Circuit :=
    ⟨g :: C.gates.map (rg s t), ren s t C.output⟩

  have compat (s t : Nat) (hs : s < 11) (ht : t < 11) (gs : List Gate) (l r : List Bool)
      (hl : 11 ≤ l.length) (he : l.length = r.length)
      (hw : ∀ i, l.getD (ren s t i) false = r.getD i false) :
      ∀ i, (run (gs.map (rg s t)) l).getD (ren s t i) false = (run gs r).getD i false := by
    induction gs generalizing l r with
    | nil => exact hw
    | cons g gs ih =>
      have rv (u : List Gate) (w : List Bool) (a : Gate) :
          run (a :: u) w = run u (w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]) := rfl
      simp only [List.map_cons, rv]
      have eqv : (rg s t g).op.eval ((rg s t g).inputs.map (fun i => l.getD i false)) =
          g.op.eval (g.inputs.map (fun i => r.getD i false)) := by
        simp only [rg, List.map_map, Function.comp_def, hw]
      rw [eqv]
      apply ih
      · simp; omega
      · simp [he]
      · intro i
        by_cases h : i < l.length
        · have hi : ren s t i < l.length := by unfold ren; split_ifs <;> omega
          rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
          exact hw i
        · have hi : ren s t i = i := by unfold ren; split_ifs <;> omega
          rw [hi, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), he]

  have fan (g : Gate) (s t : Nat) (C : Circuit) (hf : FanInTwo C)
      (hop : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
      FanInTwo (embed g s t C) := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | h
    · exact ⟨hop,hlen⟩
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
    simpa [rg] using hf z hz

  have src (x : Fin 9 → Bool) (n o : Bool) (s t : Nat) (hs : s < 11) (ht : t < 11) (i : Nat) :
      (inp x n o).getD (ren s t i) false =
        (inp x ((inp x n o).getD s false) ((inp x n o).getD t false)).getD i false := by
    by_cases h : i < 9
    · simp only [ren, if_neg (by omega : i ≠ 9), if_neg (by omega : i ≠ 10), inp]
      rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_append _ _ _ _ (by simpa using h)]
    by_cases h9 : i = 9
    · subst i; simp [ren, inp, List.getD_append_right]
    by_cases h10 : i = 10
    · subst i; simp [ren, inp, List.getD_append_right]
    simp only [ren, if_neg h9, if_neg h10]
    rw [List.getD_eq_default _ _ (by simp [inp]; omega), List.getD_eq_default _ _ (by simp [inp]; omega)]

  have transformed (g : Gate) (s t : Nat) (hs : s < 11) (ht : t < 11) (C : Circuit)
      (x : Fin 9 → Bool) (v : Bool)
      (hv : g.op.eval (g.inputs.map fun i => (List.ofFn x ++ [false]).getD i false) = v) :
      (embed g s t C).eval (List.ofFn x ++ [false]) =
      C.eval (inp x ((inp x false v).getD s false) ((inp x false v).getD t false)) := by
    change (run (C.gates.map (rg s t)) ((List.ofFn x ++ [false]) ++ [_])).getD _ false = _
    rw [hv]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact compat s t hs ht C.gates (inp x false v) _ (by simp [inp]) (by simp [inp]) (src x false v s t hs ht) C.output

  let low := ∀ C : Circuit, FanInTwo C → (∀ x, C.eval (List.ofFn x ++ [false]) = target x) → 15 ≤ C.size

  have obstruct (lo : low) (g : Gate) (s t : Nat) (hs : s < 11) (ht : t < 11) (C : Circuit)
      (hf : FanInTwo C) (small : C.size ≤ 13)
      (ok : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) (len : g.inputs.length ≤ 2)
      (v : (Fin 9 → Bool) → Bool)
      (hv : ∀ x, g.op.eval (g.inputs.map fun i => (List.ofFn x ++ [false]).getD i false) = v x) :
      ∃ x, C.eval (inp x ((inp x false (v x)).getD s false) ((inp x false (v x)).getD t false)) ≠ target x := by
    by_contra! all
    have h := lo (embed g s t C) (fan g s t C hf ok len)
      (fun x => (transformed g s t hs ht C x (v x) (hv x)).trans (all x))
    change 15 ≤ (g :: C.gates.map (rg s t)).length at h
    simp only [List.length_cons,List.length_map] at h
    change C.gates.length ≤ 13 at small
    omega
  have keep (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (w ++ [_])).getD i false = _
      rw [ih _ (by simp;omega),List.getD_append _ _ _ _ hi]

  let seed (x : Fin 9 → Bool) := x 0 || x 4
  let bank (x : Fin 9 → Bool) := List.ofFn x ++ [seed x]
  let val (j : Nat) (x : Fin 9 → Bool) := (bank x).getD j false
  let clip (i : Nat) : Fin 11 := ⟨min 10 i, by omega⟩
  have clip_val (i : Nat) (x : Fin 9 → Bool) : val (clip i).val x = val i x := by
    by_cases h : i ≤ 10
    · simp [clip,Nat.min_eq_right h]
    · simp [clip,Nat.min_eq_left (by omega : 10 ≤ i),val,bank]
      exact List.getD_eq_default _ _ (by simp;omega)
  have pins (l : List Nat) (hl : l.length ≤ 2) : ∃ a b : Fin 11,
      ∀ x, GateOp.or.eval (l.map fun i => val i x) = (val a.val x || val b.val x) := by
    rcases l with _ | ⟨i,_ | ⟨j,_ | ⟨k,ks⟩⟩⟩
    · exact ⟨10,10,fun x => by rfl⟩
    · exact ⟨clip i,clip i,fun x => by change (val i x || false) = _; simp [clip_val]⟩
    · exact ⟨clip i,clip j,fun x => by change (val i x || (val j x || false)) = _; simp [clip_val]⟩
    · simp at hl
  let good (a b : Fin 10) := a.val < b.val ∧ (a.val,b.val) ≠ (0,4) ∧
    (b.val = 9 → a.val ≠ 0 ∧ a.val ≠ 4)
  let classify (a b : Fin 11) : Prop :=
    (∃ t : Fin 11, ∀ x, (val a.val x || val b.val x) = val t.val x) ∨
    ∃ i j : Fin 10, good i j ∧ ∀ x, (val a.val x || val b.val x) = (val i.val x || val j.val x)
  have ordered (a b : Fin 11) (h : a ≤ b) : classify a b := by
    by_cases e : a = b
    · subst b; exact Or.inl ⟨a,fun x => by simp⟩
    by_cases z : b.val = 10
    · exact Or.inl ⟨a,fun x => by simp [z,val,bank]⟩
    have ab : a.val < b.val := by omega
    have hb : b.val < 10 := by omega
    by_cases p : (a.val,b.val) = (0,4)
    · obtain ⟨pa,pb⟩ := Prod.mk.inj p
      exact Or.inl ⟨9,fun x => by rw [pa,pb];rfl⟩
    by_cases q : b.val = 9 → a.val ≠ 0 ∧ a.val ≠ 4
    · exact Or.inr ⟨⟨a.val,by omega⟩,⟨b.val,hb⟩,⟨ab,p,q⟩,fun _ => rfl⟩
    push Not at q
    obtain ⟨qb,qa⟩ := q
    have casesA : a.val = 0 ∨ a.val = 4 := by tauto
    apply Or.inl
    refine ⟨9,?_⟩
    intro x
    rcases casesA with hh|hh <;> rw [hh,qb]
    · change (x 0 || (x 0 || x 4)) = _; change (x 0 || (x 0 || x 4)) = (x 0 || x 4); cases x 0 <;> rfl
    · change (x 4 || (x 0 || x 4)) = (x 0 || x 4); cases x 0 <;> cases x 4 <;> rfl
  have allPairs (a b : Fin 11) : classify a b := by
    rcases le_total a b with h|h
    · exact ordered a b h
    rcases ordered b a h with ⟨t,ht⟩|⟨i,j,good,eq⟩
    · exact Or.inl ⟨t,fun x => by rw [Bool.or_comm];exact ht x⟩
    · exact Or.inr ⟨i,j,good,fun x => by rw [Bool.or_comm];exact eq x⟩

  have aliases2527 (L : low) (j : Fin 11) (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 13) :
      ∃ x, C.eval (bank x ++ [(bank x).getD j.val false]) ≠ target x := by
    let t := ren 10 9 j.val
    have ht : t < 11 := by unfold t ren; split_ifs <;> have := j.isLt <;> omega
    obtain ⟨x,hx⟩ := obstruct L ⟨.or,[0,4]⟩ 10 t (by decide) ht C hf hs (by simp) (by decide)
      (fun x => seed x) (by intro x; change (x 0 || (x 4 || false)) = seed x; simp [seed])
    refine ⟨x,?_⟩
    have read : (inp x false (seed x)).getD t false = (bank x).getD j.val false := by
      fin_cases j <;> rfl
    rw [read] at hx
    exact hx

  have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
    simp

  let wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
    if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

  let relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (wmap n m π)⟩

  let relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
    ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
    n ≤ W.length ∧ W'.length + n = W.length + m ∧
      ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

  have rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
      (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (relGate n m π g).op.eval
        ((relGate n m π g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [relGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h3 a
    refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
    intro w
    simp only [step, hv]
    rcases Nat.lt_trichotomy w W.length with hw | hw | hw
    · have hlt : wmap n m π w < W'.length := by
        unfold wmap
        split
        · have := (π ⟨w, by assumption⟩).2; omega
        · omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 w
    · have he : wmap n m π w = W'.length := by
        unfold wmap
        split
        · omega
        · omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ wmap n m π w := by
        unfold wmap
        split
        · omega
        · omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  have rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
      ∀ W W' : List Bool, Rel n m π W W' →
        Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
    induction gs with
    | nil => intro W W' h; exact h
    | cons g gs ih =>
      intro W W' h
      exact ih _ _ (rel_step n m π W W' g h)
  let perm : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
  let ext : Fin 10 → Fin 10 := ![0,5,8,3,4,1,7,6,2,9]
  let reps : List (Fin 10 × Fin 10) :=
    [(0,1),(0,2),(0,3),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),
     (2,3),(2,4),(2,6),(2,7),(2,8),(2,9),(3,4),(3,6),(3,9),(4,6),(6,7),(6,9)]
  have cover : ∀ a b : Fin 10, good a b →
      (a,b) ∈ reps ∨ (ext a,ext b) ∈ reps ∨ (ext b,ext a) ∈ reps := by
    unfold good reps ext
    decide +kernel
  have targetPerm (x : Fin 9 → Bool) : target (x ∘ perm) = target x := by
    change (x 0 && x 5 || x 5 && x 8 || x 8 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 1 ||
      x 5 && x 7 || x 8 && x 6 || x 3 && x 2 || x 1 && x 6 || x 7 && x 2 || x 2 && x 1) = _
    unfold target
    ac_rfl
  let sig (a b : Fin 10) (x : Fin 9 → Bool) := bank x ++ [val a.val x || val b.val x]
  have permRel (a b : Fin 10) (x : Fin 9 → Bool) :
      Rel 9 9 perm (sig a b (x ∘ perm)) (sig (ext a) (ext b) x) := by
    have vp (i : Fin 10) : val (ext i).val x = val i.val (x ∘ perm) := by fin_cases i <;> rfl
    refine ⟨by simp [sig,bank],by simp [sig,bank],?_⟩
    intro i
    by_cases hi : i < 9
    · let t : Fin 9 := ⟨i,hi⟩
      change (sig (ext a) (ext b) x).getD (wmap 9 9 perm t.val) false =
        (sig a b (x ∘ perm)).getD t.val false
      generalize t = u
      fin_cases u <;> rfl
    have wp : wmap 9 9 perm i = i := by simp [wmap,hi];omega
    rw [wp]
    by_cases h9 : i = 9
    · subst i; rfl
    by_cases h10 : i = 10
    · subst i
      change (val (ext a).val x || val (ext b).val x) = _
      rw [vp,vp];rfl
    rw [List.getD_eq_default _ _ (by simp [sig,bank];omega),List.getD_eq_default _ _ (by simp [sig,bank];omega)]
  let fails (a b : Fin 10) := ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x, C.eval (sig a b x) ≠ target x
  have turn (a b : Fin 10) (h : fails (ext a) (ext b)) : fails a b := by
    intro C hf hs
    by_contra! he
    let D := relabel 9 9 perm C
    have fanD : FanInTwo D := by
      intro g hg
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
      exact ⟨(hf k hk).1,by simpa [relGate] using (hf k hk).2⟩
    obtain ⟨x,hx⟩ := h D fanD (by change (C.gates.map _).length ≤ 13; rw [List.length_map]; exact hs)
    exact hx (((rel_fold 9 9 perm C.gates _ _ (permRel a b x)).2.2 C.output).trans
      ((he (x ∘ perm)).trans (targetPerm x)))
  have flipFail (a b : Fin 10) (h : fails b a) : fails a b := by
    intro C hf hs
    simpa only [sig,Bool.or_comm (val b.val _) (val a.val _)] using h C hf hs

  have fromReps (L : low) (H : ∀ a b : Fin 10, (a,b) ∈ reps → fails a b)
      (g e : Gate) (gs : List Gate) (o : Nat)
      (hf : FanInTwo ⟨g::e::gs,o⟩)
      (wire : ∀ x : Fin 9 → Bool, ((Circuit.mk (g::e::gs) o).wires (List.ofFn x)).getD 9 false = seed x)
      (he : ∀ x : Fin 9 → Bool, (Circuit.mk (g::e::gs) o).eval (List.ofFn x) = target x)
      (op : e.op = GateOp.or) (hs : gs.length ≤ 13) : False := by
    let D : Circuit := ⟨gs,o⟩
    have hd : FanInTwo D := fun k hk => hf k (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk))
    have ds : D.size ≤ 13 := hs
    obtain ⟨a,b,hp⟩ := pins e.inputs (hf e (by simp)).2
    have correct (x : Fin 9 → Bool) : D.eval (bank x ++ [val a.val x || val b.val x]) = target x := by
      let v := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
      have hw := wire x
      change (run (e::gs) (List.ofFn x ++ [v])).getD 9 false = seed x at hw
      rw [keep _ _ _ (by simp)] at hw
      have hv : v = seed x := by simpa [List.getD_append_right] using hw
      have hx := he x
      change D.eval ((List.ofFn x ++ [v]) ++ [e.op.eval (e.inputs.map fun i => (List.ofFn x ++ [v]).getD i false)]) = _ at hx
      rw [hv,op] at hx
      change D.eval (bank x ++ [GateOp.or.eval (e.inputs.map fun i => val i x)]) = _ at hx
      simpa only [hp] using hx
    rcases allPairs a b with ⟨t,et⟩|⟨i,j,good,eq⟩
    · obtain ⟨x,hx⟩ := aliases2527 L t D hd ds
      exact hx (by have h := correct x; rw [et x] at h; exact h)
    · have fail : fails i j := by
        rcases cover i j good with e1|e2|e3
        · exact H i j e1
        · exact turn i j (H _ _ e2)
        · exact turn i j (flipFail _ _ (H _ _ e3))
      obtain ⟨x,hx⟩ := fail D hd ds
      exact hx (by simpa only [eq,sig] using correct x)

  let pivotal (C : Circuit) (a b : Fin 10) := ∀ j ∈ [a,b], ∃ x : Fin 9 → Bool,
    val j.val x = false ∧ (val a.val x || val b.val x) = true ∧
    C.eval (bank x ++ [false]) ≠ C.eval (bank x ++ [true])
  have pivotalOf (L : low) (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 13) (a b : Fin 10)
      (he : ∀ x, C.eval (sig a b x) = target x) : pivotal C a b := by
    intro j mem
    obtain ⟨x,hx⟩ := aliases2527 L ⟨j.val,by have := j.isLt; omega⟩ C hf hs
    change C.eval (bank x ++ [val j.val x]) ≠ target x at hx
    rw [← he x] at hx
    have sub : val j.val x = true → (val a.val x || val b.val x) = true := by
      intro ht
      rcases (by simpa using mem : j = a ∨ j = b) with rfl|rfl <;> simp [ht]
    change C.eval (bank x ++ [val j.val x]) ≠ C.eval (bank x ++ [val a.val x || val b.val x]) at hx
    have diff : val j.val x ≠ (val a.val x || val b.val x) := fun eq => hx (by rw [← eq])
    cases ht : val j.val x with
    | true => exact False.elim (diff (ht.trans (sub ht).symm))
    | false =>
      have hk : (val a.val x || val b.val x) = true := by
        cases h : (val a.val x || val b.val x) with
        | false => exact False.elim (diff (ht.trans h.symm))
        | true => rfl
      exact ⟨x,ht,hk,by simpa only [ht,hk] using hx⟩
  have selected : ∀ a b : Fin 10, (a,b) ∈ reps → (737869833953814245454 : Nat).testBit (10*a.val+b.val) = true := by
    unfold reps
    decide +kernel
  have L : low := checkedLower
  dsimp only
  intro C hf wire he op _ _
  by_contra! hs
  rcases C with ⟨_ | ⟨g,_ | ⟨e,gs⟩⟩,o⟩ <;> simp at op
  apply fromReps L _ g e gs o hf wire _ op
  · change (g::e::gs).length < 16 at hs
    simp at hs
    omega
  · intro a b mem C hfan size
    by_contra! all
    obtain ⟨x,hx⟩ := hard a b (selected a b mem) C hfan size (pivotalOf L C hfan size a b all)
    exact hx (all x)
  · intro x
    have h := congrFun he x
    change (Circuit.mk (g::e::gs) o).eval (List.ofFn x) = _ at h
    simpa [target,Bool.or_assoc] using h


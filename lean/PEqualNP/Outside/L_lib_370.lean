import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_370

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

abbrev run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl appendGate w

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (appendGate w g)).length = _
    rw [ih]
    simp [appendGate]
    omega

theorem get_old (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (appendGate w g).getD i false = w.getD i false := by
  simp [appendGate, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem get_new (w : List Bool) (g : Gate) :
    (appendGate w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [appendGate, List.getD_eq_getElem?_getD]

theorem get_missing (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default w false h

def move (k m : ℕ) (p : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < k then p i else m + (i - k)

def relabel (k m : ℕ) (p : ℕ → ℕ) (gs : List Gate) : List Gate :=
  gs.map fun g => ⟨g.op, g.inputs.map (move k m p)⟩

theorem move_agree (gs : List Gate) (u v : List Bool) (p : ℕ → ℕ)
    (hp : ∀ i < u.length, p i < v.length ∨ v.length + gs.length ≤ p i)
    (base : ∀ i < u.length, v.getD (p i) false = u.getD i false) :
    ∀ i, (run (relabel u.length v.length p gs) v).getD (move u.length v.length p i) false =
      (run gs u).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    by_cases hi : i < u.length
    · simpa [run, relabel, move, hi] using base i hi
    · simp [run, relabel, move, hi]
  | append_singleton gs g ih =>
    intro i
    have hp' : ∀ j < u.length, p j < v.length ∨ v.length + gs.length ≤ p j := by
      intro j hj
      rcases hp j hj with h | h
      · exact Or.inl h
      · right
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        omega
    let K := u.length
    let M := v.length
    let a := run gs u
    let b := run (relabel K M p gs) v
    let g' : Gate := ⟨g.op, g.inputs.map (move K M p)⟩
    have hal : a.length = K + gs.length := run_length _ _
    have hbl : b.length = M + gs.length := by simp [b, run_length, relabel, M]
    have hrewrite : run (relabel K M p (gs ++ [g])) v = appendGate b g' := by
      simp [relabel, run, List.foldl_append, b, g']
    have hright : run (gs ++ [g]) u = appendGate a g := by simp [run, List.foldl_append, a]
    rw [hrewrite, hright]
    change (appendGate b g').getD (move K M p i) false = (appendGate a g).getD i false
    have prev (j : ℕ) : b.getD (move K M p j) false = a.getD j false := ih hp' j
    rcases lt_trichotomy i (K + gs.length) with hi | he | hi
    · rw [get_old a g i (by omega)]
      by_cases hsource : i < K
      · rw [move, ite_eq_left hsource]
        rcases hp i hsource with hl | hl
        · rw [get_old b g' _ (by omega)]
          have h := prev i
          rw [move, ite_eq_left hsource] at h
          exact h
        · have hlarge : b.length + 1 ≤ p i := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hl
            dsimp [M] at hbl
            omega
          rw [get_missing _ _ (by simp [appendGate]; omega)]
          have h := prev i
          rw [move, ite_eq_left hsource, get_missing b _ (by omega)] at h
          exact h
      · have hback : move K M p i < b.length := by unfold move; rw [ite_eq_right hsource]; omega
        rw [get_old b g' _ hback]
        exact prev i
    · have hout : move K M p i = b.length := by rw [move, ite_eq_right (by omega)]; omega
      have ei : i = a.length := he.trans hal.symm
      rw [hout, ei, get_new, get_new]
      change g.op.eval (List.map (fun j => b.getD j false) (g.inputs.map (move K M p))) =
        g.op.eval (List.map (fun j => a.getD j false) g.inputs)
      rw [List.map_map]
      apply congrArg (fun bits => g.op.eval bits)
      exact List.map_congr_left fun j _ => prev j
    · have ha : (appendGate a g).length ≤ i := by simp [appendGate]; omega
      have hb : (appendGate b g').length ≤ move K M p i := by
        simp [appendGate, move, show ¬ i < K by omega]
        omega
      rw [get_missing _ _ ha, get_missing _ _ hb]

theorem embed_injective {n n' m m' : ℕ} (e : Fin m → Fin n) (f : Fin m' → Fin n')
    (he : Function.Injective e) (hf : Function.Injective f) :
    Function.Injective (Fin.addCases (fun u => (e u).val) (fun v => n+(f v).val)) := by
  intro u v
  refine Fin.addCases (fun l => ?_) (fun r => ?_) u
  · refine Fin.addCases (fun l' => ?_) (fun r' => ?_) v
    · simp only [Fin.addCases_left, Fin.val_inj, he.eq_iff, Fin.castAdd_inj]
      exact id
    · intro h
      simp only [Fin.addCases_left, Fin.addCases_right] at h
      have bl := (e l).isLt
      omega
  · refine Fin.addCases (fun l' => ?_) (fun r' => ?_) v
    · intro h
      simp only [Fin.addCases_left, Fin.addCases_right] at h
      have bl := (e l').isLt
      omega
    · simp only [Fin.addCases_right, Nat.add_left_cancel_iff, Fin.val_inj, hf.eq_iff, Fin.natAdd_inj]
      exact id

def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_decide]
      omega

end PEqualNP.Outside.L_lib_370

open PEqualNP.Outside.L_lib_370 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents in
theorem PEqualNP.Outside.L_lib_370 : ∀ (n n' m m' s : ℕ) (A : Fin n → Fin n' → Bool) (e : Fin m → Fin n) (f : Fin m' → Fin n'), Function.Injective e → Function.Injective f → PEqualNP.Represents.RepSizeAtMost A s → PEqualNP.Represents.RepSizeAtMost (fun u v => A (e u) (f v)) s := by
  classical
  intro n n' m m' s A e f he hf h
  obtain ⟨C,hC,hs,hr⟩ := h
  let E : Fin (m+m') → ℕ := Fin.addCases (fun u => (e u).val) (fun v => n+(f v).val)
  have hE : Function.Injective E := embed_injective e f he hf
  let p (i : ℕ) := if h : ∃ j : Fin (m+m'), E j = i then h.choose.val else m+m'+C.gates.length
  let D : Circuit := ⟨relabel (n+n') (m+m') p C.gates, move (n+n') (m+m') p C.output⟩
  refine ⟨D, ?_, by simpa [D,Circuit.size,relabel] using hs, ?_⟩
  · intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    simpa using hC q hq
  · intro u v
    change D.eval (oneEach u v) = A (e u) (f v)
    let a := inp (n+n') {(e u).val,n+(f v).val}
    let b := inp (m+m') {u.val,m+v.val}
    have al : a.length = n+n' := by simp [a,inp]
    have bl : b.length = m+m' := by simp [b,inp]
    have eu : E (Fin.castAdd m' u) = (e u).val := by simp [E]
    have ev : E (Fin.natAdd m v) = n+(f v).val := by simp [E]
    have hpr (i : ℕ) : p i < b.length ∨ b.length+C.gates.length ≤ p i := by
      rw [bl]
      unfold p
      split_ifs with h
      · exact Or.inl h.choose.isLt
      · exact Or.inr le_rfl
    have heq (i : ℕ) (hi : i < a.length) : b.getD (p i) false = a.getD i false := by
      rw [al] at hi
      change (inp _ _).getD _ false = (inp _ _).getD _ false
      rw [inp_getD, inp_getD]
      by_cases q : ∃ j : Fin (m+m'), E j = i
      · let j := q.choose
        have ej : E j = i := q.choose_spec
        have pj : p i = j.val := dite_eq_left q
        have e1 : j.val = u.val ↔ i = (e u).val := by
          rw [← ej, ← eu, hE.eq_iff]
          exact ⟨fun h => Fin.ext (by exact h), fun h => congrArg Fin.val h⟩
        have e2 : j.val = m+v.val ↔ i = n+(f v).val := by
          rw [← ej, ← ev, hE.eq_iff]
          exact ⟨fun h => Fin.ext (by exact h), fun h => congrArg Fin.val h⟩
        rw [pj, decide_eq_decide]
        simp [hi, j.isLt, e1, e2]
      · have e1 : i ≠ (e u).val := fun h => q ⟨Fin.castAdd _ u, eu.trans h.symm⟩
        have e2 : i ≠ n+(f v).val := fun h => q ⟨Fin.natAdd _ v, ev.trans h.symm⟩
        have pi : ¬p i < m+m' := by unfold p; rw [dite_eq_right q]; omega
        simp [pi,e1,e2]
    have eq := move_agree C.gates a b p (fun i _ => hpr i) heq C.output
    rw [al,bl] at eq
    rw [oneEach_eq, ← hr (e u) (f v), oneEach_eq]
    exact eq

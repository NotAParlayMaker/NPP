import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 700000 in
theorem PEqualNP.Outside.R_meta_3271_1
    (rawCut : ∀ (p s : List Gate) (o : ℕ),
      p.length + s.length ≤ 13 →
      let c : Circuit := ⟨p ++ ⟨.not, [0]⟩ :: s, o⟩
      FanInTwo c →
      (c.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 →
      (∀ (x5 : Fin (9 : ℕ) → Bool), c.eval (List.ofFn fun (x6 : Fin (9 : ℕ)) => if x6 = (0 : Fin (9 : ℕ)) then !x5 (0 : Fin (9 : ℕ)) else x5 x6) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → False)
    (internalCut : ∀ (p s : List Gate) (j o : ℕ),
      9 ≤ j → j < 9 + p.length → p.length + s.length ≤ 13 →
      let c : Circuit := ⟨p ++ ⟨.not, [j]⟩ :: s, o⟩
      let w := fun b : Bool => (Circuit.mk p 0).wires (b :: true :: List.replicate 7 false)
      FanInTwo c →
      (c.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 →
      (∀ i, (w false).getD i false = true → (w true).getD i false = true) →
      (w false).getD j false = false → (w true).getD j false = true →
      (∀ (x5 : Fin (9 : ℕ) → Bool), c.eval (List.ofFn fun (x6 : Fin (9 : ℕ)) => if x6 = (0 : Fin (9 : ℕ)) then !x5 (0 : Fin (9 : ℕ)) else x5 x6) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn fun (x6 : Fin (9 : ℕ)) => if x6 = (0 : Fin (9 : ℕ)) then !x5 (0 : Fin (9 : ℕ)) else x5 x6) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → False := by
  intro c hfan hsize hread heval
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  let run := fun (gs : List Gate) (w : List Bool) => gs.foldl step w
  let below := fun (a b : List Bool) => ∀ i, a.getD i false = true → b.getD i false = true
  let allowed := fun (g : Gate) => g.op = .and ∨ g.op = .or ∨ g.op = .not
  have opAnd (w : List Bool) : GateOp.and.eval w = w.all id := rfl
  have opOr (w : List Bool) : GateOp.or.eval w = w.any id := rfl
  have opNot (w : List Bool) : GateOp.not.eval w = !(w.headD false) := rfl
  have asRun (d : Circuit) (x : List Bool) : d.eval x = (run d.gates x).getD d.output false := rfl
  have ext : ∀ (a b : List Bool) (x y : Bool), a.length = b.length → below a b →
      (x = true → y = true) → below (a ++ [x]) (b ++ [y]) := by
    intro a b x y hlen hab hxy i hi
    by_cases h : i < a.length
    · have hh : i < b.length := by omega
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append, h, hh] using
        hab i (by simpa [List.getD_eq_getElem?_getD, List.getElem?_append, h] using hi)
    · have hh : ¬ i < b.length := by omega
      by_cases e : i = a.length
      · subst i
        simpa [List.getD_eq_getElem?_getD, List.getElem?_append, h, hh, hlen] using
          hxy (by simpa [List.getD_eq_getElem?_getD, List.getElem?_append] using hi)
      · have pa : a.length < i := by omega
        have hz : (a ++ [x]).length ≤ i := by simp; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hz] at hi
  have seek : ∀ (gs : List Gate) (a b : List Bool), (∀ g ∈ gs, allowed g) →
      a.length = b.length → below a b → ¬ below (run gs a) (run gs b) →
      ∃ (p s : List Gate) (j : ℕ) (rest : List ℕ),
        gs = p ++ ⟨.not, j :: rest⟩ :: s ∧ below (run p a) (run p b) ∧
        (run p a).getD j false = false ∧ (run p b).getD j false = true := by
    intro gs
    induction gs with
    | nil => intro a b _ _ hab hn; exact False.elim (hn hab)
    | cons g gs ih =>
      intro a b hall hlen hab hn
      let va := g.op.eval (g.inputs.map fun i => a.getD i false)
      let vb := g.op.eval (g.inputs.map fun i => b.getD i false)
      by_cases hxy : va = true → vb = true
      · have hlen' : (step a g).length = (step b g).length := by simp [step, hlen]
        obtain ⟨p, s, j, rs, ht, hp, hj, hj'⟩ :=
          ih (step a g) (step b g) (fun h hh => hall h (List.mem_cons_of_mem _ hh))
            hlen' (ext a b va vb hlen hab hxy) hn
        exact ⟨g :: p, s, j, rs, by simp [ht], hp, hj, hj'⟩
      · have ha : va = true := by cases h : va <;> simp_all
        have hb : vb = false := by cases h : vb <;> simp_all
        rcases hall g (by simp) with hand | hor | hnot
        · have ha' : ∀ i ∈ g.inputs, a.getD i false = true := by
            simpa [va, hand, opAnd] using ha
          have hb' : vb = true := by
            simpa [vb, hand, opAnd] using (fun i hi => hab i (ha' i hi) : ∀ i ∈ g.inputs, b.getD i false = true)
          simp_all
        · obtain ⟨i, hi, hai⟩ : ∃ i ∈ g.inputs, a.getD i false = true := by
            simpa [va, hor, opOr] using ha
          have hb' : vb = true := by
            simpa [vb, hor, opOr] using (show ∃ i ∈ g.inputs, b.getD i false = true from ⟨i, hi, hab i hai⟩)
          simp_all
        · cases g with
          | mk op ins =>
            change op = GateOp.not at hnot
            subst op
            cases ins with
            | nil => simp [vb, opNot] at hb
            | cons j rest =>
              exact ⟨[], gs, j, rest, rfl, hab, by simpa [run, va, opNot] using ha,
                by simpa [run, vb, opNot] using hb⟩
  let u := false :: true :: List.replicate 7 false
  let v := true :: true :: List.replicate 7 false
  have huv : below u v := by
    intro i hi
    cases i with
    | zero => simp [u] at hi
    | succ k => exact hi
  have ht : c.eval u = true := by
    have hx := heval (fun i => decide (i = 0 ∨ i = 1))
    change c.eval u = true at hx
    exact hx
  have hf : c.eval v = false := by
    have hx := heval (fun i => decide (i = 1))
    change c.eval v = false at hx
    exact hx
  have hn : ¬ below (run c.gates u) (run c.gates v) := by
    intro h
    exact Bool.noConfusion (hf.symm.trans (h c.output ht))
  have hall : ∀ g ∈ c.gates, allowed g := by
    intro g hg
    simpa [allowed, Set.mem_insert_iff, Set.mem_singleton_iff] using (hfan g hg).1
  obtain ⟨p, s, j, rs, hg, hp, hj, hj'⟩ := seek c.gates u v hall rfl huv hn
  cases c with
  | mk gs o =>
    change gs = _ at hg
    subst gs
    let tight : Circuit := ⟨p ++ ⟨.not, [j]⟩ :: s, o⟩
    have hbound : p.length + s.length ≤ 13 := by
      change (p ++ ⟨GateOp.not, j :: rs⟩ :: s).length ≤ 14 at hsize
      simp only [List.length_append, List.length_cons] at hsize
      omega
    have htight : FanInTwo tight := by
      intro g hg
      change g ∈ p ++ ⟨GateOp.not, [j]⟩ :: s at hg
      rcases List.mem_append.mp hg with h | h
      · exact hfan g (List.mem_append_left _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · simp
        · exact hfan g (List.mem_append_right _ (List.mem_cons_of_mem _ h))
    have hreads : (tight.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 := by
      change ((p ++ ⟨GateOp.not, j :: rs⟩ :: s).filter _).length ≤ 1 at hread
      change ((p ++ ⟨GateOp.not, [j]⟩ :: s).filter _).length ≤ 1
      simp only [List.filter_append, List.filter_cons, List.contains_cons, List.contains_nil,
        Bool.or_false, List.length_append] at hread ⊢
      split at hread <;> split <;> simp_all
      omega
    have real : ∀ x : Fin 9 → Bool, tight.eval (List.ofFn (fun k => if k = 0 then !x 0 else x k)) =
        (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) := by
      intro x
      rw [← heval x]
      rw [asRun, asRun]
      simp only [tight, run, List.foldl_append, List.foldl_cons]
      rfl
    by_cases hzero : j = 0
    · subst j
      exact rawCut p s o hbound htight hreads real
    have appendW : ∀ (gs' : List Gate) (w : List Bool), ∃ l : List Bool,
        run gs' w = w ++ l ∧ l.length = gs'.length := by
      intro gs'
      induction gs' with
      | nil => intro w; exact ⟨[], by simp [run], rfl⟩
      | cons g rem ih =>
        intro w
        obtain ⟨l, he, hn⟩ := ih (step w g)
        exact ⟨g.op.eval (g.inputs.map (fun i => w.getD i false)) :: l,
          by simpa [run, step, List.append_assoc] using he, by simp [hn]⟩
    obtain ⟨lo, hlo, _⟩ := appendW p u
    obtain ⟨hi, hhi, hlen⟩ := appendW p v
    have savedLo := hj
    have savedHi := hj'
    rw [hlo] at hj
    rw [hhi] at hj'
    have high : j < 9 + p.length := by
      by_contra! he
      have hh : (v ++ hi).length ≤ j := by simp only [v, List.length_append, List.length_cons, List.length_replicate, hlen]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hh] at hj'
    have low : 9 ≤ j := by
      by_contra! he
      have huj : j < u.length := by simpa [u] using he
      have hvj : j < v.length := by simpa [v] using he
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append, huj, hvj, ite_true] at hj hj'
      cases j with
      | zero => exact hzero rfl
      | succ j => exact Bool.noConfusion (hj.symm.trans hj')
    exact internalCut p s j o low high hbound htight hreads hp savedLo savedHi real

import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3352_915
    (h0 : let F := fun (x : Fin 9 → Bool) => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun e : Nat => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))); ¬∃ d : Circuit, FanInTwo d ∧ d.size ≤ 14 ∧ circuitFun 9 d = F)
    (h1 : let norm := fun (x : Fin 9 → Bool) (p : List (Bool × Nat × Nat)) (t : List (Nat × Nat)) =>
        let w := p.foldl (fun (xs : List Bool) g =>
          let a := xs.getD g.2.1 false
          let b := xs.getD g.2.2 false
          xs ++ [if g.1 then a && b else a || b]) (List.ofFn x ++ [x 0 || x 2])
        t.any (fun b => w.getD b.1 false && w.getD b.2 false)
      let F := fun (x : Fin 9 → Bool) => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun e : Nat => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))); ∀ (p : List (Bool × Nat × Nat)) (t : List (Nat × Nat)), p.countP Prod.fst ≤ 1 ∧ p.length + 2*t.length ≤ 15 → ∃ x, norm x p t ≠ F x)
    (h2 : let norm := fun (x : Fin 9 → Bool) (p : List (Bool × Nat × Nat)) (t : List (Nat × Nat)) =>
        let w := p.foldl (fun (xs : List Bool) g =>
          let a := xs.getD g.2.1 false
          let b := xs.getD g.2.2 false
          xs ++ [if g.1 then a && b else a || b]) (List.ofFn x ++ [x 0 || x 2])
        t.any (fun b => w.getD b.1 false && w.getD b.2 false)
      ∀ (c : Circuit), Monotone2 c → c.size ≤ 15 →
      (∀ d : Circuit, FanInTwo d → d.size < c.size → circuitFun 9 d ≠ circuitFun 9 c) →
      (∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) → (∀ i : Fin 9, circuitFun 9 c (fun j => decide (j=i)) = false) →
      let bad := fun j : Nat => (c.gates[j]?.map (fun g => g.op.eval [true,false])) = some false ∧ ∃ x : Fin 9 → Bool, circuitFun 9 c x = false ∧ (c.wires (List.ofFn x)).getD (9+j) false = true; ¬(∃ j k, j ≠ k ∧ bad j ∧ bad k) → ∃ p t, (p.countP Prod.fst ≤ 1 ∧ p.length + 2*t.length ≤ 15) ∧ ∀ x, norm x p t = circuitFun 9 c x)
    (h3 : let F := fun (x : Fin 9 → Bool) => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun e : Nat => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))); ∀ (c : Circuit), Monotone2 c → c.size ≤ 15 → (∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) → (∀ i : Fin 3, c.gates.countP (fun g => g.inputs.contains (![4,6,7] i)) ≤ 2) → circuitFun 9 c = F →
      let bad := fun j : Nat => (c.gates[j]?.map (fun g => g.op.eval [true,false])) = some false ∧ ∃ x : Fin 9 → Bool, circuitFun 9 c x = false ∧ (c.wires (List.ofFn x)).getD (9+j) false = true; (∃ j k, j ≠ k ∧ bad j ∧ bad k) → (∀ (v : Fin 9) (x y : Fin 9 → Bool), (∀ j, j ≠ v → x j = true → y j = true) →
          c.output ≠ v.val → F x = true → F y = false →
          ∃ p g q, c.gates = p ++ g :: q ∧ v.val ∈ g.inputs ∧
            ∀ i ∈ g.inputs, i ≠ v.val → ∀ z ∈ [x,y],
              (({gates:=p, output:=i} : Circuit).eval (List.ofFn z)) = !(g.op.eval [true,false])) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ x4 ∈ x2.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → x2.size ≤ (15 : ℕ) → (∀ (x7 : Fin (3 : ℕ)), List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (![(4 : ℕ), (6 : ℕ), (7 : ℕ)] x7)) x2.gates ≤ (2 : ℕ)) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 ≠ x1 := by
  intro F c hf hnot hfirst hsize hcaps correct
  have hm : Monotone2 c := by
    intro g hg
    obtain ⟨ha,hb⟩ := hf g hg
    refine ⟨?_,hb⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha ⊢
    exact ha.elim Or.inl (fun h => h.elim Or.inr (fun n => False.elim (hnot g hg n)))
  let bad := fun j : Nat => (c.gates[j]?.map (fun g => g.op.eval [true,false])) = some false ∧ ∃ x : Fin 9 → Bool, circuitFun 9 c x = false ∧ (c.wires (List.ofFn x)).getD (9+j) false = true
  by_cases hard : ∃ j k, j ≠ k ∧ bad j ∧ bad k
  · apply h3 c hm hsize hfirst hcaps correct hard
    let value (a : List Bool) (g : Gate) : Bool :=
      g.op.eval (g.inputs.map (fun i => a.getD i false))

    let run (gs : List Gate) (a : List Bool) : List Bool :=
      gs.foldl (fun w g => w ++ [value w g]) a

    let NoOther (v : Nat) (a b : List Bool) : Prop :=
      ∀ i, i ≠ v → a.getD i false = true → b.getD i false = true

    have extend {v : Nat} {a b : List Bool} {p q : Bool}
        (same : a.length = b.length) (before : NoOther v a b)
        (after : p = true → q = true) : NoOther v (a ++ [p]) (b ++ [q]) := by
      intro i hv h
      by_cases hi : i < a.length
      · simpa [List.getD, List.getElem?_append_left, hi, ← same] using
          before i hv (by simpa [List.getD, List.getElem?_append_left, hi] using h)
      · have hh : a.length ≤ i := by omega
        simpa [List.getD, List.getElem?_append_right, hh, ← same] using
          (show ([q][i-a.length]?).getD false = true from by
            have h' : ([p][i-a.length]?).getD false = true := by
              simpa [List.getD, List.getElem?_append_right, hh] using h
            cases eq : i-a.length with
            | zero => simp [eq] at h' ⊢; exact after h'
            | succ k => simp [eq] at h')

    have port {v : Nat} {a b : List Bool} (g : Gate)
        (allowed : g.op = .and ∨ g.op = .or) (before : NoOther v a b)
        (pa : value a g = true) (pb : value b g = false) :
        v ∈ g.inputs ∧
        ∀ i ∈ g.inputs, i ≠ v →
          (a.getD i false = !(g.op.eval [true,false]) ∧
           b.getD i false = !(g.op.eval [true,false])) := by
      rcases allowed with h | h
      · have ha : ∀ i ∈ g.inputs, a.getD i false = true := by
          simpa [value,h,GateOp.eval,List.all_eq_true] using pa
        have hb : ∃ i ∈ g.inputs, b.getD i false = false := by
          simpa [value,h,GateOp.eval,List.all_eq_false] using pb
        obtain ⟨i,hi,hz⟩ := hb
        have iv : i = v := by
          by_contra hn
          exact Bool.noConfusion (hz.symm.trans (before i hn (ha i hi)))
        exact ⟨iv ▸ hi, fun j hj hjv => by simpa [h,GateOp.eval] using And.intro (ha j hj) (before j hjv (ha j hj))⟩
      · have ha : ∃ i ∈ g.inputs, a.getD i false = true := by
          simpa [value,h,GateOp.eval,List.any_eq_true] using pa
        have hb : ∀ i ∈ g.inputs, b.getD i false = false := by
          simpa [value,h,GateOp.eval,List.any_eq_false] using pb
        obtain ⟨i,hi,hz⟩ := ha
        have iv : i = v := by
          by_contra hn
          exact Bool.noConfusion ((hb i hi).symm.trans (before i hn hz))
        refine ⟨iv ▸ hi, fun j hj hjv => ?_⟩
        have b0 := hb j hj
        have a0 : a.getD j false = false := by
          cases eq : a.getD j false with
          | false => rfl
          | true => exact Bool.noConfusion (b0.symm.trans (before j hjv eq))
        simpa [h,GateOp.eval] using And.intro a0 b0

    have earliest {v out : Nat} (gs : List Gate) (a b : List Bool)
        (allowed : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
        (same : a.length = b.length) (before : NoOther v a b) (hov : out ≠ v)
        (pa : (run gs a).getD out false = true) (pb : (run gs b).getD out false = false) :
        ∃ pre g post, gs = pre ++ g :: post ∧ v ∈ g.inputs ∧
        ∀ i ∈ g.inputs, i ≠ v →
          ((run pre a).getD i false = !(g.op.eval [true,false]) ∧
           (run pre b).getD i false = !(g.op.eval [true,false])) := by
      induction gs generalizing a b with
      | nil => exact Bool.noConfusion (pb.symm.trans (before out hov pa))
      | cons g xs ih =>
        by_cases ok : value a g = true → value b g = true
        · obtain ⟨p,k,q,he,hv,hk⟩ := ih _ _ (fun k hk => allowed k (List.mem_cons_of_mem g hk))
              (by simp [same]) (extend same before ok) pa pb
          exact ⟨g::p,k,q,by simp [he],hv,hk⟩
        · push Not at ok
          obtain ⟨hv,hp⟩ := port g (allowed g (by simp)) before ok.1 (by simpa using ok.2)
          exact ⟨[],g,xs,rfl,hv,hp⟩

    have reader_port {n : Nat} (c : Circuit) (hm : Monotone2 c)
        (v : Fin n) (x y : Fin n → Bool)
        (le : ∀ j, j ≠ v → x j = true → y j = true)
        (hov : c.output ≠ v.val)
        (pos : circuitFun n c x = true) (neg : circuitFun n c y = false) :
        ∃ pre g post, c.gates = pre ++ g :: post ∧ v.val ∈ g.inputs ∧
        ∀ i ∈ g.inputs, i ≠ v.val →
          ((({gates:=pre,output:=i} : Circuit).eval (List.ofFn x)) = !(g.op.eval [true,false]) ∧
           (({gates:=pre,output:=i} : Circuit).eval (List.ofFn y)) = !(g.op.eval [true,false])) := by
      apply earliest c.gates (List.ofFn x) (List.ofFn y) _ (by simp) _ hov pos neg
      · intro g hg
        simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (hm g hg).1
      · intro i hi h
        by_cases hlt : i < n
        · have j : (⟨i,hlt⟩ : Fin n) ≠ v := fun he => hi (congrArg Fin.val he)
          simpa [List.getD,hlt] using le ⟨i,hlt⟩ j (by simpa [List.getD,hlt] using h)
        · simp [List.getD,hlt] at h

    intro v x y sing hout px ny
    obtain ⟨p,g,q,hcq,hv,hrest⟩ := reader_port c hm v x y sing hout (by rw [correct]; exact px) (by rw [correct]; exact ny)
    refine ⟨p,g,q,hcq,hv,?_⟩
    intro i hi hiv z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact (hrest i hi hiv).1
    · rcases List.mem_cons.mp hz with rfl | hnil
      · exact (hrest i hi hiv).2
      · simp at hnil
  · have minimal (d : Circuit) (hd : FanInTwo d) (hs : d.size < c.size) : circuitFun 9 d ≠ circuitFun 9 c := by
      intro he
      exact h0 ⟨d, hd, by omega, he.trans correct⟩
    have singles : ∀ i : Fin 9, circuitFun 9 c (fun j => decide (j=i)) = false := by
      rw [correct]
      decide +kernel
    obtain ⟨p,t,shape,agree⟩ := h2 c hm hsize minimal hfirst singles hard
    obtain ⟨x,hx⟩ := h1 p t shape
    exact hx ((agree x).trans (congrFun correct x))

import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2732_53
    (residual :
      let edge : Fin 14 → Fin 14 → Prop := fun u v =>
        (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u.val 0).testBit v.val = true
      ∃ (a b c d : Fin 14) (op1 op2 : GateOp) (D : Circuit) (q : ℕ), a ≠ b ∧ c ≠ d ∧
        (op1 = .and ∨ op1 = .or) ∧ (op2 = .and ∨ op2 = .or) ∧ Monotone2 D ∧
        D.size ≤ 22 ∧ D.output < 16 + D.size ∧ q < 16 + D.size ∧
        let inp := fun x : Fin 14 → Bool => List.ofFn x ++ [op1.eval [x a,x b],op2.eval [x c,x d]]
        let out := fun x : Fin 14 → Bool => D.eval (inp x) || (x 0 && (D.wires (inp x)).getD q false)
        (∀ u v, edge u v → out (pairInput u v) = true) ∧
        ∀ x : Fin 14 → Bool,
          Maximal (fun y : Fin 14 → Bool => ¬ (∃ u v : Fin 14, edge u v ∧ y u = true ∧ y v = true)) x →
          out x = false)
    (append : ∀ (n : ℕ) (D : Circuit) (p : Fin n) (q : ℕ),
      Monotone2 D → D.output < n + D.size → q < n + D.size →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 2 ∧ ∀ x : Fin n → Bool,
        C.eval (List.ofFn x) = (D.eval (List.ofFn x) ||
          (x p && (D.wires (List.ofFn x)).getD q false)))
    : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); have x3 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x3 x4 x5 x6 : ℕ) => ((15 : ℕ) * Min.min x3 x4 + Max.max x3 x4) * (225 : ℕ) + ((15 : ℕ) * Min.min x5 x6 + Max.max x5 x6); have x4 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x4 : Equiv.Perm (Fin (14 : ℕ))) (x5 : Fin (15 : ℕ)) => if ↑x5 < (14 : ℕ) then ↑(x4 (Fin.ofNat (14 : ℕ) ↑x5)) else (14 : ℕ); ∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)) (x7 : Fin (15 : ℕ)) (x8 : Fin (15 : ℕ)) (x9 : PEqualNP.CircuitLowerBounds.GateOp) (x10 : PEqualNP.CircuitLowerBounds.GateOp) (x11 : PEqualNP.CircuitLowerBounds.Circuit),   x5 < x6 ∧     x7 < x8 ∧       (x9 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x9 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧         (x10 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧           (∀ (x12 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x13 : Fin (14 : ℕ) → Bool), x2 (x13 ∘ ⇑x12) = x2 x13) → x3 ↑x5 ↑x6 ↑x7 ↑x8 ≤ x3 (↑(x12 x5)) (↑(x12 x6)) (x4 x12 x7) (x4 x12 x8)) ∧             PEqualNP.MetaComplexity.Monotone2 x11 ∧               x11.size ≤ (24 : ℕ) ∧                 ∀ (x12 : Fin (14 : ℕ) → Bool),                   have x13 : List Bool := List.ofFn x12 ++ [x9.eval [x12 x5, x12 x6]];                   x11.eval (x13 ++ [x10.eval [x13.getD (↑x7) Bool.false, x13.getD (↑x8) Bool.false]]) = x2 x12 := by
  have renameInputs (n : ℕ) (σ : Equiv.Perm (Fin n)) (D : Circuit) (mono : Monotone2 D) :
      ∃ C : Circuit, Monotone2 C ∧ C.size = D.size ∧
        ∀ (x : Fin n → Bool) (tail : List Bool),
          C.eval (List.ofFn x ++ tail) = D.eval (List.ofFn (x ∘ σ) ++ tail) := by
    let ρ (i : ℕ) : ℕ := if h : i < n then (σ ⟨i, h⟩).val else i
    let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let agree (w z : List Bool) : Prop :=
      w.length = z.length ∧ n ≤ w.length ∧ ∀ i, w.getD (ρ i) false = z.getD i false
    have low (i : ℕ) (h : i < n) : ρ i = (σ ⟨i, h⟩).val := by
      simp only [ρ, dite_eq_left h]
    have high (i : ℕ) (h : n ≤ i) : ρ i = i := by
      simp only [ρ, dite_eq_right (Nat.not_lt.mpr h)]
    have extend (w z : List Bool) (v : Bool) (h : agree w z) :
        agree (w ++ [v]) (z ++ [v]) := by
      refine ⟨by simp only [List.length_append, h.1], ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        exact h.2.1.trans (Nat.le_add_right _ _)
      · intro i
        by_cases present : i < w.length
        · have image : ρ i < w.length := by
            by_cases raw : i < n
            · rw [low i raw]
              exact (σ ⟨i, raw⟩).isLt.trans_le h.2.1
            · rwa [high i (Nat.le_of_not_gt raw)]
          rw [List.getD_append _ _ _ _ image, List.getD_append _ _ _ _ (h.1 ▸ present)]
          exact h.2.2 i
        · rw [high i (h.2.1.trans (Nat.le_of_not_gt present)),
            List.getD_append_right _ _ _ _ (Nat.le_of_not_gt present),
            List.getD_append_right _ _ _ _ (h.1 ▸ Nat.le_of_not_gt present), h.1]
    have sameGate (w z : List Bool) (h : agree w z) (g : Gate) :
        (rename g).op.eval ((rename g).inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => z.getD i false) := by
      change g.op.eval ((g.inputs.map ρ).map (fun i => w.getD i false)) = _
      rw [List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => h.2.2 i)
    have foldAgree (gs : List Gate) (w z : List Bool) (h : agree w z) :
        agree ((gs.map rename).foldl step w) (gs.foldl step z) := by
      induction gs generalizing w z with
      | nil => exact h
      | cons g gs ih =>
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        apply ih
        change agree (w ++ [(rename g).op.eval ((rename g).inputs.map fun i => w.getD i false)])
          (z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)])
        rw [sameGate w z h g]
        exact extend _ _ _ h
    let C : Circuit := ⟨D.gates.map rename, ρ D.output⟩
    refine ⟨C, ?_, List.length_map _, ?_⟩
    · intro g hg
      change g ∈ D.gates.map rename at hg
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
      have legal := mono old hold
      refine ⟨legal.1, ?_⟩
      change (old.inputs.map ρ).length ≤ 2
      rw [List.length_map]
      exact legal.2
    · intro x tail
      have read (y : Fin n → Bool) (i : Fin n) :
          (List.ofFn y ++ tail).getD i.val false = y i := by
        have bound : i.val < (List.ofFn y).length := by
          simpa only [List.length_ofFn] using i.isLt
        rw [List.getD_append _ _ _ _ bound, List.getD_eq_getElem _ _ bound]
        exact List.getElem_ofFn _
      have initial : agree (List.ofFn x ++ tail) (List.ofFn (x ∘ σ) ++ tail) := by
        refine ⟨by simp only [List.length_append, List.length_ofFn],
          by simp only [List.length_append, List.length_ofFn]; exact Nat.le_add_right _ _, ?_⟩
        intro i
        by_cases raw : i < n
        · rw [low i raw]
          exact (read x (σ ⟨i, raw⟩)).trans (read (x ∘ σ) ⟨i, raw⟩).symm
        · have hn := Nat.le_of_not_gt raw
          rw [high i hn,
            List.getD_append_right _ _ _ _ (by simpa only [List.length_ofFn] using hn),
            List.getD_append_right _ _ _ _ (by simpa only [List.length_ofFn] using hn)]
          simp only [List.length_ofFn]
      exact (foldAgree D.gates _ _ initial).2.2 D.output

  have rankPrefix (F : (Fin 14 → Bool) → Bool) (a b c d : Fin 14)
      (ab : a ≠ b) (cd : c ≠ d) :
      let rank := fun (a b c d : Fin 14) =>
        (15 * min a.val b.val + max a.val b.val) * 225 + (15 * min c.val d.val + max c.val d.val)
      let sym := fun (σ : Equiv.Perm (Fin 14)) => ∀ x : Fin 14 → Bool, F (x ∘ σ) = F x
      ∃ (σ : Equiv.Perm (Fin 14)) (p q r s : Fin 14),
        sym σ ∧ p < q ∧ r < s ∧
        ((p = σ a ∧ q = σ b) ∨ (p = σ b ∧ q = σ a)) ∧
        ((r = σ c ∧ s = σ d) ∨ (r = σ d ∧ s = σ c)) ∧
        ∀ τ : Equiv.Perm (Fin 14), sym τ → rank p q r s ≤ rank (τ p) (τ q) (τ r) (τ s) := by
    intro rank sym
    classical
    have existsRank : ∃ k : ℕ, ∃ σ : Equiv.Perm (Fin 14), sym σ ∧ rank (σ a) (σ b) (σ c) (σ d) = k := by
      let e : Equiv.Perm (Fin 14) := Equiv.refl _
      exact ⟨rank (e a) (e b) (e c) (e d), e, fun _ => rfl, rfl⟩
    obtain ⟨σ, σsym, minimal⟩ := Nat.find_spec existsRank
    have ordered (i j : Fin 14) (ne : i ≠ j) : ∃ p q : Fin 14, p < q ∧
        ((p = i ∧ q = j) ∨ (p = j ∧ q = i)) := by
      rcases lt_or_gt_of_ne ne with lt | gt
      · exact ⟨i, j, lt, Or.inl ⟨rfl,rfl⟩⟩
      · exact ⟨j, i, gt, Or.inr ⟨rfl,rfl⟩⟩
    obtain ⟨p,q,ltpq,hpq⟩ := ordered (σ a) (σ b) (fun h => ab (σ.injective h))
    obtain ⟨r,s,ltrs,hrs⟩ := ordered (σ c) (σ d) (fun h => cd (σ.injective h))
    have pairs (τ : Equiv.Perm (Fin 14)) : rank (τ p) (τ q) (τ r) (τ s) =
        rank (τ (σ a)) (τ (σ b)) (τ (σ c)) (τ (σ d)) := by
      have pair (i j v w : Fin 14) (h : (v = i ∧ w = j) ∨ (v = j ∧ w = i)) :
          15 * min (τ v).val (τ w).val + max (τ v).val (τ w).val =
          15 * min (τ i).val (τ j).val + max (τ i).val (τ j).val := by
        rcases h with ⟨hv,hw⟩ | ⟨hv,hw⟩
        · rw [hv,hw]
        · rw [hv,hw,min_comm (τ j).val,max_comm (τ j).val]
      change (15 * min (τ p).val (τ q).val + max (τ p).val (τ q).val) * 225 +
          (15 * min (τ r).val (τ s).val + max (τ r).val (τ s).val) = _
      rw [pair (σ a) (σ b) p q hpq, pair (σ c) (σ d) r s hrs]
    refine ⟨σ,p,q,r,s,σsym,ltpq,ltrs,hpq,hrs,?_⟩
    intro τ τsym
    have compSym : sym (σ.trans τ) := by
      intro x
      change F ((x ∘ τ) ∘ σ) = F x
      exact (σsym (x ∘ τ)).trans (τsym x)
    have step := Nat.find_min' existsRank ⟨σ.trans τ, compSym, rfl⟩
    have left : rank p q r s = rank (σ a) (σ b) (σ c) (σ d) := pairs (Equiv.refl _)
    rw [left, minimal, pairs τ]
    exact step

  have evalPrefMono (D : Circuit) (legal : Monotone2 D)
      (op1 op2 : GateOp) (h1 : op1 = .and ∨ op1 = .or) (h2 : op2 = .and ∨ op2 = .or)
      (a b c d : Fin 14) (x y : Fin 14 → Bool) (le : ∀ i, x i = true → y i = true) :
      let inp := fun z : Fin 14 → Bool => List.ofFn z ++ [op1.eval [z a,z b], op2.eval [z c,z d]]
      D.eval (inp x) = true → D.eval (inp y) = true := by
    intro inp
    let supports (u v : List Bool) :=
      u.length = v.length ∧ ∀ i, u.getD i false = true → v.getD i false = true
    have foldInput (op : GateOp) (good : op = .and ∨ op = .or) (u v : List Bool)
        (huv : supports u v) (args : List ℕ) :
        op.eval (args.map fun i => u.getD i false) = true →
          op.eval (args.map fun i => v.getD i false) = true := by
      rcases good with rfl | rfl
      · change (args.map fun i => u.getD i false).all id = true →
          (args.map fun i => v.getD i false).all id = true
        intro all
        apply List.all_eq_true.mpr
        intro z hz
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
        exact huv.2 i (List.all_eq_true.mp all _ (List.mem_map.mpr ⟨i,hi,rfl⟩))
      · change (args.map fun i => u.getD i false).any id = true →
          (args.map fun i => v.getD i false).any id = true
        intro someTrue
        obtain ⟨z,hz,yep⟩ := List.any_eq_true.mp someTrue
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
        exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨i,hi,rfl⟩, huv.2 i yep⟩
    have extend (u v : List Bool) (huv : supports u v) (p q : Bool) (hpq : p = true → q = true) :
        supports (u ++ [p]) (v ++ [q]) := by
      refine ⟨by simp only [List.length_append,List.length_singleton,huv.1],?_⟩
      intro i on
      by_cases hi : i < u.length
      · rw [List.getD_append _ _ _ _ (huv.1 ▸ hi)]
        rw [List.getD_append _ _ _ _ hi] at on
        exact huv.2 i on
      · have low := Nat.le_of_not_gt hi
        rw [List.getD_append_right _ _ _ _ low] at on
        rw [List.getD_append_right _ _ _ _ (huv.1 ▸ low), ← huv.1]
        cases k : i - u.length with
        | zero =>
          change q = true
          apply hpq
          rw [k] at on
          exact on
        | succ j => simp [k] at on
    have raw (z : Fin 14 → Bool) (i : Fin 14) : (List.ofFn z).getD i.val false = z i := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
      exact List.getElem_ofFn _
    have base : supports (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp only [List.length_ofFn], ?_⟩
      intro i t
      by_cases hi : i < 14
      · have hx := raw x ⟨i,hi⟩
        have hy := raw y ⟨i,hi⟩
        rw [hx] at t
        rw [hy]
        exact le _ t
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa only [List.length_ofFn] using (Nat.le_of_not_gt hi))] at t
        change false = true at t
        exact Bool.noConfusion t
    have pre (op : GateOp) (good : op = .and ∨ op = .or) (i j : Fin 14) :
        op.eval [x i,x j] = true → op.eval [y i,y j] = true := by
      have h := foldInput op good _ _ base [i.val,j.val]
      simpa only [List.map_cons,List.map_nil,raw] using h
    have pref : supports (inp x) (inp y) := by
      have one := extend _ _ base _ _ (pre op1 h1 a b)
      have two := extend _ _ one _ _ (pre op2 h2 c d)
      simpa only [inp,List.append_assoc,List.singleton_append] using two
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have fold (gs : List Gate) (all : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (u v : List Bool)
        (ok : supports u v) : supports (gs.foldl step u) (gs.foldl step v) := by
      induction gs generalizing u v with
      | nil => exact ok
      | cons g gs ih =>
        rw [List.foldl_cons,List.foldl_cons]
        apply ih (fun k hk => all k (List.mem_cons_of_mem _ hk))
        exact extend _ _ ok _ _ (foldInput g.op (all g (List.mem_cons_self ..)) u v ok g.inputs)
    have out := fold D.gates (fun g hg => (legal g hg).1) _ _ pref
    exact out.2 D.output

  intro edges target score lift
  classical
  let edge : Fin 14 → Fin 14 → Prop := fun u v =>
    (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u.val 0).testBit v.val = true
  let P := fun x : Fin 14 → Bool => ∃ u v : Fin 14, edge u v ∧ x u = true ∧ x v = true
  have edgeSpec : ∀ u v : Fin 14, edge u v ↔ (u.val,v.val) ∈ edges := by decide +kernel
  have targetSpec (x : Fin 14 → Bool) : target x = true ↔ P x := by
    change decide (∃ u v : Fin 14, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true) = true ↔ P x
    simp only [decide_eq_true_eq, P, edgeSpec]
  obtain ⟨a,b,c,d,op1,op2,D,q,ab,cd,h1,h2,dGood,dSize,outIn,qIn,pos,neg⟩ := residual
  let inp (x : Fin 14 → Bool) := List.ofFn x ++ [op1.eval [x a,x b],op2.eval [x c,x d]]
  let asFn (x : Fin 14 → Bool) (i : Fin 16) := (inp x).getD i.val false
  have asList (x : Fin 14 → Bool) : List.ofFn (asFn x) = inp x := by
    apply List.ext_getElem
    · simp only [inp,List.length_ofFn,List.length_append,List.length_cons,List.length_nil]
    · intro i hi hj
      rw [List.getElem_ofFn]
      exact List.getD_eq_getElem _ _ hj
  have getRaw (x : Fin 14 → Bool) (tail : List Bool) (i : Fin 14) :
      (List.ofFn x ++ tail).getD i.val false = x i := by
    have bound : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
    rw [List.getD_append _ _ _ _ bound, List.getD_eq_getElem _ _ bound]
    exact List.getElem_ofFn _
  obtain ⟨C,cGood,cSize,cEval⟩ := append 16 D (0 : Fin 16) q dGood outIn qIn
  have eval (x : Fin 14 → Bool) : C.eval (inp x) =
      (D.eval (inp x) || (x 0 && (D.wires (inp x)).getD q false)) := by
    have e := cEval (asFn x)
    have raw0 : asFn x 0 = x 0 := getRaw x _ 0
    rw [asList x,raw0] at e
    exact e
  have exactC (x : Fin 14 → Bool) : C.eval (inp x) = target x := by
    have iffTrue : C.eval (inp x) = true ↔ target x = true := by
      rw [targetSpec]
      constructor
      · intro hit
        by_contra no
        obtain ⟨y, incl, maximal⟩ := Finite.exists_le_maximal (p := fun z => ¬ P z) no
        have pin (i : Fin 14) (hi : x i = true) : y i = true := by
          have iy := incl i
          cases e : y i
          · rw [hi,e] at iy
            exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) iy)
          · rfl
        have high := evalPrefMono C cGood op1 op2 h1 h2 a b c d x y pin hit
        change C.eval (inp y) = true at high
        have off : C.eval (inp y) = false := (eval y).trans (neg y maximal)
        exact Bool.noConfusion (off.symm.trans high)
      · rintro ⟨u,v,uv,hu,hv⟩
        apply evalPrefMono C cGood op1 op2 h1 h2 a b c d (pairInput u v) x
        · intro i on
          have hit : i = u ∨ i = v := of_decide_eq_true on
          rcases hit with rfl | rfl <;> assumption
        · change C.eval (inp (pairInput u v)) = true
          rw [eval]
          exact pos u v uv
    exact Bool.eq_iff_iff.mpr iffTrue
  obtain ⟨σ,u,v,w,z,sym,uv,wz,sw1,sw2,rank⟩ := rankPrefix target a b c d ab cd
  obtain ⟨E,eGood,eSize,eEval⟩ := renameInputs 14 σ C cGood
  let embed (i : Fin 14) : Fin 15 := ⟨i.val,i.isLt.trans (by decide : 14 < 15)⟩
  have liftRaw (τ : Equiv.Perm (Fin 14)) (i : Fin 14) : lift τ (embed i) = (τ i).val := by
    change (if i.val < 14 then (τ (Fin.ofNat 14 i.val)).val else 14) = _
    have index : Fin.ofNat 14 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [ite_eq_left i.isLt,index]
  have sameGate (x : Fin 14 → Bool) (op : GateOp) (good : op = .and ∨ op = .or)
      (i j k l : Fin 14) (h : (k = i ∧ l = j) ∨ (k = j ∧ l = i)) :
      op.eval [x k,x l] = op.eval [x i,x j] := by
    rcases h with ⟨hk,hl⟩ | ⟨hk,hl⟩
    · rw [hk,hl]
    · rw [hk,hl]
      rcases good with rfl | rfl
      · change (x j && (x i && true)) = (x i && (x j && true))
        rw [Bool.and_true,Bool.and_true,Bool.and_comm]
      · change (x j || (x i || false)) = (x i || (x j || false))
        rw [Bool.or_false,Bool.or_false,Bool.or_comm]
  refine ⟨u,v,embed w,embed z,op1,op2,E,uv,wz,h1,h2,?_,eGood,by omega,?_⟩
  · intro τ hτ
    rw [liftRaw,liftRaw]
    exact rank τ hτ
  · intro x
    let raw := List.ofFn x ++ [op1.eval [x u,x v]]
    change E.eval (raw ++ [op2.eval [raw.getD w.val false,raw.getD z.val false]]) = target x
    have wr : raw.getD w.val false = x w := getRaw x _ w
    have zr : raw.getD z.val false = x z := getRaw x _ z
    rw [wr,zr]
    change E.eval ((List.ofFn x ++ [op1.eval [x u,x v]]) ++ [op2.eval [x w,x z]]) = target x
    rw [List.append_assoc]
    change E.eval (List.ofFn x ++ [op1.eval [x u,x v],op2.eval [x w,x z]]) = target x
    rw [eEval, sameGate x op1 h1 (σ a) (σ b) u v sw1, sameGate x op2 h2 (σ c) (σ d) w z sw2]
    change C.eval (inp (x ∘ σ)) = target x
    rw [exactC,sym]

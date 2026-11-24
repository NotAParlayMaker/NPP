import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3606

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def gv (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [gv g (W gs x)] := by
  simp [W, gv, List.foldl_append]

lemma W_length (gs : List Gate) (x : List Bool) :
    (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

lemma W_take_succ (gs : List Gate) (k : ℕ) (hk : k < gs.length) (x : List Bool) :
    W (gs.take (k + 1)) x = W (gs.take k) x ++ [gv gs[k] (W (gs.take k) x)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  exact W_snoc (gs.take k) gs[k] x

lemma getD_snoc (L : List Bool) (v : Bool) (i : ℕ) :
    (L ++ [v]).getD i false =
      if i < L.length then L.getD i false else if i = L.length then v else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : i - L.length ≠ 0 := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero this
    rw [hm]; simp

lemma gv_mono (g : Gate) (w w' : List Bool)
    (hww : ∀ i, w.getD i false = true → w'.getD i false = true)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    gv g w = true → gv g w' = true := by
  unfold gv
  rcases hop with h | h <;> rw [h] <;> simp only [GateOp.eval]
  · simp only [List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro H t ht; exact hww t (H t ht)
  · simp only [List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    rintro ⟨t, ht, h2⟩; exact ⟨t, ht, hww t h2⟩

lemma mono (gs : List Gate) (X Y : List Bool) (hlen : X.length = Y.length)
    (hXY : ∀ i, X.getD i false = true → Y.getD i false = true) (K : ℕ) (hK : K ≤ gs.length)
    (hg : ∀ j (hj : j < K), (gs[j]'(by omega)).op = GateOp.and ∨
      (gs[j]'(by omega)).op = GateOp.or ∨
      (gv (gs[j]'(by omega)) (W (gs.take j) X) = true →
        gv (gs[j]'(by omega)) (W (gs.take j) Y) = true)) :
    ∀ k ≤ K, ∀ i, (W (gs.take k) X).getD i false = true →
      (W (gs.take k) Y).getD i false = true := by
  intro k
  induction k with
  | zero => intro _ i; simpa [W] using hXY i
  | succ k ih =>
    intro hk i hi
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    rw [W_take_succ gs k hkl, getD_snoc] at hi ⊢
    have lX := W_length (gs.take k) X
    have lY := W_length (gs.take k) Y
    have hLL : (W (gs.take k) X).length = (W (gs.take k) Y).length := by omega
    rw [← hLL]
    split_ifs at hi ⊢ with h1 h2
    · exact ih' i hi
    · rcases hg k (by omega) with h | h | h
      · exact gv_mono _ _ _ ih' (Or.inl h) hi
      · exact gv_mono _ _ _ ih' (Or.inr h) hi
      · exact h hi

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · rw [List.getElem?_eq_none (by simpa using h)]; rfl

end PEqualNP.Outside.L_meta_3606

open PEqualNP.Outside.L_meta_3606

theorem PEqualNP.Outside.L_meta_3606 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin x1.gates.length), PEqualNP.MetaComplexity.FanInTwo x1 → x2 < x3 → ↑x3 + (1 : ℕ) = x1.size → x1.output = (9 : ℕ) + ↑x3 → (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ (x10 : Fin x1.gates.length), (x1.gates.get x10).op = PEqualNP.CircuitLowerBounds.GateOp.not → x10 = x2 ∨ x10 = x3) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x11 : Fin (9 : ℕ)) => Bool.false) = Bool.false → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x12 : Fin (9 : ℕ)) => Bool.true) = Bool.true → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x13 ∧ x13.size ≤ ↑x2 ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x13 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 := by
  intro C p q hfan hpq hsize hout hp hq honly h0 h1
  have hsize' : (q : ℕ) + 1 = C.gates.length := hsize
  have hpl : (p : ℕ) < C.gates.length := p.isLt
  have hql : (q : ℕ) < C.gates.length := q.isLt
  have hpq' : (p : ℕ) < q := hpq
  -- the gate operations
  have hops : ∀ j (hj : j < (q : ℕ)), j ≠ (p : ℕ) →
      (C.gates[j]'(by omega)).op = GateOp.and ∨ (C.gates[j]'(by omega)).op = GateOp.or := by
    intro j hj hjp
    have hm : C.gates[j]'(by omega) ∈ C.gates := List.getElem_mem _
    rcases (hfan _ hm).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases honly ⟨j, by omega⟩ (by simpa using h) with h' | h'
      · exact hjp (congrArg Fin.val h')
      · have := congrArg Fin.val h'; simp at this; omega
  have hp' : (C.gates[(p : ℕ)]).op = GateOp.not := by simpa using hp
  have hq' : (C.gates[(q : ℕ)]).op = GateOp.not := by simpa using hq
  -- the value read by the first NOT, and by the output NOT
  let hv : List Bool → Bool := fun X =>
    ((C.gates[(p : ℕ)]).inputs.map fun t => (W (C.gates.take p) X).getD t false).headD false
  let bv : List Bool → Bool := fun X =>
    ((C.gates[(q : ℕ)]).inputs.map fun t => (W (C.gates.take q) X).getD t false).headD false
  have hgvp : ∀ X, gv C.gates[(p : ℕ)] (W (C.gates.take p) X) = !(hv X) := by
    intro X; simp only [gv, hv, hp', GateOp.eval]
  have hF : ∀ x : Fin 9 → Bool, circuitFun 9 C x = !(bv (List.ofFn x)) := by
    intro x
    change (W C.gates (List.ofFn x)).getD C.output false = _
    rw [hout]
    have hgs : W C.gates (List.ofFn x) = W (C.gates.take ((q : ℕ) + 1)) (List.ofFn x) := by
      rw [List.take_of_length_le (by omega)]
    rw [hgs, W_take_succ C.gates q hql, getD_snoc]
    have hl : (W (C.gates.take q) (List.ofFn x)).length = 9 + q := by
      rw [W_length]; simp only [List.length_ofFn, List.length_take]; omega
    simp only [hl, lt_self_iff_false, ↓reduceIte, gv, bv, hq', GateOp.eval]
  have headD_mono : ∀ (l : List ℕ) (f g : ℕ → Bool), (∀ t, f t = true → g t = true) →
      (l.map f).headD false = true → (l.map g).headD false = true := by
    intro l f g hfg
    cases l with
    | nil => simp
    | cons a l => simpa using hfg a
  have hvmono : ∀ X Y : List Bool, X.length = Y.length →
      (∀ i, X.getD i false = true → Y.getD i false = true) → hv X = true → hv Y = true := by
    intro X Y hlen hXY
    apply headD_mono
    apply mono C.gates X Y hlen hXY p (by omega) _ p le_rfl
    intro j hj
    rcases hops j (by omega) (by omega) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have bvmono : ∀ X Y : List Bool, X.length = Y.length →
      (∀ i, X.getD i false = true → Y.getD i false = true) →
      (!(hv X) = true → !(hv Y) = true) → bv X = true → bv Y = true := by
    intro X Y hlen hXY hN
    apply headD_mono
    apply mono C.gates X Y hlen hXY q (by omega) _ q le_rfl
    intro j hj
    by_cases hjp : j = (p : ℕ)
    · subst hjp
      right; right
      rw [hgvp, hgvp]; exact hN
    · rcases hops j hj hjp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  refine ⟨⟨C.gates.take p, (C.gates[(p : ℕ)]).inputs.headD (9 + p)⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact hfan g (List.mem_of_mem_take hg)
  · simp [Circuit.size]
  · funext x
    have hD : circuitFun 9 ⟨C.gates.take p, (C.gates[(p : ℕ)]).inputs.headD (9 + p)⟩ x
        = hv (List.ofFn x) := by
      change (W (C.gates.take p) (List.ofFn x)).getD _ false = _
      simp only [hv]
      cases hin : (C.gates[(p : ℕ)]).inputs with
      | nil =>
        simp only [List.headD_nil, List.map_nil]
        rw [List.getD_eq_default]
        rw [W_length]; simp
      | cons a l => simp
    rw [hD, hF]
    have hZ : ∀ i, (List.ofFn fun _ : Fin 9 => false).getD i false = true →
        (List.ofFn x).getD i false = true := by
      intro i; rw [ofFn_getD]; split_ifs <;> simp
    have hO : ∀ i, (List.ofFn x).getD i false = true →
        (List.ofFn fun _ : Fin 9 => true).getD i false = true := by
      intro i; rw [ofFn_getD, ofFn_getD]; split_ifs <;> simp
    have e0 := hF (fun _ => false)
    have e1 := hF (fun _ => true)
    rw [h0] at e0
    rw [h1] at e1
    cases hX : hv (List.ofFn x)
    · have hZv : hv (List.ofFn fun _ : Fin 9 => false) = false := by
        cases hz : hv (List.ofFn fun _ : Fin 9 => false)
        · rfl
        · have := hvmono _ _ (by simp) hZ hz; rw [hX] at this; exact absurd this (by simp)
      have hb0 : bv (List.ofFn fun _ : Fin 9 => false) = true := by
        cases hb : bv (List.ofFn fun _ : Fin 9 => false)
        · rw [hb] at e0; simp at e0
        · rfl
      have := bvmono _ _ (by simp) hZ (by rw [hZv, hX]; simp) hb0
      rw [this]; rfl
    · have hb1 : bv (List.ofFn fun _ : Fin 9 => true) = false := by
        cases hb : bv (List.ofFn fun _ : Fin 9 => true)
        · rfl
        · rw [hb] at e1; simp at e1
      cases hbx : bv (List.ofFn x)
      · rfl
      · have hv1 := hvmono _ _ (by simp) hO hX
        have := bvmono _ _ (by simp) hO (by rw [hX, hv1]; simp) hbx
        rw [hb1] at this; exact absurd this (by simp)

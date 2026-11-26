import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18205
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK PEqualNP.TopForm
open PEqualNP.ReadTwo (wval)

theorem foldl_snoc_prefix {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_prefix {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_init {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d
      = init.getD i d :=
  getD_of_prefix (foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _) hi d

theorem foldl_snoc_beyond {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : init.length + gs.length ≤ i) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d = d := by
  apply List.getD_eq_default
  rw [foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
  exact hi

theorem foldl_snoc_gate {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < init.length + j) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD
        (init.length + j) d
      = G (gs[j].inputs.map fun i =>
          (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d)
          gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init
    with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
    simp; omega
  have hpre : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]) <+:
      gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _
  have hpre2 := (List.prefix_append P _).trans hpre
  rw [getD_of_prefix hpre (by simp; omega)]
  have e1 : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]).getD (init.length + j) d
      = G (gs[j].inputs.map fun i => P.getD i d) gs[j] := by
    rw [← hPl]; simp
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_of_prefix hpre2 (by rw [hPl]; exact hrb i hi)]

theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl
      (fun R g => R ++ [(fun ins (g : Gate) => g.op.eval ins) (g.inputs.map fun i => R.getD i false) g])
      x := rfl

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

section Wires
variable (C : Circuit) (n : ℕ)

abbrev W (x : Fin n → Bool) (i : ℕ) : Bool := (C.wires (List.ofFn x)).getD i false

theorem W_input (x : Fin n → Bool) (i : ℕ) (hi : i < n) : W C n x i = x ⟨i, hi⟩ := by
  unfold W
  rw [wires_eq, foldl_snoc_init (fun ins (g : Gate) => g.op.eval ins) false _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem W_gate (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    W C n x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W C n x)) := by
  unfold W
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (fun ins (g : Gate) => g.op.eval ins) false (List.ofFn x) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_ofFn] at this
  rw [wires_eq, this]

end Wires

theorem binary_g {C : Circuit} {n : ℕ} (ao : IsAO2 n C) (j : ℕ) (hj : j<C.gates.length) :
    ∃ l r, (gateAt C j).inputs=[l,r] ∧ l<n+j ∧ r<n+j ∧
      ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) := by
  have mem : gateAt C j ∈ C.gates := by rw [gateAt_eq C j hj]; exact List.getElem_mem _
  obtain ⟨l,r,eq⟩ := List.length_eq_two.1 (ao.2.2 _ mem)
  exact ⟨l,r,eq,ao.2.1 j hj l (by simp [eq]),ao.2.1 j hj r (by simp [eq]),ao.1 _ mem⟩


abbrev sv {n : ℕ} (C : Circuit) (a : Fin n) := W C n (PEqualNP.ReadTwo.indW n {a.val})
abbrev excl {n : ℕ} (C : Circuit) (a b : Fin n) (w : ℕ) :=
  sv C a w = true ∧ sv C b w = false
abbrev arc {n : ℕ} (C : Circuit) (a b : Fin n) (u v : ℕ) :=
  n ≤ v ∧ u ∈ (gateAt C (v-n)).inputs ∧ excl C a b u ∧ excl C a b v

theorem choosePred (op : GateOp) (ho : op = .and ∨ op = .or)
    (a b c d : Bool) (h : op.eval [a,b] = true) (k : op.eval [c,d] = false) :
    (a = true ∧ c = false) ∨ (b = true ∧ d = false) := by
  rcases ho with rfl | rfl <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all [GateOp.eval]

theorem trace {n : ℕ} {C : Circuit} (ao : IsAO2 n C) (a b : Fin n) (w : ℕ) :
    w < n + C.gates.length → excl C a b w → Relation.ReflTransGen (arc C a b) a.val w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hd
    by_cases hbase : w < n
    · have hx := hd.1
      change W C n (PEqualNP.ReadTwo.indW n {a.val}) w = true at hx
      rw [W_input _ _ _ _ hbase] at hx
      have heq : w = a.val := by simpa [PEqualNP.ReadTwo.indW] using hx
      rw [heq]
    · let j := w - n
      have he : w = n + j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      obtain ⟨l,r,hr,hl',hr',hop⟩ := binary_g ao j hj
      have vals (v : Fin n) : sv C v w = (gateAt C j).op.eval [sv C v l, sv C v r] := by
        change W C n _ w = _
        rw [he,W_gate _ _ _ _ hj (ao.2.1 j hj),hr]
        rfl
      have hOut := hd
      obtain ⟨ha,hb⟩ := hd
      rw [vals] at ha hb
      have pred := choosePred _ hop _ _ _ _ ha hb
      have next (i : ℕ) (hi : i ∈ [l,r]) (small : i < w) (good : excl C a b i) :
          Relation.ReflTransGen (arc C a b) a.val w := by
        apply (ih i small (by omega) good).tail
        exact ⟨by omega,by change i ∈ (gateAt C j).inputs; rw [hr]; exact hi,good,hOut⟩
      rcases pred with left | right
      · exact next l (by simp) (by omega) left
      · exact next r (by simp) (by omega) right

end PEqualNP.Outside.L_meta_18205

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_18205 in
theorem PEqualNP.Outside.L_meta_18205 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 x5 : Fin x1) (x6 : ℕ),       PEqualNP.ReadTwo.isAnd x2 x6 →         have x8 : Fin x1 → ℕ → Bool := fun (x8 : Fin x1) => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW x1 {↑x8});         have x9 : ℕ → Prop := fun (x9 : ℕ) => x8 x4 x9 = Bool.true ∧ x8 x5 x9 = Bool.false;         have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => x1 ≤ x11 ∧ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x11 - x1)).inputs ∧ x9 x10 ∧ x9 x11;         x8 x4 (x1 + x6) = Bool.true → (∀ x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs, x8 x5 x12 = Bool.false) → ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs, x9 x13 ∧ Relation.ReflTransGen x10 (↑x4) x13 := by
  intro n C ao a b j hand
  dsimp only
  intro yes no i hi
  change sv C a (n+j) = true at yes
  change ∀ t ∈ (gateAt C j).inputs, sv C b t = false at no
  change excl C a b i ∧ Relation.ReflTransGen (arc C a b) a.val i
  have hv : W C n (PEqualNP.ReadTwo.indW n {a.val}) (n+j) = true := yes
  rw [W_gate _ _ _ _ hand.1 (ao.2.1 j hand.1),hand.2] at hv
  have hAll : ∀ t ∈ (gateAt C j).inputs, sv C a t = true := by
    simpa [GateOp.eval, Function.comp_def] using hv
  have good : excl C a b i := ⟨hAll i hi,no i hi⟩
  exact ⟨good,trace ao a b i (by have h := ao.2.1 j hand.1 i hi; have hh := hand.1; omega) good⟩

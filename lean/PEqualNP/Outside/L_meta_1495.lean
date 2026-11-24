import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1495_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

def deps (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.head?.toList
  | _ => g.inputs

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ deps g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, l⟩ := g
  cases op with
  | not =>
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton, forall_eq] at h
      simp [GateOp.eval, h]
  | _ =>
    simp only [deps] at h
    rw [List.map_congr_left h]

theorem getD_eraseIdx_lt (l : List Bool) (p i : ℕ) (hi : i < p) :
    (l.eraseIdx p).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hi]

theorem getD_eraseIdx_ge (l : List Bool) (p i : ℕ) (hi : p ≤ i) :
    (l.eraseIdx p).getD i false = l.getD (i + 1) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hi]

def ren (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def renG (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren p r)⟩

def del (G : List Gate) (t p r : ℕ) : List Gate := G.take t ++ (G.drop (t + 1)).map (renG p r)

theorem deps_renG (p r : ℕ) (g : Gate) : deps (renG p r g) = (deps g).map (ren p r) := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [deps, renG]

theorem del_foldl_aux (W : List Bool) (p r : ℕ) (hr : r < p ∨ W.length ≤ r) :
    ∀ (L : List Gate) (v : List Bool), L.foldl step v = W → p < v.length →
      (∀ g ∈ L, p ∈ deps g → W.getD p false = W.getD r false) →
      (L.map (renG p r)).foldl step (v.eraseIdx p) = W.eraseIdx p := by
  intro L
  induction L with
  | nil =>
    intro v hW _ _
    simp only [List.foldl_nil] at hW
    subst hW
    rfl
  | cons g L ih =>
    intro v hW hp hv
    rw [List.foldl_cons] at hW
    rw [List.map_cons, List.foldl_cons]
    have hvW : ∀ i, i < v.length → v.getD i false = W.getD i false := fun i hi => by
      rw [← hW, foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact (getD_append_lt _ _ _ hi).symm
    have hWlen : v.length + 1 + L.length = W.length := by
      have := congrArg List.length hW
      rw [foldl_step_length] at this
      simp only [step, List.length_append, List.length_singleton] at this
      omega
    have hstep : step (v.eraseIdx p) (renG p r g) = (step v g).eraseIdx p := by
      simp only [step, renG, List.map_map]
      rw [List.eraseIdx_append_of_lt_length hp]
      congr 2
      apply eval_congr
      intro i hi
      simp only [Function.comp, ren]
      split_ifs with h1 h2
      · exact getD_eraseIdx_lt _ _ _ h1
      · subst h2
        rcases hr with hr | hr
        · rw [getD_eraseIdx_lt _ _ _ hr, hvW _ (by omega), hvW _ hp]
          exact (hv g (by simp) hi).symm
        · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega), hvW _ hp,
            hv g (by simp) hi, getD_of_length_le _ _ hr]
      · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]
    rw [hstep]
    exact ih _ hW (by simp only [step, List.length_append, List.length_singleton]; omega)
      (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))

theorem del_foldl (G : List Gate) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    (del G t (x.length + t) r).foldl step x = (G.foldl step x).eraseIdx (x.length + t) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by simp
  have hWlen : (G.foldl step x).length = x.length + G.length := foldl_step_length _ _
  have hW' : (G.drop (t + 1)).foldl step (step ((G.take t).foldl step x) G[t]) = G.foldl step x := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlen : ((G.take t).foldl step x).length = x.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  have hv0 : (G.take t).foldl step x = (step ((G.take t).foldl step x) G[t]).eraseIdx (x.length + t) := by
    simp only [step]
    rw [List.eraseIdx_append_of_length_le (by omega)]
    simp [hlen]
  unfold del
  rw [List.foldl_append, hv0]
  exact del_foldl_aux _ (x.length + t) r (by rwa [hWlen]) _ _ hW'
    (by simp only [step, List.length_append, List.length_singleton, hlen]; omega) hv

theorem del_eval (G : List Gate) (o : ℕ) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false)
    (ho : o = x.length + t → (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    Circuit.eval ⟨del G t (x.length + t) r, ren (x.length + t) r o⟩ x = Circuit.eval ⟨G, o⟩ x := by
  simp only [Circuit.eval, wires_eq]
  rw [del_foldl G x t r ht hr hv]
  unfold ren
  split_ifs with h1 h2
  · exact getD_eraseIdx_lt _ _ _ h1
  · subst h2
    rcases hr with hr | hr
    · rw [getD_eraseIdx_lt _ _ _ hr]
      exact (ho rfl).symm
    · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt (by rw [foldl_step_length]; omega), foldl_step_length]; omega),
        ho rfl, getD_of_length_le _ _ (by rw [foldl_step_length]; exact hr)]
  · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]

theorem del_length (G : List Gate) (t p r : ℕ) (ht : t < G.length) :
    (del G t p r).length = G.length - 1 := by
  simp only [del, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem gateAt_del_lt (G : List Gate) (t p r o k : ℕ) (ht : t < G.length) (hk : k < t) :
    gateAt ⟨del G t p r, o⟩ k = gateAt ⟨G, o⟩ k := by
  simp only [gateAt, del, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [List.length_take, Nat.min_eq_left ht.le]; exact hk)]
  rw [List.getElem?_take_of_lt hk]

theorem gateAt_del_ge (G : List Gate) (t p r o k : ℕ) (ht : t < G.length) (hk : t ≤ k)
    (hkl : k < G.length - 1) :
    gateAt ⟨del G t p r, o⟩ k = renG p r (gateAt ⟨G, o⟩ (k + 1)) := by
  simp only [gateAt, del, List.getD_eq_getElem?_getD]
  have htlen : (G.take t).length = t := by rw [List.length_take, Nat.min_eq_left ht.le]
  rw [List.getElem?_append_right (by rw [htlen]; exact hk)]
  rw [htlen]
  rw [List.getElem?_map, List.getElem?_drop]
  have hkp : k + 1 < G.length := by omega
  have hidx : t + 1 + (k - t) = k + 1 := by omega
  rw [hidx, List.getElem?_eq_getElem hkp]
  simp

theorem readsBack_del (n t r o : ℕ) (G : List Gate) (ht : t < G.length) (hr : r < n + t)
    (h : ReadsBack n ⟨G, o⟩) : ReadsBack n ⟨del G t (n + t) r, o⟩ := by
  intro k hk i hi
  have hkl : k < G.length - 1 := by
    rw [del_length G t (n + t) r ht] at hk
    exact hk
  have hglen : 0 < G.length := by omega
  have hk1 : k + 1 < G.length := by omega
  by_cases hkt : k < t
  · have hkg : k < G.length := by omega
    have hgate := gateAt_del_lt G t (n + t) r o k ht hkt
    rw [hgate] at hi
    exact h k hkg i hi
  · have hkt' : t ≤ k := by omega
    have hgate := gateAt_del_ge G t (n + t) r o k ht hkt' hkl
    rw [hgate] at hi
    rcases List.mem_map.mp hi with ⟨w, hw, rfl⟩
    have hwlt : w < n + (k + 1) := h (k + 1) hk1 w hw
    unfold ren
    split_ifs with h1 h2
    · omega
    · omega
    · omega

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem no_dup {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j r : ℕ) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hmin : ∀ C' : Circuit, IsAO2 n C' → circuitFun n C' = graphFun G ∅ → C.size ≤ C'.size)
    (hj : j < C.gates.length) (hne : n + j ≠ C.output) (hr : r < n + j)
    (hv : ∀ x : Fin n → Bool,
      gateVal n C j x = (C.gates.foldl step (List.ofFn x)).getD r false) : False := by
  set C' : Circuit := ⟨del C.gates j (n + j) r, ren (n + j) r C.output⟩ with hC'
  have hsize' : C'.size = C.gates.length - 1 := by
    simp only [hC', Circuit.size]
    exact del_length C.gates j (n + j) r hj
  have hdel_eval : ∀ x : Fin n → Bool,
      Circuit.eval C' (List.ofFn x) = Circuit.eval C (List.ofFn x) := by
    intro x
    have hlen : (List.ofFn x).length = n := by simp
    have h := del_eval C.gates C.output (List.ofFn x) j r hj
      (by rw [hlen]; exact Or.inl hr)
      (by
        intro g hg hd
        have hvx := hv x
        rw [hlen] at hd ⊢
        simpa [gateVal, wires_eq] using hvx)
      (by
        intro ho
        have ho' : n + j = C.output := by
          rw [hlen] at ho
          exact ho.symm
        exact absurd ho' hne)
    simpa [hC', hlen] using h
  have hAO' : IsAO2 n C' := by
    rcases hAO with ⟨hAOonly, hRB, hlen2⟩
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [hC', del, List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g', hg', rfl⟩
      · exact hAOonly g (List.mem_of_mem_take hg)
      · exact hAOonly g' (List.mem_of_mem_drop hg')
    · exact readsBack_del n j r C.output C.gates hj hr hRB
    · intro g hg
      simp only [hC', del, List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g', hg', rfl⟩
      · exact hlen2 g (List.mem_of_mem_take hg)
      · simp only [renG, List.length_map]
        exact hlen2 g' (List.mem_of_mem_drop hg')
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    show C'.eval (List.ofFn x) = graphFun G ∅ x
    exact (hdel_eval x).trans (congrFun hfun x)
  have hle := hmin C' hAO' hfun'
  have hclen : C.size = C.gates.length := rfl
  omega

end PEqualNP.Outside.L_meta_1495_aux

theorem PEqualNP.Outside.L_meta_1495 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.IsLeastAO G C →
  ∀ (j : ℕ), j < C.gates.length → n + j ≠ C.output →
    (∀ i < j, ∃ x : Fin n → Bool,
        PEqualNP.EdgeOwnership.gateVal n C i x ≠ PEqualNP.EdgeOwnership.gateVal n C j x) ∧
    (∀ u : Fin n, ∃ x : Fin n → Bool, x u ≠ PEqualNP.EdgeOwnership.gateVal n C j x) := by
  intro n G _ C hleast j hj hne
  rcases hleast with ⟨hAO, hfun, hmin⟩
  constructor
  · intro i hi
    by_contra hcon
    have heq : ∀ x : Fin n → Bool,
        PEqualNP.EdgeOwnership.gateVal n C i x =
          PEqualNP.EdgeOwnership.gateVal n C j x := by
      intro x
      by_contra hx
      exact hcon ⟨x, hx⟩
    refine PEqualNP.Outside.L_meta_1495_aux.no_dup G C j (n + i) hAO hfun hmin hj hne
      (by omega) ?_
    intro x
    exact (heq x).symm
  · intro u
    by_contra hcon
    have heq : ∀ x : Fin n → Bool, x u =
        PEqualNP.EdgeOwnership.gateVal n C j x := by
      intro x
      by_contra hx
      exact hcon ⟨x, hx⟩
    refine PEqualNP.Outside.L_meta_1495_aux.no_dup G C j u.val hAO hfun hmin hj hne
      (by have := u.isLt; omega) ?_
    intro x
    rw [PEqualNP.Outside.L_meta_1495_aux.foldl_step_getD C.gates (List.ofFn x) u.val
      (by simpa only [List.length_ofFn] using u.isLt)]
    rw [PEqualNP.Outside.L_meta_1495_aux.getD_ofFn x u.val u.isLt]
    exact (heq x).symm

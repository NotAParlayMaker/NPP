import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4821

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- One evaluation step: the wire list grows by the value of the gate.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_len : ∀ (gs : List Gate) (u : List Bool),
    (gs.foldl step u).length = u.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro u; simp
  | cons g gs ih =>
    intro u
    rw [List.foldl_cons, ih]
    simp [step]
    omega

-- The wire renaming after gate number q is deleted.
def rn (q k : ℕ) : ℕ := if k < q then k else k - 1

def ren (q : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rn q)⟩

theorem fold_del (q : ℕ) : ∀ (gs : List Gate) (u v : List Bool),
    (∀ g ∈ gs, q ∉ g.inputs) → v.length + 1 = u.length → q < u.length →
    (∀ i, i ≠ q → v.getD (rn q i) false = u.getD i false) →
    ∀ i, i ≠ q →
      ((gs.map (ren q)).foldl step v).getD (rn q i) false = (gs.foldl step u).getD i false := by
  intro gs
  induction gs with
  | nil => intro u v _ _ _ h i hi; exact h i hi
  | cons g gs ih =>
    intro u v hno hl hq h i hi
    simp only [List.map_cons, List.foldl_cons]
    have hval : (ren q g).op.eval ((ren q g).inputs.map fun i => v.getD i false) =
        g.op.eval (g.inputs.map fun i => u.getD i false) := by
      show g.op.eval ((g.inputs.map (rn q)).map fun i => v.getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha))
    apply ih (step u g) (step v (ren q g))
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
      (by simp [step]; omega) (by simp [step]; omega) ?_ i hi
    intro k hk
    unfold step
    rw [hval]
    by_cases hku : k < u.length
    · have hr : rn q k < v.length := by unfold rn; split <;> omega
      rw [List.getD_append _ _ _ _ hr, List.getD_append _ _ _ _ hku]
      exact h k hk
    · have hr : v.length ≤ rn q k := by unfold rn; split <;> omega
      rw [List.getD_append_right _ _ _ _ hr, List.getD_append_right _ _ _ _ (by omega)]
      congr 1
      unfold rn
      split <;> omega

theorem fold_ind (q : ℕ) : ∀ (gs : List Gate) (u v : List Bool),
    (∀ g ∈ gs, q ∉ g.inputs) → u.length = v.length →
    (∀ i, i ≠ q → u.getD i false = v.getD i false) →
    ∀ i, i ≠ q → (gs.foldl step u).getD i false = (gs.foldl step v).getD i false := by
  intro gs
  induction gs with
  | nil => intro u v _ _ h i hi; exact h i hi
  | cons g gs ih =>
    intro u v hno hl h i hi
    simp only [List.foldl_cons]
    have hval : g.op.eval (g.inputs.map fun i => u.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha))
    apply ih (step u g) (step v g)
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
      (by simp [step]; omega) ?_ i hi
    intro k hk
    unfold step
    rw [hval]
    by_cases hku : k < u.length
    · rw [List.getD_append _ _ _ _ hku, List.getD_append _ _ _ _ (by omega)]
      exact h k hk
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

theorem del_fun (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ)
    (x : List Bool) (hx : x.length = n)
    (hno : ∀ h ∈ post, (n + pre.length) ∉ h.inputs) (hout : out ≠ n + pre.length) :
    (⟨pre ++ post.map (ren (n + pre.length)), rn (n + pre.length) out⟩ : Circuit).eval x =
      (⟨pre ++ g :: post, out⟩ : Circuit).eval x := by
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  simp only [List.foldl_append, List.foldl_cons]
  apply fold_del (n + pre.length) post (step (pre.foldl step x) g) (pre.foldl step x) hno
    (by simp [step]) (by simp [step, fold_len, hx]) ?_ out hout
  intro i hi
  have hlen : (pre.foldl step x).length = n + pre.length := by rw [fold_len, hx]
  generalize pre.foldl step x = W at hlen
  unfold step
  by_cases hi' : i < n + pre.length
  · rw [show rn (n + pre.length) i = i from if_pos hi',
      List.getD_append _ _ _ _ (by omega)]
  · have hr : rn (n + pre.length) i = i - 1 := if_neg hi'
    rw [hr, List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by simp; omega)]

theorem rb_iff (n : ℕ) (gs : List Gate) (out : ℕ) :
    ReadsBack n ⟨gs, out⟩ ↔
      ∀ (j : ℕ) (g : Gate), gs[j]? = some g → ∀ i ∈ g.inputs, i < n + j := by
  unfold ReadsBack gateAt
  constructor
  · intro h j g hg i hi
    have hj : j < gs.length := (List.getElem?_eq_some_iff.mp hg).1
    have := h j hj i
    rw [List.getD_eq_getElem?_getD, hg] at this
    exact this hi
  · intro h j hj i hi
    have hg : gs[j]? = some gs[j] := List.getElem?_eq_getElem hj
    rw [List.getD_eq_getElem?_getD, hg] at hi
    exact h j gs[j] hg i hi

theorem del_ao2 (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (out out' : ℕ)
    (h : IsAO2 n ⟨pre ++ g :: post, out⟩)
    (hno : ∀ h ∈ post, (n + pre.length) ∉ h.inputs) :
    IsAO2 n ⟨pre ++ post.map (ren (n + pre.length)), out'⟩ := by
  obtain ⟨hao, hrb, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_map] at hg'
    rcases hg' with h | ⟨g0, hg0, rfl⟩
    · exact hao g' (by simp [h])
    · exact hao g0 (by simp [hg0])
  · rw [rb_iff] at hrb ⊢
    intro j g' hg' i hi
    by_cases hj : j < pre.length
    · rw [List.getElem?_append_left hj] at hg'
      exact hrb j g' (by rw [List.getElem?_append_left hj]; exact hg') i hi
    · rw [List.getElem?_append_right (by omega), List.getElem?_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.mp hg'
      have hmem : g0 ∈ post := List.mem_of_getElem? hg0
      have horig : (pre ++ g :: post)[j + 1]? = some g0 := by
        rw [List.getElem?_append_right (by omega)]
        have e : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        rw [e, List.getElem?_cons_succ]
        exact hg0
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
      have hlt := hrb (j + 1) g0 horig a ha
      have hne : a ≠ n + pre.length := fun e => hno g0 hmem (e ▸ ha)
      unfold rn
      split <;> omega
  · intro g' hg'
    simp only [List.mem_append, List.mem_map] at hg'
    rcases hg' with h | ⟨g0, hg0, rfl⟩
    · exact h2 g' (by simp [h])
    · have := h2 g0 (by simp [hg0])
      simpa [ren] using this

theorem del_exists (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ)
    (h : IsAO2 n ⟨pre ++ g :: post, out⟩)
    (hno : ∀ h ∈ post, (n + pre.length) ∉ h.inputs) (hout : out ≠ n + pre.length) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ x : Fin n → Bool, circuitFun n D x = circuitFun n ⟨pre ++ g :: post, out⟩ x) ∧
      D.size < (pre ++ g :: post).length := by
  refine ⟨⟨pre ++ post.map (ren (n + pre.length)), rn (n + pre.length) out⟩,
    del_ao2 n pre g post out _ h hno, ?_, ?_⟩
  · intro x
    unfold circuitFun
    exact del_fun n pre g post out (List.ofFn x) (by simp) hno hout
  · simp [Circuit.size]

theorem unread_input_false {N : ℕ} (E : Finset (Fin N × Fin N)) (s : Equiv.Perm (Fin N))
    (C : Circuit)
    (hF : ∀ x : Fin (N + N) → Bool, circuitFun (N + N) C x =
      decide (∃ (p : Fin N) (l : Fin N), (p, l) ∈ E ∧ x (Fin.castAdd N p) = true ∧
        x (Fin.natAdd N l) = true))
    (hm : ∀ p : Fin N, (p, s p) ∈ E) (p : Fin N) (v : Fin (N + N))
    (hv : v = Fin.castAdd N p ∨ v = Fin.natAdd N (s p))
    (hno : ∀ g ∈ C.gates, v.val ∉ g.inputs) (hout : C.output ≠ v.val) : False := by
  have ne1 : ∀ (a b : Fin N), Fin.castAdd N a ≠ Fin.natAdd N b := by
    intro a b h
    have h' := congrArg Fin.val h
    have ha := a.isLt
    simp at h'
    omega
  have h1 : circuitFun (N + N) C
      (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N (s p))) = true := by
    rw [hF]
    simp only [decide_eq_true_eq]
    exact ⟨p, s p, hm p, by simp, by simp⟩
  have h2 : circuitFun (N + N) C
      (fun i => decide (i ≠ v) && decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N (s p))) =
        false := by
    rw [hF]
    simp only [decide_eq_false_iff_not]
    rintro ⟨p', l', -, hp', hl'⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp' hl'
    rcases hp'.2 with e | e
    · rcases hl'.2 with e' | e'
      · exact ne1 _ _ e'.symm
      · rcases hv with rfl | rfl
        · exact hp'.1 e
        · exact hl'.1 e'
    · exact ne1 _ _ e
  have h3 : circuitFun (N + N) C
      (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N (s p))) =
      circuitFun (N + N) C
      (fun i => decide (i ≠ v) && decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N (s p))) := by
    unfold circuitFun Circuit.eval
    rw [wires_eq, wires_eq]
    apply fold_ind v.val C.gates _ _ hno (by simp) ?_ C.output hout
    intro i hi
    by_cases h : i < N + N
    · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
      simp only [List.getElem_ofFn]
      have hne : (⟨i, h⟩ : Fin (N + N)) ≠ v := fun e => hi (congrArg Fin.val e)
      simp [hne]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  rw [h1, h2] at h3
  exact Bool.noConfusion h3

theorem step_main {N : ℕ} (E : Finset (Fin N × Fin N)) (s : Equiv.Perm (Fin N))
    (hE : N < E.card) (hm : ∀ p : Fin N, (p, s p) ∈ E) (C : Circuit)
    (hC : IsAO2 (N + N) C)
    (hF : ∀ x : Fin (N + N) → Bool, circuitFun (N + N) C x =
      decide (∃ (p : Fin N) (l : Fin N), (p, l) ∈ E ∧ x (Fin.castAdd N p) = true ∧
        x (Fin.natAdd N l) = true)) :
    (C.output + 1 = N + N + C.size ∧
      (List.flatMap Gate.inputs C.gates).toFinset = Finset.range (N + N + C.size - 1)) ∨
    ∃ D : Circuit, IsAO2 (N + N) D ∧
      (∀ x : Fin (N + N) → Bool, circuitFun (N + N) D x =
        decide (∃ (p : Fin N) (l : Fin N), (p, l) ∈ E ∧ x (Fin.castAdd N p) = true ∧
          x (Fin.natAdd N l) = true)) ∧ D.size < C.size := by
  obtain ⟨⟨p0, _⟩, _⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
  obtain ⟨gs, out⟩ := C
  simp only [Circuit.size]
  have split : ∀ j, j < gs.length → ∃ pre g post, gs = pre ++ g :: post ∧ pre.length = j := by
    intro j hj
    refine ⟨gs.take j, gs[j], gs.drop (j + 1), ?_, ?_⟩
    · rw [List.getElem_cons_drop]
      exact (List.take_append_drop j gs).symm
    · simp
      omega
  by_cases hs : gs.length = 0
  · exfalso
    have hgs : gs = [] := List.eq_nil_of_length_eq_zero hs
    subst hgs
    by_cases ho : out = (Fin.castAdd N p0).val
    · refine unread_input_false E s ⟨[], out⟩ hF hm p0 (Fin.natAdd N (s p0)) (Or.inr rfl)
        (by simp) ?_
      have := p0.isLt
      simp at ho ⊢
      omega
    · exact unread_input_false E s ⟨[], out⟩ hF hm p0 (Fin.castAdd N p0) (Or.inl rfl)
        (by simp) ho
  by_cases hout : out = N + N + gs.length - 1
  · by_cases hall : ∀ w < N + N + gs.length - 1, ∃ g ∈ gs, w ∈ g.inputs
    · left
      refine ⟨by omega, ?_⟩
      ext w
      simp only [List.mem_toFinset, List.mem_flatMap, Finset.mem_range]
      constructor
      · rintro ⟨g, hg, hw⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        have := (rb_iff (N + N) gs out).mp hC.2.1 j gs[j] (List.getElem?_eq_getElem hj) w hw
        omega
      · exact hall w
    · right
      push_neg at hall
      obtain ⟨w, hw, hno⟩ := hall
      by_cases hwn : w < N + N
      · exfalso
        by_cases hwN : w < N
        · exact unread_input_false E s ⟨gs, out⟩ hF hm ⟨w, hwN⟩ ⟨w, hwn⟩
            (Or.inl (Fin.ext rfl)) hno (by simp; omega)
        · exact unread_input_false E s ⟨gs, out⟩ hF hm (s.symm ⟨w - N, by omega⟩) ⟨w, hwn⟩
            (Or.inr (Fin.ext (by simp; omega))) hno (by simp; omega)
      · obtain ⟨pre, g, post, rfl, hlen⟩ := split (w - (N + N)) (by omega)
        have hw' : w = N + N + pre.length := by omega
        subst hw'
        obtain ⟨D, hD, hDF, hDs⟩ := del_exists (N + N) pre g post out hC
          (fun h hh => hno h (by simp [hh])) (by simp at hout hw; omega)
        exact ⟨D, hD, fun x => (hDF x).trans (hF x), hDs⟩
  · right
    obtain ⟨pre, g, post, rfl, hlen⟩ := split (gs.length - 1) (by omega)
    have hpost : post = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_append, List.length_cons] at hlen
      omega
    subst hpost
    obtain ⟨D, hD, hDF, hDs⟩ := del_exists (N + N) pre g [] out hC
      (by simp) (by simp at hout; omega)
    exact ⟨D, hD, fun x => (hDF x).trans (hF x), hDs⟩

theorem final {N : ℕ} (E : Finset (Fin N × Fin N)) (s : Equiv.Perm (Fin N))
    (hE : N < E.card) (hm : ∀ p : Fin N, (p, s p) ∈ E) :
    ∀ (k : ℕ) (C : Circuit), C.size = k → IsAO2 (N + N) C →
      (∀ x : Fin (N + N) → Bool, circuitFun (N + N) C x =
        decide (∃ (p : Fin N) (l : Fin N), (p, l) ∈ E ∧ x (Fin.castAdd N p) = true ∧
          x (Fin.natAdd N l) = true)) →
      ∃ D : Circuit, IsAO2 (N + N) D ∧
        (∀ x : Fin (N + N) → Bool, circuitFun (N + N) D x =
          decide (∃ (p : Fin N) (l : Fin N), (p, l) ∈ E ∧ x (Fin.castAdd N p) = true ∧
            x (Fin.natAdd N l) = true)) ∧
        D.size ≤ C.size ∧ D.output + 1 = N + N + D.size ∧
        (List.flatMap Gate.inputs D.gates).toFinset = Finset.range (N + N + D.size - 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hk hC hF
    rcases step_main E s hE hm C hC hF with hclean | ⟨D, hD, hDF, hlt⟩
    · exact ⟨C, hC, hF, le_refl _, hclean.1, hclean.2⟩
    · obtain ⟨D', h1, h2, h3, h4, h5⟩ := ih D.size (by omega) D rfl hD hDF
      exact ⟨D', h1, h2, by omega, h4, h5⟩

end PEqualNP.Outside.L_meta_4821

theorem PEqualNP.Outside.L_meta_4821 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x6 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 x6 = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x1), (x7, x8) ∈ x2 ∧ x6 (Fin.castAdd x1 x7) = Bool.true ∧ x6 (Fin.natAdd x1 x8) = Bool.true);   x1 < x2.card → (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → x5 x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x10 ∧ x5 x10 ∧ x10.size ≤ x4.size ∧ x10.output + (1 : ℕ) = x1 + x1 + x10.size ∧ (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x10.gates).toFinset = Finset.range (x1 + x1 + x10.size - (1 : ℕ)) := by
  intro N E s C P hE hm hC hF
  exact PEqualNP.Outside.L_meta_4821.final E s hE hm C.size C rfl hC hF

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_214_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = w ++ _
    rw [ht]
    simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]
  simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def andCount (gs : List Gate) : Nat := (gs.map (fun g => isAnd g.op)).count true

theorem andCount_cons (g : Gate) (gs : List Gate) :
    andCount (g :: gs) = (if isAnd g.op then 1 else 0) + andCount gs := by
  unfold andCount
  simp only [List.map_cons]
  cases h : isAnd g.op <;> simp [h, Nat.add_comm]

theorem andCount_append (gs gs' : List Gate) :
    andCount (gs ++ gs') = andCount gs + andCount gs' := by
  simp [andCount, List.map_append, List.count_append]

theorem andCount_or_nil : andCount [⟨GateOp.or, []⟩] = 0 := by
  rfl

theorem andCount_and_nil : andCount [⟨GateOp.and, []⟩] = 1 := by
  rfl

def WF (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem WF_append {gs gs' : List Gate} (h1 : WF gs) (h2 : WF gs') : WF (gs ++ gs') := by
  intro g hg
  simp only [List.mem_append] at hg
  rcases hg with hg | hg
  · exact h1 g hg
  · exact h2 g hg

def Bld (n a : Nat) (F : (Fin n → Bool) → Bool) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : Nat), WF gs ∧ andCount gs ≤ a ∧
    out < m + gs.length ∧
    ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_congr {n a : Nat} {F H : (Fin n → Bool) → Bool}
    (h : ∀ x, F x = H x) (hF : Bld n a F) : Bld n a H := by
  intro m hm
  obtain ⟨gs, out, wf, hc, ho, ev⟩ := hF m hm
  refine ⟨gs, out, wf, hc, ho, ?_⟩
  intro w hw
  rw [ev w hw, h]

theorem bld_var (n : Nat) (i : Fin n) : Bld n 0 (fun x => x i) := by
  intro m hm
  refine ⟨[], i.1, by simp [WF], by simp [andCount], lt_of_lt_of_le i.2 hm, ?_⟩
  intro w hw
  simp [wiresFrom, List.getD_eq_getElem?_getD]

theorem bld_false (n : Nat) : Bld n 0 (fun _ : Fin n → Bool => false) := by
  intro m hm
  refine ⟨[⟨GateOp.or, []⟩], m, ?_, by simpa [andCount_or_nil], by simp, ?_⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    simp [WF, GateOp.eval]
  · intro w hw
    simp [wiresFrom, GateOp.eval, List.getD_eq_getElem?_getD, hw]

theorem bld_bin {n a b d : Nat} (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (c : Bool → Bool → Bool)
    (hc : ∀ x y, op.eval [x, y] = c x y) (hd : andCount [⟨op, []⟩] ≤ d)
    {F H : (Fin n → Bool) → Bool} (hF : Bld n a F) (hH : Bld n b H) :
    Bld n (a + b + d) (fun x => c (F x) (H x)) := by
  intro m hm
  obtain ⟨gs1, o1, wf1, hc1, ho1, ev1⟩ := hF m hm
  obtain ⟨gs2, o2, wf2, hc2, ho2, ev2⟩ := hH (m + gs1.length) (Nat.le_trans hm (Nat.le_add_right m gs1.length))
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · apply WF_append (WF_append wf1 wf2)
    intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    simp [hop]
  · rw [andCount_append (gs1 ++ gs2) [⟨op, [o1, o2]⟩], andCount_append]
    exact Nat.add_le_add (Nat.add_le_add hc1 hc2) hd
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.lt_succ_self (m + gs1.length + gs2.length)
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    change (u ++ [op.eval ([o1, o2].map fun i => u.getD i false)]).getD
        (m + gs1.length + gs2.length) false = c (F (fun i => w.getD i false)) (H (fun i => w.getD i false))
    rw [← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by simpa [lv] using ho1), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom gs1 w i (by rw [hw]; exact lt_of_lt_of_le i.2 hm)]
    rw [e1, e2]

theorem bld_or {n a b : Nat} {F H : (Fin n → Bool) → Bool}
    (hF : Bld n a F) (hH : Bld n b H) : Bld n (a + b) (fun x => F x || H x) := by
  have h := bld_bin GateOp.or (Or.inr rfl) (fun x y => x || y)
    (by intro x y; simp [GateOp.eval]) (by rw [andCount_or_nil]) hF hH
  rw [Nat.add_zero] at h
  exact h

theorem bld_and {n a b : Nat} {F H : (Fin n → Bool) → Bool}
    (hF : Bld n a F) (hH : Bld n b H) : Bld n (a + b + 1) (fun x => F x && H x) := by
  simpa using bld_bin GateOp.and (Or.inl rfl) (fun x y => x && y)
    (by intro x y; simp [GateOp.eval]) (by rw [andCount_and_nil]) hF hH

theorem bld_exists (n : Nat) (s : Finset (Fin n)) :
    Bld n 0 (fun x => decide (∃ u ∈ s, x u = true)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine bld_congr (fun x => ?_) (bld_false n)
      simp
  | insert u s hu ih =>
      have h := bld_or (bld_var n u) ih
      refine bld_congr (fun x => ?_) h
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
      constructor
      · rintro (hx | ⟨v, hv, hx⟩)
        · exact ⟨u, Or.inl rfl, hx⟩
        · exact ⟨v, Or.inr hv, hx⟩
      · rintro ⟨v, hv, hx⟩
        rcases hv with rfl | hv
        · exact Or.inl hx
        · exact Or.inr ⟨v, hv, hx⟩

open Classical in
theorem bld_term (n : Nat) (G : SimpleGraph (Fin n)) (t : Fin n) :
    Bld n 1 (fun x => x t && decide (∃ u ∈ Finset.univ.filter (fun u => G.Adj t u), x u = true)) := by
  have h := bld_and (bld_var n t) (bld_exists n (Finset.univ.filter (fun u => G.Adj t u)))
  simpa using h

open Classical in
theorem bld_star (n : Nat) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) :
    Bld n T.card (fun x => decide (∃ t ∈ T,
      x t = true ∧ ∃ u ∈ Finset.univ.filter (fun u => G.Adj t u), x u = true)) := by
  induction T using Finset.induction_on with
  | empty =>
      refine bld_congr (fun x => ?_) (bld_false n)
      simp
  | insert t T ht ih =>
      have h := bld_or (bld_term n G t) ih
      have h' : Bld n (1 + T.card) (fun x =>
          (x t && decide (∃ u ∈ Finset.univ.filter (fun u => G.Adj t u), x u = true)) ||
            decide (∃ v ∈ T, x v = true ∧
              ∃ u ∈ Finset.univ.filter (fun u => G.Adj v u), x u = true)) := by
        simpa using h
      have h'' : Bld n (1 + T.card) (fun x => decide (∃ t' ∈ insert t T,
          x t' = true ∧ ∃ u ∈ Finset.univ.filter (fun u => G.Adj t' u), x u = true)) := by
        refine bld_congr (fun x => ?_) h'
        by_cases hxt : x t = true <;>
        by_cases ha : ∃ u ∈ Finset.univ.filter (fun u => G.Adj t u), x u = true <;>
        by_cases hb : ∃ v ∈ T, x v = true ∧
            ∃ u ∈ Finset.univ.filter (fun u => G.Adj v u), x u = true <;>
          simp [hxt, ha, hb, Finset.mem_insert]
      rw [Finset.card_insert_of_notMem ht]
      simpa [Nat.add_comm] using h''

theorem exists_and_finset (gs : List Gate) :
    ∃ A : Finset Nat, A.card ≤ andCount gs ∧
      ∀ j g, gs[j]? = some g → g.op = GateOp.and → j ∈ A := by
  classical
  induction gs with
  | nil =>
      refine ⟨∅, by simp [andCount], ?_⟩
      intro j g hj
      simp at hj
  | cons g gs ih =>
      obtain ⟨A, hAc, hA⟩ := ih
      by_cases hg : isAnd g.op = true
      · refine ⟨insert 0 (A.image Nat.succ), ?_, ?_⟩
        · calc
            (insert 0 (A.image Nat.succ)).card = (A.image Nat.succ).card + 1 :=
              Finset.card_insert_of_notMem (by simp)
            _ ≤ A.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
            _ ≤ andCount gs + 1 := Nat.add_le_add_right hAc 1
            _ = andCount (g :: gs) := by rw [andCount_cons]; simp [hg, Nat.add_comm]
        · intro j g' hgate hjand
          cases j with
          | zero =>
              simp
          | succ j =>
              simp at hgate
              exact Finset.mem_insert_of_mem
                (Finset.mem_image.mpr ⟨j, hA j g' hgate hjand, rfl⟩)
      · refine ⟨A.image Nat.succ, ?_, ?_⟩
        · calc
            (A.image Nat.succ).card ≤ A.card := Finset.card_image_le
            _ ≤ andCount gs := hAc
            _ = andCount (g :: gs) := by rw [andCount_cons]; simp [hg]
        · intro j g' hgate hjand
          cases j with
          | zero =>
              simp at hgate
              subst g'
              exfalso
              have hi : isAnd g.op = true := by rw [hjand]; rfl
              exact hg hi
          | succ j =>
              simp at hgate
              exact Finset.mem_image.mpr ⟨j, hA j g' hgate hjand, rfl⟩

open Classical in
theorem star (n : Nat) (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (hcover : ∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      (∃ A : Finset Nat, A.card ≤ T.card ∧
        ∀ (j : Nat) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) ∧
      ∀ x : Fin n → Bool,
        (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
  obtain ⟨gs, out, wf, hc, ho, ev⟩ := bld_star n G T n le_rfl
  obtain ⟨A, hAc, hA⟩ := exists_and_finset gs
  let C : Circuit := ⟨gs, out⟩
  refine ⟨C, ?_, ⟨A, le_trans hAc hc, hA⟩, ?_⟩
  · intro g hg
    simpa [PEqualNP.MetaComplexity.Monotone2] using wf g hg
  · intro x
    have e : C.eval (List.ofFn x) =
        decide (∃ t ∈ T, x t = true ∧
          ∃ u ∈ Finset.univ.filter (fun u => G.Adj t u), x u = true) := by
      rw [show C.eval (List.ofFn x) = (wiresFrom gs (List.ofFn x)).getD out false from rfl]
      simpa using ev (List.ofFn x) (by simp)
    rw [e, decide_eq_true_eq]
    constructor
    · rintro ⟨t, ht, hxt, u, hu, hxu⟩
      have hadj : G.Adj t u := by simpa using hu
      exact ⟨t, u, hadj, hxt, hxu⟩
    · rintro ⟨u, v, hadj, hxu, hxv⟩
      rcases hcover u v hadj with huT | hvT
      · refine ⟨u, huT, hxu, v, ?_, hxv⟩
        simp [hadj]
      · refine ⟨v, hvT, hxv, u, ?_, hxu⟩
        simp [hadj.symm]

end PEqualNP.Outside.L_meta_214_aux

theorem PEqualNP.Outside.L_meta_214 :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)),
    (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      (∃ A : Finset ℕ, A.card ≤ T.card ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧
      ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
  intro n G T hcover
  exact PEqualNP.Outside.L_meta_214_aux.star n G T hcover

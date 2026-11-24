import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4838_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wf_append (pre post : List Gate) (w : List Bool) :
    wf (pre ++ post) w = wf post (wf pre w) := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

def sk (N i : ℕ) : ℕ := if i < N then i else i - 1

def rn (N a i : ℕ) : ℕ := if i < N then i else if i = N then a else i - 1

theorem getD_mid (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) :
    (A ++ b :: E).getD N false = b := by
  subst hN
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl A.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem getD_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (i : ℕ) (hi : i ≠ N) :
    (A ++ E).getD (sk N i) false = (A ++ b :: E).getD i false := by
  subst hN
  unfold sk
  by_cases h : i < A.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    have h1 : A.length ≤ i - 1 := by omega
    have h2 : A.length ≤ i := by omega
    have h3 : i - A.length = (i - 1 - A.length) + 1 := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
      List.getElem?_append_right h2]
    rw [h3, List.getElem?_cons_succ]

theorem getD_rn (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (i : ℕ) :
    (A ++ E).getD (rn N a i) false = (A ++ b :: E).getD i false := by
  by_cases h : i = N
  · have e : rn N a N = a := by
      unfold rn
      rw [if_neg (lt_irrefl _), if_pos rfl]
    have ha' : a < A.length := by omega
    rw [h, getD_mid A E b N hN, e, ← hb]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha']
  · have e : rn N a i = sk N i := by
      unfold rn sk
      by_cases h' : i < N
      · rw [if_pos h', if_pos h']
      · rw [if_neg h', if_neg h, if_neg h']
    rw [e]
    exact getD_sk A E b N hN i h

theorem surg (T : Gate → Gate) (A : List Bool) (b : Bool) :
    ∀ (post : List Gate) (E : List Bool),
      (∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (A ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (A ++ E').getD i false)) →
      ∃ E2 : List Bool, wf post (A ++ b :: E) = A ++ b :: E2 ∧
        wf (post.map T) (A ++ E) = A ++ E2 := by
  intro post
  induction post with
  | nil => intro E _; exact ⟨E, rfl, rfl⟩
  | cons h post ih =>
    intro E hT
    have e := hT h (List.mem_cons.mpr (Or.inl rfl)) E
    obtain ⟨E2, h1, h2⟩ :=
      ih (E ++ [h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)])
        (fun h' hh' E' => hT h' (List.mem_cons.mpr (Or.inr hh')) E')
    refine ⟨E2, ?_, ?_⟩
    · rw [wf_cons, List.append_assoc, List.cons_append]
      exact h1
    · rw [List.map_cons, wf_cons, ← e, List.append_assoc]
      exact h2

def Tc (N a : ℕ) (h : Gate) : Gate := ⟨h.op, h.inputs.map (rn N a)⟩

theorem sound_c (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (h : Gate) :
    h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
      = (Tc N a h).op.eval ((Tc N a h).inputs.map fun i => (A ++ E).getD i false) := by
  have e : (h.inputs.map (rn N a)).map (fun i => (A ++ E).getD i false)
      = h.inputs.map fun i => (A ++ b :: E).getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact getD_rn A E b N hN a ha hb i
  show h.op.eval _ = h.op.eval ((h.inputs.map (rn N a)).map fun i => (A ++ E).getD i false)
  rw [e]

theorem Tc_legal (N a : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tc N a h).op = GateOp.and ∨ (Tc N a h).op = GateOp.or) ∧ (Tc N a h).inputs.length ≤ 2 := by
  refine ⟨hl.1, ?_⟩
  show (h.inputs.map (rn N a)).length ≤ 2
  rw [List.length_map]
  exact hl.2

theorem Tc_rb (N a : ℕ) (ha : a < N) (h : Gate) (M : ℕ) (hM : N ≤ M)
    (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tc N a h).inputs, i < M := by
  intro i hi'
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
  have := hi j hj
  unfold rn
  split_ifs <;> omega

theorem asm (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : C.gates = pre ++ g :: post) (T : Gate → Gate) (o' : ℕ)
    (hmono : Monotone2 C) (hrb : ReadsBack n C)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, n + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M) :
    Monotone2 ⟨pre ++ post.map T, o'⟩ ∧ ReadsBack n ⟨pre ++ post.map T, o'⟩ ∧
      Circuit.size ⟨pre ++ post.map T, o'⟩ + 1 = C.size := by
  have legal := legal_of C hmono
  refine ⟨?_, ?_, ?_⟩
  · intro g' hg'
    have hg2 : g' ∈ pre ∨ g' ∈ post.map T := List.mem_append.mp hg'
    rcases hg2 with hp | hp
    · exact hmono g' (by rw [hC]; exact List.mem_append.mpr (Or.inl hp))
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      have hl := hTm h (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh)))))
      refine ⟨?_, hl.2⟩
      rcases hl.1 with e | e
      · exact Or.inl e
      · exact Or.inr e
  · intro j hj i hi
    have hj' : j < pre.length + post.length := by simpa using hj
    by_cases hjp : j < pre.length
    · have e : gateAt ⟨pre ++ post.map T, o'⟩ j = gateAt C j := by
        simp only [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
      rw [e] at hi
      exact hrb j (by rw [hC]; simp only [List.length_append, List.length_cons]; omega) i hi
    · have hjk : j - pre.length < post.length := by omega
      have e1 : gateAt ⟨pre ++ post.map T, o'⟩ j = T (post[j - pre.length]) := by
        simp [gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_of_not_lt hjp), hjk]
      have e2 : gateAt C (j + 1) = post[j - pre.length] := by
        have h3 : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ j + 1 by omega), h3, hjk]
      rw [e1] at hi
      have hmem : post[j - pre.length] ∈ C.gates := by
        rw [hC]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.getElem_mem hjk))))
      have hold : ∀ i ∈ (post[j - pre.length]).inputs, i < (n + j) + 1 := by
        intro i hi2
        have := hrb (j + 1) (by rw [hC]; simp only [List.length_append, List.length_cons]; omega)
          i (by rw [e2]; exact hi2)
        omega
      exact hTr _ (legal _ hmem) (n + j) (by omega) hold i hi
  · show (pre ++ post.map T).length + 1 = C.gates.length
    rw [hC]
    simp only [List.length_append, List.length_map, List.length_cons]
    omega

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (wf gs W1).getD i false = true → (wf gs W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; exact H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [wf_cons, wf_cons]
    apply ih _ _ (by simp [hl]) (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [getD_snoc, hl]
    split_ifs
    · rcases hop g (List.mem_cons.mpr (Or.inl rfl)) with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem wf_ext : ∀ (gs : List Gate) (w : List Bool), ∃ E : List Bool, wf gs w = w ++ E := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], (List.append_nil w).symm⟩
  | cons g gs ih =>
    intro w
    obtain ⟨E, hE⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: E, ?_⟩
    rw [wf_cons, hE, List.append_assoc]
    rfl

theorem old_wires (pre post : List Gate) (g : Gate) (x : List Bool) :
    ∃ E : List Bool, wf (pre ++ g :: post) x
      = wf pre x ++ g.op.eval (g.inputs.map fun i => (wf pre x).getD i false) :: E := by
  obtain ⟨E, hE⟩ := wf_ext post
    (wf pre x ++ [g.op.eval (g.inputs.map fun i => (wf pre x).getD i false)])
  refine ⟨E, ?_⟩
  rw [wf_append, wf_cons, hE, List.append_assoc]
  rfl

theorem getD_left (A L : List Bool) (a : ℕ) (ha : a < A.length) :
    (A ++ L).getD a false = A.getD a false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha]

theorem new_eval (pre post : List Gate) (N a o : ℕ) (x : List Bool)
    (hlen : (wf pre x).length = N) (ha : a < N) :
    (wf (pre ++ post.map (Tc N a)) x).getD (rn N a o) false
      = (wf post (wf pre x ++ [(wf pre x).getD a false])).getD o false := by
  obtain ⟨E2, h1, h2⟩ := surg (Tc N a) (wf pre x) ((wf pre x).getD a false) post []
    (fun h _ E' => sound_c (wf pre x) E' _ N hlen a ha rfl h)
  rw [List.append_nil] at h2
  have h1' : wf post (wf pre x ++ [(wf pre x).getD a false])
      = wf pre x ++ (wf pre x).getD a false :: E2 := h1
  rw [wf_append, h2, h1']
  exact getD_rn (wf pre x) E2 _ N hlen a ha rfl o

theorem swap_le (post : List Gate) (hop : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (A : List Bool) (u v : Bool) (huv : u = true → v = true) (o : ℕ)
    (h : (wf post (A ++ [u])).getD o false = true) :
    (wf post (A ++ [v])).getD o false = true := by
  refine mono post (A ++ [u]) (A ++ [v]) (by simp) hop ?_ o h
  intro i
  simp only [getD_snoc]
  split_ifs
  · exact huv
  · exact id

theorem core (n : ℕ) (C : Circuit) (pre post : List Gate) (gj : Gate)
    (hC : C.gates = pre ++ gj :: post) (hmono : Monotone2 C) (hrb : ReadsBack n C)
    (t w a : ℕ) (ht : t < n + pre.length) (haN : a < n + pre.length)
    (hw : w < n + C.size)
    (hyp : ∀ x : List Bool, x.length = n →
      ((C.wires x).getD (n + pre.length) false = true → (C.wires x).getD a false = true) ∧
      ((C.wires x).getD t false = true →
        (C.wires x).getD (n + pre.length) false = (C.wires x).getD a false)) :
    ∃ (C' : Circuit) (w' : ℕ), Monotone2 C' ∧ ReadsBack n C' ∧ C'.size + 1 = C.size ∧
      t < n + C'.size ∧ w' < n + C'.size ∧ ∀ x : List Bool, x.length = n →
        (C'.wires x).getD t false = (C.wires x).getD t false ∧
        ((C.wires x).getD w false = true → (C'.wires x).getD w' false = true) ∧
        ((C.wires x).getD t false = true →
          (C'.wires x).getD w' false = (C.wires x).getD w false) := by
  obtain ⟨m1, m2, m3⟩ := asm n C pre post gj hC (Tc (n + pre.length) a) C.output hmono hrb
    (fun h hl => Tc_legal _ _ h hl) (fun h _ M hM hi => Tc_rb _ _ haN h M hM hi)
  have hsz : C.size = pre.length + post.length + 1 := by
    show C.gates.length = _
    rw [hC]
    simp only [List.length_append, List.length_cons]
    omega
  have hsz' : Circuit.size ⟨pre ++ post.map (Tc (n + pre.length) a), C.output⟩
      = pre.length + post.length := by
    show (pre ++ post.map (Tc (n + pre.length) a)).length = _
    simp only [List.length_append, List.length_map]
  refine ⟨⟨pre ++ post.map (Tc (n + pre.length) a), C.output⟩, rn (n + pre.length) a w,
    m1, m2, m3, ?_, ?_, ?_⟩
  · rw [hsz']
    omega
  · rw [hsz']
    unfold rn
    split_ifs <;> omega
  intro x hx
  have hlen : (wf pre x).length = n + pre.length := by rw [wf_len, hx]
  have hpostop : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := fun h hh =>
    (legal_of C hmono h (by
      rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh))))).1
  obtain ⟨E, hE⟩ := old_wires pre post gj x
  have hwa : (C.wires x).getD a false = (wf pre x).getD a false := by
    show (wf C.gates x).getD a false = _
    rw [hC, hE]
    exact getD_left _ _ a (by rw [hlen]; exact haN)
  have hwt : (C.wires x).getD t false = (wf pre x).getD t false := by
    show (wf C.gates x).getD t false = _
    rw [hC, hE]
    exact getD_left _ _ t (by rw [hlen]; exact ht)
  have hwN : (C.wires x).getD (n + pre.length) false
      = gj.op.eval (gj.inputs.map fun i => (wf pre x).getD i false) := by
    show (wf C.gates x).getD (n + pre.length) false = _
    rw [hC, hE]
    exact getD_mid _ _ _ _ hlen
  have hold : (C.wires x).getD w false = (wf post (wf pre x ++
      [gj.op.eval (gj.inputs.map fun i => (wf pre x).getD i false)])).getD w false := by
    show (wf C.gates x).getD w false = _
    rw [hC, wf_append, wf_cons]
  have hnew : (Circuit.wires ⟨pre ++ post.map (Tc (n + pre.length) a), C.output⟩ x).getD
      (rn (n + pre.length) a w) false
        = (wf post (wf pre x ++ [(wf pre x).getD a false])).getD w false :=
    new_eval pre post _ a w x hlen haN
  have hnewt : (Circuit.wires ⟨pre ++ post.map (Tc (n + pre.length) a), C.output⟩ x).getD
      t false = (wf pre x).getD t false := by
    obtain ⟨E3, hE3⟩ := wf_ext (post.map (Tc (n + pre.length) a)) (wf pre x)
    show (wf (pre ++ post.map (Tc (n + pre.length) a)) x).getD t false = _
    rw [wf_append, hE3]
    exact getD_left _ _ t (by rw [hlen]; exact ht)
  obtain ⟨hy1, hy2⟩ := hyp x hx
  rw [hwN, hwa] at hy1
  rw [hwN, hwa, hwt] at hy2
  rw [hnew, hnewt, hold, hwt]
  refine ⟨rfl, fun h => swap_le post hpostop _ _ _ hy1 w h, fun h => ?_⟩
  rw [hy2 h]

end PEqualNP.Outside.L_meta_4838_aux

theorem PEqualNP.Outside.L_meta_4838 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 x6 : ℕ), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x3 < x5 → x1 ≤ x5 → x5 < x1 + x2.size → x4 < x1 + x2.size → x6 < x5 → (∀ (x14 : List Bool), x14.length = x1 → ((x2.wires x14).getD x5 Bool.false = Bool.true → (x2.wires x14).getD x6 Bool.false = Bool.true) ∧ ((x2.wires x14).getD x3 Bool.false = Bool.true → (x2.wires x14).getD x5 Bool.false = (x2.wires x14).getD x6 Bool.false)) → ∃ (x15 : PEqualNP.CircuitLowerBounds.Circuit) (x16 : ℕ), PEqualNP.MetaComplexity.Monotone2 x15 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x15 ∧ x15.size + (1 : ℕ) = x2.size ∧ x3 < x1 + x15.size ∧ x16 < x1 + x15.size ∧ ∀ (x17 : List Bool), x17.length = x1 → (x15.wires x17).getD x3 Bool.false = (x2.wires x17).getD x3 Bool.false ∧ ((x2.wires x17).getD x4 Bool.false = Bool.true → (x15.wires x17).getD x16 Bool.false = Bool.true) ∧ ((x2.wires x17).getD x3 Bool.false = Bool.true → (x15.wires x17).getD x16 Bool.false = (x2.wires x17).getD x4 Bool.false) := by
  intro n C t w e p hmono hrb hte hne hes hws hpe hyp
  have hsz : C.size = C.gates.length := rfl
  have hm : e - n < C.gates.length := by omega
  obtain ⟨pre, post, gj, hC, hpl, _⟩ :=
    PEqualNP.Outside.L_meta_4838_aux.split_gates C.gates (e - n) hm
  have he : e = n + pre.length := by omega
  subst he
  exact PEqualNP.Outside.L_meta_4838_aux.core n C pre post gj hC hmono hrb t w p hte hpe hws hyp

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2642_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

-- One evaluation step of `Circuit.wires`.
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

-- The value of the gate at position `t` of `G` as read in the wires.
theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

-- The wires a gate's value depends on: all inputs, or the head for `NOT`.
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

-- Renaming of wire indices after the wire `p` is deleted, its readers sent to `r`.
def ren (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def renG (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren p r)⟩

-- The gates with gate `t` (wire `p`) deleted and the later gates renamed.
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

theorem fanInTwo_del (G : List Gate) (o : ℕ) (t p r o' : ℕ) (h : FanInTwo ⟨G, o⟩) :
    FanInTwo ⟨del G t p r, o'⟩ := by
  simp only [FanInTwo] at h ⊢
  intro g hg
  simp only [del, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g', hg', rfl⟩
  · exact h g (List.mem_of_mem_take hg)
  · obtain ⟨h1, h2⟩ := h g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [renG] using h2⟩


theorem eraseRedirect_eq_ren (n m p : ℕ) : eraseRedirect n m p = ren (n + m) p := by
  funext i
  simp only [eraseRedirect, ren]
  split_ifs <;> omega

theorem eraseGate_eq_del (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.size) :
    eraseGate n C m p = ⟨del C.gates m (n + m) p, ren (n + m) p C.output⟩ := by
  simp only [eraseGate, Circuit.size] at hm ⊢
  rw [if_pos hm, eraseRedirect_eq_ren]
  rfl

theorem deps_subset (g : Gate) : ∀ i ∈ deps g, i ∈ g.inputs := by
  rcases g with ⟨op, ins⟩
  cases op <;> cases ins <;> simp [deps]

theorem eraseGate_fanInTwo (n : ℕ) (C : Circuit) (m p : ℕ)
    (hm : m < C.size) (hfan : FanInTwo C) : FanInTwo (eraseGate n C m p) := by
  rw [eraseGate_eq_del n C m p hm]
  exact fanInTwo_del C.gates C.output m (n + m) p _ hfan

theorem eraseGate_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.size) :
    (eraseGate n C m p).size + 1 = C.size := by
  rw [eraseGate_eq_del n C m p hm]
  change (del C.gates m (n + m) p).length + 1 = C.gates.length
  rw [del_length _ _ _ _ hm]
  change m < C.gates.length at hm
  omega

theorem eraseGate_eval (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.size)
    (hp : p < n + m ∨ n + C.size ≤ p) (x : Fin n → Bool)
    (h : (C.wires (List.ofFn x)).getD (n + m) false =
          (C.wires (List.ofFn x)).getD p false ∨
      (C.output ≠ n + m ∧ ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs)) :
    (eraseGate n C m p).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  rw [eraseGate_eq_del n C m p hm]
  have hl : (List.ofFn x).length = n := List.length_ofFn
  have hp' : p < (List.ofFn x).length + m ∨
      (List.ofFn x).length + C.gates.length ≤ p := by simpa [Circuit.size] using hp
  have hv : ∀ g ∈ C.gates.drop (m + 1), (List.ofFn x).length + m ∈ deps g →
      (C.gates.foldl step (List.ofFn x)).getD ((List.ofFn x).length + m) false =
      (C.gates.foldl step (List.ofFn x)).getD p false := by
    intro g hg hi
    rcases h with h | h
    · simpa only [hl, wires_eq] using h
    · exact (h.2 g hg (by simpa only [hl] using deps_subset g _ hi)).elim
  have ho : C.output = (List.ofFn x).length + m →
      (C.gates.foldl step (List.ofFn x)).getD ((List.ofFn x).length + m) false =
      (C.gates.foldl step (List.ofFn x)).getD p false := by
    intro he
    rcases h with h | h
    · simpa only [hl, wires_eq] using h
    · exact (h.1 (by simpa only [hl] using he)).elim
  simpa only [hl] using del_eval C.gates C.output (List.ofFn x) m p hm hp' hv ho

def pinWire (u v big i : ℕ) : ℕ := if i = u ∨ i = v then big else i

def pinGate (u v big : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (pinWire u v big)⟩

def pinCircuit (n : ℕ) (u v : Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (pinGate u.val v.val (n + C.size)),
    pinWire u.val v.val (n + C.size) C.output⟩

theorem pinCircuit_size (n : ℕ) (u v : Fin n) (C : Circuit) :
    (pinCircuit n u v C).size = C.size := by
  simp [pinCircuit, Circuit.size]

theorem pinCircuit_fanInTwo (n : ℕ) (u v : Fin n) (C : Circuit) (hf : FanInTwo C) :
    FanInTwo (pinCircuit n u v C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  obtain ⟨h1, h2⟩ := hf g' hg'
  exact ⟨h1, by simpa [pinGate] using h2⟩

theorem pin_step (u v big : ℕ) (w z : List Bool) (g : Gate)
    (hlen : w.length = z.length) (hu : u < w.length) (hv : v < w.length)
    (hbig : w.length + 1 ≤ big)
    (h : ∀ i, w.getD (pinWire u v big i) false = z.getD i false) :
    ∀ i, (step w (pinGate u v big g)).getD (pinWire u v big i) false =
      (step z g).getD i false := by
  have he : (pinGate u v big g).op.eval
      ((pinGate u v big g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => z.getD i false) := by
    simp only [pinGate, List.map_map]
    congr 1
    exact List.map_congr_left (fun i _ => h i)
  intro i
  by_cases hi : i = u ∨ i = v
  · have hil : i < z.length := by rcases hi with rfl | rfl <;> omega
    rw [pinWire, if_pos hi]
    calc
      (step w (pinGate u v big g)).getD big false = false :=
        getD_of_length_le _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)
      _ = z.getD i false := by
        have hi' := h i
        rw [pinWire, if_pos hi, getD_of_length_le _ _ (by omega)] at hi'
        exact hi'
      _ = (step z g).getD i false := (getD_append_lt _ _ _ hil).symm
  · rw [pinWire, if_neg hi]
    by_cases hil : i < w.length
    · rw [show (step w (pinGate u v big g)).getD i false = w.getD i false from
          getD_append_lt _ _ _ hil,
        show (step z g).getD i false = z.getD i false from
          getD_append_lt _ _ _ (by omega)]
      simpa only [pinWire, if_neg hi] using h i
    · by_cases hie : i = w.length
      · subst i
        simp only [step, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right le_rfl,
          List.getElem?_append_right (show z.length ≤ w.length by omega)]
        simpa only [← hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
          List.getD_eq_getElem?_getD] using he
      · rw [getD_of_length_le _ _ (by simp only [step, List.length_append, List.length_singleton]; omega),
          getD_of_length_le _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]

theorem pin_foldl (u v big : ℕ) (G : List Gate) (w z : List Bool)
    (hlen : w.length = z.length) (hu : u < w.length) (hv : v < w.length)
    (hbig : w.length + G.length ≤ big)
    (h : ∀ i, w.getD (pinWire u v big i) false = z.getD i false) :
    ∀ i, ((G.map (pinGate u v big)).foldl step w).getD (pinWire u v big i) false =
      (G.foldl step z).getD i false := by
  induction G generalizing w z with
  | nil => exact h
  | cons g G ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih (step w (pinGate u v big g)) (step z g)
    · simp only [step, List.length_append, List.length_singleton, hlen]
    · simp only [step, List.length_append, List.length_singleton]; omega
    · simp only [step, List.length_append, List.length_singleton]; omega
    · simp only [step, List.length_append, List.length_singleton]
      simp only [List.length_cons] at hbig
      omega
    · exact pin_step u v big w z g hlen hu hv (by
        simp only [List.length_cons] at hbig
        omega) h

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem pinCircuit_eval (n : ℕ) (u v : Fin n) (C : Circuit) (x : Fin n → Bool) :
    (pinCircuit n u v C).eval (List.ofFn x) =
      C.eval (List.ofFn (Function.update (Function.update x u false) v false)) := by
  let y := Function.update (Function.update x u false) v false
  have hi : ∀ i, (List.ofFn x).getD (pinWire u.val v.val (n + C.size) i) false =
      (List.ofFn y).getD i false := by
    intro i
    by_cases hp : i = u.val ∨ i = v.val
    · rw [pinWire, if_pos hp, getD_of_length_le _ _ (by simp)]
      rcases hp with rfl | rfl
      · rw [ofFn_getD y u.val u.isLt]
        simp [y, Function.update_apply]
      · rw [ofFn_getD y v.val v.isLt]
        simp [y]
    · rw [pinWire, if_neg hp]
      by_cases hn : i < n
      · rw [ofFn_getD x i hn, ofFn_getD y i hn]
        have hu : (⟨i, hn⟩ : Fin n) ≠ u := fun e => hp (Or.inl (congrArg Fin.val e))
        have hv : (⟨i, hn⟩ : Fin n) ≠ v := fun e => hp (Or.inr (congrArg Fin.val e))
        simp [y, Function.update_of_ne hu, Function.update_of_ne hv]
      · rw [getD_of_length_le _ _ (by simp; omega), getD_of_length_le _ _ (by simp; omega)]
  have h := pin_foldl u.val v.val (n + C.size) C.gates (List.ofFn x) (List.ofFn y)
    (by simp) (by simpa using u.isLt) (by simpa using v.isLt)
    (by simp [Circuit.size]) hi C.output
  exact h

end PEqualNP.Outside.L_meta_2642_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves PEqualNP.Outside.L_meta_2642_aux in
theorem PEqualNP.Outside.L_meta_2642 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo (x5 (0 : ℕ)) →     (∀ x7 < x2,         ∃ (x9 : ℕ) (x10 : ℕ),           x9 < (x5 x7).size ∧             (x10 < x1 + x9 ∨ x1 + (x5 x7).size ≤ x10) ∧               x5 (x7 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x5 x7) x9 x10 ∧                 ((∀ (x11 : Fin x1 → Bool),                     have x12 : List Bool := (x5 x7).wires (List.ofFn (Function.update (Function.update x11 x3 Bool.false) x4 Bool.false));                     x12.getD (x1 + x9) Bool.false = x12.getD x10 Bool.false) ∨                   (x5 x7).output ≠ x1 + x9 ∧ ∀ x11 ∈ List.drop (x9 + (1 : ℕ)) (x5 x7).gates, x1 + x9 ∉ x11.inputs)) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + x2 = (x5 (0 : ℕ)).size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = (x5 (0 : ℕ)).eval (List.ofFn (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false)) := by
  intro n k u v C hfan hsteps
  have hind : ∀ i : ℕ, i ≤ k → FanInTwo (C i) ∧ (C i).size + i = (C 0).size ∧
      ∀ x : Fin n → Bool,
        (C i).eval (List.ofFn (Function.update (Function.update x u false) v false)) =
          (C 0).eval (List.ofFn (Function.update (Function.update x u false) v false)) := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨hfan, by omega, fun _ => rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨hf, hs, he⟩ := ih (by omega)
      obtain ⟨m, p, hm, hp, hn, hv⟩ := hsteps i (by omega)
      have hf' : FanInTwo (C (i + 1)) := by
        rw [hn]
        exact eraseGate_fanInTwo n (C i) m p hm hf
      have hs' : (C (i + 1)).size + 1 = (C i).size := by
        rw [hn]
        exact eraseGate_size n (C i) m p hm
      refine ⟨hf', by omega, ?_⟩
      intro x
      rw [hn]
      exact (eraseGate_eval n (C i) m p hm hp
        (Function.update (Function.update x u false) v false)
        (hv.elim (fun h => Or.inl (h x)) Or.inr)).trans (he x)
  obtain ⟨hf, hs, he⟩ := hind k le_rfl
  refine ⟨pinCircuit n u v (C k), pinCircuit_fanInTwo n u v (C k) hf, ?_, ?_⟩
  · rwa [pinCircuit_size]
  · intro x
    rw [pinCircuit_eval]
    exact he x

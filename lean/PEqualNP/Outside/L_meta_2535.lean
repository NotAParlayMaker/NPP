import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

namespace PEqualNP.Outside.L_meta_2535_aux

/-- The value a gate writes on the wire list `w`. -/
def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

/-- The wires after running the gates `gs` on the wire list `w`. -/
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [value g w]) w

theorem wires_eq (C : Circuit) (w : List Bool) : C.wires w = run C.gates w := rfl

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [value g w]) := rfl

theorem run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp; omega

theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem getD_out (w : List Bool) {i : ℕ} (h : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ h

/-! ## Erasing a gate -/

/-- Reading the erased list at a renamed index. -/
theorem getD_erase (O : List Bool) {j p r : ℕ} (hj : j < O.length)
    (hp : p < j ∨ O.length ≤ p) (hjp : r = j → O.getD j false = O.getD p false) :
    (O.eraseIdx j).getD (if r = j then p else if j < r then r - 1 else r) false =
      O.getD r false := by
  have hlen : (O.eraseIdx j).length = O.length - 1 := by
    rw [List.length_eraseIdx, if_pos hj]
  by_cases h1 : r = j
  · subst h1
    rw [if_pos rfl, hjp rfl]
    rcases hp with hp | hp
    · simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eraseIdx_of_lt hp]
    · rw [getD_out _ (by omega), getD_out _ hp]
  · rw [if_neg h1]
    by_cases h2 : j < r
    · rw [if_pos h2]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eraseIdx_of_ge (by omega), Nat.sub_add_cancel (by omega)]
    · rw [if_neg h2]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eraseIdx_of_lt (by omega)]

/-- The renamed gate. -/
def ren (j p : ℕ) (h : Gate) : Gate :=
  ⟨h.op, h.inputs.map (fun i => if i = j then p else if j < i then i - 1 else i)⟩

theorem value_ren (O : List Bool) {j p : ℕ} (hj : j < O.length) (hp : p < j ∨ O.length ≤ p)
    (h : Gate) (hjp : j ∈ h.inputs → O.getD j false = O.getD p false) :
    value (ren j p h) (O.eraseIdx j) = value h O := by
  unfold value ren
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro r hr
  exact getD_erase O hj hp (fun e => hjp (e ▸ hr))

/-- The suffix after an erased wire `j`: the renamed suffix on the erased list is the erased
run. -/
theorem run_erase (suf : List Gate) (O : List Bool) {j p : ℕ} (hj : j < O.length)
    (hp : p < j ∨ O.length + suf.length ≤ p)
    (hjp : (∃ h ∈ suf, j ∈ h.inputs) → O.getD j false = O.getD p false) :
    run (suf.map (ren j p)) (O.eraseIdx j) = (run suf O).eraseIdx j := by
  induction suf generalizing O with
  | nil => rfl
  | cons h suf ih =>
    rw [List.map_cons, run_cons, run_cons]
    have hp' : p < j ∨ O.length ≤ p := by
      rcases hp with hp | hp
      · exact Or.inl hp
      · right; simp at hp; omega
    have hv := value_ren O hj hp' h (fun e => hjp ⟨h, List.mem_cons_self, e⟩)
    rw [hv, ← List.eraseIdx_append_of_lt_length hj]
    apply ih
    · simp; omega
    · rcases hp with hp | hp
      · exact Or.inl hp
      · right; simp at hp ⊢; omega
    · intro hex
      have h1 : O.getD j false = O.getD p false :=
        hjp (by obtain ⟨g, hg, hg'⟩ := hex; exact ⟨g, List.mem_cons_of_mem _ hg, hg'⟩)
      rw [List.getD_append _ _ _ _ hj, h1]
      rcases hp with hp | hp
      · rw [List.getD_append _ _ _ _ (by omega)]
      · simp only [List.length_cons] at hp
        rw [getD_out O (by omega), getD_out _ (by simp; omega)]

/-- Erasing gate `m` with redirect `p` keeps the value, when wire `n + m` agrees with wire `p`
wherever it is read. -/
theorem erase_eval (n : ℕ) (C : Circuit) {m p : ℕ} (hm : m < C.gates.length)
    (hp : p < n + m ∨ n + C.gates.length ≤ p) (w : List Bool) (hw : w.length = n)
    (hv : (∃ h ∈ C.gates.drop (m + 1), n + m ∈ h.inputs) ∨ C.output = n + m →
      (C.wires w).getD (n + m) false = (C.wires w).getD p false) :
    (eraseGate n C m p).eval w = C.eval w := by
  unfold eraseGate
  rw [if_pos hm]
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  set pre := C.gates.take m
  set suf := C.gates.drop (m + 1)
  set g := C.gates[m]
  have hpre : pre.length = m := by simp [pre]; omega
  have hsuf : suf.length = C.gates.length - (m + 1) := by simp [suf]
  set u := run pre w with hu
  have hul : u.length = n + m := by rw [hu, run_length, hw, hpre]
  set O := u ++ [value g u] with hO
  have hOl : O.length = n + m + 1 := by simp [O, hul]
  have hfull : C.wires w = run suf O := by
    rw [wires_eq, hsplit, run_append, run_cons]
  have hj : n + m < O.length := by omega
  have hO' : O.eraseIdx (n + m) = u := by
    rw [hO, List.eraseIdx_append_of_length_le (by omega), hul, Nat.sub_self]
    simp
  have hfl : (C.wires w).length = n + C.gates.length := by rw [wires_eq, run_length, hw]
  -- values at `n + m` and `p` are the same in `O` and in the full run
  have hjO : (C.wires w).getD (n + m) false = O.getD (n + m) false := by
    rw [hfull, run_preserves _ _ _ hj]
  have hpO : (C.wires w).getD p false = O.getD p false := by
    rcases hp with hp | hp
    · rw [hfull, run_preserves _ _ _ (by omega)]
    · rw [getD_out _ (by omega), getD_out _ (by omega)]
  have hp2 : p < n + m ∨ O.length + suf.length ≤ p := by
    rcases hp with hp | hp
    · exact Or.inl hp
    · right; omega
  have key : ∀ o, (Circuit.mk (pre ++ suf.map (ren (n + m) p)) o).wires w
      = (run suf O).eraseIdx (n + m) := by
    intro o
    rw [wires_eq, run_append, ← hu, ← hO']
    exact run_erase suf O hj hp2 (fun hex => by rw [← hjO, ← hpO]; exact hv (Or.inl hex))
  have hmap : (fun g : Gate => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate)) =
      ren (n + m) p := by
    funext g; rfl
  rw [hmap]
  unfold Circuit.eval
  rw [key, hfull]
  have hfl' : (run suf O).length = n + C.gates.length := by rw [← hfull, hfl]
  unfold eraseRedirect
  apply getD_erase _ (by omega)
  · rcases hp with hp | hp
    · exact Or.inl hp
    · right; omega
  · intro ho
    rw [← hfull, hv (Or.inr ho)]


/-! ## Reading one more wire -/

theorem getD_snoc (O : List Bool) (v : Bool) (r : ℕ) :
    (O ++ [v]).getD r false =
      if r < O.length then O.getD r false else if r = O.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · exact getD_out _ (by simp; omega)

/-- The wire of gate `m` holds the gate's value on the wires before it. -/
theorem wire_gate (n : ℕ) (C : Circuit) {m : ℕ} (hm : m < C.gates.length) (w : List Bool)
    (hw : w.length = n) :
    (C.wires w).getD (n + m) false = value C.gates[m] (run (C.gates.take m) w) := by
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have hl : (run (C.gates.take m) w).length = n + m := by
    rw [run_length, hw]; simp; omega
  have h2 : run C.gates w = run (C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1)) w :=
    congrArg (fun l => run l w) hsplit
  rw [wires_eq, h2, run_append, run_cons, run_preserves _ _ _ (by simp; omega),
    getD_snoc, if_neg (by omega), if_pos hl.symm]

/-! ## Setting input `i` to false: reads of `i` go to an absent wire `B` -/

def rest (i B : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun r => if r = i then B else r)⟩

theorem run_rest (i B : ℕ) (gs : List Gate) (O0 O1 : List Bool) (hl : O0.length = O1.length)
    (hag : ∀ r, r ≠ i → O0.getD r false = O1.getD r false) (hi : i < O1.length)
    (hi0 : O1.getD i false = false) (hB : O0.length + gs.length ≤ B) :
    (run (gs.map (rest i B)) O0).length = (run gs O1).length ∧
      ∀ r, r ≠ i → (run (gs.map (rest i B)) O0).getD r false = (run gs O1).getD r false := by
  induction gs generalizing O0 O1 with
  | nil => exact ⟨hl, hag⟩
  | cons g gs ih =>
    rw [List.map_cons, run_cons, run_cons]
    have hv : value (rest i B g) O0 = value g O1 := by
      unfold value rest
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro r _
      show O0.getD (if r = i then B else r) false = O1.getD r false
      by_cases h : r = i
      · subst h
        rw [if_pos rfl, getD_out O0 (show O0.length ≤ B by simp at hB; omega), hi0]
      · rw [if_neg h, hag r h]
    rw [hv]
    apply ih
    · simp [hl]
    · intro r hr
      rw [getD_snoc, getD_snoc, hag r hr, hl]
    · simp; omega
    · rw [List.getD_append _ _ _ _ hi, hi0]
    · simp at hB ⊢; omega

/-- A gate reads `i` in a way that matters: an AND or OR with `i` among its inputs, or a NOT
whose first input is `i`. -/
def Eff (i : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some i) ∨ (g.op ≠ GateOp.not ∧ i ∈ g.inputs)

theorem value_indep (i : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (he : ¬ Eff i g)
    (O O' : List Bool) (hag : ∀ r, r ≠ i → O.getD r false = O'.getD r false) :
    value g O = value g O' := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  unfold Eff at he
  rcases hop with rfl | rfl | rfl
  · have hni : i ∉ ins := fun h => he (Or.inr ⟨by simp, h⟩)
    unfold value; congr 1
    apply List.map_congr_left
    intro r hr; exact hag r (fun e => hni (e ▸ hr))
  · have hni : i ∉ ins := fun h => he (Or.inr ⟨by simp, h⟩)
    unfold value; congr 1
    apply List.map_congr_left
    intro r hr; exact hag r (fun e => hni (e ▸ hr))
  · rcases ins with _ | ⟨r, rest⟩
    · rfl
    · have hr : r ≠ i := fun e => he (Or.inl ⟨rfl, by simp [e]⟩)
      have h := hag r hr
      simp only [List.getD_eq_getElem?_getD] at h
      simp [value, GateOp.eval, List.getD_eq_getElem?_getD, h]

theorem run_indep (i : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (he : ∀ g ∈ gs, ¬ Eff i g) (O O' : List Bool) (hl : O.length = O'.length)
    (hag : ∀ r, r ≠ i → O.getD r false = O'.getD r false) :
    ∀ r, r ≠ i → (run gs O).getD r false = (run gs O').getD r false := by
  induction gs generalizing O O' with
  | nil => exact hag
  | cons g gs ih =>
    rw [run_cons, run_cons,
      value_indep i g (hop g List.mem_cons_self) (he g List.mem_cons_self) O O' hag]
    apply ih (fun g hg => hop g (List.mem_cons_of_mem _ hg))
      (fun g hg => he g (List.mem_cons_of_mem _ hg))
    · simp [hl]
    · intro r hr; rw [getD_snoc, getD_snoc, hag r hr, hl]

/-! ## Readers of a wire `q` that is always true -/

def fixT (q B : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => ⟨GateOp.and, g.inputs.filter (fun r => r ≠ q)⟩
  | GateOp.or => if q ∈ g.inputs then ⟨GateOp.not, [B]⟩ else g
  | GateOp.not => if g.inputs.head? = some q then ⟨GateOp.or, []⟩ else ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem all_filter (l : List ℕ) (q : ℕ) (f : ℕ → Bool) (hq : f q = true) :
    ((l.filter (fun r => r ≠ q)).map f).all id = (l.map f).all id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = q
    · subst h
      rw [List.filter_cons_of_neg (by simp), ih, List.map_cons, List.all_cons, hq]
      rfl
    · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.map_cons,
        List.all_cons, List.all_cons, ih]

theorem value_fixT (q B : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (W : List Bool) (hq : W.getD q false = true) (hB : W.getD B false = false) :
    value (fixT q B g) W = value g W := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · show ((ins.filter (fun r => r ≠ q)).map (fun i => W.getD i false)).all id =
      (ins.map (fun i => W.getD i false)).all id
    exact all_filter ins q _ hq
  · by_cases hm : q ∈ ins
    · show value (if q ∈ ins then ⟨GateOp.not, [B]⟩ else ⟨GateOp.or, ins⟩) W = _
      rw [if_pos hm]
      simp only [value, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hB,
        Bool.not_false]
      symm
      rw [List.any_eq_true]
      exact ⟨_, List.mem_map_of_mem hm, by simpa using hq⟩
    · show value (if q ∈ ins then ⟨GateOp.not, [B]⟩ else ⟨GateOp.or, ins⟩) W = _
      rw [if_neg hm]
  · show value (if ins.head? = some q then ⟨GateOp.or, []⟩ else ⟨GateOp.not, ins.take 1⟩) W = _
    by_cases hh : ins.head? = some q
    · rw [if_pos hh]
      rcases ins with _ | ⟨a, rest⟩
      · simp at hh
      · simp at hh; subst hh
        simp only [List.getD_eq_getElem?_getD] at hq
        simp [value, GateOp.eval, List.getD_eq_getElem?_getD, hq]
    · rw [if_neg hh]
      rcases ins with _ | ⟨a, rest⟩ <;> rfl


theorem run_fixT (q B : ℕ) (suf : List Gate)
    (hop : ∀ g ∈ suf, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (W : List Bool) (hqW : q < W.length) (hq : W.getD q false = true)
    (hB : W.length + suf.length ≤ B) :
    run (suf.map (fixT q B)) W = run suf W := by
  induction suf generalizing W with
  | nil => rfl
  | cons g suf ih =>
    rw [List.map_cons, run_cons, run_cons,
      value_fixT q B g (hop g List.mem_cons_self) W hq (getD_out _ (by simp at hB; omega))]
    apply ih (fun g hg => hop g (List.mem_cons_of_mem _ hg))
    · simp; omega
    · rw [List.getD_append _ _ _ _ hqW, hq]
    · simp at hB ⊢; omega

theorem fixT_noread (q B : ℕ) (hqB : q ≠ B) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    q ∉ (fixT q B g).inputs := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · show q ∉ ins.filter (fun r => r ≠ q)
    simp
  · show q ∉ (if q ∈ ins then (⟨GateOp.not, [B]⟩ : Gate) else ⟨GateOp.or, ins⟩).inputs
    split_ifs with h
    · simpa using hqB
    · exact h
  · show q ∉ (if ins.head? = some q then (⟨GateOp.or, []⟩ : Gate)
      else ⟨GateOp.not, ins.take 1⟩).inputs
    split_ifs with h
    · simp
    · rcases ins with _ | ⟨a, rest⟩
      · simp
      · have : a ≠ q := fun e => h (by simp [e])
        simpa using this.symm

theorem fixT_fan (q B : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (fixT q B g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (fixT q B g).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · refine ⟨Or.inl rfl, ?_⟩
    show (ins.filter (fun r => r ≠ q)).length ≤ 2
    exact (List.length_filter_le _ _).trans hlen
  · show (if q ∈ ins then (⟨GateOp.not, [B]⟩ : Gate) else ⟨GateOp.or, ins⟩).op ∈ _ ∧
      (if q ∈ ins then (⟨GateOp.not, [B]⟩ : Gate) else ⟨GateOp.or, ins⟩).inputs.length ≤ 2
    split_ifs
    · simp
    · exact ⟨by simp, hlen⟩
  · show (if ins.head? = some q then (⟨GateOp.or, []⟩ : Gate) else ⟨GateOp.not, ins.take 1⟩).op ∈ _ ∧
      (if ins.head? = some q then (⟨GateOp.or, []⟩ : Gate)
        else ⟨GateOp.not, ins.take 1⟩).inputs.length ≤ 2
    split_ifs
    · simp
    · refine ⟨by simp, ?_⟩
      simp only [List.length_take]; omega

theorem erase_fan (n : ℕ) (C : Circuit) (m p : ℕ) (h : FanInTwo C) :
    FanInTwo (eraseGate n C m p) := by
  unfold eraseGate
  split_ifs
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h g (List.mem_of_mem_take hg)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      have := h g0 (List.mem_of_mem_drop hg0)
      exact ⟨this.1, by simpa using this.2⟩
  · exact h

theorem erase_size (n : ℕ) (C : Circuit) {m : ℕ} (p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).size = C.gates.length - 1 := by
  unfold eraseGate Circuit.size
  rw [if_pos hm]
  simp; omega

/-- An OR gate reading `i` (renamed to the absent wire `B`) copies its other input. -/
theorem or_val (i B : ℕ) (ins : List ℕ) (hlen : ins.length ≤ 2) (hi : i ∈ ins)
    (u : List Bool) (hB : u.getD B false = false) :
    value ⟨GateOp.or, ins.map (fun r => if r = i then B else r)⟩ u =
      u.getD ((ins.filter (fun r => r ≠ i)).headD B) false := by
  have hB' : u[B]?.getD false = false := by simpa [List.getD_eq_getElem?_getD] using hB
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at hi
  · simp at hi; subst hi
    simp [value, GateOp.eval, hB]
  · by_cases ha : a = i
    · subst ha
      by_cases hb : b = a
      · subst hb; simp [value, GateOp.eval, hB]
      · simp [value, GateOp.eval, hB, hB', hb, List.filter_cons, List.getD_eq_getElem?_getD]
    · have hb : b = i := by simp at hi; rcases hi with h | h <;> [exact absurd h.symm ha; exact h.symm]
      subst hb
      simp [value, GateOp.eval, hB, hB', ha, List.filter_cons, List.getD_eq_getElem?_getD]
  · simp at hlen

/-- The input list read at `r`. -/
theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (r : ℕ) :
    (List.ofFn x).getD r false = if h : r < n then x ⟨r, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl


theorem restrict (n s : ℕ) (F : (Fin n → Bool) → Bool) (v : Fin n)
    (hC : HasCircuitSize n F s)
    (hsens : ∃ x, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x y, F (Function.update x v false) ≠ F (Function.update y v false)) :
    HasCircuitSize n (fun x => F (Function.update x v false)) (s - 1) := by
  classical
  obtain ⟨C, hfan, hsize, hev⟩ := hC
  unfold Circuit.size at hsize
  set i : ℕ := v.val with hi_def
  have hin : i < n := v.isLt
  set L := C.gates.length with hL
  set B := n + L + 1 with hB_def
  have hop : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
    fun g hg => (hfan g hg).1
  have hag0 : ∀ (x : Fin n → Bool) (b : Bool) (r : ℕ), r ≠ i →
      (List.ofFn x).getD r false = (List.ofFn (Function.update x v b)).getD r false := by
    intro x b r hr
    rw [ofFn_getD, ofFn_getD]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; apply hr; rw [hi_def, ← e]
    · rfl
  have hiv : ∀ (x : Fin n → Bool) (b : Bool), (List.ofFn (Function.update x v b)).getD i false = b := by
    intro x b
    rw [ofFn_getD, dif_pos hin]
    simp [hi_def]
  have hout : C.output ≠ i := by
    intro ho
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have key : ∀ x, F (Function.update x v false) = false := by
      intro x
      rw [← hev, Circuit.eval, ho, wires_eq, run_preserves _ _ _ (by simp; omega), hiv]
    rw [key, key]
  let C0 : Circuit := ⟨C.gates.map (rest i B), C.output⟩
  have hC0l : C0.gates.length = L := by simp [C0, hL]
  have hC0 : ∀ x, C0.eval (List.ofFn x) = F (Function.update x v false) := by
    intro x
    rw [← hev]
    exact (run_rest i B C.gates (List.ofFn x) (List.ofFn (Function.update x v false)) (by simp)
      (hag0 x false) (by simp; omega) (hiv x false) (by simp; omega)).2 _ hout
  have hfan0 : FanInTwo C0 := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hfan g0 hg0).1, by simpa [rest] using (hfan g0 hg0).2⟩
  have heff : ∃ m, ∃ hm : m < L, Eff i C.gates[m] := by
    by_contra hno
    push_neg at hno
    obtain ⟨x, hx⟩ := hsens
    apply hx
    rw [← hev, ← hev]
    unfold Circuit.eval
    rw [wires_eq, wires_eq]
    refine run_indep i C.gates hop ?_ _ _ (by simp) ?_ _ hout
    · intro g hg
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hg
      exact hno m hm
    · intro r hr
      rw [← hag0 x false r hr, ← hag0 x true r hr]
  obtain ⟨m, hm, he⟩ := heff
  have hm0 : m < C0.gates.length := by omega
  set gm := C.gates[m] with hgm
  have hg0 : C0.gates[m] = rest i B gm := by simp [C0, hgm]
  set u : (Fin n → Bool) → List Bool := fun x => run (C0.gates.take m) (List.ofFn x) with hu
  have hwire : ∀ x : Fin n → Bool, (C0.wires (List.ofFn x)).getD (n + m) false = value (rest i B gm) (u x) := by
    intro x
    rw [wire_gate n C0 hm0 _ (by simp), hg0]
  have hulen : ∀ x : Fin n → Bool, (u x).length = n + m := by
    intro x; simp only [hu]; rw [run_length]; simp; omega
  have huB : ∀ x : Fin n → Bool, (u x).getD B false = false := fun x => getD_out _ (by rw [hulen]; omega)
  have hfull : ∀ x : Fin n → Bool, C0.wires (List.ofFn x) = run (C0.gates.drop m) (u x) := by
    intro x
    rw [wires_eq, hu]
    simp only
    rw [← run_append, List.take_append_drop]
  have hfullB : ∀ x : Fin n → Bool, (C0.wires (List.ofFn x)).getD B false = false :=
    fun x => getD_out (C0.wires (List.ofFn x))
      (by rw [wires_eq, run_length, List.length_ofFn, hC0l]; omega)
  have hpre : ∀ (x : Fin n → Bool) (r : ℕ), r < n + m → (C0.wires (List.ofFn x)).getD r false = (u x).getD r false := by
    intro x r hr
    rw [hfull, run_preserves _ _ _ (by rw [hulen]; exact hr)]
  have hsz : C0.gates.length - 1 ≤ s - 1 := by omega
  have hBin : n + C0.gates.length ≤ B := by omega
  obtain ⟨hopm, hlenm⟩ := hfan gm (List.getElem_mem hm)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hopm
  rcases hopm with h | h | h
  · -- AND reading the absent wire: constantly false
    have hi_in : i ∈ gm.inputs := by
      rcases he with ⟨h', _⟩ | ⟨_, h'⟩
      · rw [h] at h'; cases h'
      · exact h'
    have hval : ∀ x : Fin n → Bool, value (rest i B gm) (u x) = false := by
      intro x
      unfold value rest
      rw [h]
      simp only [GateOp.eval]
      rw [Bool.eq_false_iff]
      intro hall
      rw [List.all_eq_true] at hall
      have := hall ((u x).getD B false) (by
        simp only [List.map_map, List.mem_map]
        exact ⟨i, hi_in, by simp⟩)
      rw [id, huB x] at this
      exact Bool.false_ne_true this
    refine ⟨eraseGate n C0 m B, erase_fan n C0 m B hfan0, by rw [erase_size n C0 B hm0]; exact hsz,
      fun x => ?_⟩
    rw [erase_eval n C0 hm0 (Or.inr hBin) _ (by simp)
      (fun _ => by rw [hwire, hval x, hfullB])]
    exact hC0 x
  · -- OR reading the absent wire: a copy of its other input
    have hi_in : i ∈ gm.inputs := by
      rcases he with ⟨h', _⟩ | ⟨_, h'⟩
      · rw [h] at h'; cases h'
      · exact h'
    set y := (gm.inputs.filter (fun r => r ≠ i)).headD B with hy
    set p := if y < n + m then y else B with hp_def
    have hpp : p < n + m ∨ n + C0.gates.length ≤ p := by
      rw [hp_def]; split_ifs with hy'
      · exact Or.inl hy'
      · exact Or.inr hBin
    have hval : ∀ x : Fin n → Bool, value (rest i B gm) (u x) = (C0.wires (List.ofFn x)).getD p false := by
      intro x
      have hr : rest i B gm = ⟨GateOp.or, gm.inputs.map (fun r => if r = i then B else r)⟩ := by
        unfold rest; rw [h]
      rw [hr, or_val i B gm.inputs hlenm hi_in (u x) (huB x), ← hy, hp_def]
      split_ifs with hy'
      · rw [hpre x y hy']
      · rw [getD_out _ (by rw [hulen]; omega), hfullB]
    refine ⟨eraseGate n C0 m p, erase_fan n C0 m p hfan0, by rw [erase_size n C0 p hm0]; exact hsz,
      fun x => ?_⟩
    rw [erase_eval n C0 hm0 hpp _ (by simp) (fun _ => by rw [hwire, hval x])]
    exact hC0 x
  · -- NOT reading the absent wire first: constantly true
    have hhead : gm.inputs.head? = some i := by
      rcases he with ⟨_, h'⟩ | ⟨h', _⟩
      · exact h'
      · exact absurd h h'
    obtain ⟨tl, htl⟩ : ∃ tl, gm.inputs = i :: tl := by
      rcases hq : gm.inputs with _ | ⟨a, tl⟩
      · rw [hq] at hhead; cases hhead
      · rw [hq] at hhead; simp at hhead; exact ⟨tl, by rw [hhead]⟩
    have hval : ∀ x : Fin n → Bool, value (rest i B gm) (u x) = true := by
      intro x
      unfold value rest
      rw [h, htl]
      have := huB x
      simp only [List.getD_eq_getElem?_getD] at this
      simp [GateOp.eval, List.getD_eq_getElem?_getD, this]
    have hout0 : C0.output ≠ n + m := by
      intro ho
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      rw [← hC0, ← hC0]
      unfold Circuit.eval
      rw [ho, hwire, hwire, hval, hval]
    let C1 : Circuit :=
      ⟨C0.gates.take (m + 1) ++ (C0.gates.drop (m + 1)).map (fixT (n + m) B), C0.output⟩
    have hC1l : C1.gates.length = L := by
      simp [C1]; omega
    have hdrop : C1.gates.drop (m + 1) = (C0.gates.drop (m + 1)).map (fixT (n + m) B) := by
      simp only [C1]
      rw [List.drop_append_of_le_length (by simp; omega)]
      simp
    have hC1w : ∀ x : Fin n → Bool, C1.wires (List.ofFn x) = C0.wires (List.ofFn x) := by
      intro x
      have hW : (run (C0.gates.take (m + 1)) (List.ofFn x)).getD (n + m) false = true := by
        have h2 := hwire x
        rw [hval x, wires_eq, ← List.take_append_drop (m + 1) C0.gates, run_append,
          run_preserves _ _ _ (by rw [run_length]; simp; omega)] at h2
        exact h2
      rw [wires_eq, wires_eq, run_append,
        run_fixT (n + m) B _ (fun g hg => (hfan0 g (List.mem_of_mem_drop hg)).1) _
          (by rw [run_length]; simp; omega) hW (by rw [run_length]; simp; omega),
        ← run_append, List.take_append_drop]
    have hfan1 : FanInTwo C1 := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hfan0 g (List.mem_of_mem_take hg)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        exact fixT_fan _ _ g0 (hfan0 g0 (List.mem_of_mem_drop hg0))
    have hm1 : m < C1.gates.length := by omega
    refine ⟨eraseGate n C1 m B, erase_fan n C1 m B hfan1,
      by rw [erase_size n C1 B hm1]; omega, fun x => ?_⟩
    rw [erase_eval n C1 hm1 (Or.inr (by omega)) _ (by simp) ?_]
    · show C1.eval (List.ofFn x) = F (Function.update x v false)
      rw [← hC0 x]
      unfold Circuit.eval
      rw [hC1w]
    · rintro (⟨g, hg, hgr⟩ | ho)
      · rw [hdrop] at hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        exact absurd hgr (fixT_noread _ _ (by omega) g0 (hfan0 g0 (List.mem_of_mem_drop hg0)).1)
      · exact absurd ho hout0

end PEqualNP.Outside.L_meta_2535_aux

theorem PEqualNP.Outside.L_meta_2535 : ∀ (x1 x2 : ℕ) (x3 : (Fin x1 → Bool) → Bool) (x4 : Fin x1), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x2 → (∃ (x6 : Fin x1 → Bool), x3 (Function.update x6 x4 Bool.false) ≠ x3 (Function.update x6 x4 Bool.true)) → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x3 (Function.update x7 x4 Bool.false) ≠ x3 (Function.update x8 x4 Bool.false)) → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x8 : Fin x1 → Bool) => x3 (Function.update x8 x4 Bool.false)) (x2 - (1 : ℕ)) :=
  fun n s F v hC hsens hnc => PEqualNP.Outside.L_meta_2535_aux.restrict n s F v hC hsens hnc

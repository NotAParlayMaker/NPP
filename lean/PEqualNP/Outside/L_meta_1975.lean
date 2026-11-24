import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1975_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

-- the wires a gate names in the slots that count: one slot for NOT, two for AND and OR
def eff (g : Gate) : List ℕ :=
  List.take (bif g.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) g.inputs

def OkGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

lemma okGate_of_fanInTwo (C : Circuit) (hC : FanInTwo C) : ∀ g ∈ C.gates, OkGate g := by
  intro g hg
  obtain ⟨h1, h2⟩ := hC g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

lemma fanInTwo_of_ok (C : Circuit) (h : ∀ g ∈ C.gates, OkGate g) : FanInTwo C := by
  intro g hg
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

-- the value of a gate depends only on the wires it names in its counted slots
lemma gate_congr (g : Gate) (hg : OkGate g) (σ : ℕ → ℕ) (F F' : ℕ → Bool)
    (h : ∀ i ∈ eff g, F i = F' (σ i)) :
    g.op.eval (g.inputs.map F) = g.op.eval ((g.inputs.map σ).map F') := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  simp only [eff] at h
  rcases hop with rfl | rfl | rfl
  · have h2 : ∀ i ∈ inputs, F i = F' (σ i) := by
      intro i hi
      apply h
      simpa [GateOp.eval, List.take_of_length_le hlen] using hi
    rw [List.map_map]
    congr 1
    exact List.map_congr_left h2
  · have h2 : ∀ i ∈ inputs, F i = F' (σ i) := by
      intro i hi
      apply h
      simpa [GateOp.eval, List.take_of_length_le hlen] using hi
    rw [List.map_map]
    congr 1
    exact List.map_congr_left h2
  · cases inputs with
    | nil => rfl
    | cons a r =>
      have h3 := h a (by simp [GateOp.eval])
      simp [GateOp.eval, h3]

def ren (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map σ⟩

-- the invariant of the simulation: the second wire list is the first one seen through sigma
def Inv (d : ℕ) (σ : ℕ → ℕ) (P : ℕ → Prop) (w w' : List Bool) : Prop :=
  w.length = w'.length + d ∧
  (∀ i, P i → i < w.length → σ i < w'.length ∧ w.getD i false = w'.getD (σ i) false) ∧
  (∀ i, w.length ≤ i → σ i + d = i)

lemma Inv.getD_eq {d : ℕ} {σ : ℕ → ℕ} {P : ℕ → Prop} {w w' : List Bool}
    (h : Inv d σ P w w') (i : ℕ) (hi : P i) : w.getD i false = w'.getD (σ i) false := by
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hlt : i < w.length
  · exact (h2 i hi hlt).2
  · have h4 := h3 i (by omega)
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma Inv.step {d : ℕ} {σ : ℕ → ℕ} {P : ℕ → Prop} {w w' : List Bool}
    (h : Inv d σ P w w') (g : Gate) (hg : OkGate g) (hP : ∀ i ∈ eff g, P i) :
    Inv d σ P (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [(ren σ g).op.eval ((ren σ g).inputs.map fun i => w'.getD i false)]) := by
  have hb : (ren σ g).op.eval ((ren σ g).inputs.map fun i => w'.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [ren]
    exact (gate_congr g hg σ (fun i => w.getD i false) (fun i => w'.getD i false)
      (fun i hi => h.getD_eq i (hP i hi))).symm
  rw [hb]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp; omega, ?_, ?_⟩
  · intro i hi hlt
    by_cases hlt' : i < w.length
    · obtain ⟨h4, h5⟩ := h2 i hi hlt'
      refine ⟨by simp; omega, ?_⟩
      rw [getD_snoc_lt _ _ _ _ hlt', getD_snoc_lt _ _ _ _ h4, h5]
    · have hi' : i = w.length := by
        simp at hlt
        omega
      have h4 := h3 i (by omega)
      have h5 : σ i = w'.length := by omega
      refine ⟨by simp; omega, ?_⟩
      rw [getD_snoc_eq _ _ _ _ hi', getD_snoc_eq _ _ _ _ h5]
  · intro i hi
    apply h3
    simp at hi
    omega

lemma sim (d : ℕ) (σ : ℕ → ℕ) (P : ℕ → Prop) (gs : List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hP : ∀ g ∈ gs, ∀ i ∈ eff g, P i) :
    ∀ w w' : List Bool, Inv d σ P w w' →
      Inv d σ P (wiresFrom gs w) (wiresFrom (gs.map (ren σ)) w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    exact ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hP g' (List.mem_cons_of_mem _ hg')) _ _
      (h.step g (hok g List.mem_cons_self) (hP g List.mem_cons_self))

lemma ren_ok (σ : ℕ → ℕ) (g : Gate) (hg : OkGate g) : OkGate (ren σ g) := by
  obtain ⟨h1, h2⟩ := hg
  exact ⟨h1, by simpa [ren] using h2⟩

-- a gate whose wire nobody names, and which is not the output, can be deleted
lemma remove_gate (n : ℕ) (C : Circuit) (hC : FanInTwo C) (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output ≠ n + j) (hun : ∀ g ∈ C.gates, n + j ∉ eff g) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size + 1 = C.size ∧
      ∀ x : List Bool, x.length = n → C'.eval x = C.eval x := by
  have hok := okGate_of_fanInTwo C hC
  let σ : ℕ → ℕ := fun i => if n + j < i then i - 1 else i
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hpre : ∀ g ∈ C.gates.take j, g ∈ C.gates := fun g hg => List.mem_of_mem_take hg
  have hpost : ∀ g ∈ C.gates.drop (j + 1), g ∈ C.gates := fun g hg => List.mem_of_mem_drop hg
  refine ⟨⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (ren σ), σ C.output⟩, ?_, ?_, ?_⟩
  · apply fanInTwo_of_ok
    intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hok g (hpre g hg)
    · exact ren_ok σ g' (hok g' (hpost g' hg'))
  · simp only [Circuit.size, List.length_append, List.length_map, List.length_take,
      List.length_drop]
    omega
  · intro x hx
    have hW : C.wires x = wiresFrom (C.gates.drop (j + 1))
        (wiresFrom (C.gates.take j) x ++
          [(C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
            (wiresFrom (C.gates.take j) x).getD i false)]) := by
      have : C.wires x = wiresFrom C.gates x := rfl
      rw [this]
      conv_lhs => rw [hsplit]
      rw [wiresFrom_append, wiresFrom_cons]
    have hlen : (wiresFrom (C.gates.take j) x).length = n + j := by
      rw [wiresFrom_length, hx, List.length_take]
      omega
    have hinv0 : Inv 1 σ (fun i => i ≠ n + j)
        (wiresFrom (C.gates.take j) x ++
          [(C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
            (wiresFrom (C.gates.take j) x).getD i false)])
        (wiresFrom (C.gates.take j) x) := by
      refine ⟨by simp, ?_, ?_⟩
      · intro i hi hlt
        have hlt' : i < n + j := by
          simp at hlt
          omega
        have hσ : σ i = i := by
          show (if n + j < i then i - 1 else i) = i
          split_ifs <;> omega
        rw [hσ]
        exact ⟨by omega, getD_snoc_lt _ _ _ _ (by omega)⟩
      · intro i hi
        have hlt' : n + j < i := by
          simp at hi
          omega
        show (if n + j < i then i - 1 else i) + 1 = i
        split_ifs
        omega
    have hinv := sim 1 σ (fun i => i ≠ n + j) (C.gates.drop (j + 1))
      (fun g hg => hok g (hpost g hg))
      (fun g hg i hi hij => hun g (hpost g hg) (hij ▸ hi)) _ _ hinv0
    have hW' : Circuit.wires ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (ren σ), σ C.output⟩ x
        = wiresFrom ((C.gates.drop (j + 1)).map (ren σ)) (wiresFrom (C.gates.take j) x) := by
      have : Circuit.wires ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (ren σ), σ C.output⟩ x
          = wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (ren σ)) x := rfl
      rw [this, wiresFrom_append]
    simp only [Circuit.eval]
    rw [hW, hW']
    exact (hinv.getD_eq C.output hout).symm

-- an input that nobody names does not matter
lemma unread_input (C : Circuit) (hC : FanInTwo C) (a : ℕ) (hout : C.output ≠ a)
    (hun : ∀ g ∈ C.gates, a ∉ eff g) (x y : List Bool) (hlen : x.length = y.length)
    (hxy : ∀ i, i ≠ a → x.getD i false = y.getD i false) : C.eval x = C.eval y := by
  have hok := okGate_of_fanInTwo C hC
  have hinv0 : Inv 0 id (fun i => i ≠ a) x y := by
    refine ⟨by simpa using hlen, ?_, ?_⟩
    · intro i hi hlt
      exact ⟨by simpa [hlen] using hlt, hxy i hi⟩
    · intro i _
      rfl
  have hinv := sim 0 id (fun i => i ≠ a) C.gates hok
    (fun g hg i hi hia => hun g hg (hia ▸ hi)) _ _ hinv0
  have hid : C.gates.map (ren id) = C.gates := by
    have : ∀ g : Gate, ren id g = g := by
      intro g
      cases g
      simp [ren]
    have h2 : ren id = id := funext this
    rw [h2, List.map_id]
  rw [hid] at hinv
  exact hinv.getD_eq C.output hout

-- the number of gates naming wire i in a counted slot
def cnt (gs : List Gate) (i : ℕ) : ℕ := (gs.filter (fun g => (eff g).contains i)).length

lemma cnt_cons (g : Gate) (gs : List Gate) (i : ℕ) :
    cnt (g :: gs) i = (if i ∈ eff g then 1 else 0) + cnt gs i := by
  simp only [cnt, List.filter_cons]
  by_cases h : i ∈ eff g
  · simp [h]
    omega
  · simp [h]

lemma eff_length (g : Gate) : (eff g).length ≤ 2 := by
  simp only [eff, List.length_take]
  cases (g.op.eval [Bool.false]) <;> simp

-- double counting: every gate has at most two counted slots
lemma count_le (gs : List Gate) (I : Finset ℕ) : ∑ i ∈ I, cnt gs i ≤ 2 * gs.length := by
  induction gs with
  | nil => simp [cnt]
  | cons g gs ih =>
    have h2 : ∑ i ∈ I, (if i ∈ eff g then 1 else 0) ≤ 2 := by
      rw [← Finset.card_filter]
      calc (I.filter (fun i => i ∈ eff g)).card ≤ (eff g).toFinset.card :=
            Finset.card_le_card (by
              intro i hi
              simp only [Finset.mem_filter] at hi
              simpa using hi.2)
        _ ≤ (eff g).length := List.toFinset_card_le _
        _ ≤ 2 := eff_length g
    simp only [cnt_cons, Finset.sum_add_distrib, List.length_cons]
    omega

lemma cnt_pos (gs : List Gate) (i : ℕ) (h : ∃ g ∈ gs, i ∈ eff g) : 1 ≤ cnt gs i := by
  obtain ⟨g, hg, hi⟩ := h
  simp only [cnt]
  apply List.length_pos_of_mem (a := g)
  simp [List.mem_filter, hg, hi]

lemma exists_of_cnt_zero_not (gs : List Gate) (i : ℕ) (h : ¬ 1 ≤ cnt gs i) :
    ∀ g ∈ gs, i ∉ eff g := by
  intro g hg hi
  exact h (cnt_pos gs i ⟨g, hg, hi⟩)

lemma lower (n m out : ℕ) (gs : List Gate) (hm : gs.length = m) (A : Finset (Fin n))
    (h3 : ∀ v : Fin n, v ∉ A → cnt gs v = 3)
    (h1 : ∀ v : Fin n, v ∈ A → 1 ≤ cnt gs v)
    (hg : ∀ j, j < m → n + j ≠ out → 1 ≤ cnt gs (n + j)) :
    (∑ v : Fin n, (if v ∈ A then 1 else 3)) + (m - 1) ≤ 2 * m := by
  have hle := count_le gs (Finset.range (n + m))
  rw [Finset.sum_range_add, hm] at hle
  have hA : ∑ v : Fin n, (if v ∈ A then 1 else 3) ≤ ∑ i ∈ Finset.range n, cnt gs i := by
    rw [Finset.sum_range]
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : v ∈ A
    · simpa [hv] using h1 v hv
    · simp [hv, h3 v hv]
  have hG : m - 1 ≤ ∑ j ∈ Finset.range m, cnt gs (n + j) := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range m)
      (fun j => n + j ≠ out)
    have hone : ((Finset.range m).filter (fun j => ¬ (n + j ≠ out))).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_filter, not_not] at ha hb
      omega
    have hcard : m - 1 ≤ ((Finset.range m).filter (fun j => n + j ≠ out)).card := by
      simp only [Finset.card_range] at hsplit
      omega
    calc m - 1 ≤ ((Finset.range m).filter (fun j => n + j ≠ out)).card := hcard
      _ = ∑ j ∈ (Finset.range m).filter (fun j => n + j ≠ out), 1 := by simp
      _ ≤ ∑ j ∈ (Finset.range m).filter (fun j => n + j ≠ out), cnt gs (n + j) :=
          Finset.sum_le_sum (by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_range] at hj
            exact hg j hj.1 hj.2)
      _ ≤ ∑ j ∈ Finset.range m, cnt gs (n + j) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  omega

-- the explicit circuit: x_t AND (x_u OR x_w), then one OR per free input, then AND, OR per edge
def chainA : ℕ → List ℕ → List Gate
  | _, [] => []
  | k, a :: r => ⟨GateOp.or, [k, a]⟩ :: chainA (k + 1) r

def chainE : ℕ → List (ℕ × ℕ) → List Gate
  | _, [] => []
  | k, pq :: r => ⟨GateOp.and, [pq.1, pq.2]⟩ :: ⟨GateOp.or, [k, k + 1]⟩ :: chainE (k + 2) r

lemma chainA_length (k : ℕ) (l : List ℕ) : (chainA k l).length = l.length := by
  induction l generalizing k with
  | nil => rfl
  | cons a r ih => simp [chainA, ih]

lemma chainE_length (k : ℕ) (l : List (ℕ × ℕ)) : (chainE k l).length = 2 * l.length := by
  induction l generalizing k with
  | nil => rfl
  | cons a r ih =>
    simp [chainE, ih]
    omega

lemma chainA_ok (k : ℕ) (l : List ℕ) : ∀ g ∈ chainA k l, OkGate g := by
  induction l generalizing k with
  | nil =>
    intro g hg
    simp [chainA] at hg
  | cons a r ih =>
    intro g hg
    simp only [chainA, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨Or.inr (Or.inl rfl), by simp⟩
    · exact ih _ g hg

lemma chainE_ok (k : ℕ) (l : List (ℕ × ℕ)) : ∀ g ∈ chainE k l, OkGate g := by
  induction l generalizing k with
  | nil =>
    intro g hg
    simp [chainE] at hg
  | cons a r ih =>
    intro g hg
    simp only [chainE, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · exact ⟨Or.inl rfl, by simp⟩
    · exact ⟨Or.inr (Or.inl rfl), by simp⟩
    · exact ih _ g hg

lemma eval_or2 (b1 b2 : Bool) : GateOp.or.eval [b1, b2] = (b1 || b2) := by
  simp [GateOp.eval]

lemma eval_and2 (b1 b2 : Bool) : GateOp.and.eval [b1, b2] = (b1 && b2) := by
  simp [GateOp.eval]

lemma chainA_spec (ν : ℕ → Bool) (B : ℕ) : ∀ (l : List ℕ) (k : ℕ) (w : List Bool),
    w.length = k + 1 → B ≤ k → (∀ i, i < B → w.getD i false = ν i) → (∀ a ∈ l, a < B) →
    (wiresFrom (chainA k l) w).getD (k + l.length) false = (w.getD k false || l.any ν) := by
  intro l
  induction l with
  | nil =>
    intro k w hw hB hν hl
    simp [chainA, wiresFrom]
  | cons a r ih =>
    intro k w hw hB hν hl
    have ha : a < B := hl a List.mem_cons_self
    simp only [chainA, wiresFrom_cons]
    have hb : GateOp.or.eval (([k, a] : List ℕ).map fun i => w.getD i false) =
        (w.getD k false || ν a) := by
      show GateOp.or.eval [w.getD k false, w.getD a false] = _
      rw [eval_or2, hν a ha]
    rw [hb]
    have h := ih (k + 1) (w ++ [(w.getD k false || ν a)]) (by simp; omega) (by omega)
      (fun i hi => by rw [getD_snoc_lt _ _ _ _ (by omega)]; exact hν i hi)
      (fun a' ha' => hl a' (List.mem_cons_of_mem _ ha'))
    rw [getD_snoc_eq _ _ _ _ (by omega)] at h
    have hidx : k + (a :: r).length = k + 1 + r.length := by
      simp
      omega
    rw [hidx, h]
    simp [List.any_cons, Bool.or_assoc]

lemma chainE_spec (ν : ℕ → Bool) (B : ℕ) : ∀ (l : List (ℕ × ℕ)) (k : ℕ) (w : List Bool),
    w.length = k + 1 → B ≤ k → (∀ i, i < B → w.getD i false = ν i) →
    (∀ pq ∈ l, pq.1 < B ∧ pq.2 < B) →
    (wiresFrom (chainE k l) w).getD (k + 2 * l.length) false =
      (w.getD k false || l.any (fun pq => ν pq.1 && ν pq.2)) := by
  intro l
  induction l with
  | nil =>
    intro k w hw hB hν hl
    simp [chainE, wiresFrom]
  | cons pq r ih =>
    intro k w hw hB hν hl
    obtain ⟨hp, hq⟩ := hl pq List.mem_cons_self
    simp only [chainE, wiresFrom_cons]
    have hb1 : GateOp.and.eval (([pq.1, pq.2] : List ℕ).map fun i => w.getD i false) =
        (ν pq.1 && ν pq.2) := by
      show GateOp.and.eval [w.getD pq.1 false, w.getD pq.2 false] = _
      rw [eval_and2, hν _ hp, hν _ hq]
    rw [hb1]
    have hb2 : GateOp.or.eval (([k, k + 1] : List ℕ).map fun i =>
        (w ++ [(ν pq.1 && ν pq.2)]).getD i false) = (w.getD k false || (ν pq.1 && ν pq.2)) := by
      simp only [List.map_cons, List.map_nil]
      rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_eq _ _ _ _ (by omega)]
      simp [GateOp.eval]
    rw [hb2]
    have h := ih (k + 2)
      (w ++ [(ν pq.1 && ν pq.2)] ++ [(w.getD k false || (ν pq.1 && ν pq.2))])
      (by simp; omega) (by omega)
      (fun i hi => by
        rw [getD_snoc_lt _ _ _ _ (by simp; omega), getD_snoc_lt _ _ _ _ (by omega)]
        exact hν i hi)
      (fun pq' h' => hl pq' (List.mem_cons_of_mem _ h'))
    rw [getD_snoc_eq _ _ _ _ (by simp; omega)] at h
    have hidx : k + 2 * (pq :: r).length = k + 2 + 2 * r.length := by
      simp
      omega
    rw [hidx, h]
    simp [List.any_cons, Bool.or_assoc]

def dnf (n t u w : ℕ) (la : List ℕ) (le : List (ℕ × ℕ)) : Circuit :=
  ⟨⟨GateOp.or, [u, w]⟩ :: ⟨GateOp.and, [t, n]⟩ ::
      (chainA (n + 1) la ++ chainE (n + 1 + la.length) le),
    n + 1 + la.length + 2 * le.length⟩

lemma dnf_size (n t u w : ℕ) (la : List ℕ) (le : List (ℕ × ℕ)) :
    (dnf n t u w la le).size = 2 + la.length + 2 * le.length := by
  simp only [dnf, Circuit.size, List.length_cons, List.length_append, chainA_length,
    chainE_length]
  omega

lemma dnf_fanInTwo (n t u w : ℕ) (la : List ℕ) (le : List (ℕ × ℕ)) :
    FanInTwo (dnf n t u w la le) := by
  apply fanInTwo_of_ok
  intro g hg
  simp only [dnf, List.mem_cons, List.mem_append] at hg
  rcases hg with rfl | rfl | hg | hg
  · exact ⟨Or.inr (Or.inl rfl), by simp⟩
  · exact ⟨Or.inl rfl, by simp⟩
  · exact chainA_ok _ _ g hg
  · exact chainE_ok _ _ g hg

lemma dnf_eval (n t u w : ℕ) (la : List ℕ) (le : List (ℕ × ℕ)) (x : List Bool)
    (hx : x.length = n) (ht : t < n)
    (hla : ∀ a ∈ la, a < n) (hle : ∀ pq ∈ le, pq.1 < n ∧ pq.2 < n) :
    (dnf n t u w la le).eval x =
      (((x.getD t false && (x.getD u false || x.getD w false)) ||
        la.any (fun a => x.getD a false)) ||
        le.any (fun pq => x.getD pq.1 false && x.getD pq.2 false)) := by
  have hW : (dnf n t u w la le).wires x =
      wiresFrom (chainE (n + 1 + la.length) le) (wiresFrom (chainA (n + 1) la)
        (x ++ [(x.getD u false || x.getD w false)] ++
          [(x.getD t false && (x.getD u false || x.getD w false))])) := by
    have h0 : (dnf n t u w la le).wires x = wiresFrom (dnf n t u w la le).gates x := rfl
    rw [h0]
    simp only [dnf, wiresFrom_cons, wiresFrom_append]
    have hb1 : GateOp.or.eval (([u, w] : List ℕ).map fun i => x.getD i false) =
        (x.getD u false || x.getD w false) := by
      simp [GateOp.eval]
    rw [hb1]
    have hb2 : GateOp.and.eval (([t, n] : List ℕ).map fun i =>
        (x ++ [(x.getD u false || x.getD w false)]).getD i false) =
        (x.getD t false && (x.getD u false || x.getD w false)) := by
      simp only [List.map_cons, List.map_nil]
      rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_eq _ _ _ _ (by omega)]
      simp [GateOp.eval]
    rw [hb2]
  have hν2 : ∀ i, i < n → (x ++ [(x.getD u false || x.getD w false)] ++
      [(x.getD t false && (x.getD u false || x.getD w false))]).getD i false =
      x.getD i false := by
    intro i hi
    rw [getD_snoc_lt _ _ _ _ (by simp; omega), getD_snoc_lt _ _ _ _ (by omega)]
  have hA := chainA_spec (fun i => x.getD i false) n la (n + 1)
    (x ++ [(x.getD u false || x.getD w false)] ++
      [(x.getD t false && (x.getD u false || x.getD w false))])
    (by simp; omega) (by omega) hν2 hla
  rw [getD_snoc_eq _ _ _ _ (by simp; omega)] at hA
  have hE := chainE_spec (fun i => x.getD i false) n le (n + 1 + la.length)
    (wiresFrom (chainA (n + 1) la)
      (x ++ [(x.getD u false || x.getD w false)] ++
        [(x.getD t false && (x.getD u false || x.getD w false))]))
    (by rw [wiresFrom_length, chainA_length]; simp; omega) (by omega)
    (fun i hi => by rw [wiresFrom_getD_lt _ _ _ (by simp; omega)]; exact hν2 i hi) hle
  simp only [Circuit.eval]
  rw [hW]
  have hout : (dnf n t u w la le).output = n + 1 + la.length + 2 * le.length := rfl
  rw [hout, hE, hA]

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    (List.ofFn x).getD (v : ℕ) false = x v := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma anyA {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) :
    ((A.toList.map (fun a : Fin n => (a : ℕ))).any (fun a => (List.ofFn x).getD a false) = true) ↔
      ∃ a ∈ A, x a = true := by
  simp only [List.any_map, List.any_eq_true, Finset.mem_toList, Function.comp, getD_ofFn]

lemma anyE {n : ℕ} (E : Finset (Sym2 (Fin n))) (x : Fin n → Bool) :
    ((E.toList.map (fun e : Sym2 (Fin n) => (((Quot.out e).1 : ℕ), ((Quot.out e).2 : ℕ)))).any
        (fun pq => (List.ofFn x).getD pq.1 false && (List.ofFn x).getD pq.2 false) = true) ↔
      ∃ e ∈ E, x (Quot.out e).1 = true ∧ x (Quot.out e).2 = true := by
  simp only [List.any_map, List.any_eq_true, Finset.mem_toList, Function.comp, getD_ofFn,
    Bool.and_eq_true]

lemma sum_ite_card {n : ℕ} (A : Finset (Fin n)) (a b : ℕ) :
    (∑ v : Fin n, (if v ∈ A then a else b)) + b * A.card = a * A.card + b * n := by
  classical
  have h := Finset.sum_ite (s := (Finset.univ : Finset (Fin n))) (p := fun v => v ∈ A)
    (fun _ => a) (fun _ => b)
  rw [h]
  simp only [Finset.sum_const, smul_eq_mul]
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun v => v ∈ A)
  have hA : (Finset.univ.filter (fun v : Fin n => v ∈ A)) = A := by
    ext v
    simp
  rw [hA] at hc ⊢
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have hb : b * _ = b * n := congrArg (fun k => b * k) hc
  rw [← hb]
  ring

-- the upper bound: a circuit with |A| + 2|E| - 2 gates
lemma upper (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (f : (Fin n → Bool) → Bool)
    (h1 : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (h3 : ∀ u w : Fin n, G.Adj u w → u ∉ A)
    (h4 : ∃ u w : Fin n, G.Adj u w)
    (h5 : ∀ x : Fin n → Bool, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u w : Fin n, G.Adj u w ∧ x u = true ∧ x w = true) :
    ∃ s : ℕ, HasCircuitSize n f s ∧ s + 2 + 2 * A.card = 3 * n := by
  classical
  obtain ⟨t, t', htt'⟩ := h4
  have htA : t ∉ A := h3 t t' htt'
  obtain ⟨u, w, z, huw, -, -, hset⟩ := Set.ncard_eq_three.mp (h1 t htA)
  have htu : G.Adj t u := by
    have hmem : u ∈ G.neighborSet t := by
      rw [hset]
      simp
    exact (G.mem_neighborSet t u).mp hmem
  have htw : G.Adj t w := by
    have hmem : w ∈ G.neighborSet t := by
      rw [hset]
      simp
    exact (G.mem_neighborSet t w).mp hmem
  have he1 : s(t, u) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact htu
  have he2 : s(t, w) ∈ G.edgeFinset.erase s(t, u) := by
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro h
      rcases Sym2.eq_iff.mp h with ⟨_, h'⟩ | ⟨h', _⟩
      · exact huw h'.symm
      · exact G.ne_of_adj htu h'
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact htw
  have hcard : ((G.edgeFinset.erase s(t, u)).erase s(t, w)).card + 1 + 1 =
      G.edgeFinset.card := by
    rw [Finset.card_erase_add_one he2, Finset.card_erase_add_one he1]
  have hdeg : ∀ v : Fin n, G.degree v = if v ∈ A then 0 else 3 := by
    intro v
    have hdn : G.degree v = (G.neighborSet v).ncard := by
      rw [Set.ncard_eq_toFinset_card' (G.neighborSet v)]
      rfl
    by_cases hv : v ∈ A
    · have hempty : G.neighborSet v = ∅ := by
        ext w'
        simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
        intro hadj
        exact h3 v w' hadj hv
      rw [hdn, hempty, Set.ncard_empty]
      simp [hv]
    · rw [hdn, h1 v hv]
      simp [hv]
  have hsum : ∑ v : Fin n, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hS := sum_ite_card A 0 3
  simp only [← hdeg] at hS
  refine ⟨(dnf n t u w (A.toList.map (fun a : Fin n => (a : ℕ)))
    (((G.edgeFinset.erase s(t, u)).erase s(t, w)).toList.map
      (fun e : Sym2 (Fin n) => (((Quot.out e).1 : ℕ), ((Quot.out e).2 : ℕ))))).size, ?_, ?_⟩
  · refine ⟨_, dnf_fanInTwo _ _ _ _ _ _, le_refl _, ?_⟩
    intro x
    rw [dnf_eval n t u w _ _ (List.ofFn x) (by simp) t.isLt
      (by
        intro a ha
        simp only [List.mem_map] at ha
        obtain ⟨a', _, rfl⟩ := ha
        exact a'.isLt)
      (by
        intro pq hpq
        simp only [List.mem_map] at hpq
        obtain ⟨e, _, rfl⟩ := hpq
        exact ⟨(Quot.out e).1.isLt, (Quot.out e).2.isLt⟩)]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, anyA, anyE, getD_ofFn]
    rw [h5 x]
    constructor
    · rintro ((⟨ht, hu | hw⟩ | hA) | ⟨e, he, hp, hq⟩)
      · exact Or.inr ⟨t, u, htu, ht, hu⟩
      · exact Or.inr ⟨t, w, htw, ht, hw⟩
      · exact Or.inl hA
      · have he' : e ∈ G.edgeFinset := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he)
        rw [← Sym2.mk_fst_out_snd_out e, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] at he'
        exact Or.inr ⟨_, _, he', hp, hq⟩
    · rintro (hA | ⟨p, q, hadj, hp, hq⟩)
      · exact Or.inl (Or.inr hA)
      · by_cases hc1 : s(p, q) = s(t, u)
        · left
          left
          rcases Sym2.eq_iff.mp hc1 with ⟨hpt, hqu⟩ | ⟨hpu, hqt⟩
          · rw [hpt] at hp
            rw [hqu] at hq
            exact ⟨hp, Or.inl hq⟩
          · rw [hpu] at hp
            rw [hqt] at hq
            exact ⟨hq, Or.inl hp⟩
        · by_cases hc2 : s(p, q) = s(t, w)
          · left
            left
            rcases Sym2.eq_iff.mp hc2 with ⟨hpt, hqw⟩ | ⟨hpw, hqt⟩
            · rw [hpt] at hp
              rw [hqw] at hq
              exact ⟨hp, Or.inr hq⟩
            · rw [hpw] at hp
              rw [hqt] at hq
              exact ⟨hq, Or.inr hp⟩
          · right
            refine ⟨s(p, q), ?_, ?_⟩
            · rw [Finset.mem_erase, Finset.mem_erase, SimpleGraph.mem_edgeFinset,
                SimpleGraph.mem_edgeSet]
              exact ⟨hc2, hc1, hadj⟩
            · rcases Sym2.eq_iff.mp (Sym2.mk_fst_out_snd_out s(p, q)) with
                ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · rw [h1', h2']
                exact ⟨hp, hq⟩
              · rw [h1', h2']
                exact ⟨hq, hp⟩
  · rw [dnf_size]
    simp only [List.length_map, Finset.length_toList]
    omega

-- the residual hypothesis contradicts leastness
lemma main_false (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) (C : Circuit)
    (h1 : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (h3 : ∀ u w : Fin n, G.Adj u w → u ∉ A)
    (h4 : ∃ u w : Fin n, G.Adj u w)
    (h5 : ∀ x : Fin n → Bool, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u w : Fin n, G.Adj u w ∧ x u = true ∧ x w = true)
    (h6 : FanInTwo C) (h7 : circuitFun n C = f)
    (h8 : ∀ s : ℕ, HasCircuitSize n f s → C.size ≤ s)
    (h9 : ∀ v ∉ A, cnt C.gates (v : ℕ) = 3) : False := by
  classical
  have hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := fun x => congrFun h7 x
  obtain ⟨s, hs, hs2⟩ := upper n G A f h1 h3 h4 h5
  have hms : C.size ≤ s := h8 s hs
  obtain ⟨t, u, htu⟩ := h4
  have htA : t ∉ A := h3 t u htu
  have huA : u ∉ A := h3 u t htu.symm
  have hf0 : f (fun _ => false) = false := by
    by_contra hcon
    have htrue : f (fun _ => false) = true := by simpa using hcon
    rcases (h5 _).mp htrue with ⟨a, _, ha⟩ | ⟨p, q, _, hp, _⟩
    · exact Bool.false_ne_true ha
    · exact Bool.false_ne_true hp
  have hL1 : ∀ v : Fin n, v ∈ A → 1 ≤ cnt C.gates (v : ℕ) := by
    intro a ha
    by_contra hcon
    have hun := exists_of_cnt_zero_not C.gates _ hcon
    by_cases hout : C.output = (a : ℕ)
    · have hval : ∀ x : Fin n → Bool, f x = x a := by
        intro x
        rw [← hev x]
        have hw' : C.eval (List.ofFn x) = (wiresFrom C.gates (List.ofFn x)).getD C.output false :=
          rfl
        rw [hw', hout, wiresFrom_getD_lt _ _ _ (by simp), getD_ofFn]
      have hx := hval (fun v => decide (v = t ∨ v = u))
      have hfx : f (fun v => decide (v = t ∨ v = u)) = true :=
        (h5 _).mpr (Or.inr ⟨t, u, htu, by simp, by simp⟩)
      rw [hfx] at hx
      have hat : a ≠ t := fun h => htA (h ▸ ha)
      have hau : a ≠ u := fun h => huA (h ▸ ha)
      simp [hat, hau] at hx
    · have heq := unread_input C h6 (a : ℕ) hout hun
        (List.ofFn (fun v : Fin n => decide (v = a))) (List.ofFn (fun _ : Fin n => false))
        (by simp)
        (by
          intro i hi
          by_cases hin : i < n
          · have e1 := getD_ofFn (fun v : Fin n => decide (v = a)) ⟨i, hin⟩
            have e2 := getD_ofFn (fun _ : Fin n => false) ⟨i, hin⟩
            simp only at e1 e2
            rw [e1, e2]
            simp only [decide_eq_false_iff_not]
            intro h
            exact hi (by rw [← h])
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      rw [hev, hev, hf0] at heq
      have hfa : f (fun v => decide (v = a)) = true :=
        (h5 _).mpr (Or.inl ⟨a, ha, by simp⟩)
      rw [hfa] at heq
      exact Bool.noConfusion heq
  have hL2 : ∀ j, j < C.gates.length → n + j ≠ C.output → 1 ≤ cnt C.gates (n + j) := by
    intro j hj hout
    by_contra hcon
    have hun := exists_of_cnt_zero_not C.gates _ hcon
    obtain ⟨C', hC', hsz, hval⟩ := remove_gate n C h6 j hj (fun h => hout h.symm) hun
    have hsize : HasCircuitSize n f C'.size :=
      ⟨C', hC', le_refl _, fun x => by rw [hval _ (by simp), hev]⟩
    have hle := h8 _ hsize
    omega
  have hlow := lower n C.gates.length C.output C.gates rfl A h9 hL1 hL2
  have hS1 := sum_ite_card A 1 3
  have hsz : C.size = C.gates.length := rfl
  omega

end PEqualNP.Outside.L_meta_1975_aux

theorem PEqualNP.Outside.L_meta_1975 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length = (3 : ℕ) ∧ ∀ x17 ∈ x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.or) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  intro x1 x2 x3 x4 x5 h1 _ h3 h4 h5 h6 h7 h8 h9
  exact (PEqualNP.Outside.L_meta_1975_aux.main_false x1 x2 x3 x4 x5 h1 h3 h4 h5 h6 h7 h8
    (fun v hv => (h9 v hv).1)).elim

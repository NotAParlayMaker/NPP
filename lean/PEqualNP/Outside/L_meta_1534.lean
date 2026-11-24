import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1534_aux

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = gs.foldl stepW x := rfl

theorem foldl_stepW_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

theorem foldl_stepW_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_take_getD (gs : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((gs.take t).foldl stepW w).length) :
    (gs.foldl stepW w).getD i false = ((gs.take t).foldl stepW w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t gs, List.foldl_append]
  exact foldl_stepW_getD _ _ _ hi

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem gate_val (gs : List Gate) (x : List Bool) (t : ℕ) (ht : t < gs.length) :
    (gs.foldl stepW x).getD (x.length + t) false =
      (gs[t]).op.eval ((gs[t]).inputs.map fun i =>
        if i < x.length + t then (gs.foldl stepW x).getD i false else false) := by
  have hsplit : gs = gs.take t ++ gs[t] :: gs.drop (t + 1) := by
    simp [List.take_append_drop]
  have hlen : ((gs.take t).foldl stepW x).length = x.length + t := by
    rw [foldl_stepW_length, List.length_take, Nat.min_eq_left ht.le]
  have hlhs : (gs.foldl stepW x).getD (x.length + t) false =
      (gs[t]).op.eval ((gs[t]).inputs.map fun i =>
        ((gs.take t).foldl stepW x).getD i false) := by
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [foldl_stepW_getD _ _ _ (by simp only [stepW, List.length_append, List.length_singleton, hlen]; omega)]
    simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ((gs.take t).foldl stepW x).length ≤ x.length + t), hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hlhs]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hi
  · exact (foldl_take_getD gs x t i (by omega)).symm
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem ofFn_getD (n : ℕ) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

theorem input_val (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (gs.foldl stepW (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [foldl_stepW_getD _ _ _ (by simpa using hi), ofFn_getD n x i hi]

theorem beyond_val (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    (gs.foldl stepW (List.ofFn x)).getD i false = false := by
  apply getD_ge
  rw [foldl_stepW_length, List.length_ofFn]
  exact hi

theorem gate_val_fn (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (t : ℕ) (ht : t < gs.length) :
    (gs.foldl stepW (List.ofFn x)).getD (n + t) false =
      (gs[t]).op.eval ((gs[t]).inputs.map fun i =>
        if i < n + t then (gs.foldl stepW (List.ofFn x)).getD i false else false) := by
  have h := gate_val gs (List.ofFn x) t ht
  rw [List.length_ofFn] at h
  exact h

theorem all_map_mono (l : List ℕ) (f g : ℕ → Bool) (hfg : ∀ i, f i = true → g i = true) :
    (l.map f).all id = true → (l.map g).all id = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    rintro ⟨h1, h2⟩
    exact ⟨hfg a h1, ih h2⟩

theorem any_map_mono (l : List ℕ) (f g : ℕ → Bool) (hfg : ∀ i, f i = true → g i = true) :
    (l.map f).any id = true → (l.map g).any id = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id_eq]
    rintro (h1 | h2)
    · exact Or.inl (hfg a h1)
    · exact Or.inr (ih h2)

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (hfg : ∀ i, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · exact all_map_mono l f g hfg
  · exact any_map_mono l f g hfg

theorem getD_snoc (l : List Bool) (a : Bool) (i : ℕ) :
    (l ++ [a]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then a else false := by
  rcases Nat.lt_trichotomy i l.length with hi | hi | hi
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hi), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hi]
  · subst hi
    rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl _)), ite_eq_left_of_eq_true _ _ (eq_true rfl),
      List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
    simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    apply getD_ge
    simp
    omega

theorem step_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (x y : List Bool)
    (hl : x.length = y.length) (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (stepW x g).getD i false = true → (stepW y g).getD i false = true := by
  intro i
  unfold stepW
  rw [getD_snoc, getD_snoc, ← hl]
  split_ifs with h1 h2
  · exact h i
  · exact eval_mono g.op hg g.inputs _ _ h
  · exact id

theorem W_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (x y : List Bool), x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ i, (gs.foldl stepW x).getD i false = true → (gs.foldl stepW y).getD i false = true := by
  induction gs with
  | nil =>
    intro x y _ h i
    exact h i
  | cons g gs ih =>
    intro x y hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [stepW, hl]
    · exact step_mono g (hgs g (by simp)) x y hl h

def Zset (n : ℕ) (gs : List Gate) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n =>
    (gs.foldl stepW (List.ofFn (fun k : Fin n => decide (k = u)))).getD (n + j) false = true)

theorem mem_Zset (n : ℕ) (gs : List Gate) (j : ℕ) (u : Fin n) :
    u ∈ Zset n gs j ↔
      (gs.foldl stepW (List.ofFn (fun k : Fin n => decide (k = u)))).getD (n + j) false = true := by
  simp [Zset]

noncomputable def newGate (n : ℕ) (gs : List Gate) (j : ℕ) (g : Gate) : Gate :=
  if (Zset n gs j).card ≤ 1 then ⟨GateOp.or, (Zset n gs j).toList.map Fin.val⟩ else g

noncomputable def gates2 (n : ℕ) (gs : List Gate) : List Gate :=
  List.ofFn (fun j : Fin gs.length => newGate n gs j.val (gs.get j))

theorem gates2_length (n : ℕ) (gs : List Gate) : (gates2 n gs).length = gs.length := by
  simp [gates2]

theorem gates2_get (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hj2 : j < (gates2 n gs).length) :
    (gates2 n gs)[j] = newGate n gs j gs[j] := by
  simp [gates2]

theorem or_val (n : ℕ) (gs : List Gate) (j : ℕ) (hs : List Gate) (x : Fin n → Bool) :
    GateOp.or.eval (((Zset n gs j).toList.map Fin.val).map fun i =>
        if i < n + j then (hs.foldl stepW (List.ofFn x)).getD i false else false) = true ↔
      ∃ u ∈ Zset n gs j, x u = true := by
  have hin : ∀ u : Fin n,
      (if u.val < n + j then (hs.foldl stepW (List.ofFn x)).getD u.val false else false) = x u := by
    intro u
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), input_val n hs x u.val u.isLt]
  simp only [GateOp.eval, List.map_map, List.any_map, List.any_eq_true, Finset.mem_toList,
    Function.comp_apply, hin, id_eq]

theorem agree (n : ℕ) (gs : List Gate) (u : Fin n) :
    ∀ i : ℕ, ((gates2 n gs).foldl stepW (List.ofFn (fun k : Fin n => decide (k = u)))).getD i false =
      (gs.foldl stepW (List.ofFn (fun k : Fin n => decide (k = u)))).getD i false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.lt_or_ge i n with hi | hi
    · rw [input_val n _ _ i hi, input_val n _ _ i hi]
    · rcases Nat.lt_or_ge i (n + gs.length) with hi2 | hi2
      · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
        have hj : j < gs.length := by omega
        have hj2 : j < (gates2 n gs).length := by rw [gates2_length]; exact hj
        rw [gate_val_fn n (gates2 n gs) _ j hj2, gates2_get n gs j hj hj2]
        unfold newGate
        split_ifs with hc
        · rw [Bool.eq_iff_iff, or_val, ← mem_Zset]
          constructor
          · rintro ⟨u', hu', hd⟩
            have : u' = u := of_decide_eq_true hd
            rw [← this]
            exact hu'
          · intro h
            exact ⟨u, h, decide_eq_true rfl⟩
        · rw [gate_val_fn n gs _ j hj]
          congr 1
          apply List.map_congr_left
          intro i' _
          split_ifs with h'
          · exact ih i' h'
          · rfl
      · rw [beyond_val n _ _ i (by rw [gates2_length]; exact hi2), beyond_val n _ _ i hi2]

theorem sing_le (n : ℕ) (x : Fin n → Bool) (u : Fin n) (hu : x u = true) :
    ∀ i, (List.ofFn (fun k : Fin n => decide (k = u))).getD i false = true →
      (List.ofFn x).getD i false = true := by
  intro i
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [ofFn_getD n _ i hi, ofFn_getD n _ i hi]
    intro h
    have : (⟨i, hi⟩ : Fin n) = u := of_decide_eq_true h
    rw [this]
    exact hu
  · rw [getD_ge _ _ (by simpa using hi)]
    intro h
    exact absurd h (by simp)

theorem dom (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) :
    ∀ i : ℕ, ((gates2 n gs).foldl stepW (List.ofFn x)).getD i false = true →
      (gs.foldl stepW (List.ofFn x)).getD i false = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.lt_or_ge i n with hi | hi
    · rw [input_val n _ _ i hi, input_val n _ _ i hi]
      exact id
    · rcases Nat.lt_or_ge i (n + gs.length) with hi2 | hi2
      · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
        have hj : j < gs.length := by omega
        have hj2 : j < (gates2 n gs).length := by rw [gates2_length]; exact hj
        rw [gate_val_fn n (gates2 n gs) _ j hj2, gates2_get n gs j hj hj2]
        unfold newGate
        split_ifs with hc
        · rw [or_val]
          rintro ⟨u, hu, hxu⟩
          exact W_mono gs hgs _ _ (by simp) (sing_le n x u hxu) (n + j) ((mem_Zset n gs j u).mp hu)
        · rw [gate_val_fn n gs _ j hj]
          apply eval_mono _ (hgs _ (List.getElem_mem hj))
          intro i'
          split_ifs with h'
          · exact ih i' h'
          · exact id
      · rw [beyond_val n _ _ i (by rw [gates2_length]; exact hi2)]
        intro h
        exact absurd h (by simp)

theorem gates2_ops (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g2 ∈ gates2 n gs, (g2.op = GateOp.and ∨ g2.op = GateOp.or) ∧ g2.inputs.length ≤ 2 := by
  intro g2 hg2
  obtain ⟨j, hj2, rfl⟩ := List.getElem_of_mem hg2
  have hj : j < gs.length := by rw [gates2_length] at hj2; exact hj2
  rw [gates2_get n gs j hj hj2]
  unfold newGate
  split_ifs with hc
  · refine ⟨Or.inr rfl, ?_⟩
    simp only [List.length_map, Finset.length_toList]
    omega
  · exact hgs _ (List.getElem_mem hj)

theorem filter_eq (n : ℕ) (gs : List Gate) (j : ℕ) :
    Finset.univ.filter (fun au : Fin n =>
      ((gates2 n gs).foldl stepW (List.ofFn (fun auk : Fin n => decide (auk = au)))).getD (n + j) false = true)
      = Zset n gs j := by
  unfold Zset
  apply Finset.filter_congr
  intro u _
  rw [agree n gs u (n + j)]

theorem narrow_val (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hc : (Zset n gs j).card ≤ 1) (x : Fin n → Bool) :
    ((gates2 n gs).foldl stepW (List.ofFn x)).getD (n + j) false = true ↔
      ∃ av : Fin n, ((gates2 n gs).foldl stepW
        (List.ofFn (fun avk : Fin n => decide (avk = av)))).getD (n + j) false = true ∧ x av = true := by
  have hj2 : j < (gates2 n gs).length := by rw [gates2_length]; exact hj
  rw [gate_val_fn n (gates2 n gs) _ j hj2, gates2_get n gs j hj hj2]
  unfold newGate
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc), or_val]
  constructor
  · rintro ⟨u, hu, hxu⟩
    refine ⟨u, ?_, hxu⟩
    rw [agree n gs u (n + j)]
    exact (mem_Zset n gs j u).mp hu
  · rintro ⟨u, hu, hxu⟩
    refine ⟨u, ?_, hxu⟩
    rw [agree n gs u (n + j)] at hu
    exact (mem_Zset n gs j u).mpr hu

end PEqualNP.Outside.L_meta_1534_aux

theorem PEqualNP.Outside.L_meta_1534 : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (S : Fin m → Finset (Fin n)) (D : Set (Fin n → Bool)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ v : Fin n, (fun vk : Fin n => decide (vk = v)) ∈ D) → (∀ (w : Fin m) (x : Fin n → Bool), x ∈ D → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (out w) false = decide (∃ v0 ∈ S w, x v0 = true)) → ∃ gates2 : List PEqualNP.CircuitLowerBounds.Gate, gates2.length ≤ gates.length ∧ (∀ g2 ∈ gates2, (g2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g2.inputs.length ≤ 2) ∧ (∀ ak : ℕ, ak < gates2.length → (Finset.univ.filter (fun au : Fin n => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn (fun auk : Fin n => decide (auk = au)))).getD (n + ak) false = true)).card ≤ 1 → ∀ ax : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn ax)).getD (n + ak) false = decide (∃ av : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn (fun avk : Fin n => decide (avk = av)))).getD (n + ak) false = true ∧ ax av = true)) ∧ ∀ (w2 : Fin m) (x2 : Fin n → Bool), x2 ∈ D → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn x2)).getD (out w2) false = decide (∃ v2 ∈ S w2, x2 v2 = true) := by
  intro n m gates out S D h1 h2 h3
  have hops : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => (h1 g hg).1
  have hops2 := PEqualNP.Outside.L_meta_1534_aux.gates2_ops n gates h1
  refine ⟨PEqualNP.Outside.L_meta_1534_aux.gates2 n gates, ?_, hops2, ?_, ?_⟩
  · rw [PEqualNP.Outside.L_meta_1534_aux.gates2_length]
  · intro ak hak hcard ax
    rw [PEqualNP.Outside.L_meta_1534_aux.gates2_length] at hak
    have hcard' : (PEqualNP.Outside.L_meta_1534_aux.Zset n gates ak).card ≤ 1 := by
      rw [← PEqualNP.Outside.L_meta_1534_aux.filter_eq n gates ak]
      exact hcard
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact PEqualNP.Outside.L_meta_1534_aux.narrow_val n gates ak hak hcard' ax
  · intro w2 x2 hx2
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    constructor
    · intro h
      have hold := PEqualNP.Outside.L_meta_1534_aux.dom n gates hops x2 (out w2) h
      have h3' : (gates.foldl PEqualNP.Outside.L_meta_1534_aux.stepW (List.ofFn x2)).getD (out w2) false =
          decide (∃ v0 ∈ S w2, x2 v0 = true) := h3 w2 x2 hx2
      rw [h3'] at hold
      exact of_decide_eq_true hold
    · rintro ⟨v0, hv0, hx⟩
      have hsing : (gates.foldl PEqualNP.Outside.L_meta_1534_aux.stepW (List.ofFn (fun vk : Fin n => decide (vk = v0)))).getD (out w2) false =
          decide (∃ v1 ∈ S w2, (fun vk : Fin n => decide (vk = v0)) v1 = true) :=
        h3 w2 (fun vk : Fin n => decide (vk = v0)) (h2 v0)
      have htrue : (gates.foldl PEqualNP.Outside.L_meta_1534_aux.stepW
          (List.ofFn (fun vk : Fin n => decide (vk = v0)))).getD (out w2) false = true := by
        rw [hsing]
        exact decide_eq_true ⟨v0, hv0, decide_eq_true rfl⟩
      rw [← PEqualNP.Outside.L_meta_1534_aux.agree n gates v0 (out w2)] at htrue
      exact PEqualNP.Outside.L_meta_1534_aux.W_mono _ (fun g hg => (hops2 g hg).1) _ _ (by simp)
        (PEqualNP.Outside.L_meta_1534_aux.sing_le n x2 v0 hx) (out w2) htrue

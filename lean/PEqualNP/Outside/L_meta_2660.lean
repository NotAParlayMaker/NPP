import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2660

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h


lemma ite_true_iff (c : Prop) [Decidable c] (b : Bool) :
    (if c then b else false) = true ↔ c ∧ b = true := by
  by_cases h : c <;> simp [h]

lemma W_and_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) :
    W n C x (n + k) = true ↔ ∀ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
  rw [W_gate n C x k hk, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
  constructor
  · intro h w hw
    exact (ite_true_iff _ _).mp (h _ ⟨w, hw, rfl⟩)
  · rintro h b ⟨w, hw, rfl⟩
    exact (ite_true_iff _ _).mpr (h w hw)

lemma W_or_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) :
    W n C x (n + k) = true ↔ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
  rw [W_gate n C x k hk, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  constructor
  · rintro ⟨b, ⟨w, hw, rfl⟩, h⟩
    exact ⟨w, hw, (ite_true_iff _ _).mp h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨_, ⟨w, hw, rfl⟩, (ite_true_iff _ _).mpr h⟩

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk i hi
    obtain ⟨w, _, hn, hlt, h⟩ := (inCone_iff n C i k hk).mp hi
    rcases h with h | h
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

lemma gate_mono2 (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length ≤ 2 := by
  have hg := hM (C.gates[k]) (List.getElem_mem hk)
  rw [← gateAt_eq C k hk] at hg
  have h1 := hg.1
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact ⟨h1, hg.2⟩

def Reach (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P t.val →
    (∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ a ∈ (gateAt C k).inputs, a < n + k → P a → P (n + k)) → P w

lemma reach_refl (n : ℕ) (C : Circuit) (t : Fin n) : Reach n C t t.val := fun _ h _ => h

lemma reach_step (n : ℕ) (C : Circuit) (t : Fin n) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a : ℕ) (ha : a ∈ (gateAt C k).inputs)
    (hlt : a < n + k) (h : Reach n C t a) : Reach n C t (n + k) :=
  fun P h0 hs => hs k hk hop a ha hlt (h P h0 hs)

lemma reach_inv (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (h : Reach n C t w) :
    w = t.val ∨ ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
      ∃ a ∈ (gateAt C k).inputs, a < n + k ∧ Reach n C t a := by
  have h2 := h (fun w => Reach n C t w ∧ (w = t.val ∨ ∃ k, k < C.gates.length ∧ w = n + k ∧
      (gateAt C k).op = GateOp.or ∧ ∃ a ∈ (gateAt C k).inputs, a < n + k ∧ Reach n C t a))
    ⟨reach_refl n C t, Or.inl rfl⟩
    (fun k hk hop a ha hlt ih => ⟨reach_step n C t k hk hop a ha hlt ih.1,
      Or.inr ⟨k, hk, rfl, hop, a, ha, hlt, ih.1⟩⟩)
  exact h2.2

lemma reach_val (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (y : Fin n → Bool)
    (hy : y t = true) (h : Reach n C t w) : W n C y w = true :=
  h (fun w => W n C y w = true) (by rw [W_input n C y t.val t.isLt]; exact hy)
    (fun k hk hop a ha hlt ih => (W_or_iff n C y k hk hop).mpr ⟨a, ha, hlt, ih⟩)

open PEqualNP.EdgeOwnership in
lemma descent (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x : Fin n → Bool) :
    ∀ k, k < C.gates.length → W n C x (n + k) = true →
      (gateAt C k).op = GateOp.and ∨
      (∃ i, InCone n C i k ∧ (gateAt C i).op = GateOp.and ∧ W n C x (n + i) = true) ∨
      (∃ u : Fin n, x u = true ∧ Reach n C u (n + k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hx
    rcases (gate_mono2 C hM k hk).1 with hop | hop
    · exact Or.inl hop
    · obtain ⟨w, hw, hlt, hwx⟩ := (W_or_iff n C x k hk hop).mp hx
      by_cases hwn : w < n
      · right; right
        refine ⟨⟨w, hwn⟩, ?_, ?_⟩
        · rw [← W_input n C x w hwn]; exact hwx
        · exact reach_step n C ⟨w, hwn⟩ k hk hop w hw hlt (reach_refl n C ⟨w, hwn⟩)
      · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
        have he : n + k' - n = k' := by omega
        rcases ih k' (by omega) (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨u, hu, hdom⟩
        · right; left
          exact ⟨k', (inCone_iff n C k' k hk).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩,
            h, hwx⟩
        · right; left
          exact ⟨i, (inCone_iff n C i k hk).mpr
            ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩, hia, hix⟩
        · right; right
          exact ⟨u, hu, reach_step n C u k hk hop (n + k') hw hlt hdom⟩

open PEqualNP.EdgeOwnership in
lemma owns_reach (n : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (p q : Fin n) (ho : Owns n C j p q) :
    ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C p w ∨ Reach n C q w) := by
  obtain ⟨_, _, hval, hno⟩ := ho
  intro w hw
  have hval' : W n C (pairInput p q) (n + j) = true := hval
  obtain ⟨hlt, hwx⟩ := (W_and_iff n C _ j hj hop).mp hval' w hw
  refine ⟨hlt, ?_⟩
  by_cases hwn : w < n
  · rw [W_input n C _ w hwn] at hwx
    have h' : (⟨w, hwn⟩ : Fin n) = p ∨ (⟨w, hwn⟩ : Fin n) = q := of_decide_eq_true hwx
    rcases h' with h | h
    · left
      rw [← h]; exact reach_refl n C ⟨w, hwn⟩
    · right
      rw [← h]; exact reach_refl n C ⟨w, hwn⟩
  · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
    have he : n + k' - n = k' := by omega
    have hk'j : k' < j := by omega
    have hc : InCone n C k' j :=
      (inCone_iff n C k' j hj).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩
    rcases descent n C hM (pairInput p q) k' (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨t, ht, hdom⟩
    · have hf : W n C (pairInput p q) (n + k') = false := hno k' hk'j hc h
      rw [hwx] at hf
      exact absurd hf (by simp)
    · have hc2 : InCone n C i j := (inCone_iff n C i j hj).mpr
        ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩
      have hij := inCone_lt n C j hj i hc2
      have hf : W n C (pairInput p q) (n + i) = false := hno i hij hc2 hia
      rw [hix] at hf
      exact absurd hf (by simp)
    · have h' : t = p ∨ t = q := of_decide_eq_true ht
      rcases h' with h | h
      · left; rw [← h]; exact hdom
      · right; rw [← h]; exact hdom

noncomputable def R (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun t => Reach n C t w)

lemma mem_R (n : ℕ) (C : Circuit) (w : ℕ) (t : Fin n) : t ∈ R n C w ↔ Reach n C t w := by
  unfold R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma R_card_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) : (R n C w).card ≤ 1 := by
  refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
  have h1 : w = a.val := by
    rcases reach_inv n C a w ((mem_R n C w a).mp ha) with h | ⟨k, _, h, _⟩
    · exact h
    · omega
  have h2 : w = b.val := by
    rcases reach_inv n C b w ((mem_R n C w b).mp hb) with h | ⟨k, _, h, _⟩
    · exact h
    · omega
  exact Fin.ext (h1.symm.trans h2)

lemma R_gate (n : ℕ) (C : Circuit) (k : ℕ) (t : Fin n) (ht : t ∈ R n C (n + k)) :
    k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ a ∈ (gateAt C k).inputs, a < n + k ∧ Reach n C t a := by
  rcases reach_inv n C t (n + k) ((mem_R n C (n + k) t).mp ht) with h | ⟨k', hk', h, hop, hex⟩
  · have := t.isLt
    omega
  · have hkk : k = k' := by omega
    rw [hkk]
    exact ⟨hk', hop, hex⟩

lemma count_abs {α : Type} [DecidableEq α] (f : ℕ → Finset α)
    (h : ∀ m, 2 ≤ (f m).card →
      ∃ ch : Finset ℕ, ch.card ≤ 2 ∧ (∀ a ∈ ch, a < m) ∧ f m ⊆ ch.biUnion f) :
    ∀ (m : ℕ) (W : Finset ℕ), (∀ w ∈ W, w < m) →
      (W.biUnion f).card ≤ W.card + ((Finset.range m).filter (fun w => 2 ≤ (f w).card)).card := by
  intro m
  induction m with
  | zero =>
    intro W hW
    have hW0 : W = ∅ := Finset.eq_empty_of_forall_notMem (fun w hw => by have := hW w hw; omega)
    rw [hW0]
    simp
  | succ m ih =>
    intro W hW
    have hmono : ((Finset.range m).filter (fun w => 2 ≤ (f w).card)).card ≤
        ((Finset.range (m + 1)).filter (fun w => 2 ≤ (f w).card)).card := by
      refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
      intro w hw
      rw [Finset.mem_range] at hw ⊢
      omega
    by_cases hm : m ∈ W
    · have hWpos : 1 ≤ W.card := Finset.card_pos.mpr ⟨m, hm⟩
      have hcardE : (W.erase m).card = W.card - 1 := Finset.card_erase_of_mem hm
      by_cases hb : 2 ≤ (f m).card
      · obtain ⟨ch, hch2, hchlt, hsub⟩ := h m hb
        have hW' : ∀ w ∈ W.erase m ∪ ch, w < m := by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · have h1 := hW w (Finset.mem_of_mem_erase hw)
            have h2 := Finset.ne_of_mem_erase hw
            omega
          · exact hchlt w hw
        have h1 := ih (W.erase m ∪ ch) hW'
        have h3 : W.biUnion f ⊆ (W.erase m ∪ ch).biUnion f := by
          intro x hx
          obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.mp hx
          by_cases hwm : w = m
          · rw [hwm] at hxw
            obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp (hsub hxw)
            exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_union_right _ ha, hxa⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hw⟩), hxw⟩
        have h4 := Finset.card_le_card h3
        have h5 : (W.erase m ∪ ch).card ≤ (W.erase m).card + ch.card := Finset.card_union_le _ _
        have h6 : ((Finset.range (m + 1)).filter (fun w => 2 ≤ (f w).card)).card =
            ((Finset.range m).filter (fun w => 2 ≤ (f w).card)).card + 1 := by
          rw [Finset.range_add_one, Finset.filter_insert]
          simp only [hb, ↓reduceIte]
          rw [Finset.card_insert_of_notMem]
          simp
        omega
      · have hW' : ∀ w ∈ W.erase m, w < m := by
          intro w hw
          have h1 := hW w (Finset.mem_of_mem_erase hw)
          have h2 := Finset.ne_of_mem_erase hw
          omega
        have h1 := ih (W.erase m) hW'
        have h3 : W.biUnion f ⊆ (W.erase m).biUnion f ∪ f m := by
          intro x hx
          obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.mp hx
          by_cases hwm : w = m
          · rw [hwm] at hxw
            exact Finset.mem_union_right _ hxw
          · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_erase.mpr ⟨hwm, hw⟩, hxw⟩)
        have h4 := Finset.card_le_card h3
        have h5 : ((W.erase m).biUnion f ∪ f m).card ≤ ((W.erase m).biUnion f).card + (f m).card :=
          Finset.card_union_le _ _
        omega
    · have hW' : ∀ w ∈ W, w < m := by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ m := fun e => hm (e ▸ hw)
        omega
      have h1 := ih W hW'
      omega


noncomputable def Bad (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (c : Fin n) (w : ℕ) :
    Finset (Fin n) := by
  classical exact (R n C w).filter (fun t => ¬ G.Adj c t)

lemma mem_Bad (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (c : Fin n) (w : ℕ) (t : Fin n) :
    t ∈ Bad n G C c w ↔ t ∈ R n C w ∧ ¬ G.Adj c t := by
  unfold Bad
  simp only [Finset.mem_filter]

noncomputable def Fk (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (k : ℕ) (c : Fin n)
    (w : ℕ) : Finset (Fin n) := by
  classical exact (R n C w).filter (fun x => G.Adj c x ∧ (Bad n G C c w).card ≤ k)

lemma mem_Fk (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (k : ℕ) (c : Fin n) (w : ℕ)
    (x : Fin n) :
    x ∈ Fk n G C k c w ↔ x ∈ R n C w ∧ G.Adj c x ∧ (Bad n G C c w).card ≤ k := by
  unfold Fk
  simp only [Finset.mem_filter]

lemma Fk_sub (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (k : ℕ) (c : Fin n) (w : ℕ) :
    Fk n G C k c w ⊆ R n C w := fun x hx => ((mem_Fk n G C k c w x).mp hx).1

lemma Fk_split (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (hM : Monotone2 C) (k : ℕ)
    (c : Fin n) (m : ℕ) (h2 : 2 ≤ (Fk n G C k c m).card) :
    ∃ ch : Finset ℕ, ch.card ≤ 2 ∧ (∀ a ∈ ch, a < m) ∧
      Fk n G C k c m ⊆ ch.biUnion (Fk n G C k c) := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h2
  have hbad : (Bad n G C c m).card ≤ k := ((mem_Fk n G C k c m x).mp hx).2.2
  by_cases hmn : m < n
  · exact absurd (Finset.card_le_one.mp (R_card_input n C m hmn) x (Fk_sub n G C k c m hx) y
      (Fk_sub n G C k c m hy)) hxy
  · obtain ⟨k', rfl⟩ : ∃ k', m = n + k' := ⟨m - n, by omega⟩
    obtain ⟨hk, hop, _⟩ := R_gate n C k' x (Fk_sub n G C k c (n + k') hx)
    refine ⟨((gateAt C k').inputs.filter (fun a => decide (a < n + k'))).toFinset, ?_, ?_, ?_⟩
    · exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans
        (gate_mono2 C hM k' hk).2)
    · intro a ha
      rw [List.mem_toFinset, List.mem_filter] at ha
      exact of_decide_eq_true ha.2
    · intro t ht
      have ht' := (mem_Fk n G C k c _ t).mp ht
      obtain ⟨_, _, a, ha, hlt, hr⟩ := R_gate n C k' t ht'.1
      refine Finset.mem_biUnion.mpr ⟨a, ?_, ?_⟩
      · rw [List.mem_toFinset, List.mem_filter]
        exact ⟨ha, decide_eq_true hlt⟩
      · refine (mem_Fk n G C k c a t).mpr ⟨(mem_R n C a t).mpr hr, ht'.2.1, ?_⟩
        refine le_trans (Finset.card_le_card ?_) hbad
        intro s hs
        have hs' := (mem_Bad n G C c a s).mp hs
        exact (mem_Bad n G C c _ s).mpr ⟨(mem_R n C (n + k') s).mpr
          (reach_step n C s k' hk hop a ha hlt ((mem_R n C a s).mp hs'.1)), hs'.2⟩

lemma side_aux (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (k : ℕ) (F : Finset (Fin n))
    (hF : F.card ≤ k) (a b : ℕ) (c x : Fin n) (hc : c ∉ F) (hx : x ∉ F)
    (hca : Reach n C c a) (hxb : Reach n C x b)
    (huniq : ∀ s, s ∉ F → Reach n C s a → s = c)
    (hbip : ∀ s, s ∉ F → ∀ t, t ∉ F → Reach n C s a → Reach n C t b → G.Adj s t) :
    c ∈ R n C a ∧ (R n C a).card ≤ k + 1 ∧ x ∈ Fk n G C k c b := by
  classical
  refine ⟨(mem_R n C a c).mpr hca, ?_, ?_⟩
  · have hsub : R n C a ⊆ insert c F := by
      intro s hs
      by_cases hsF : s ∈ F
      · exact Finset.mem_insert_of_mem hsF
      · rw [huniq s hsF ((mem_R n C a s).mp hs)]
        exact Finset.mem_insert_self c F
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))
  · refine (mem_Fk n G C k c b x).mpr ⟨(mem_R n C b x).mpr hxb, hbip c hc x hx hca hxb, ?_⟩
    refine le_trans (Finset.card_le_card ?_) hF
    intro t ht
    have ht' := (mem_Bad n G C c b t).mp ht
    by_contra htF
    exact ht'.2 (hbip c hc t htF hca ((mem_R n C b t).mp ht'.1))

open PEqualNP.EdgeOwnership in
lemma stark (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hM : Monotone2 C) (k : ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (u v : Fin n) (ho : Owns n C j u v)
    (F : Finset (Fin n)) (hF : F.card ≤ k) (hu : u ∉ F) (hv : v ∉ F)
    (hclean : ∀ p, p ∉ F → ∀ q, q ∉ F → gateVal n C j (pairInput p q) = true → G.Adj p q) :
    ∃ a ∈ (gateAt C j).inputs, ∃ b ∈ (gateAt C j).inputs, b < n + j ∧ ∃ c : Fin n,
      c ∈ R n C a ∧ (R n C a).card ≤ k + 1 ∧
      ((u = c ∧ v ∈ Fk n G C k c b) ∨ (v = c ∧ u ∈ Fk n G C k c b)) := by
  have F1 := owns_reach n C hM j hj hop
  have F3 : ∀ s, s ∉ F → ∀ t, t ∉ F →
      (∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C s w ∨ Reach n C t w)) → G.Adj s t := by
    intro s hs t ht h
    have hs' : pairInput s t s = true := by simp [pairInput]
    have ht' : pairInput s t t = true := by simp [pairInput]
    have hval : W n C (pairInput s t) (n + j) = true :=
      (W_and_iff n C _ j hj hop).mpr (fun w hw => ⟨(h w hw).1,
        (h w hw).2.elim (fun d => reach_val n C s w _ hs' d) (fun d => reach_val n C t w _ ht' d)⟩)
    exact hclean s hs t ht hval
  have hlen := (gate_mono2 C hM j hj).2
  have hF0 := F1 u v ho
  rcases hin : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · have hadj := F3 u hu u hu (by rw [hin]; intro w hw; simp at hw)
    exact absurd rfl hadj.ne
  · have h1 := hF0 a (by rw [hin]; simp)
    rcases h1.2 with d | d
    · have hadj := F3 u hu u hu (by
        rw [hin]; intro w hw
        have hwa : w = a := by simpa using hw
        rw [hwa]; exact ⟨h1.1, Or.inl d⟩)
      exact absurd rfl hadj.ne
    · have hadj := F3 v hv v hv (by
        rw [hin]; intro w hw
        have hwa : w = a := by simpa using hw
        rw [hwa]; exact ⟨h1.1, Or.inl d⟩)
      exact absurd rfl hadj.ne
  · have hlta : a < n + j := (hF0 a (by rw [hin]; simp)).1
    have hltb : b < n + j := (hF0 b (by rw [hin]; simp)).1
    have hamem : a ∈ (gateAt C j).inputs := by rw [hin]; simp
    have hbmem : b ∈ (gateAt C j).inputs := by rw [hin]; simp
    have hbip : ∀ s, s ∉ F → ∀ t, t ∉ F → Reach n C s a → Reach n C t b → G.Adj s t := by
      intro s hs t ht da db
      refine F3 s hs t ht ?_
      rw [hin]; intro w hw
      have hwab : w = a ∨ w = b := by simpa using hw
      rcases hwab with hwa | hwb
      · rw [hwa]; exact ⟨hlta, Or.inl da⟩
      · rw [hwb]; exact ⟨hltb, Or.inr db⟩
    have hbip' : ∀ s, s ∉ F → ∀ t, t ∉ F → Reach n C s b → Reach n C t a → G.Adj s t :=
      fun s hs t ht db da => (hbip t ht s hs da db).symm
    have hloop : ∀ t, t ∉ F → Reach n C t a → Reach n C t b → False :=
      fun t ht da db => absurd rfl (hbip t ht t ht da db).ne
    have hA : (Reach n C u a ∧ Reach n C v b) ∨ (Reach n C v a ∧ Reach n C u b) := by
      have h1 := hF0 a hamem
      have h2 := hF0 b hbmem
      rcases h1.2 with pa | qa <;> rcases h2.2 with pb | qb
      · exact (hloop u hu pa pb).elim
      · exact Or.inl ⟨pa, qb⟩
      · exact Or.inr ⟨qa, pb⟩
      · exact (hloop v hv qa qb).elim
    by_cases hc : ∀ s, s ∉ F → ∀ s', s' ∉ F → Reach n C s a → Reach n C s' a → s = s'
    · rcases hA with h | h
      · obtain ⟨e1, e2, e3⟩ := side_aux n G C k F hF a b u v hu hv h.1 h.2
          (fun s hs hsa => hc s hs u hu hsa h.1) hbip
        exact ⟨a, by simp, b, by simp, hltb, u, e1, e2, Or.inl ⟨rfl, e3⟩⟩
      · obtain ⟨e1, e2, e3⟩ := side_aux n G C k F hF a b v u hv hu h.1 h.2
          (fun s hs hsa => hc s hs v hv hsa h.1) hbip
        exact ⟨a, by simp, b, by simp, hltb, v, e1, e2, Or.inr ⟨rfl, e3⟩⟩
    · simp only [not_forall, exists_prop] at hc
      obtain ⟨a1, ha1F, a2, ha2F, ha1, ha2, hne⟩ := hc
      have huniq : ∀ t, t ∉ F → ∀ t', t' ∉ F → Reach n C t b → Reach n C t' b → t = t' := by
        intro t htF t' ht'F ht ht'
        by_contra hne'
        exact h4 a1 t a2 t' hne hne' ⟨hbip a1 ha1F t htF ha1 ht, (hbip a2 ha2F t htF ha2 ht).symm,
          hbip a2 ha2F t' ht'F ha2 ht', (hbip a1 ha1F t' ht'F ha1 ht').symm⟩
      rcases hA with h | h
      · obtain ⟨e1, e2, e3⟩ := side_aux n G C k F hF b a v u hv hu h.2 h.1
          (fun s hs hsb => huniq s hs v hv hsb h.2) hbip'
        exact ⟨b, by simp, a, by simp, hlta, v, e1, e2, Or.inr ⟨rfl, e3⟩⟩
      · obtain ⟨e1, e2, e3⟩ := side_aux n G C k F hF b a u v hu hv h.2 h.1
          (fun s hs hsb => huniq s hs u hu hsb h.2) hbip'
        exact ⟨b, by simp, a, by simp, hlta, u, e1, e2, Or.inl ⟨rfl, e3⟩⟩
  · have hl : (a :: b :: c :: r).length ≤ 2 := hin ▸ hlen
    simp only [List.length_cons] at hl
    omega

lemma centers (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (k : ℕ) (w : ℕ) :
    (Finset.univ.filter (fun c : Fin n => 2 ≤ (Fk n G C k c w).card)).card ≤
      (2 * k + 1).choose 2 + 1 := by
  classical
  by_cases hr : 2 * k + 2 ≤ (R n C w).card
  · have h1 : (Finset.univ.filter (fun c : Fin n => 2 ≤ (Fk n G C k c w).card)).card ≤ 1 := by
      refine Finset.card_le_one.mpr (fun c hc c' hc' => ?_)
      by_contra hne
      have hc1 := (Finset.mem_filter.mp hc).2
      have hc2 := (Finset.mem_filter.mp hc').2
      obtain ⟨x0, hx0, _⟩ := Finset.one_lt_card.mp hc1
      obtain ⟨y0, hy0, _⟩ := Finset.one_lt_card.mp hc2
      have hb1 : (Bad n G C c w).card ≤ k := ((mem_Fk n G C k c w x0).mp hx0).2.2
      have hb2 : (Bad n G C c' w).card ≤ k := ((mem_Fk n G C k c' w y0).mp hy0).2.2
      have hsub : R n C w ⊆ Bad n G C c w ∪ Bad n G C c' w ∪
          (R n C w).filter (fun t => G.Adj c t ∧ G.Adj c' t) := by
        intro t ht
        by_cases e1 : G.Adj c t
        · by_cases e2 : G.Adj c' t
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, e1, e2⟩)
          · exact Finset.mem_union_left _
              (Finset.mem_union_right _ ((mem_Bad n G C c' w t).mpr ⟨ht, e2⟩))
        · exact Finset.mem_union_left _
            (Finset.mem_union_left _ ((mem_Bad n G C c w t).mpr ⟨ht, e1⟩))
      have hcard := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
      have hCom : 1 < ((R n C w).filter (fun t => G.Adj c t ∧ G.Adj c' t)).card := by omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hCom
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      exact h4 c x c' y hne hxy ⟨hx'.1, hx'.2.symm, hy'.2, hy'.1.symm⟩
    omega
  · have hf : ∀ c : Fin n, ∀ h : 2 ≤ (Fk n G C k c w).card,
        Classical.choose (Finset.exists_subset_card_eq h) ⊆ Fk n G C k c w ∧
          (Classical.choose (Finset.exists_subset_card_eq h)).card = 2 :=
      fun c h => Classical.choose_spec (Finset.exists_subset_card_eq h)
    let f : Fin n → Finset (Fin n) := fun c =>
      if h : 2 ≤ (Fk n G C k c w).card then Classical.choose (Finset.exists_subset_card_eq h)
      else ∅
    have hf' : ∀ c : Fin n, 2 ≤ (Fk n G C k c w).card →
        f c ⊆ Fk n G C k c w ∧ (f c).card = 2 := by
      intro c hc
      simp only [f, dif_pos hc]
      exact hf c hc
    have h1 : (Finset.univ.filter (fun c : Fin n => 2 ≤ (Fk n G C k c w).card)).card ≤
        ((R n C w).powersetCard 2).card := by
      refine Finset.card_le_card_of_injOn f (fun c hc => ?_) (fun c hc c' hc' heq => ?_)
      · obtain ⟨hs, hcard⟩ := hf' c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
        exact Finset.mem_coe.mpr (Finset.mem_powersetCard.mpr ⟨hs.trans (Fk_sub n G C k c w), hcard⟩)
      · by_contra hne
        obtain ⟨hs, hcard⟩ := hf' c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
        obtain ⟨hs', _⟩ := hf' c' (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < (f c).card)
        have hx1 := (mem_Fk n G C k c w x).mp (hs hx)
        have hy1 := (mem_Fk n G C k c w y).mp (hs hy)
        have hx2 := (mem_Fk n G C k c' w x).mp (hs' (by rw [← heq]; exact hx))
        have hy2 := (mem_Fk n G C k c' w y).mp (hs' (by rw [← heq]; exact hy))
        exact h4 c x c' y hne hxy ⟨hx1.2.1, hx2.2.1.symm, hy2.2.1, hy1.2.1.symm⟩
    rw [Finset.card_powersetCard] at h1
    have h2 : (R n C w).card.choose 2 ≤ (2 * k + 1).choose 2 := Nat.choose_le_choose 2 (by omega)
    omega

lemma num1 (k : ℕ) : 4 * (k + 1) ≤ 2 ^ (k + 2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega

lemma ch2 (m : ℕ) : (m + 2).choose 2 = m.choose 2 + (2 * m + 1) := by
  have h1 : (m + 2).choose 2 = (m + 1).choose 1 + (m + 1).choose 2 :=
    Nat.choose_succ_succ (m + 1) 1
  have h2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
  rw [h1, h2, Nat.choose_one_right, Nat.choose_one_right]
  ring

lemma num2 (k : ℕ) : (2 * k + 1).choose 2 + 1 ≤ 2 ^ (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (2 * (k + 1) + 1).choose 2 = (2 * k + 1).choose 2 + (4 * k + 3) := by
      have h : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      rw [h, ch2]
      ring
    have h1 := num1 k
    rw [e, pow_succ]
    omega

open PEqualNP.EdgeOwnership in
theorem keyk (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hM : Monotone2 C) (k : ℕ) (T : Finset (Sym2 (Fin n)))
    (hT : ∀ e ∈ T, ∃ u v : Fin n, e = s(u, v) ∧ ∃ j : Fin C.gates.length,
      Owns n C (↑j) u v ∧ ∃ F : Finset (Fin n), F.card ≤ k ∧ u ∉ F ∧ v ∉ F ∧
        ∀ p ∉ F, ∀ q ∉ F, gateVal n C (↑j) (pairInput p q) = true → G.Adj p q) :
    T.card ≤ 2 ^ (k + 2) * C.gates.length := by
  classical
  let L := C.gates.length
  let S : ℕ → Finset (Fin n) := fun j =>
    ((gateAt C j).inputs.toFinset.filter (fun a => (R n C a).card ≤ k + 1)).biUnion (R n C)
  let V : Fin n → ℕ → Finset ℕ := fun c j =>
    if c ∈ S j then (gateAt C j).inputs.toFinset else ∅
  let JA : Finset ℕ := (Finset.range L).filter (fun j => (gateAt C j).op = GateOp.and)
  let Wc : Fin n → Finset ℕ := fun c => (JA.biUnion (V c)).filter (fun w => w < n + L)
  let BigW : Finset ℕ := (Finset.range (n + L)).filter (fun w => 2 ≤ (R n C w).card)
  let Bc : Fin n → Finset ℕ := fun c => BigW.filter (fun w => 2 ≤ (Fk n G C k c w).card)
  let JO : Finset ℕ := (Finset.range L).filter (fun i => 2 ≤ (R n C (n + i)).card)
  have step1 : T ⊆ Finset.univ.biUnion
      (fun c => ((Wc c).biUnion (Fk n G C k c)).image (fun l => s(c, l))) := by
    intro e he
    obtain ⟨u, v, rfl, j, ho, F, hF, hu, hv, hcl⟩ := hT e he
    obtain ⟨a, ha, b, hb, hlt, c, hcR, hcard, hcase⟩ :=
      stark n G h4 C hM k j j.isLt ho.2.1 u v ho F hF hu hv hcl
    have hmemW : b ∈ Wc c := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨j, ?_, ?_⟩, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, ho.2.1⟩
      · have hcS : c ∈ S j := Finset.mem_biUnion.mpr
          ⟨a, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ha, hcard⟩, hcR⟩
        simp only [V, if_pos hcS]
        exact List.mem_toFinset.mpr hb
      · have := j.isLt
        omega
    refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, ?_⟩
    rcases hcase with ⟨huc, hv'⟩ | ⟨hvc, hu'⟩
    · exact Finset.mem_image.mpr ⟨v, Finset.mem_biUnion.mpr ⟨b, hmemW, hv'⟩, by rw [huc]⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_biUnion.mpr ⟨b, hmemW, hu'⟩,
        by rw [hvc]; exact Sym2.eq_swap⟩
  have step2 : T.card ≤ ∑ c : Fin n, ((Wc c).card + (Bc c).card) := by
    refine (Finset.card_le_card step1).trans (Finset.card_biUnion_le.trans ?_)
    refine Finset.sum_le_sum (fun c _ => Finset.card_image_le.trans ?_)
    refine (count_abs (Fk n G C k c) (fun m hm => Fk_split n G C hM k c m hm) (n + L) (Wc c)
      (fun w hw => (Finset.mem_filter.mp hw).2)).trans ?_
    refine Nat.add_le_add_left (Finset.card_le_card ?_) _
    intro w hw
    obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hw1, hw2.trans (Finset.card_le_card (Fk_sub n G C k c w))⟩, hw2⟩
  have step3 : ∑ c : Fin n, (Wc c).card ≤ JA.card * (4 * (k + 1)) := by
    have h1 : ∀ c, (Wc c).card ≤ ∑ j ∈ JA, (V c j).card := fun c =>
      (Finset.card_filter_le _ _).trans Finset.card_biUnion_le
    have h2 : ∀ j ∈ JA, ∑ c : Fin n, (V c j).card ≤ 4 * (k + 1) := by
      intro j hj
      have hjL : j < L := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hin2 : (gateAt C j).inputs.toFinset.card ≤ 2 :=
        (List.toFinset_card_le _).trans (gate_mono2 C hM j hjL).2
      have hS : (S j).card ≤ 2 * (k + 1) := by
        refine Finset.card_biUnion_le.trans ?_
        refine (Finset.sum_le_card_nsmul _ _ (k + 1)
          (fun a ha => (Finset.mem_filter.mp ha).2)).trans ?_
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hin2)
      have h3 : ∑ c : Fin n, (V c j).card =
          (S j).card * (gateAt C j).inputs.toFinset.card := by
        have e : ∀ c, (V c j).card =
            if c ∈ S j then (gateAt C j).inputs.toFinset.card else 0 := by
          intro c
          simp only [V]
          split_ifs <;> simp
        simp only [e]
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
      rw [h3]
      calc (S j).card * (gateAt C j).inputs.toFinset.card ≤ (2 * (k + 1)) * 2 :=
            Nat.mul_le_mul hS hin2
        _ = 4 * (k + 1) := by ring
    calc ∑ c : Fin n, (Wc c).card ≤ ∑ c : Fin n, ∑ j ∈ JA, (V c j).card :=
          Finset.sum_le_sum (fun c _ => h1 c)
      _ = ∑ j ∈ JA, ∑ c : Fin n, (V c j).card := Finset.sum_comm
      _ ≤ ∑ j ∈ JA, 4 * (k + 1) := Finset.sum_le_sum h2
      _ = JA.card * (4 * (k + 1)) := by rw [Finset.sum_const, smul_eq_mul]
  have step4 : ∑ c : Fin n, (Bc c).card ≤ BigW.card * ((2 * k + 1).choose 2 + 1) := by
    have e1 : ∀ c, (Bc c).card =
        ∑ w ∈ BigW, if 2 ≤ (Fk n G C k c w).card then 1 else 0 :=
      fun c => Finset.card_filter _ _
    have e2 : ∀ w, (Finset.univ.filter (fun c : Fin n => 2 ≤ (Fk n G C k c w).card)).card =
        ∑ c : Fin n, if 2 ≤ (Fk n G C k c w).card then 1 else 0 :=
      fun w => Finset.card_filter _ _
    simp only [e1]
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum (fun w _ => (e2 w).symm.le.trans (centers n G h4 C k w))).trans ?_
    rw [Finset.sum_const, smul_eq_mul]
  have step4b : BigW.card ≤ JO.card := by
    have h3 : BigW ⊆ JO.image (fun i => n + i) := by
      intro w hw
      have e2 := (Finset.mem_filter.mp hw).2
      have hnw : ¬ w < n := fun hlt => by
        have := R_card_input n C w hlt
        omega
      obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
      obtain ⟨x, hx, _⟩ := Finset.one_lt_card.mp e2
      obtain ⟨hi, _, _⟩ := R_gate n C i x hx
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, e2⟩, rfl⟩
    exact (Finset.card_le_card h3).trans Finset.card_image_le
  have step5 : JA.card + JO.card ≤ L := by
    have hd : Disjoint JA JO := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      have e1 := (Finset.mem_filter.mp hj).2
      have e2 := (Finset.mem_filter.mp hj').2
      obtain ⟨x, hx, _⟩ := Finset.one_lt_card.mp e2
      obtain ⟨_, hor, _⟩ := R_gate n C j x hx
      rw [e1] at hor
      cases hor
    have h1 : (JA ∪ JO).card = JA.card + JO.card := Finset.card_union_of_disjoint hd
    have h2 : JA ∪ JO ⊆ Finset.range L :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have h3 := Finset.card_le_card h2
    rw [Finset.card_range] at h3
    omega
  have hsum : ∑ c : Fin n, ((Wc c).card + (Bc c).card) =
      ∑ c : Fin n, (Wc c).card + ∑ c : Fin n, (Bc c).card := Finset.sum_add_distrib
  have n1 := num1 k
  have n2 := num2 k
  have m1 : JA.card * (4 * (k + 1)) ≤ JA.card * 2 ^ (k + 2) := Nat.mul_le_mul_left _ n1
  have m2 : BigW.card * ((2 * k + 1).choose 2 + 1) ≤ JO.card * 2 ^ (k + 2) :=
    Nat.mul_le_mul step4b n2
  have m3 : (JA.card + JO.card) * 2 ^ (k + 2) ≤ L * 2 ^ (k + 2) := Nat.mul_le_mul_right _ step5
  have m4 : (JA.card + JO.card) * 2 ^ (k + 2) = JA.card * 2 ^ (k + 2) + JO.card * 2 ^ (k + 2) :=
    Nat.add_mul _ _ _
  have m5 : L * 2 ^ (k + 2) = 2 ^ (k + 2) * C.gates.length := Nat.mul_comm _ _
  omega

end PEqualNP.Outside.L_meta_2660

theorem PEqualNP.Outside.L_meta_2660 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1) (x5 : x2.Walk x4 x4), x5.IsCycle → (5 : ℕ) ≤ x5.length) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → ∀ (x7 : ℕ), ∀ x8 ⊆ x2.edgeFinset, (∀ x10 ∈ x8, ∃ (x12 : Fin x1) (x13 : Fin x1), x10 = s(x12, x13) ∧ ∃ (x14 : Fin x5.gates.length), PEqualNP.EdgeOwnership.Owns x1 x5 (↑x14) x12 x13 ∧ ∃ (x15 : Finset (Fin x1)), x15.card ≤ x7 ∧ x12 ∉ x15 ∧ x13 ∉ x15 ∧ ∀ x16 ∉ x15, ∀ x18 ∉ x15, PEqualNP.EdgeOwnership.gateVal x1 x5 (↑x14) (PEqualNP.EdgeOwnership.pairInput x16 x18) = Bool.true → x2.Adj x16 x18) → x8.card ≤ (2 : ℕ) ^ (x7 + (2 : ℕ)) * x5.size := by
  intro n G _x3 hg C hM k S _ hS
  have h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    intro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
    let W : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
    have hW : W.IsCycle := by
      refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [W]⟩
      simp only [W, SimpleGraph.Walk.tail_cons]
      simp [hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hac.symm, hbd]
    have h5 := hg a W hW
    have h4 : W.length = 4 := rfl
    omega
  have hs : C.size = C.gates.length := rfl
  rw [hs]
  exact PEqualNP.Outside.L_meta_2660.keyk n G h4 C hM k S hS

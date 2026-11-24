import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1534

open PEqualNP.CircuitLowerBounds

theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ x =
      Circuit.wires ⟨gs, 0⟩ x ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_snoc, List.length_append, ih, List.length_append]
    simp only [List.length_singleton]
    omega

theorem getD_snoc (L : List Bool) (b : Bool) (i : ℕ) :
    (L ++ [b]).getD i false =
      if i < L.length then L.getD i false else if i = L.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < L.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1]
    by_cases h2 : i = L.length
    · rw [if_pos h2]; subst h2; simp
    · rw [if_neg h2, List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega)]
      rfl

theorem getD_ofFn (n : ℕ) (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [dif_pos h, List.getElem?_eq_getElem (by simpa using h)]; simp
  · rw [dif_neg h, List.getElem?_eq_none (by simpa using h)]; rfl

theorem wires_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (Circuit.wires ⟨gs, 0⟩ x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_snoc, getD_snoc, if_pos (by rw [wires_length]; omega), ih]

def W (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false

def val (n : ℕ) (gs : List Gate) (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => W n gs x i)

def Norm (n : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  (Finset.univ.filter (fun au : Fin n => f (fun auk : Fin n => decide (auk = au)) = true)).card ≤ 1 →
    ∀ ax : Fin n → Bool, f ax = decide (∃ av : Fin n, f (fun avk : Fin n => decide (avk = av)) = true ∧ ax av = true)

theorem W_snoc (n : ℕ) (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    W n (gs ++ [g]) x i =
      if i < n + gs.length then W n gs x i else if i = n + gs.length then val n gs g x else false := by
  simp only [W, val]
  rw [wires_snoc, getD_snoc, wires_length, List.length_ofFn]

theorem W_input (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (v : Fin n) :
    W n gs x v.val = x v := by
  simp only [W]
  rw [wires_input _ _ _ (by simp), getD_ofFn, dif_pos v.isLt]

theorem W_nil (n : ℕ) (x : Fin n → Bool) (i : ℕ) :
    W n [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  simp only [W, Circuit.wires, List.foldl_nil]
  exact getD_ofFn n x i

theorem eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : ℕ → Bool)
    (hab : ∀ i, a i = true → b i = true) :
    g.op.eval (g.inputs.map a) = true → g.op.eval (g.inputs.map b) = true := by
  rcases hop with h | h
  · rw [h]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro H y hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact hab i (H _ ⟨i, hi, rfl⟩)
  · rw [h]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨y, ⟨i, hi, rfl⟩, hy⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hab i hy⟩

theorem core (n : ℕ) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ gates2 : List Gate, gates2.length = gates.length ∧
      (∀ g2 ∈ gates2, (g2.op = GateOp.and ∨ g2.op = GateOp.or) ∧ g2.inputs.length ≤ 2) ∧
      (∀ (x : Fin n → Bool) (i : ℕ), W n gates2 x i = true → W n gates x i = true) ∧
      (∀ (x : Fin n → Bool) (i : ℕ) (v : Fin n),
          W n gates (fun u : Fin n => decide (u = v)) i = true → x v = true →
            W n gates2 x i = true) ∧
      (∀ ak : ℕ, ak < gates2.length → Norm n (fun y => W n gates2 y (n + ak))) := by
  induction gates using List.reverseRecOn with
  | nil =>
    refine ⟨[], rfl, ?_, ?_, ?_, ?_⟩
    · intro g2 h; simp at h
    · intro x i h; exact h
    · intro x i v h hxv
      rw [W_nil] at h ⊢
      by_cases hi : i < n
      · rw [dif_pos hi] at h ⊢
        have hiv : (⟨i, hi⟩ : Fin n) = v := by simpa using h
        rw [hiv]; exact hxv
      · rw [dif_neg hi] at h; exact absurd h (by decide)
    · intro ak h; simp at h
  | append_singleton gs g ih =>
    have hgs : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' h => hg g' (List.mem_append_left _ h)
    have hgg := hg g (by simp)
    obtain ⟨gs2, hlen, hop, ha, hb, hn⟩ := ih hgs
    have hA : ∀ x : Fin n → Bool, val n gs2 g x = true → val n gs g x = true :=
      fun x => eval_mono g hgg.1 _ _ (fun i => ha x i)
    have hB : ∀ (x : Fin n → Bool) (v : Fin n),
        val n gs g (fun u : Fin n => decide (u = v)) = true → x v = true →
          val n gs2 g x = true :=
      fun x v h hxv => eval_mono g hgg.1 _ _ (fun i hi => hb x i v hi hxv) h
    have hex : ∃ g2 : Gate, ((g2.op = GateOp.and ∨ g2.op = GateOp.or) ∧ g2.inputs.length ≤ 2) ∧
        (∀ x : Fin n → Bool, val n gs2 g2 x = true → val n gs g x = true) ∧
        (∀ (x : Fin n → Bool) (v : Fin n),
          val n gs g (fun u : Fin n => decide (u = v)) = true → x v = true →
            val n gs2 g2 x = true) ∧
        Norm n (val n gs2 g2) := by
      by_cases h0 : ∀ v : Fin n, ¬ (val n gs g (fun u : Fin n => decide (u = v)) = true)
      · refine ⟨⟨GateOp.or, []⟩, ⟨Or.inr rfl, by simp⟩, ?_, ?_, ?_⟩
        · intro x h; simp [val, GateOp.eval] at h
        · intro x v h; exact absurd h (h0 v)
        · intro _ ax; simp [val, GateOp.eval]
      · by_cases h1 : ∃ v : Fin n, ∀ u : Fin n,
            val n gs g (fun u' : Fin n => decide (u' = u)) = true ↔ u = v
        · obtain ⟨v, hv⟩ := h1
          have hval : ∀ y : Fin n → Bool, val n gs2 ⟨GateOp.or, [v.val]⟩ y = y v := by
            intro y
            simp only [val, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              id_eq, Bool.or_false]
            exact W_input n gs2 y v
          refine ⟨⟨GateOp.or, [v.val]⟩, ⟨Or.inr rfl, by simp⟩, ?_, ?_, ?_⟩
          · intro x h
            rw [hval] at h
            exact hA x (hB x v ((hv v).mpr rfl) h)
          · intro x u h hxu
            rw [hval]
            have huv := (hv u).mp h
            rw [← huv]; exact hxu
          · intro _ ax
            simp only [hval]
            cases hc : ax v with
            | true =>
              symm
              rw [decide_eq_true_eq]
              exact ⟨v, by simp, hc⟩
            | false =>
              symm
              rw [decide_eq_false_iff_not]
              rintro ⟨av, h1, h2⟩
              have hvav : v = av := by simpa using h1
              subst hvav
              rw [hc] at h2
              exact absurd h2 (by decide)
        · refine ⟨g, hgg, hA, hB, ?_⟩
          intro hcard
          exfalso
          obtain ⟨v, hv⟩ := not_forall.mp h0
          have hv := not_not.mp hv
          obtain ⟨u, hu⟩ := not_forall.mp (not_exists.mp h1 v)
          have huv : u ≠ v := by
            intro h
            apply hu
            rw [h]
            exact ⟨fun _ => rfl, fun _ => hv⟩
          have hu' : val n gs g (fun u' : Fin n => decide (u' = u)) = true := by
            by_contra hc
            apply hu
            exact ⟨fun h => absurd h hc, fun h => absurd h huv⟩
          have m1 : v ∈ Finset.univ.filter
              (fun au : Fin n => val n gs2 g (fun auk : Fin n => decide (auk = au)) = true) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hB _ v hv (by simp)
          have m2 : u ∈ Finset.univ.filter
              (fun au : Fin n => val n gs2 g (fun auk : Fin n => decide (auk = au)) = true) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hB _ u hu' (by simp)
          exact huv (Finset.card_le_one.mp hcard u m2 v m1)
    obtain ⟨g2, hop2, hA2, hB2, hN2⟩ := hex
    refine ⟨gs2 ++ [g2], by simp [hlen], ?_, ?_, ?_, ?_⟩
    · intro g' hg'
      rcases List.mem_append.mp hg' with h | h
      · exact hop g' h
      · rw [List.mem_singleton.mp h]; exact hop2
    · intro x i h
      rw [W_snoc] at h ⊢
      rw [hlen] at h
      by_cases h1 : i < n + gs.length
      · rw [if_pos h1] at h ⊢; exact ha x i h
      · by_cases h2 : i = n + gs.length
        · rw [if_neg h1, if_pos h2] at h ⊢; exact hA2 x h
        · rw [if_neg h1, if_neg h2] at h; exact absurd h (by decide)
    · intro x i v h hxv
      rw [W_snoc] at h ⊢
      rw [hlen]
      by_cases h1 : i < n + gs.length
      · rw [if_pos h1] at h ⊢; exact hb x i v h hxv
      · by_cases h2 : i = n + gs.length
        · rw [if_neg h1, if_pos h2] at h ⊢; exact hB2 x v h hxv
        · rw [if_neg h1, if_neg h2] at h; exact absurd h (by decide)
    · intro ak hak
      rw [List.length_append, List.length_singleton] at hak
      by_cases h1 : ak < gs2.length
      · have key : (fun y : Fin n → Bool => W n (gs2 ++ [g2]) y (n + ak)) =
            (fun y : Fin n → Bool => W n gs2 y (n + ak)) := by
          funext y
          rw [W_snoc, if_pos (by omega)]
        rw [key]; exact hn ak h1
      · have key : (fun y : Fin n → Bool => W n (gs2 ++ [g2]) y (n + ak)) = val n gs2 g2 := by
          funext y
          rw [W_snoc, if_neg (by omega), if_pos (by omega)]
        rw [key]; exact hN2

end PEqualNP.Outside.L_meta_1534

theorem PEqualNP.Outside.L_meta_1534 : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (S : Fin m → Finset (Fin n)) (D : Set (Fin n → Bool)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ v : Fin n, (fun vk : Fin n => decide (vk = v)) ∈ D) → (∀ (w : Fin m) (x : Fin n → Bool), x ∈ D → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (out w) false = decide (∃ v0 ∈ S w, x v0 = true)) → ∃ gates2 : List PEqualNP.CircuitLowerBounds.Gate, gates2.length ≤ gates.length ∧ (∀ g2 ∈ gates2, (g2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g2.inputs.length ≤ 2) ∧ (∀ ak : ℕ, ak < gates2.length → (Finset.univ.filter (fun au : Fin n => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn (fun auk : Fin n => decide (auk = au)))).getD (n + ak) false = true)).card ≤ 1 → ∀ ax : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn ax)).getD (n + ak) false = decide (∃ av : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn (fun avk : Fin n => decide (avk = av)))).getD (n + ak) false = true ∧ ax av = true)) ∧ ∀ (w2 : Fin m) (x2 : Fin n → Bool), x2 ∈ D → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn x2)).getD (out w2) false = decide (∃ v2 ∈ S w2, x2 v2 = true) := by
  intro n m gates out S D hg hD hout
  obtain ⟨gates2, hlen, hop, ha, hb, hn⟩ := PEqualNP.Outside.L_meta_1534.core n gates hg
  refine ⟨gates2, le_of_eq hlen, hop, hn, ?_⟩
  intro w2 x2 hx2
  have h := hout w2 x2 hx2
  by_cases hE : ∃ v ∈ S w2, x2 v = true
  · obtain ⟨v, hv, hxv⟩ := hE
    have h1 := hout w2 _ (hD v)
    have h2 : ∃ v0 ∈ S w2, (fun vk : Fin n => decide (vk = v)) v0 = true := ⟨v, hv, by simp⟩
    rw [decide_eq_true h2] at h1
    have h3 := hb x2 (out w2) v h1 hxv
    rw [decide_eq_true ⟨v, hv, hxv⟩]
    exact h3
  · rw [decide_eq_false hE] at h ⊢
    by_contra hne
    have h4 := ha x2 (out w2) (eq_true_of_ne_false hne)
    exact absurd (h.symm.trans h4) (by decide)

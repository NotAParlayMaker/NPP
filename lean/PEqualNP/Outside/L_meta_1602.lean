import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1602

theorem wires_snoc (gs : List Gate) (g : Gate) (o o2 : ℕ) (l : List Bool) :
    Circuit.wires ⟨gs ++ [g], o⟩ l = Circuit.wires ⟨gs, o2⟩ l ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, o2⟩ l).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (o : ℕ) (l : List Bool) :
    (Circuit.wires ⟨gs, o⟩ l).length = l.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_snoc gs g o o, List.length_append, ih]
    simp
    omega

theorem foldl_prefix (r : List Gate) : ∀ l : List Bool,
    l <+: r.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l := by
  induction r with
  | nil => intro l; simp
  | cons g r ih =>
    intro l
    rw [List.foldl_cons]
    exact (List.prefix_append l _).trans (ih _)

theorem wires_prefix (gs r : List Gate) (o o2 : ℕ) (l : List Bool) :
    Circuit.wires ⟨gs, o⟩ l <+: Circuit.wires ⟨gs ++ r, o2⟩ l := by
  simp only [Circuit.wires, List.foldl_append]
  exact foldl_prefix r _

theorem getD_prefix (l1 l2 : List Bool) (h : l1 <+: l2) (i : ℕ) (hi : i < l1.length) :
    l2.getD i false = l1.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem all_mono (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i = true → f2 i = true) (l : List ℕ)
    (h1 : (l.map f1).all id = true) : (l.map f2).all id = true := by
  simp only [List.all_eq_true, List.mem_map] at *
  rintro b ⟨a, ha, rfl⟩
  exact h a (h1 _ ⟨a, ha, rfl⟩)

theorem any_mono (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i = true → f2 i = true) (l : List ℕ)
    (h1 : (l.map f1).any id = true) : (l.map f2).any id = true := by
  simp only [List.any_eq_true, List.mem_map] at *
  obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := h1
  exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩

theorem wlen (n : ℕ) (gs : List Gate) (z : Fin n → Bool) :
    (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).length = n + gs.length := by
  rw [wires_length]
  simp

-- the value of the newest wire
theorem hval (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool) :
    (Circuit.wires ⟨gs ++ [g], 0⟩ (List.ofFn z)).getD (n + gs.length) false =
      g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false) := by
  have hlen := wlen n gs z
  rw [wires_snoc gs g 0 0, List.getD_append_right _ _ _ _ (by omega), hlen]
  simp

-- older wires keep their value
theorem hold (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool) (w : ℕ)
    (hw : w < n + gs.length) :
    (Circuit.wires ⟨gs ++ [g], 0⟩ (List.ofFn z)).getD w false =
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD w false := by
  have hlen := wlen n gs z
  rw [wires_snoc gs g 0 0, List.getD_append _ _ _ _ (by omega)]

-- wires past the end read false
theorem hbig (n : ℕ) (gs : List Gate) (z : Fin n → Bool) (w : ℕ) (hw : n + gs.length ≤ w) :
    (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD w false = false := by
  have hlen := wlen n gs z
  have h2 : (Circuit.wires ⟨gs, 0⟩ (List.ofFn z))[w]? = none :=
    List.getElem?_eq_none (by omega)
  simp [List.getD_eq_getElem?_getD, h2]

-- every wire of an AND/OR list is monotone in the input
theorem mono (n : ℕ) : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (w : ℕ) (x y : Fin n → Bool), (∀ v : Fin n, x v = true → y v = true) →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD w false = true →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD w false = true := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ w x y hxy h
    simp only [Circuit.wires, List.foldl_nil] at h ⊢
    by_cases hw : w < n
    · simp [List.getD_eq_getElem?_getD, hw] at h ⊢
      exact hxy _ h
    · simp [List.getD_eq_getElem?_getD, hw] at h
  | append_singleton gs g ih =>
    intro hops w x y hxy h
    have ih' := ih (fun g' hg' => hops g' (by simp [hg']))
    rcases lt_trichotomy w (n + gs.length) with hw | hw | hw
    · rw [hold n gs g _ w hw] at h ⊢
      exact ih' w x y hxy h
    · subst hw
      rw [hval] at h ⊢
      rcases hops g (by simp) with ho | ho
      · rw [ho] at h ⊢
        exact all_mono _ _ (fun i hi => ih' i x y hxy hi) _ h
      · rw [ho] at h ⊢
        exact any_mono _ _ (fun i hi => ih' i x y hxy hi) _ h
    · rw [hbig n (gs ++ [g]) x w
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)] at h
      exact absurd h (by decide)

-- a wire true at an independent input is true at one of its single points
theorem single (n : ℕ) (H : SimpleGraph (Fin n)) (e0 : Fin n) (L : List Gate)
    (hops : ∀ g ∈ L, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hand : ∀ k : ℕ, k < L.length → (L.getD k ⟨GateOp.or, []⟩).op = GateOp.and →
      ∀ e w : Fin n, ¬ H.Adj e w →
        (Circuit.wires ⟨L, 0⟩
          (List.ofFn (PEqualNP.EdgeOwnership.pairInput e w))).getD (n + k) false = false) :
    ∀ (gs rest : List Gate), L = gs ++ rest →
    ∀ (w : ℕ) (x : Fin n → Bool),
      (∀ u v : Fin n, H.Adj u v → x u = true → x v = true → False) →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD w false = true →
      ∃ i : Fin n, x i = true ∧
        (Circuit.wires ⟨gs, 0⟩
          (List.ofFn (PEqualNP.EdgeOwnership.pairInput i i))).getD w false = true := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro rest _ w x hx h
    simp only [Circuit.wires, List.foldl_nil] at h ⊢
    by_cases hw : w < n
    · have hx' : x ⟨w, hw⟩ = true := by
        simpa [List.getD_eq_getElem?_getD, hw] using h
      refine ⟨⟨w, hw⟩, hx', ?_⟩
      simp [List.getD_eq_getElem?_getD, hw, PEqualNP.EdgeOwnership.pairInput]
    · simp [List.getD_eq_getElem?_getD, hw] at h
  | append_singleton gs g ih =>
    intro rest hg w x hx h
    have ih' := ih (g :: rest) (by simp [hg])
    have hopsgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => (hops g' (by rw [hg]; simp [hg'])).1
    have hgm : g ∈ L := by rw [hg]; simp
    rcases lt_trichotomy w (n + gs.length) with hw | hw | hw
    · rw [hold n gs g _ w hw] at h
      obtain ⟨i, hi, hi2⟩ := ih' w x hx h
      exact ⟨i, hi, by rw [hold n gs g _ w hw]; exact hi2⟩
    · subst hw
      rw [hval] at h
      have hfull : ∀ z : Fin n → Bool,
          (Circuit.wires ⟨L, 0⟩ (List.ofFn z)).getD (n + gs.length) false =
          g.op.eval (g.inputs.map fun i =>
            (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false) := by
        intro z
        rw [← hval n gs g z, hg]
        exact getD_prefix _ _ (wires_prefix (gs ++ [g]) rest 0 0 _) _
          (by rw [wires_length]
              simp only [List.length_ofFn, List.length_append, List.length_cons,
                List.length_nil]
              omega)
      have hk : gs.length < L.length := by rw [hg]; simp
      have hgetq : L[gs.length]? = some g := by rw [hg]; simp
      have hget : L.getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD, hgetq]
      rcases (hops g hgm).1 with ho | ho
      · rw [ho] at h
        have hall : ∀ a ∈ g.inputs,
            (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD a false = true := by
          intro a ha
          have h' : (g.inputs.map fun i =>
              (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false).all id = true := h
          rw [List.all_eq_true] at h'
          exact h' _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
        have key : ∀ l : List ℕ, l.length ≤ 2 →
            (∀ a ∈ l, (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD a false = true) →
            ∃ e1 e2 : Fin n, ¬ H.Adj e1 e2 ∧ ∀ a ∈ l,
              (Circuit.wires ⟨gs, 0⟩
                (List.ofFn (PEqualNP.EdgeOwnership.pairInput e1 e2))).getD a false = true := by
          intro l hl hal
          rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
          · exact ⟨e0, e0, fun hh => H.ne_of_adj hh rfl, by intro a ha; simp at ha⟩
          · obtain ⟨i, hi, hi2⟩ := ih' a x hx (hal a (by simp))
            refine ⟨i, i, fun hh => H.ne_of_adj hh rfl, ?_⟩
            intro a' ha'
            have haa : a' = a := by simpa using ha'
            rw [haa]
            exact hi2
          · obtain ⟨i, hi, hi2⟩ := ih' a x hx (hal a (by simp))
            obtain ⟨j, hj, hj2⟩ := ih' b x hx (hal b (by simp))
            refine ⟨i, j, fun hh => hx i j hh hi hj, ?_⟩
            intro a' ha'
            have haa : a' = a ∨ a' = b := by simpa using ha'
            rcases haa with haa | haa
            · rw [haa]
              refine mono n gs hopsgs _ _ _ ?_ hi2
              intro v hv
              have hv' : v = i := by simpa [PEqualNP.EdgeOwnership.pairInput] using hv
              simp [PEqualNP.EdgeOwnership.pairInput, hv']
            · rw [haa]
              refine mono n gs hopsgs _ _ _ ?_ hj2
              intro v hv
              have hv' : v = j := by simpa [PEqualNP.EdgeOwnership.pairInput] using hv
              simp [PEqualNP.EdgeOwnership.pairInput, hv']
          · simp only [List.length_cons] at hl
            omega
        obtain ⟨e1, e2, hee, hE⟩ := key g.inputs (hops g hgm).2 hall
        have hf := hand gs.length hk (by rw [hget]; exact ho) e1 e2 hee
        rw [hfull, ho] at hf
        have ht : (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩
            (List.ofFn (PEqualNP.EdgeOwnership.pairInput e1 e2))).getD i false).all id
            = true := by
          rw [List.all_eq_true]
          intro b hb
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
          exact hE a ha
        exact absurd (ht.symm.trans hf) (by decide)
      · rw [ho] at h
        have h' : (g.inputs.map fun i =>
            (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false).any id = true := h
        rw [List.any_eq_true] at h'
        obtain ⟨b, hb, hb2⟩ := h'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        obtain ⟨i, hi, hi2⟩ := ih' a x hx hb2
        refine ⟨i, hi, ?_⟩
        rw [hval, ho]
        show (g.inputs.map fun i' => (Circuit.wires ⟨gs, 0⟩
            (List.ofFn (PEqualNP.EdgeOwnership.pairInput i i))).getD i' false).any id = true
        rw [List.any_eq_true]
        exact ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, hi2⟩
    · rw [hbig n (gs ++ [g]) x w
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)] at h
      exact absurd h (by decide)

end PEqualNP.Outside.L_meta_1602

theorem PEqualNP.Outside.L_meta_1602 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
  intro hyp m H inst h4 D hmono hfun hand
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨T, hT, hc⟩ := hyp 0 H h4 [] 0 (by simp)
      (by intro x; simp [Circuit.eval, Circuit.wires]) (fun i => i.elim0)
    simp only [List.length_nil] at hc
    exact ⟨T, hT, by omega⟩
  · have e0 : Fin m := ⟨0, hm⟩
    have hops : ∀ g ∈ D.gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hmono g hg
      exact ⟨h1, h2⟩
    have hand' : ∀ k : ℕ, k < D.gates.length →
        (D.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.and →
        ∀ e w : Fin m, ¬ H.Adj e w →
          (Circuit.wires ⟨D.gates, 0⟩
            (List.ofFn (PEqualNP.EdgeOwnership.pairInput e w))).getD (m + k) false = false :=
      fun k hk hop e w hew => hand k hk hop e w hew
    have hres := hyp m H h4 D.gates D.output hops
      (by
        intro x
        have h1 : Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x) =
            PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ x := congrFun hfun x
        rw [h1]
        simp [PEqualNP.MetaComplexity.NestedCover.graphFun])
      (by
        intro i x hi hw
        by_contra hne
        have hx : ∀ u v : Fin m, H.Adj u v → x u = true → x v = true → False :=
          fun u v huv hu hv => hne ⟨u, v, huv, hu, hv⟩
        obtain ⟨t, ht, ht2⟩ := PEqualNP.Outside.L_meta_1602.single m H e0 D.gates hops hand'
          D.gates [] (by simp) (m + (i : ℕ)) x hx hw
        have hop : (D.gates.getD (i : ℕ) ⟨GateOp.or, []⟩).op = GateOp.and := by
          rw [List.getD_eq_getElem _ _ i.2]
          exact hi
        have hf := hand' (i : ℕ) i.2 hop t t (fun hh => H.ne_of_adj hh rfl)
        exact absurd (ht2.symm.trans hf) (by decide))
    exact hres

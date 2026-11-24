import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1456

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def V (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gates.foldl stp (List.ofFn x)).getD i false

lemma getD_lt (w : List Bool) (v : Bool) (i : ℕ) (h : i < w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  first
    | exact List.getD_append _ _ _ _ h
    | simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_last (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  first
    | exact List.getD_eq_default _ _ h
    | simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma len_fold (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stp w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp only [stp, List.length_append, List.length_cons, List.length_nil]
    omega

lemma pre_fold (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (gs.foldl stp w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have h1 : i < (stp w g).length := by
      simp only [stp, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.foldl_cons, ih (stp w g) i h1]
    exact getD_lt w _ i hi

lemma gate_fold (gs : List Gate) :
    ∀ (w : List Bool) (k : ℕ) (hk : k < gs.length),
      (gs.foldl stp w).getD (w.length + k) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i => ((gs.take k).foldl stp w).getD i false) := by
  induction gs with
  | nil => intro w k hk; simp at hk
  | cons g gs ih =>
    intro w k hk
    cases k with
    | zero =>
      have h1 : w.length < (stp w g).length := by
        simp only [stp, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, Nat.add_zero, pre_fold gs (stp w g) w.length h1]
      simp only [stp, List.take_zero, List.foldl_nil, List.getElem_cons_zero]
      exact getD_last w _
    | succ k =>
      have hk' : k < gs.length := by
        simp only [List.length_cons] at hk
        omega
      have h := ih (stp w g) k hk'
      have hl : (stp w g).length + k = w.length + (k + 1) := by
        simp only [stp, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hl] at h
      simpa only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ] using h

lemma V_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    V gates x i = x ⟨i, hi⟩ := by
  unfold V
  rw [pre_fold gates (List.ofFn x) i (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma V_ge (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : n + gates.length ≤ i) :
    V gates x i = false := by
  unfold V
  apply getD_big
  rw [len_fold, List.length_ofFn]
  exact hi

lemma V_gate (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length) :
    V gates x (n + k) =
      (gates[k]).op.eval ((gates[k]).inputs.map fun i => if i < n + k then V gates x i else false) := by
  unfold V
  have h := gate_fold gates (List.ofFn x) k hk
  rw [List.length_ofFn] at h
  rw [h]
  have hlen : ((gates.take k).foldl stp (List.ofFn x)).length = n + k := by
    rw [len_fold, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hsplit : gates.foldl stp (List.ofFn x) =
      (gates.drop k).foldl stp ((gates.take k).foldl stp (List.ofFn x)) := by
    rw [← List.foldl_append, List.take_append_drop]
  have hmap : ((gates[k]).inputs.map fun i => ((gates.take k).foldl stp (List.ofFn x)).getD i false) =
      (gates[k]).inputs.map fun i =>
        if i < n + k then (gates.foldl stp (List.ofFn x)).getD i false else false := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < n + k
    · rw [if_pos hi, hsplit,
        pre_fold (gates.drop k) ((gates.take k).foldl stp (List.ofFn x)) i (by rw [hlen]; exact hi)]
    · rw [if_neg hi]
      exact getD_big _ i (by rw [hlen]; omega)
  rw [hmap]

lemma and_map {α : Type} (l : List α) (f : α → Bool) :
    GateOp.eval GateOp.and (l.map f) = true ↔ ∀ a ∈ l, f a = true := by
  simp [GateOp.eval]

lemma or_map {α : Type} (l : List α) (f : α → Bool) :
    GateOp.eval GateOp.or (l.map f) = true ↔ ∃ a ∈ l, f a = true := by
  simp [GateOp.eval]

lemma three_in_two (l : List ℕ) (hl : l.length ≤ 2) (a b c : ℕ)
    (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l) : a = b ∨ a = c ∨ b = c := by
  match l, hl with
  | [], _ => simp at ha
  | [u], _ =>
    simp only [List.mem_singleton] at ha hb
    left
    rw [ha, hb]
  | [u, v], _ =>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha hb hc
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> simp
  | _ :: _ :: _ :: _, h =>
    simp only [List.length_cons] at h
    omega

-- the top input off L: every wire that is true somewhere off L is true there
lemma mono_top {n : ℕ} (gates : List Gate) (L : Finset (Fin n)) (j : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ (k : ℕ) (hk : k < gates.length), (gates[k]).op = GateOp.not → k = j)
    (hN : V gates (fun v : Fin n => decide (v ∉ L)) (n + j) = true) :
    ∀ (i : ℕ) (x : Fin n → Bool), (∀ v ∈ L, x v = false) → V gates x i = true →
      V gates (fun v : Fin n => decide (v ∉ L)) i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro x hx hv
    by_cases hin : i < n
    · rw [V_input gates x i hin] at hv
      rw [V_input gates _ i hin]
      simp only [decide_eq_true_eq]
      intro hmem
      rw [hx _ hmem] at hv
      exact Bool.noConfusion hv
    · by_cases hlen : i < n + gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gates.length := by omega
        rw [V_gate gates x k hk] at hv
        rw [V_gate gates _ k hk]
        rcases (hops (gates[k]) (List.getElem_mem hk)).1 with h | h | h
        · rw [h] at hv ⊢
          rw [and_map] at hv ⊢
          intro a ha
          have h2 := hv a ha
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at h2 ⊢
            exact ih a hlt x hx h2
          · rw [if_neg hlt] at h2
            exact Bool.noConfusion h2
        · rw [h] at hv ⊢
          rw [or_map] at hv ⊢
          obtain ⟨a, ha, h2⟩ := hv
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at h2
            exact ⟨a, ha, by rw [if_pos hlt]; exact ih a hlt x hx h2⟩
          · rw [if_neg hlt] at h2
            exact Bool.noConfusion h2
        · have hkj := hnot k hk h
          rw [← V_gate gates _ k hk, hkj]
          exact hN
      · rw [V_ge gates x i (by omega)] at hv
        exact Bool.noConfusion hv

lemma core {n : ℕ} (q : ℕ) (L : Finset (Fin n)) (hcard : L.card = q + 1) (gates : List Gate)
    (o : ℕ) (j : Fin gates.length)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hout : ∀ x : Fin n → Bool, V gates x o = decide (∃ v ∈ L, x v = true))
    (hN : ∀ x : Fin n → Bool, (∀ v ∈ L, x v = false) → V gates x (n + (j : ℕ)) = true)
    (I : Finset (Fin gates.length))
    (hI : ∀ g : Fin gates.length, ((gates.get g).op = GateOp.or ∧
      (∀ x : Fin n → Bool, (∀ v ∈ L, x v = false) → V gates x (n + (g : ℕ)) = false) ∧
      2 ≤ (L.filter (fun p => V gates (fun v : Fin n => decide (v = p)) (n + (g : ℕ)) = true)).card) →
        g ∈ I) :
    q ≤ I.card := by
  have htop : ∀ v ∈ L, (fun v : Fin n => decide (v ∉ L)) v = false := by
    intro v hv
    simp [hv]
  have hmono := mono_top gates L (j : ℕ) hops
    (fun k hk h => congrArg Fin.val (huniq ⟨k, hk⟩ h)) (hN _ htop)
  -- a wire false off L, as a statement
  have key : ∀ K : ℕ, K ≤ gates.length →
      ∃ (c : Fin n → ℕ) (T : Finset (Fin gates.length)),
        (∀ i : ℕ, i < n + K → (∀ x : Fin n → Bool, (∀ v ∈ L, x v = false) → V gates x i = false) →
          ∀ p ∈ L, ∀ p' ∈ L, V gates (fun v : Fin n => decide (v = p)) i = true →
            V gates (fun v : Fin n => decide (v = p')) i = true → c p = c p') ∧
        (∀ g ∈ T, (g : ℕ) < K ∧ ((gates.get g).op = GateOp.or ∧
          (∀ x : Fin n → Bool, (∀ v ∈ L, x v = false) → V gates x (n + (g : ℕ)) = false) ∧
          2 ≤ (L.filter (fun p => V gates (fun v : Fin n => decide (v = p)) (n + (g : ℕ)) = true)).card)) ∧
        L.card ≤ (L.image c).card + T.card := by
    intro K
    induction K with
    | zero =>
      intro _
      refine ⟨fun p => (p : ℕ), ∅, ?_, ?_, ?_⟩
      · intro i hi _ p _ p' _ h1 h2
        have hi' : i < n := by omega
        rw [V_input gates _ i hi'] at h1 h2
        simp only [decide_eq_true_eq] at h1 h2
        rw [← h1, ← h2]
      · intro g hg
        simp at hg
      · rw [Finset.card_image_of_injective _ Fin.val_injective]
        omega
    | succ K ih =>
      intro hK
      have hk : K < gates.length := by omega
      obtain ⟨c, T, hc, hT, hcount⟩ := ih (by omega)
      by_cases hconst : ∀ p ∈ L, ∀ p' ∈ L,
          V gates (fun v : Fin n => decide (v = p)) (n + K) = true →
          V gates (fun v : Fin n => decide (v = p')) (n + K) = true → c p = c p'
      · refine ⟨c, T, ?_, ?_, hcount⟩
        · intro i hi hF p hp p' hp' h1 h2
          by_cases hiK : i < n + K
          · exact hc i hiK hF p hp p' hp' h1 h2
          · have : i = n + K := by omega
            subst this
            exact hconst p hp p' hp' h1 h2
        · intro g hg
          exact ⟨by have := (hT g hg).1; omega, (hT g hg).2⟩
      · by_cases hF : ∀ x : Fin n → Bool, (∀ v ∈ L, x v = false) → V gates x (n + K) = false
        · -- the gate is false off L and joins two classes: it is an OR gate reading two wires
          push_neg at hconst
          obtain ⟨p, hp, p', hp', h1, h2, hne⟩ := hconst
          have hg1 := V_gate gates (fun v : Fin n => decide (v = p)) K hk
          have hg2 := V_gate gates (fun v : Fin n => decide (v = p')) K hk
          rw [h1] at hg1
          rw [h2] at hg2
          have hlen2 := (hops (gates[K]) (List.getElem_mem hk)).2
          rcases (hops (gates[K]) (List.getElem_mem hk)).1 with h | h | h
          · -- AND: some input is false at the top input off L, so false off L, and holds both points
            exfalso
            have htopF := hF _ htop
            rw [V_gate gates _ K hk, h] at htopF
            have hnotall : ¬ ∀ a ∈ (gates[K]).inputs,
                (if a < n + K then V gates (fun v : Fin n => decide (v ∉ L)) a else false) = true := by
              intro hall
              rw [(and_map _ _).mpr hall] at htopF
              exact Bool.noConfusion htopF
            push_neg at hnotall
            obtain ⟨a, ha, hfa⟩ := hnotall
            rw [h] at hg1 hg2
            have e1 := (and_map _ _).mp hg1.symm a ha
            have e2 := (and_map _ _).mp hg2.symm a ha
            by_cases hlt : a < n + K
            · rw [if_pos hlt] at e1 e2 hfa
              have hFa : ∀ x : Fin n → Bool, (∀ v ∈ L, x v = false) → V gates x a = false := by
                intro x hx
                by_contra hcon
                have ht : V gates x a = true := by
                  cases hval : V gates x a
                  · exact absurd hval hcon
                  · rfl
                exact hfa (hmono a x hx ht)
              exact hne (hc a hlt hFa p hp p' hp' e1 e2)
            · rw [if_neg hlt] at e1
              exact Bool.noConfusion e1
          · -- OR
            rw [h] at hg1 hg2
            obtain ⟨a, ha, ea⟩ := (or_map _ _).mp hg1.symm
            obtain ⟨a', ha', ea'⟩ := (or_map _ _).mp hg2.symm
            have hlt : a < n + K := by
              by_contra hcon
              rw [if_neg hcon] at ea
              exact Bool.noConfusion ea
            have hlt' : a' < n + K := by
              by_contra hcon
              rw [if_neg hcon] at ea'
              exact Bool.noConfusion ea'
            rw [if_pos hlt] at ea
            rw [if_pos hlt'] at ea'
            -- every input wire that exists is false off L
            have hFin : ∀ b ∈ (gates[K]).inputs, b < n + K →
                ∀ x : Fin n → Bool, (∀ v ∈ L, x v = false) → V gates x b = false := by
              intro b hb hbl x hx
              by_contra hcon
              have ht : V gates x b = true := by
                cases hval : V gates x b
                · exact absurd hval hcon
                · rfl
              have hgx := V_gate gates x K hk
              rw [h] at hgx
              have : V gates x (n + K) = true := by
                rw [hgx]
                exact (or_map _ _).mpr ⟨b, hb, by rw [if_pos hbl]; exact ht⟩
              rw [hF x hx] at this
              exact Bool.noConfusion this
            have haa' : a ≠ a' := by
              intro heq
              subst heq
              exact hne (hc a hlt (hFin a ha hlt) p hp p' hp' ea ea')
            -- the class of every point true at the gate is one of the two
            have hcls : ∀ r ∈ L, V gates (fun v : Fin n => decide (v = r)) (n + K) = true →
                c r = c p ∨ c r = c p' := by
              intro r hr hrv
              have hgr := V_gate gates (fun v : Fin n => decide (v = r)) K hk
              rw [hrv, h] at hgr
              obtain ⟨b, hb, eb⟩ := (or_map _ _).mp hgr.symm
              have hbl : b < n + K := by
                by_contra hcon
                rw [if_neg hcon] at eb
                exact Bool.noConfusion eb
              rw [if_pos hbl] at eb
              rcases three_in_two _ hlen2 a a' b ha ha' hb with e | e | e
              · exact absurd e haa'
              · subst e
                left
                exact hc a hlt (hFin a ha hlt) r hr p hp eb ea
              · subst e
                right
                exact hc a' hlt' (hFin a' ha' hlt') r hr p' hp' eb ea'
            have hnew : (⟨K, hk⟩ : Fin gates.length) ∉ T := by
              intro hmem
              have := (hT _ hmem).1
              simp at this
            refine ⟨fun r => if c r = c p' then c p else c r, insert ⟨K, hk⟩ T, ?_, ?_, ?_⟩
            · intro i hi hFi r hr r' hr' e1 e2
              by_cases hiK : i < n + K
              · have := hc i hiK hFi r hr r' hr' e1 e2
                simp only [this]
              · have hiK' : i = n + K := by omega
                subst hiK'
                rcases hcls r hr e1 with e | e <;> rcases hcls r' hr' e2 with e' | e' <;>
                  simp [e, e']
            · intro g hg
              rw [Finset.mem_insert] at hg
              rcases hg with rfl | hg
              · refine ⟨by simp, h, hF, ?_⟩
                have : 1 < (L.filter (fun r => V gates (fun v : Fin n => decide (v = r)) (n + K) = true)).card := by
                  rw [Finset.one_lt_card]
                  exact ⟨p, by simp [hp, h1], p', by simp [hp', h2], fun e => hne (by rw [e])⟩
                exact this
              · exact ⟨by have := (hT g hg).1; omega, (hT g hg).2⟩
            · have hsub : (L.image c).erase (c p') ⊆ L.image (fun r => if c r = c p' then c p else c r) := by
                intro t ht
                rw [Finset.mem_erase] at ht
                obtain ⟨htne, htm⟩ := ht
                rw [Finset.mem_image] at htm ⊢
                obtain ⟨r, hr, rfl⟩ := htm
                exact ⟨r, hr, by simp [htne]⟩
              have h3 := Finset.card_le_card hsub
              have h4 := Finset.pred_card_le_card_erase (s := L.image c) (a := c p')
              have h5 : (insert (⟨K, hk⟩ : Fin gates.length) T).card = T.card + 1 := by
                first
                  | exact Finset.card_insert_of_notMem hnew
                  | exact Finset.card_insert_of_not_mem hnew
              rw [h5]
              omega
          · -- the NOT gate is true off L
            exfalso
            have hkj : K = (j : ℕ) := congrArg Fin.val (huniq ⟨K, hk⟩ h)
            have := hF _ htop
            rw [hkj, hN _ htop] at this
            exact Bool.noConfusion this
        · refine ⟨c, T, ?_, ?_, hcount⟩
          · intro i hi hFi p hp p' hp' h1 h2
            by_cases hiK : i < n + K
            · exact hc i hiK hFi p hp p' hp' h1 h2
            · have : i = n + K := by omega
              subst this
              exact absurd hFi hF
          · intro g hg
            exact ⟨by have := (hT g hg).1; omega, (hT g hg).2⟩
  obtain ⟨c, T, hc, hT, hcount⟩ := key gates.length (Nat.le_refl _)
  -- the output wire is false off L and true at every point of L
  have hne : L.Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨p0, hp0⟩ := hne
  have hpt : ∀ p ∈ L, V gates (fun v : Fin n => decide (v = p)) o = true := by
    intro p hp
    rw [hout]
    simp only [decide_eq_true_eq]
    exact ⟨p, hp, by simp⟩
  have ho : o < n + gates.length := by
    by_contra hcon
    have := hpt p0 hp0
    rw [V_ge gates _ o (by omega)] at this
    exact Bool.noConfusion this
  have hFo : ∀ x : Fin n → Bool, (∀ v ∈ L, x v = false) → V gates x o = false := by
    intro x hx
    rw [hout]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv
    rw [hx v hv]
    exact Bool.noConfusion
  have himg : (L.image c).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_image] at ha hb
    obtain ⟨r, hr, rfl⟩ := ha
    obtain ⟨r', hr', rfl⟩ := hb
    exact hc o ho hFo r hr r' hr' (hpt r hr) (hpt r' hr')
  have hTI : T ⊆ I := fun g hg => hI g (hT g hg).2
  have := Finset.card_le_card hTI
  omega

end PEqualNP.Outside.L_meta_1456

theorem PEqualNP.Outside.L_meta_1456 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    (S i0).card = q + 1 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, (∀ v ∈ S i0, x v = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = true) →
    ∀ I : Finset (Fin gates.length), (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (∀ x : Fin n → Bool, (∀ v ∈ S i0, x v = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn x) = false) ∧
      2 ≤ ((S i0).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = p))) = true)).card) → g ∈ I) → q ≤ I.card := by
  intro q n m S i0 hcard gates out j hops _ huniq hout hN I hI
  exact PEqualNP.Outside.L_meta_1456.core q (S i0) hcard gates (out i0) j hops huniq (hout i0) hN I hI

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1517

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

lemma not_val (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (j h : ℕ) (hj : j < gates.length)
    (hhj : h < j) (hop : (gates[j]).op = GateOp.not)
    (hin : ∃ r : List ℕ, (gates[j]).inputs = (n + h) :: r) :
    V gates x (n + j) = !(V gates x (n + h)) := by
  obtain ⟨r, hr⟩ := hin
  rw [V_gate gates x j hj, hop, hr]
  have hlt : n + h < n + j := by omega
  simp [GateOp.eval, hlt]

-- above an input where the wire the NOT gate reads is true, every wire is monotone
lemma mono_up {n : ℕ} (gates : List Gate) (j h : ℕ) (hj : j < gates.length) (hhj : h < j)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ (k : ℕ) (hk : k < gates.length), (gates[k]).op = GateOp.not → k = j)
    (hjop : (gates[j]).op = GateOp.not)
    (hjin : ∃ r : List ℕ, (gates[j]).inputs = (n + h) :: r)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true)
    (hx : V gates x (n + h) = true) :
    ∀ i : ℕ, V gates x i = true → V gates y i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hv
    by_cases hin : i < n
    · rw [V_input gates x i hin] at hv
      rw [V_input gates y i hin]
      exact hxy _ hv
    · by_cases hlen : i < n + gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gates.length := by omega
        rcases (hops (gates[k]) (List.getElem_mem hk)).1 with hh | hh | hh
        · rw [V_gate gates x k hk, hh, and_map] at hv
          rw [V_gate gates y k hk, hh, and_map]
          intro a ha
          have h2 := hv a ha
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at h2 ⊢
            exact ih a hlt h2
          · rw [if_neg hlt] at h2
            exact Bool.noConfusion h2
        · rw [V_gate gates x k hk, hh, or_map] at hv
          rw [V_gate gates y k hk, hh, or_map]
          obtain ⟨a, ha, h2⟩ := hv
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at h2
            exact ⟨a, ha, by rw [if_pos hlt]; exact ih a hlt h2⟩
          · rw [if_neg hlt] at h2
            exact Bool.noConfusion h2
        · have hkj := hnot k hk hh
          rw [hkj, not_val gates x j h hj hhj hjop hjin, hx] at hv
          simp at hv
      · rw [V_ge gates x i (by omega)] at hv
        exact Bool.noConfusion hv

-- one reference input r and one test input z p for each point p of L: joining the points of L
-- takes one OR gate for each point but one
lemma merge_count {n : ℕ} (gates : List Gate) (j : ℕ) (L : Finset (Fin n))
    (r : Fin n → Bool) (z : Fin n → Fin n → Bool)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ (k : ℕ) (hk : k < gates.length), (gates[k]).op = GateOp.not → k = j)
    (hin : ∀ v : ℕ, v < n → V gates r v = false → ∀ p ∈ L, ∀ p' ∈ L,
      V gates (z p) v = true → V gates (z p') v = true → p = p')
    (hN : ∀ p ∈ L, V gates (z p) (n + j) = false)
    (o : ℕ) (ho : V gates r o = false) (hop : ∀ p ∈ L, V gates (z p) o = true) :
    ∃ T : Finset (Fin gates.length),
      (∀ g ∈ T, (gates.get g).op = GateOp.or ∧ V gates r (n + (g : ℕ)) = false ∧
        (∃ p ∈ L, ∃ p' ∈ L, p ≠ p' ∧ V gates (z p) (n + (g : ℕ)) = true ∧
          V gates (z p') (n + (g : ℕ)) = true) ∧
        (n + j) ∉ (gates.get g).inputs) ∧
      L.card ≤ T.card + 1 := by
  have key : ∀ K : ℕ, K ≤ gates.length →
      ∃ (c : Fin n → ℕ) (T : Finset (Fin gates.length)),
        (∀ i : ℕ, i < n + K → V gates r i = false → ∀ p ∈ L, ∀ p' ∈ L,
          V gates (z p) i = true → V gates (z p') i = true → c p = c p') ∧
        (∀ g ∈ T, (g : ℕ) < K ∧ ((gates.get g).op = GateOp.or ∧ V gates r (n + (g : ℕ)) = false ∧
          (∃ p ∈ L, ∃ p' ∈ L, p ≠ p' ∧ V gates (z p) (n + (g : ℕ)) = true ∧
            V gates (z p') (n + (g : ℕ)) = true) ∧
          (n + j) ∉ (gates.get g).inputs)) ∧
        L.card ≤ (L.image c).card + T.card := by
    intro K
    induction K with
    | zero =>
      intro _
      refine ⟨fun p => (p : ℕ), ∅, ?_, ?_, ?_⟩
      · intro i hi hF p hp p' hp' h1 h2
        have hi' : i < n := by omega
        rw [hin i hi' hF p hp p' hp' h1 h2]
      · intro g hg
        simp at hg
      · rw [Finset.card_image_of_injective _ Fin.val_injective]
        omega
    | succ K ih =>
      intro hK
      have hk : K < gates.length := by omega
      obtain ⟨c, T, hc, hT, hcount⟩ := ih (by omega)
      by_cases hconst : ∀ p ∈ L, ∀ p' ∈ L, V gates (z p) (n + K) = true →
          V gates (z p') (n + K) = true → c p = c p'
      · refine ⟨c, T, ?_, ?_, hcount⟩
        · intro i hi hF p hp p' hp' h1 h2
          by_cases hiK : i < n + K
          · exact hc i hiK hF p hp p' hp' h1 h2
          · have : i = n + K := by omega
            subst this
            exact hconst p hp p' hp' h1 h2
        · intro g hg
          exact ⟨by have := (hT g hg).1; omega, (hT g hg).2⟩
      · by_cases hF : V gates r (n + K) = false
        · push_neg at hconst
          obtain ⟨p, hp, p', hp', h1, h2, hne⟩ := hconst
          have hg1 := V_gate gates (z p) K hk
          have hg2 := V_gate gates (z p') K hk
          have hgr := V_gate gates r K hk
          rw [h1] at hg1
          rw [h2] at hg2
          rw [hF] at hgr
          have hlen2 := (hops (gates[K]) (List.getElem_mem hk)).2
          rcases (hops (gates[K]) (List.getElem_mem hk)).1 with h | h | h
          · exfalso
            rw [h] at hg1 hg2 hgr
            have hnotall : ¬ ∀ a ∈ (gates[K]).inputs,
                (if a < n + K then V gates r a else false) = true := by
              intro hall
              rw [(and_map _ _).mpr hall] at hgr
              exact Bool.noConfusion hgr
            push_neg at hnotall
            obtain ⟨a, ha, hfa⟩ := hnotall
            have e1 := (and_map _ _).mp hg1.symm a ha
            have e2 := (and_map _ _).mp hg2.symm a ha
            by_cases hlt : a < n + K
            · rw [if_pos hlt] at e1 e2 hfa
              have hFa : V gates r a = false := by
                cases hval : V gates r a
                · rfl
                · exact absurd hval hfa
              exact hne (hc a hlt hFa p hp p' hp' e1 e2)
            · rw [if_neg hlt] at e1
              exact Bool.noConfusion e1
          · rw [h] at hg1 hg2 hgr
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
            have hFin : ∀ b ∈ (gates[K]).inputs, b < n + K → V gates r b = false := by
              intro b hb hbl
              cases hval : V gates r b
              · rfl
              · exfalso
                have hor : GateOp.eval GateOp.or ((gates[K]).inputs.map fun i =>
                    if i < n + K then V gates r i else false) = true :=
                  (or_map _ _).mpr ⟨b, hb, by rw [if_pos hbl]; exact hval⟩
                rw [hor] at hgr
                exact Bool.noConfusion hgr
            have haa' : a ≠ a' := by
              intro heq
              subst heq
              exact hne (hc a hlt (hFin a ha hlt) p hp p' hp' ea ea')
            have hcls : ∀ q ∈ L, V gates (z q) (n + K) = true → c q = c p ∨ c q = c p' := by
              intro q hq hqv
              have hgq := V_gate gates (z q) K hk
              rw [hqv, h] at hgq
              obtain ⟨b, hb, eb⟩ := (or_map _ _).mp hgq.symm
              have hbl : b < n + K := by
                by_contra hcon
                rw [if_neg hcon] at eb
                exact Bool.noConfusion eb
              rw [if_pos hbl] at eb
              rcases three_in_two _ hlen2 a a' b ha ha' hb with e | e | e
              · exact absurd e haa'
              · subst e
                left
                exact hc a hlt (hFin a ha hlt) q hq p hp eb ea
              · subst e
                right
                exact hc a' hlt' (hFin a' ha' hlt') q hq p' hp' eb ea'
            have hnew : (⟨K, hk⟩ : Fin gates.length) ∉ T := by
              intro hmem
              have := (hT _ hmem).1
              simp at this
            have hNin : (n + j) ∉ (gates[K]).inputs := by
              intro hmem
              rcases three_in_two _ hlen2 a a' (n + j) ha ha' hmem with e | e | e
              · exact haa' e
              · rw [e, hN p hp] at ea
                exact Bool.noConfusion ea
              · rw [e, hN p' hp'] at ea'
                exact Bool.noConfusion ea'
            refine ⟨fun q => if c q = c p' then c p else c q, insert ⟨K, hk⟩ T, ?_, ?_, ?_⟩
            · intro i hi hFi q hq q' hq' e1 e2
              by_cases hiK : i < n + K
              · have := hc i hiK hFi q hq q' hq' e1 e2
                simp only [this]
              · have hiK' : i = n + K := by omega
                subst hiK'
                rcases hcls q hq e1 with e | e <;> rcases hcls q' hq' e2 with e' | e' <;>
                  simp [e, e']
            · intro g hg
              rw [Finset.mem_insert] at hg
              rcases hg with rfl | hg
              · exact ⟨by simp, h, hF, ⟨p, hp, p', hp', fun e => hne (by rw [e]), h1, h2⟩, hNin⟩
              · exact ⟨by have := (hT g hg).1; omega, (hT g hg).2⟩
            · have hsub : (L.image c).erase (c p') ⊆
                  L.image (fun q => if c q = c p' then c p else c q) := by
                intro t ht
                rw [Finset.mem_erase] at ht
                obtain ⟨htne, htm⟩ := ht
                rw [Finset.mem_image] at htm ⊢
                obtain ⟨q, hq, rfl⟩ := htm
                exact ⟨q, hq, by simp [htne]⟩
              have h3 := Finset.card_le_card hsub
              have h4 := Finset.pred_card_le_card_erase (s := L.image c) (a := c p')
              have h5 : (insert (⟨K, hk⟩ : Fin gates.length) T).card = T.card + 1 :=
                Finset.card_insert_of_notMem hnew
              rw [h5]
              omega
          · exfalso
            have hkj := hnot K hk h
            rw [hkj, hN p hp] at h1
            exact Bool.noConfusion h1
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
  refine ⟨T, fun g hg => (hT g hg).2, ?_⟩
  by_cases hne : L.Nonempty
  · obtain ⟨p0, hp0⟩ := hne
    have ho' : o < n + gates.length := by
      by_contra hcon
      have := hop p0 hp0
      rw [V_ge gates _ o (by omega)] at this
      exact Bool.noConfusion this
    have himg : (L.image c).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_image] at ha hb
      obtain ⟨r1, hr1, rfl⟩ := ha
      obtain ⟨r2, hr2, rfl⟩ := hb
      exact hc o ho' ho r1 hr1 r2 hr2 (hop r1 hr1) (hop r2 hr2)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

-- facts about the thirteen lines, by evaluation
set_option maxRecDepth 8192 in
lemma line_card : ∀ t : Fin 13, ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)).card = 4 := by
  decide

set_option maxRecDepth 8192 in
lemma line_meet : ∀ t t' : Fin 13, t ≠ t' →
    (({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) ∩ {t', t' + 1, t' + 3, t' + 9}).card ≤ 1 := by
  decide

set_option maxRecDepth 8192 in
lemma line_off : ∀ t t' : Fin 13, t ≠ t' →
    ∃ v ∈ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)),
      v ∉ ({t', t' + 1, t' + 3, t' + 9} : Finset (Fin 13)) := by
  decide

set_option maxRecDepth 8192 in
lemma point_lines : ∀ t a : Fin 13, a ∈ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) →
    ∃ s : Fin 13, s ≠ t ∧ a ∈ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13)) := by
  decide

lemma succ_ne : ∀ t : Fin 13, t + 1 ≠ t := by
  decide

def cl (L : Fin 13 → Finset (Fin 13)) (t : Fin 13) : Fin 13 → Bool :=
  fun v => decide (v ∉ L t)

def zz (B : Fin 13 → Fin 13 → Finset (Fin 13)) (t p : Fin 13) : Fin 13 → Bool :=
  fun v => decide (v = p ∨ v ∈ B t p)

abbrev good (gates : List Gate) (L : Fin 13 → Finset (Fin 13))
    (B : Fin 13 → Fin 13 → Finset (Fin 13)) (j : ℕ) (t : Fin 13) (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ V gates (cl L t) (13 + (g : ℕ)) = false ∧
    (∃ p ∈ L t, ∃ p' ∈ L t, p ≠ p' ∧ V gates (zz B t p) (13 + (g : ℕ)) = true ∧
      V gates (zz B t p') (13 + (g : ℕ)) = true) ∧
    (13 + j) ∉ (gates.get g).inputs

lemma card5 {α : Type} [DecidableEq α] [Fintype α] (A : Finset α) (a b : α) (S Z : Finset α)
    (hab : a ≠ b) (haA : a ∉ A) (hbA : b ∉ A) (haS : a ∉ S) (hbS : b ∉ S) (haZ : a ∉ Z)
    (hbZ : b ∉ Z) (hAS : ∀ x ∈ A, x ∉ S) (hAZ : ∀ x ∈ A, x ∉ Z) (hSZ : ∀ x ∈ S, x ∉ Z) :
    A.card + 2 + S.card + Z.card ≤ Fintype.card α := by
  have h1 : (A ∪ S).card = A.card + S.card :=
    Finset.card_union_of_disjoint (Finset.disjoint_left.mpr hAS)
  have hd : Disjoint (A ∪ S) Z := by
    rw [Finset.disjoint_left]
    intro x hx
    rcases Finset.mem_union.mp hx with hx1 | hx1
    · exact hAZ x hx1
    · exact hSZ x hx1
  have h2 : ((A ∪ S) ∪ Z).card = (A ∪ S).card + Z.card := Finset.card_union_of_disjoint hd
  have hb : b ∉ (A ∪ S) ∪ Z := by
    simp [hbA, hbS, hbZ]
  have ha : a ∉ insert b ((A ∪ S) ∪ Z) := by
    simp [hab, haA, haS, haZ]
  have h3 : (insert b ((A ∪ S) ∪ Z)).card = ((A ∪ S) ∪ Z).card + 1 :=
    Finset.card_insert_of_notMem hb
  have h4 : (insert a (insert b ((A ∪ S) ∪ Z))).card = (insert b ((A ∪ S) ∪ Z)).card + 1 :=
    Finset.card_insert_of_notMem ha
  have h5 := Finset.card_le_univ (insert a (insert b ((A ∪ S) ∪ Z)))
  omega

lemma core (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (gates : List Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hjop : (gates.get j).op = GateOp.not)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hhj : h < j) (hjin : ∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r)
    (hout : ∀ (t : Fin 13) (x : Fin 13 → Bool),
      V gates x (o t) = decide (∃ v ∈ L t, x v = true))
    (hco : ∀ t : Fin 13, V gates (fun v : Fin 13 => decide (v ∉ L t)) (13 + (h : ℕ)) = true)
    (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13))
    (hB : ∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧
      V gates (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p)) (13 + (h : ℕ)) = true)
    (hcompat : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty)))
    (I : Finset (Fin gates.length))
    (hI : ∀ g ∈ I, (gates.get g).op = GateOp.and ∧
      ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
        13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) :
    (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 + 3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length := by
  classical
  have hj : (j : ℕ) < gates.length := j.isLt
  have hhj' : (h : ℕ) < (j : ℕ) := hhj
  have hnot : ∀ (k : ℕ) (hk : k < gates.length), (gates[k]).op = GateOp.not → k = (j : ℕ) :=
    fun k hk hop => congrArg Fin.val (huniq ⟨k, hk⟩ hop)
  have hNv : ∀ x : Fin 13 → Bool, V gates x (13 + (j : ℕ)) = !(V gates x (13 + (h : ℕ))) :=
    fun x => not_val gates x j h hj hhj' hjop hjin
  have hmono : ∀ x y : Fin 13 → Bool, (∀ v, x v = true → y v = true) →
      V gates x (13 + (h : ℕ)) = true → ∀ i : ℕ, V gates x i = true → V gates y i = true :=
    fun x y hxy hx => mono_up gates j h hj hhj' hops hnot hjop hjin x y hxy hx
  have hco' : ∀ t : Fin 13, V gates (cl L t) (13 + (h : ℕ)) = true := hco
  have hB' : ∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ V gates (zz B t p) (13 + (h : ℕ)) = true := hB
  have hNco : ∀ s : Fin 13, V gates (cl L s) (13 + (j : ℕ)) = false := by
    intro s
    rw [hNv, hco' s]
    rfl
  have hcard4 : ∀ t : Fin 13, (L t).card = 4 := by
    intro t
    rw [hL]
    exact line_card t
  have hmeet : ∀ t t' : Fin 13, t ≠ t' → ∀ p p' : Fin 13, p ∈ L t → p' ∈ L t → p ∈ L t' →
      p' ∈ L t' → p = p' := by
    intro t t' htt p p' h1 h2 h3 h4
    have hc := line_meet t t' htt
    rw [← hL t, ← hL t'] at hc
    exact Finset.card_le_one.mp hc p (Finset.mem_inter.mpr ⟨h1, h3⟩) p' (Finset.mem_inter.mpr ⟨h2, h4⟩)
  have hoff : ∀ t t' : Fin 13, t ≠ t' → ∃ v ∈ L t, v ∉ L t' := by
    intro t t' htt
    have := line_off t t' htt
    rw [← hL t, ← hL t'] at this
    exact this
  have hpl : ∀ t a : Fin 13, a ∈ L t → ∃ s : Fin 13, s ≠ t ∧ a ∈ L s := by
    intro t a ha
    rw [hL] at ha
    obtain ⟨s, hs, hsm⟩ := point_lines t a ha
    exact ⟨s, hs, by rw [hL]; exact hsm⟩
  -- the output of line t on the co-line inputs
  have hot : ∀ t : Fin 13, V gates (cl L t) (o t) = false := by
    intro t
    rw [hout]
    simp [cl]
  have hos : ∀ t s : Fin 13, s ≠ t → V gates (cl L s) (o t) = true := by
    intro t s hs
    rw [hout]
    simp only [decide_eq_true_eq]
    obtain ⟨v, hv, hvn⟩ := hoff t s (Ne.symm hs)
    exact ⟨v, hv, by simp [cl, hvn]⟩
  -- three OR gates for each line of Lam
  have hthree : ∀ t ∈ Lam, 3 ≤ (Finset.univ.filter (fun g => good gates L B (j : ℕ) t g)).card := by
    intro t ht
    obtain ⟨T, hT, hTc⟩ := merge_count gates (j : ℕ) (L t) (cl L t) (zz B t) hops hnot
      (by
        intro v hv hF p hp p' hp' h1 h2
        rw [V_input gates _ v hv] at hF h1 h2
        simp only [cl, zz, decide_eq_false_iff_not, not_not, decide_eq_true_eq] at hF h1 h2
        have hnb : ∀ q ∈ L t, (⟨v, hv⟩ : Fin 13) ∉ B t q := by
          intro q hq hm
          have hmem : (⟨v, hv⟩ : Fin 13) ∈ B t q ∩ L t := Finset.mem_inter.mpr ⟨hm, hF⟩
          rw [(hB t ht q hq).1] at hmem
          simp at hmem
        rcases h1 with e1 | e1
        · rcases h2 with e2 | e2
          · rw [← e1, ← e2]
          · exact absurd e2 (hnb p' hp')
        · exact absurd e1 (hnb p hp))
      (by
        intro p hp
        rw [hNv, (hB' t ht p hp).2]
        rfl)
      (o t) (hot t)
      (by
        intro p hp
        rw [hout]
        simp only [decide_eq_true_eq]
        exact ⟨p, hp, by simp [zz]⟩)
    have hsub : T ⊆ Finset.univ.filter (fun g => good gates L B (j : ℕ) t g) := by
      intro g hg
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hT g hg⟩
    have h1 := Finset.card_le_card hsub
    have h2 := hcard4 t
    omega
  -- a good gate of one line of Lam is true off every other line through a point of its own
  have hhalf : ∀ t ∈ Lam, ∀ t' : Fin 13, t ≠ t' → ∀ g : Fin gates.length, good gates L B (j : ℕ) t g →
      V gates (cl L t') (13 + (g : ℕ)) = false → ∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty := by
    intro t ht t' htt g hg hF'
    obtain ⟨_, _, ⟨p, hp, p', hp', hpp, e1, e2⟩, _⟩ := hg
    have hex : ∃ q ∈ L t, q ∉ L t' ∧ V gates (zz B t q) (13 + (g : ℕ)) = true := by
      by_cases hpin : p ∈ L t'
      · refine ⟨p', hp', ?_, e2⟩
        intro hp'in
        exact hpp (hmeet t t' htt p p' hp hp' hpin hp'in)
      · exact ⟨p, hp, hpin, e1⟩
    obtain ⟨q, hq, hqn, eq⟩ := hex
    refine ⟨q, Finset.mem_sdiff.mpr ⟨hq, hqn⟩, ?_⟩
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hle : ∀ v, zz B t q v = true → cl L t' v = true := by
      intro v hv
      simp only [zz, decide_eq_true_eq] at hv
      simp only [cl, decide_eq_true_eq]
      intro hvin
      rcases hv with rfl | hv
      · exact hqn hvin
      · have hmem : v ∈ B t q ∩ L t' := Finset.mem_inter.mpr ⟨hv, hvin⟩
        rw [hemp] at hmem
        simp at hmem
    have := hmono (zz B t q) (cl L t') hle (hB' t ht q hq).2 (13 + (g : ℕ)) eq
    rw [hF'] at this
    exact Bool.noConfusion this
  have hdisj : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' →
      Disjoint (Finset.univ.filter (fun g => good gates L B (j : ℕ) t g))
        (Finset.univ.filter (fun g => good gates L B (j : ℕ) t' g)) := by
    intro t ht t' ht' htt
    rw [Finset.disjoint_left]
    intro g hg hg'
    rw [Finset.mem_filter] at hg hg'
    exact hcompat t ht t' ht' htt
      ⟨hhalf t ht t' htt g hg.2 hg'.2.2.1, hhalf t' ht' t (Ne.symm htt) g hg'.2 hg.2.2.1⟩
  have hS3 : 3 * Lam.card ≤
      (Lam.biUnion (fun t => Finset.univ.filter (fun g => good gates L B (j : ℕ) t g))).card := by
    rw [Finset.card_biUnion hdisj]
    have := Finset.card_nsmul_le_sum Lam
      (fun t => (Finset.univ.filter (fun g => good gates L B (j : ℕ) t g)).card) 3 hthree
    rw [smul_eq_mul] at this
    omega
  -- one more gate for each line: the first wire with the co-line values of its OR
  have hWex : ∀ t : Fin 13, ∃ g : ℕ, g < gates.length ∧ V gates (cl L t) (13 + g) = false ∧
      ∀ s : Fin 13, s ≠ t → V gates (cl L s) (13 + g) = true := by
    intro t
    have h13 : 13 ≤ o t := by
      by_contra hcon
      have hlt : o t < 13 := by omega
      have hv0 := hot t
      rw [V_input gates _ (o t) hlt] at hv0
      simp only [cl, decide_eq_false_iff_not, not_not] at hv0
      obtain ⟨s, hs, hsm⟩ := hpl t ⟨o t, hlt⟩ hv0
      have hv1 := hos t s hs
      rw [V_input gates _ (o t) hlt] at hv1
      simp [cl, hsm] at hv1
    have hlen : o t < 13 + gates.length := by
      by_contra hcon
      have hv1 := hos t (t + 1) (succ_ne t)
      rw [V_ge gates _ (o t) (by omega)] at hv1
      exact Bool.noConfusion hv1
    have he : 13 + (o t - 13) = o t := by omega
    refine ⟨o t - 13, by omega, ?_, ?_⟩
    · rw [he]
      exact hot t
    · intro s hs
      rw [he]
      exact hos t s hs
  have hWmin : ∀ t : Fin 13, ∃ g : ℕ, (g < gates.length ∧ V gates (cl L t) (13 + g) = false ∧
      ∀ s : Fin 13, s ≠ t → V gates (cl L s) (13 + g) = true) ∧
      ∀ g' : ℕ, g' < g → ¬ (g' < gates.length ∧ V gates (cl L t) (13 + g') = false ∧
        ∀ s : Fin 13, s ≠ t → V gates (cl L s) (13 + g') = true) :=
    fun t => ⟨Nat.find (hWex t), Nat.find_spec (hWex t), fun g' hg' => Nat.find_min (hWex t) hg'⟩
  choose W hW hWm using hWmin
  have hWinj : ∀ t t' : Fin 13, W t = W t' → t = t' := by
    intro t t' heq
    by_contra hne
    have h1 := (hW t).2.1
    have h2 := (hW t').2.2 t hne
    rw [← heq, h1] at h2
    exact Bool.noConfusion h2
  have hWj : ∀ t : Fin 13, W t ≠ (j : ℕ) := by
    intro t heq
    have h1 := (hW t).2.2 (t + 1) (succ_ne t)
    rw [heq, hNco] at h1
    exact Bool.noConfusion h1
  have hWh : ∀ t : Fin 13, W t ≠ (h : ℕ) := by
    intro t heq
    have h1 := (hW t).2.1
    rw [heq, hco' t] at h1
    exact Bool.noConfusion h1
  have hWread : ∀ t : Fin 13, ¬ ((j : ℕ) < W t ∧ 13 + (j : ℕ) ∈ (gates[W t]'(hW t).1).inputs) := by
    intro t ⟨hjW, hmem⟩
    have hK := (hW t).1
    have hlen2 := (hops (gates[W t]) (List.getElem_mem hK)).2
    have hgs : ∀ s : Fin 13, V gates (cl L s) (13 + W t) =
        (gates[W t]).op.eval ((gates[W t]).inputs.map fun i =>
          if i < 13 + W t then V gates (cl L s) i else false) :=
      fun s => V_gate gates (cl L s) (W t) hK
    rcases (hops (gates[W t]) (List.getElem_mem hK)).1 with hh | hh | hh
    · have h1 := (hW t).2.2 (t + 1) (succ_ne t)
      rw [hgs, hh, and_map] at h1
      have h2 := h1 _ hmem
      have hlt13 : 13 + (j : ℕ) < 13 + W t := by omega
      rw [if_pos hlt13, hNco] at h2
      exact Bool.noConfusion h2
    · -- every true co-line value comes from the one other wire the gate reads
      have hwit : ∀ s : Fin 13, s ≠ t → ∃ b ∈ (gates[W t]).inputs, b < 13 + W t ∧
          V gates (cl L s) b = true := by
        intro s hs
        have h1 := (hW t).2.2 s hs
        rw [hgs, hh, or_map] at h1
        obtain ⟨b, hb, eb⟩ := h1
        have hbl : b < 13 + W t := by
          by_contra hcon
          rw [if_neg hcon] at eb
          exact Bool.noConfusion eb
        rw [if_pos hbl] at eb
        exact ⟨b, hb, hbl, eb⟩
      obtain ⟨b0, hb0, hb0l, eb0⟩ := hwit (t + 1) (succ_ne t)
      have hb0j : b0 ≠ 13 + (j : ℕ) := by
        intro e
        rw [e, hNco] at eb0
        exact Bool.noConfusion eb0
      have hall : ∀ s : Fin 13, s ≠ t → V gates (cl L s) b0 = true := by
        intro s hs
        obtain ⟨b, hb, _, eb⟩ := hwit s hs
        rcases three_in_two _ hlen2 b0 b (13 + (j : ℕ)) hb0 hb hmem with e | e | e
        · rw [e]
          exact eb
        · exact absurd e hb0j
        · rw [e, hNco] at eb
          exact Bool.noConfusion eb
      have hfalse : V gates (cl L t) b0 = false := by
        cases hval : V gates (cl L t) b0
        · rfl
        · exfalso
          have h1 := (hW t).2.1
          rw [hgs, hh] at h1
          have hor : GateOp.eval GateOp.or ((gates[W t]).inputs.map fun i =>
              if i < 13 + W t then V gates (cl L t) i else false) = true :=
            (or_map _ _).mpr ⟨b0, hb0, by rw [if_pos hb0l]; exact hval⟩
          rw [hor] at h1
          exact Bool.noConfusion h1
      by_cases hb13 : b0 < 13
      · rw [V_input gates _ b0 hb13] at hfalse
        simp only [cl, decide_eq_false_iff_not, not_not] at hfalse
        obtain ⟨s, hs, hsm⟩ := hpl t ⟨b0, hb13⟩ hfalse
        have h1 := hall s hs
        rw [V_input gates _ b0 hb13] at h1
        simp [cl, hsm] at h1
      · have he : 13 + (b0 - 13) = b0 := by omega
        refine hWm t (b0 - 13) (by omega) ⟨by omega, ?_, ?_⟩
        · rw [he]
          exact hfalse
        · intro s hs
          rw [he]
          exact hall s hs
    · have := hnot (W t) hK hh
      omega
  -- the AND gates of I lie strictly below h
  have hIlt : ∀ g ∈ I, g < h := by
    intro g hg
    have := (hI g hg).2 (Finset.univ.filter (fun g' : Fin gates.length => g' < h)) (by
      intro i g' hi _ hlt
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hi with rfl | hi
      · exact hlt
      · rw [Finset.mem_filter] at hi
        exact lt_trans hlt hi.2)
    rw [Finset.mem_filter] at this
    exact this.2
  have hjh : j ≠ h := fun e => by
    rw [e] at hhj
    exact lt_irrefl _ hhj
  have hjA : j ∉ Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs) := by
    intro hm
    rw [Finset.mem_filter] at hm
    exact lt_irrefl _ hm.2.1
  have hhA : h ∉ Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs) := by
    intro hm
    rw [Finset.mem_filter] at hm
    exact lt_asymm hhj hm.2.1
  have hjS : j ∉ Lam.biUnion (fun t => Finset.univ.filter (fun g => good gates L B (j : ℕ) t g)) := by
    intro hm
    rw [Finset.mem_biUnion] at hm
    obtain ⟨t, _, hg⟩ := hm
    rw [Finset.mem_filter] at hg
    have h1 := hg.2.1
    rw [hjop] at h1
    exact GateOp.noConfusion h1
  have hhS : h ∉ Lam.biUnion (fun t => Finset.univ.filter (fun g => good gates L B (j : ℕ) t g)) := by
    intro hm
    rw [Finset.mem_biUnion] at hm
    obtain ⟨t, _, hg⟩ := hm
    rw [Finset.mem_filter] at hg
    have h1 := hg.2.2.1
    rw [hco' t] at h1
    exact Bool.noConfusion h1
  have hAS : ∀ x ∈ Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs),
      x ∉ Lam.biUnion (fun t => Finset.univ.filter (fun g => good gates L B (j : ℕ) t g)) := by
    intro x hx hm
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_biUnion] at hm
    obtain ⟨t, _, hg⟩ := hm
    rw [Finset.mem_filter] at hg
    exact hg.2.2.2.2 hx.2.2
  -- first count: the AND gates of I
  have hX : (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 +
      (Lam.biUnion (fun t => Finset.univ.filter (fun g => good gates L B (j : ℕ) t g))).card + I.card ≤
      Fintype.card (Fin gates.length) := by
    apply card5 _ j h _ I hjh hjA hhA hjS hhS
    · intro hm
      exact lt_asymm hhj (hIlt j hm)
    · intro hm
      exact lt_irrefl _ (hIlt h hm)
    · exact hAS
    · intro x hx hm
      rw [Finset.mem_filter] at hx
      exact lt_asymm (lt_trans (hIlt x hm) hhj) hx.2.1
    · intro x hx hm
      rw [Finset.mem_biUnion] at hx
      obtain ⟨t, _, hg⟩ := hx
      rw [Finset.mem_filter] at hg
      have h1 := hg.2.1
      rw [(hI x hm).1] at h1
      exact GateOp.noConfusion h1
  -- second count: one gate for each line outside Lam
  have hY : (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 +
      (Lam.biUnion (fun t => Finset.univ.filter (fun g => good gates L B (j : ℕ) t g))).card +
      (Lamᶜ.image (fun t => (⟨W t, (hW t).1⟩ : Fin gates.length))).card ≤
      Fintype.card (Fin gates.length) := by
    apply card5 _ j h _ _ hjh hjA hhA hjS hhS
    · intro hm
      rw [Finset.mem_image] at hm
      obtain ⟨t, _, e⟩ := hm
      exact hWj t (congrArg Fin.val e)
    · intro hm
      rw [Finset.mem_image] at hm
      obtain ⟨t, _, e⟩ := hm
      exact hWh t (congrArg Fin.val e)
    · exact hAS
    · intro x hx hm
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_image] at hm
      obtain ⟨t, _, rfl⟩ := hm
      exact hWread t ⟨hx.2.1, hx.2.2⟩
    · intro x hx hm
      rw [Finset.mem_biUnion] at hx
      obtain ⟨t', ht', hg⟩ := hx
      rw [Finset.mem_filter] at hg
      rw [Finset.mem_image] at hm
      obtain ⟨t, ht, rfl⟩ := hm
      rw [Finset.mem_compl] at ht
      have hne : t' ≠ t := fun e => ht (e ▸ ht')
      have h1 := hg.2.2.1
      have h2 := (hW t).2.2 t' hne
      exact Bool.noConfusion (h1.symm.trans h2)
  have hS5 : (Lamᶜ.image (fun t => (⟨W t, (hW t).1⟩ : Fin gates.length))).card = 13 - Lam.card := by
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_compl, Fintype.card_fin]
    · intro t t' e
      exact hWinj t t' (congrArg Fin.val e)
  rw [Fintype.card_fin] at hX hY
  rcases Nat.le_total (13 - Lam.card) I.card with hm | hm
  · rw [max_eq_right hm]
    omega
  · rw [max_eq_left hm]
    omega

end PEqualNP.Outside.L_meta_1517

theorem PEqualNP.Outside.L_meta_1517 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p))) = true) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 + 3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length := by
  intro L hL gates o j h hops hjop huniq hhj hjin hout hco Lam B hB hcompat I hI
  exact PEqualNP.Outside.L_meta_1517.core L hL gates o j h hops hjop huniq hhj hjin hout hco Lam B hB hcompat I hI

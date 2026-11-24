import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1562

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_append (A B : List Gate) (x : List Bool) : run (A ++ B) x = run B (run A x) := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_value' {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    value ⟨gs, 0⟩ x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then value ⟨gs, 0⟩ x r else false) := by
  have h := gate_value ⟨gs, 0⟩ x (n + k) (by omega) (by change n + k < n + gs.length; omega)
  simpa only [Nat.add_sub_cancel_left] using h

def V {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool := value ⟨gs, 0⟩ x w

lemma V_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    V gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then V gs x r else false) :=
  gate_value' gs x k hk

lemma V_missing {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gs.length ≤ w) : V gs x w = false :=
  missing_value ⟨gs, 0⟩ x w hw

lemma V_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    V gs x w = x ⟨w, hw⟩ := by
  change (run gs (List.ofFn x)).getD w false = x ⟨w, hw⟩
  have hp : w < (List.ofFn x).length := by simpa using hw
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma three_distinct (l : List ℕ) (a b c : ℕ) (hl : l.length ≤ 2) (ha : a ∈ l) (hb : b ∈ l)
    (hc : c ∈ l) : a = b ∨ b = c ∨ a = c := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at ha
  · simp at ha hb hc; omega
  · simp at ha hb hc; omega
  · simp at hl

lemma mono {n : ℕ} (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ w, V gs x w = true → V gs y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [V_input gs x w hn, V_input gs y w hn]
      exact hxy _
    by_cases hw : n + gs.length ≤ w
    · rw [V_missing gs x w hw]
      intro hh
      exact Bool.noConfusion hh
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < gs.length := by omega
    rw [V_gate gs x k hk, V_gate gs y k hk]
    have hr (r : ℕ) : (if r < n + k then V gs x r else false) = true →
        (if r < n + k then V gs y r else false) = true := by
      by_cases h' : r < n + k
      · simpa [h'] using ih r h'
      · simp [h']
    rcases hops gs[k] (List.getElem_mem hk) with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
      intro hx b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
      intro hx
      obtain ⟨b, hb, hv⟩ := hx
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hv⟩


def c {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun v => decide (v ∉ S)

def z {n : ℕ} (y : Finset (Fin n)) (u : Fin n) : Fin n → Bool := fun v => decide (v ∈ y ∨ v = u)

def Q {n : ℕ} (gs : List Gate) (S0 y : Finset (Fin n)) (u : Fin n) (k : ℕ) : Prop :=
  k < gs.length ∧ V gs (c S0) (n + k) = false ∧ V gs (z y u) (n + k) = true ∧
    ∃ u' ∈ S0, u' < u ∧ V gs (z y u') (n + k) = true

lemma src {n : ℕ} (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (y : Fin n → Bool) (k : ℕ) (hk : k < gs.length) (hy : V gs y (n + k) = false) :
    (∀ x : Fin n → Bool, V gs x (n + k) = false) ∨
    (∃ r, r < n + k ∧ V gs y r = false ∧
      ∀ x : Fin n → Bool, V gs x (n + k) = true → V gs x r = true) ∨
    ((∀ r ∈ gs[k].inputs, r < n + k → V gs y r = false) ∧
      ∀ x : Fin n → Bool, V gs x (n + k) = true →
        ∃ r ∈ gs[k].inputs, r < n + k ∧ V gs x r = true) := by
  rcases hops gs[k] (List.getElem_mem hk) with hop | hop
  · by_cases hex : ∃ r ∈ gs[k].inputs, (if r < n + k then V gs y r else false) = false
    · obtain ⟨r, hr, hf⟩ := hex
      have hall : ∀ x : Fin n → Bool, V gs x (n + k) = true →
          (if r < n + k then V gs x r else false) = true := by
        intro x hx
        rw [V_gate gs x k hk, hop] at hx
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx
        exact hx _ ⟨r, hr, rfl⟩
      by_cases hlt : r < n + k
      · have hyr : V gs y r = false := by simpa [hlt] using hf
        exact Or.inr (Or.inl ⟨r, hlt, hyr, fun x hx => by simpa [hlt] using hall x hx⟩)
      · refine Or.inl fun x => ?_
        by_contra hne
        have hx : V gs x (n + k) = true := by simpa using hne
        have := hall x hx
        simp [hlt] at this
    · exfalso
      rw [V_gate gs y k hk, hop] at hy
      have hall : (gs[k].inputs.map fun r => if r < n + k then V gs y r else false).all id
          = true := by
        simp only [List.all_eq_true, List.mem_map, id_eq]
        rintro b ⟨r, hr, rfl⟩
        by_contra hb
        exact hex ⟨r, hr, by simpa using hb⟩
      simp only [GateOp.eval] at hy
      rw [hall] at hy
      exact Bool.noConfusion hy
  · have hin : ∀ r ∈ gs[k].inputs, r < n + k → ∀ x : Fin n → Bool, V gs x r = true →
        V gs x (n + k) = true := by
      intro r hr hlt x hx
      rw [V_gate gs x k hk, hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      exact ⟨_, ⟨r, hr, rfl⟩, by simp [hlt, hx]⟩
    refine Or.inr (Or.inr ⟨fun r hr hlt => ?_, fun x hx => ?_⟩)
    · by_contra hb
      have hb' : V gs y r = true := by simpa using hb
      have := hin r hr hlt y hb'
      rw [hy] at this
      exact Bool.noConfusion this
    · rw [V_gate gs x k hk, hop] at hx
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx
      obtain ⟨b, ⟨r, hr, rfl⟩, hb⟩ := hx
      by_cases hlt : r < n + k
      · exact ⟨r, hr, hlt, by simpa [hlt] using hb⟩
      · simp [hlt] at hb

lemma good_min {n : ℕ} (gs : List Gate) (S0 y : Finset (Fin n))
    (hy0 : ∀ u ∈ S0, u ∉ y) (r k : ℕ) (u : Fin n) (hg : V gs (c S0) r = false)
    (hlt : r < n + k) (hmin : ∀ j < k, ¬ Q gs S0 y u j) (h1 : V gs (z y u) r = true)
    (u' : Fin n) (hu' : u' ∈ S0) (hlt' : u' < u) (h2 : V gs (z y u') r = true) : False := by
  by_cases hr : r < n
  · rw [V_input gs _ r hr] at h1 h2 hg
    have hS : (⟨r, hr⟩ : Fin n) ∈ S0 := by simpa [c] using hg
    have hy := hy0 _ hS
    simp only [z, hy, false_or, decide_eq_true_eq] at h1 h2
    rw [← h1, ← h2] at hlt'
    exact lt_irrefl _ hlt'
  · obtain ⟨j, rfl⟩ : ∃ j, r = n + j := ⟨r - n, by omega⟩
    by_cases hj : j < gs.length
    · exact hmin j (by omega) ⟨hj, hg, h1, u', hu', hlt', h2⟩
    · rw [V_missing gs _ _ (by omega)] at h1
      exact Bool.noConfusion h1

lemma row_inj {n : ℕ} (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (S0 y : Finset (Fin n))
    (hy0 : ∀ u ∈ S0, u ∉ y) (k : ℕ) (p r : Fin n)
    (hQp : Q gs S0 y p k) (hminp : ∀ j < k, ¬ Q gs S0 y p j)
    (hQr : Q gs S0 y r k) (hminr : ∀ j < k, ¬ Q gs S0 y r j)
    (hr : r ∈ S0) (hrp : r < p) : False := by
  obtain ⟨hk, hyk, h2, p', hp', hlt, h3⟩ := hQp
  obtain ⟨_, _, g2, r', hr', hlt', g3⟩ := hQr
  rcases src gs hops (c S0) k hk hyk with h | ⟨r0, hl0, hg0, hx⟩ | ⟨hgood, hsrc⟩
  · rw [h] at h2
    exact Bool.noConfusion h2
  · exact good_min gs S0 y hy0 r0 k p hg0 hl0 hminp (hx _ h2) r hr hrp (hx _ g2)
  · obtain ⟨r1, hr1, hl1, hv1⟩ := hsrc _ h2
    obtain ⟨r2, hr2, hl2, hv2⟩ := hsrc _ g2
    obtain ⟨r3, hr3, hl3, hv3⟩ := hsrc _ g3
    rcases three_distinct _ r1 r2 r3 (hlen _ (List.getElem_mem hk)) hr1 hr2 hr3 with e1 | e1 | e1
    · subst e1
      exact good_min gs S0 y hy0 r1 k p (hgood r1 hr1 hl1) hl1 hminp hv1 r hr hrp hv2
    · subst e1
      exact good_min gs S0 y hy0 r2 k r (hgood r2 hr2 hl2) hl2 hminr hv2 r' hr' hlt' hv3
    · subst e1
      exact good_min gs S0 y hy0 r1 k p (hgood r1 hr1 hl1) hl1 hminp hv1 r' hr'
        (lt_trans hlt' hrp) hv3

lemma hit {n : ℕ} (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (S1 y0 : Finset (Fin n)) (hd : Disjoint y0 S1) (u : Fin n) (w : ℕ)
    (h1 : V gs (z y0 u) w = true) (hc : V gs (c S1) w = false) : u ∈ S1 := by
  by_contra hu
  have hm := mono gs hops (z y0 u) (c S1) (by
    intro p hp
    have hp' : p ∈ y0 ∨ p = u := by simpa [z] using hp
    have : p ∉ S1 := by
      rcases hp' with h | h
      · exact Finset.disjoint_left.mp hd h
      · rw [h]; exact hu
    simp [c, this]) w h1
  rw [hc] at hm
  exact Bool.noConfusion hm

lemma cross {n : ℕ} (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (S0 S1 y0 : Finset (Fin n)) (k : ℕ) (u : Fin n) (hu : u ∈ S0) (hQ : Q gs S0 y0 u k)
    (hc : V gs (c S1) (n + k) = false) (hinter : (S0 ∩ S1).card ≤ 1) : ¬ Disjoint y0 S1 := by
  intro hd
  obtain ⟨hk, hyk, h2, u', hu', hlt, h3⟩ := hQ
  have a1 := hit gs hops S1 y0 hd u _ h2 hc
  have a2 := hit gs hops S1 y0 hd u' _ h3 hc
  have h12 := Finset.card_le_one.mp hinter u (Finset.mem_inter.mpr ⟨hu, a1⟩)
    u' (Finset.mem_inter.mpr ⟨hu', a2⟩)
  rw [h12] at hlt
  exact lt_irrefl _ hlt

lemma main (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (gs : List Gate) (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdis : ∀ i : Fin m, Disjoint (y i) (S i))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hbelow : ∀ (i : Fin m) (x : Fin n → Bool), V gs x (out i) = true → ∃ p ∈ S i, x p = true)
    (hfire : ∀ i : Fin m, ∀ p ∈ S i, V gs (z (y i) p) (out i) = true)
    (hD : ∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) :
    ∑ i : Fin m, (S i).card ≤ D * gs.length + m := by
  classical
  have hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  have hlen : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g h => (hg g h).2
  have hy0 : ∀ i, ∀ u ∈ S i, u ∉ y i := fun i => Finset.disjoint_right.mp (hdis i)
  have hco : ∀ i, V gs (c (S i)) (out i) = false := by
    intro i
    by_contra hb
    have hb' : V gs (c (S i)) (out i) = true := by simpa using hb
    obtain ⟨p, hp, hpc⟩ := hbelow i _ hb'
    simp [c, hp] at hpc
  let A : Fin m → Finset (Fin n) := fun w => (S w).filter (fun u => ∃ u' ∈ S w, u' < u)
  have hA : ∀ w, (S w).card ≤ (A w).card + 1 := by
    intro w
    by_cases hne : (S w).Nonempty
    · have hsub : (S w).erase ((S w).min' hne) ⊆ A w := by
        intro u hu
        refine Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hu, (S w).min' hne,
          Finset.min'_mem _ hne, ?_⟩
        exact lt_of_le_of_ne (Finset.min'_le _ u (Finset.mem_of_mem_erase hu))
          (Ne.symm (Finset.ne_of_mem_erase hu))
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.min'_mem _ hne)] at h1
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  have hE : ∀ w, ∀ u ∈ A w, ∃ k, Q gs (S w) (y w) u k := by
    intro w u hu
    obtain ⟨huS, u', hu', hlt⟩ := Finset.mem_filter.mp hu
    have t1 := hfire w u huS
    have t2 := hfire w u' hu'
    have t0 := hco w
    by_cases hn : out w < n
    · exfalso
      rw [V_input gs _ _ hn] at t1 t2 t0
      have hS0 : (⟨out w, hn⟩ : Fin n) ∈ S w := by simpa [c] using t0
      have hyy := hy0 w _ hS0
      simp only [z, hyy, false_or, decide_eq_true_eq] at t1 t2
      rw [← t1, ← t2] at hlt
      exact lt_irrefl _ hlt
    by_cases hw : n + gs.length ≤ out w
    · exfalso
      rw [V_missing gs _ _ hw] at t1
      exact Bool.noConfusion t1
    obtain ⟨k0, hk0⟩ : ∃ k, out w = n + k := ⟨out w - n, by omega⟩
    rw [hk0] at t0 t1 t2
    exact ⟨k0, by omega, t0, t1, u', hu', hlt, t2⟩
  let F : Fin m → Fin n → ℕ := fun w u =>
    if h : ∃ k, Q gs (S w) (y w) u k then Nat.find h else 0
  have hF : ∀ w, ∀ u ∈ A w, Q gs (S w) (y w) u (F w u) ∧
      ∀ j < F w u, ¬ Q gs (S w) (y w) u j := by
    intro w u hu
    have h := hE w u hu
    have e1 : F w u = Nat.find h := by simp only [F, h, ↓reduceDIte]
    rw [e1]
    exact ⟨Nat.find_spec h, fun r hr => Nat.find_min h hr⟩
  have hcard : (Finset.univ.sigma A).card ≤ D * (Finset.range gs.length).card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := fun p : (Σ _ : Fin m, Fin n) => F p.1 p.2)
    · intro p hp
      have hp' := (Finset.mem_sigma.mp hp).2
      exact Finset.mem_range.mpr (hF _ _ hp').1.1
    · intro k _
      have hinj : Set.InjOn (fun p : (Σ _ : Fin m, Fin n) => p.1)
          ((Finset.univ.sigma A).filter (fun p => F p.1 p.2 = k) : Finset (Σ _ : Fin m, Fin n)) := by
        rintro ⟨w, u⟩ hp ⟨w', u'⟩ hp' heq
        have hw : w = w' := heq
        subst hw
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
        obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp')
        have hu : u ∈ A w := (Finset.mem_sigma.mp hp1).2
        have hu' : u' ∈ A w := (Finset.mem_sigma.mp hq1).2
        have heq' : F w u = F w u' := by
          have e1 : F w u = k := hp2
          have e2 : F w u' = k := hq2
          rw [e1, e2]
        obtain ⟨q1, m1⟩ := hF w u hu
        obtain ⟨q2, m2⟩ := hF w u' hu'
        have huu : u = u' := by
          by_contra hne
          rw [← heq'] at q2 m2
          rcases lt_or_gt_of_ne hne with hh | hh
          · exact row_inj gs hops hlen (S w) (y w) (hy0 w) (F w u) u' u
              q2 m2 q1 m1 (Finset.mem_filter.mp hu).1 hh
          · exact row_inj gs hops hlen (S w) (y w) (hy0 w) (F w u) u u'
              q1 m1 q2 m2 (Finset.mem_filter.mp hu').1 hh
        rw [huu]
      rw [← Finset.card_image_of_injOn hinj]
      apply hD
      intro i hi j hj hij
      obtain ⟨⟨w, u⟩, hp, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨⟨w', u'⟩, hp', rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hp'
      have hu : u ∈ A w := (Finset.mem_sigma.mp hp1).2
      have hu' : u' ∈ A w' := (Finset.mem_sigma.mp hq1).2
      have e1 : F w u = k := hp2
      have e2 : F w' u' = k := hq2
      obtain ⟨q1, _⟩ := hF w u hu
      obtain ⟨q2, _⟩ := hF w' u' hu'
      rw [e1] at q1
      rw [e2] at q2
      exact cross gs hops (S w) (S w') (y w) k u (Finset.mem_filter.mp hu).1 q1 q2.2.1
        (hS w w' hij)
  rw [Finset.card_sigma, Finset.card_range] at hcard
  calc ∑ w1 : Fin m, (S w1).card
      ≤ ∑ w1 : Fin m, ((A w1).card + 1) := Finset.sum_le_sum fun w _ => hA w
    _ = ∑ w1 : Fin m, (A w1).card + m := by
        rw [Finset.sum_add_distrib]; simp
    _ ≤ D * gs.length + m := by omega

end PEqualNP.Outside.L_meta_1562

theorem PEqualNP.Outside.L_meta_1562 : ¬ (∃ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) ∧ (∀ i : Fin m, Disjoint (y i) (S i)) ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) ∧ (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) ∧ (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) ∧ D * C.gates.length + m < ∑ i : Fin m, (S i).card) := by
  rintro ⟨n, m, D, S, y, C, o, h1, h2, h3, h4, h5, h6, h7⟩
  have h := PEqualNP.Outside.L_meta_1562.main n m D S y C.gates o h1 h2 h3 h4 h5 h6
  omega

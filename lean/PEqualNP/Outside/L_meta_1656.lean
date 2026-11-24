import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1656

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

lemma V_and {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and) (hin : ∀ r ∈ gs[k].inputs, r < n + k) :
    V gs x (n + k) = true ↔ ∀ r ∈ gs[k].inputs, V gs x r = true := by
  rw [V_gate gs x k hk, hop]
  simp only [GateOp.eval, List.all_eq_true, id_eq]
  constructor
  · intro h r hr
    have := h _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
    simpa [hin r hr] using this
  · intro h b hb
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    simpa [hin r hr] using h r hr

lemma V_or {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) (hin : ∀ r ∈ gs[k].inputs, r < n + k) :
    V gs x (n + k) = true ↔ ∃ r ∈ gs[k].inputs, V gs x r = true := by
  rw [V_gate gs x k hk, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq]
  constructor
  · rintro ⟨b, hb, hv⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    exact ⟨r, hr, by simpa [hin r hr] using hv⟩
  · rintro ⟨r, hr, hv⟩
    exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, by simpa [hin r hr] using hv⟩

lemma card_merge (A : Finset ℕ) (a b : ℕ) :
    A.card ≤ (A.image (fun x => if x = a then b else x)).card + 1 := by
  have h1 : (A.erase a).card ≤ (A.image (fun x => if x = a then b else x)).card := by
    apply Finset.card_le_card_of_injOn (fun x => if x = a then b else x)
    · intro x hx
      have hx2 : x ∈ A.erase a := hx
      exact Finset.mem_image_of_mem _ (Finset.mem_erase.mp hx2).2
    · intro x hx z hz hxz
      have hx2 : x ∈ A.erase a := hx
      have hz2 : z ∈ A.erase a := hz
      have hxz2 : (if x = a then b else x) = (if z = a then b else z) := hxz
      rw [ite_eq_right (Finset.mem_erase.mp hx2).1, ite_eq_right (Finset.mem_erase.mp hz2).1] at hxz2
      exact hxz2
  have h2 := Finset.pred_card_le_card_erase (s := A) (a := a)
  omega

lemma main {n : ℕ} (gs : List Gate) (l y : Finset (Fin n))
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hrd : ∀ k : ℕ, ∀ g : Gate, gs[k]? = some g → ∀ i ∈ g.inputs, i < n + k) :
    ∀ m : ℕ, ∃ (c : Fin n → ℕ) (s : Finset ℕ), l.card ≤ (l.image c).card + s.card ∧
      (∀ k ∈ s, n + k < m ∧ ∃ g : Gate, gs[k]? = some g ∧ g.op = GateOp.or ∧
        V gs (fun u : Fin n => decide (u ∈ y)) (n + k) = false ∧
        ∃ i1 ∈ g.inputs, ∃ i2 ∈ g.inputs, i1 ≠ i2 ∧ ∃ p1 ∈ l, ∃ p2 ∈ l,
          V gs (fun u : Fin n => decide (u ∈ y ∨ u = p1)) i1 = true ∧
          V gs (fun u : Fin n => decide (u ∈ y ∨ u = p2)) i2 = true) ∧
      (∀ w < m, V gs (fun u : Fin n => decide (u ∈ y)) w = false → ∀ p1 ∈ l, ∀ p2 ∈ l,
        V gs (fun u : Fin n => decide (u ∈ y ∨ u = p1)) w = true →
        V gs (fun u : Fin n => decide (u ∈ y ∨ u = p2)) w = true → c p1 = c p2) := by
  intro m
  induction m with
  | zero =>
    refine ⟨fun p => p.val, ∅, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ Fin.val_injective]; simp
    · intro k hk; simp at hk
    · intro w hw; exact absurd hw (Nat.not_lt_zero w)
  | succ m ih =>
    obtain ⟨c, s, hcard, hs, hinv⟩ := ih
    have keep : (V gs (fun u : Fin n => decide (u ∈ y)) m = false → ∀ p1 ∈ l, ∀ p2 ∈ l,
        V gs (fun u : Fin n => decide (u ∈ y ∨ u = p1)) m = true →
        V gs (fun u : Fin n => decide (u ∈ y ∨ u = p2)) m = true → c p1 = c p2) →
        ∃ (c : Fin n → ℕ) (s : Finset ℕ), l.card ≤ (l.image c).card + s.card ∧
      (∀ k ∈ s, n + k < m + 1 ∧ ∃ g : Gate, gs[k]? = some g ∧ g.op = GateOp.or ∧
        V gs (fun u : Fin n => decide (u ∈ y)) (n + k) = false ∧
        ∃ i1 ∈ g.inputs, ∃ i2 ∈ g.inputs, i1 ≠ i2 ∧ ∃ p1 ∈ l, ∃ p2 ∈ l,
          V gs (fun u : Fin n => decide (u ∈ y ∨ u = p1)) i1 = true ∧
          V gs (fun u : Fin n => decide (u ∈ y ∨ u = p2)) i2 = true) ∧
      (∀ w < m + 1, V gs (fun u : Fin n => decide (u ∈ y)) w = false → ∀ p1 ∈ l, ∀ p2 ∈ l,
        V gs (fun u : Fin n => decide (u ∈ y ∨ u = p1)) w = true →
        V gs (fun u : Fin n => decide (u ∈ y ∨ u = p2)) w = true → c p1 = c p2) := by
      intro hm
      refine ⟨c, s, hcard, fun k hk => ⟨by have := (hs k hk).1; omega, (hs k hk).2⟩, ?_⟩
      intro w hw
      rcases Nat.lt_succ_iff_lt_or_eq.mp hw with h | h
      · exact hinv w h
      · rw [h]; exact hm
    by_cases hn : m < n
    · apply keep
      intro hY p1 hp1 p2 hp2 h1 h2
      rw [V_input gs _ m hn] at hY h1 h2
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hY h1 h2
      have e1 := h1.resolve_left hY
      have e2 := h2.resolve_left hY
      exact (congrArg c e1).symm.trans (congrArg c e2)
    by_cases hw : n + gs.length ≤ m
    · apply keep
      intro hY p1 hp1 p2 hp2 h1 h2
      rw [V_missing gs _ m hw] at h1
      exact Bool.noConfusion h1
    obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    have hk : k < gs.length := by omega
    have hgk : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
    have hin : ∀ r ∈ gs[k].inputs, r < n + k := hrd k gs[k] hgk
    obtain ⟨hop, hlen⟩ := hops gs[k] (List.getElem_mem hk)
    by_cases hY : V gs (fun u : Fin n => decide (u ∈ y)) (n + k) = false
    swap
    · apply keep
      intro hY2
      exact absurd hY2 hY
    rcases hop with hop | hop
    · apply keep
      intro _ p1 hp1 p2 hp2 h1 h2
      obtain ⟨r, hr, hrv⟩ : ∃ r ∈ gs[k].inputs,
          V gs (fun u : Fin n => decide (u ∈ y)) r = false := by
        by_contra hcon
        have hall : ∀ r ∈ gs[k].inputs, V gs (fun u : Fin n => decide (u ∈ y)) r = true := by
          intro r hr
          by_contra hne
          exact hcon ⟨r, hr, by simpa using hne⟩
        have hh := (V_and gs _ k hk hop hin).mpr hall
        rw [hY] at hh
        exact Bool.noConfusion hh
      exact hinv r (hin r hr) hrv p1 hp1 p2 hp2 ((V_and gs _ k hk hop hin).mp h1 r hr)
        ((V_and gs _ k hk hop hin).mp h2 r hr)
    · have hYall : ∀ r ∈ gs[k].inputs, V gs (fun u : Fin n => decide (u ∈ y)) r = false := by
        intro r hr
        by_contra hne
        have ht : V gs (fun u : Fin n => decide (u ∈ y)) r = true := by simpa using hne
        have hh := (V_or gs _ k hk hop hin).mpr ⟨r, hr, ht⟩
        rw [hY] at hh
        exact Bool.noConfusion hh
      by_cases hgood : ∃ i1 ∈ gs[k].inputs, ∃ i2 ∈ gs[k].inputs, i1 ≠ i2 ∧ ∃ p1 ∈ l, ∃ p2 ∈ l,
          V gs (fun u : Fin n => decide (u ∈ y ∨ u = p1)) i1 = true ∧
          V gs (fun u : Fin n => decide (u ∈ y ∨ u = p2)) i2 = true
      · obtain ⟨i1, hi1, i2, hi2, hne, p1, hp1, p2, hp2, hv1, hv2⟩ := hgood
        have hkey : ∀ q ∈ l, V gs (fun u : Fin n => decide (u ∈ y ∨ u = q)) (n + k) = true →
            (if c q = c p1 then c p2 else c q) = c p2 := by
          intro q hq hqv
          obtain ⟨r, hr, hrv⟩ := (V_or gs _ k hk hop hin).mp hqv
          rcases three_distinct gs[k].inputs r i1 i2 hlen hr hi1 hi2 with h | h | h
          · rw [← h] at hv1
            have hc := hinv r (hin r hr) (hYall r hr) q hq p1 hp1 hrv hv1
            rw [ite_eq_left hc]
          · exact absurd h hne
          · rw [← h] at hv2
            have hc := hinv r (hin r hr) (hYall r hr) q hq p2 hp2 hrv hv2
            rw [hc]
            exact ite_self _
        refine ⟨fun q => if c q = c p1 then c p2 else c q, insert k s, ?_, ?_, ?_⟩
        · have hnot : k ∉ s := fun hks => by have := (hs k hks).1; omega
          rw [Finset.card_insert_of_notMem hnot]
          have himg : l.image (fun q => if c q = c p1 then c p2 else c q) =
              (l.image c).image (fun x => if x = c p1 then c p2 else x) :=
            (Finset.image_image (s := l) (f := c)
              (g := fun x => if x = c p1 then c p2 else x)).symm
          rw [himg]
          have hm := card_merge (l.image c) (c p1) (c p2)
          omega
        · intro k2 hk2
          rcases Finset.mem_insert.mp hk2 with h | h
          · rw [h]
            exact ⟨by omega, gs[k], hgk, hop, hY, i1, hi1, i2, hi2, hne, p1, hp1, p2, hp2,
              hv1, hv2⟩
          · exact ⟨by have := (hs k2 h).1; omega, (hs k2 h).2⟩
        · intro w hw hYw q1 hq1 q2 hq2 h1 h2
          show (if c q1 = c p1 then c p2 else c q1) = (if c q2 = c p1 then c p2 else c q2)
          rcases Nat.lt_succ_iff_lt_or_eq.mp hw with h | h
          · have hc := hinv w h hYw q1 hq1 q2 hq2 h1 h2
            rw [hc]
          · rw [h] at h1 h2
            rw [hkey q1 hq1 h1, hkey q2 hq2 h2]
      · apply keep
        intro _ q1 hq1 q2 hq2 h1 h2
        obtain ⟨r1, hr1, hv1⟩ := (V_or gs _ k hk hop hin).mp h1
        obtain ⟨r2, hr2, hv2⟩ := (V_or gs _ k hk hop hin).mp h2
        have heq : r1 = r2 := by
          by_contra hne
          exact hgood ⟨r1, hr1, r2, hr2, hne, q1, hq1, q2, hq2, hv1, hv2⟩
        rw [← heq] at hv2
        exact hinv r1 (hin r1 hr1) (hYall r1 hr1) q1 hq1 q2 hq2 hv1 hv2

end PEqualNP.Outside.L_meta_1656

theorem PEqualNP.Outside.L_meta_1656 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ) (l y : Finset (Fin n)),
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y)))).getD out false = false →
  (∀ p ∈ l, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u = p)))).getD out false = true) →
  ∃ s : Finset ℕ, l.card ≤ s.card + 1 ∧ ∀ k ∈ s, ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g ∧
    g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y)))).getD (n + k) false = false ∧
    ∃ i1 ∈ g.inputs, ∃ i2 ∈ g.inputs, i1 ≠ i2 ∧ ∃ p1 ∈ l, ∃ p2 ∈ l,
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y ∨ u = p1)))).getD i1 false = true ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y ∨ u = p2)))).getD i2 false = true := by
  intro n gates out l y hops hrd hY hE
  obtain ⟨c, s, hcard, hs, hinv⟩ :=
    PEqualNP.Outside.L_meta_1656.main gates l y hops hrd (out + 1)
  refine ⟨s, ?_, fun k hk => (hs k hk).2⟩
  have hsame : ∀ p1 ∈ l, ∀ p2 ∈ l, c p1 = c p2 := by
    intro p1 hp1 p2 hp2
    have hup : ∀ p ∈ l, PEqualNP.Outside.L_meta_1656.V gates
        (fun u : Fin n => decide (u ∈ y ∨ u = p)) out = true := by
      intro p hp
      refine PEqualNP.Outside.L_meta_1656.mono gates (fun g hg => (hops g hg).1)
        (fun u : Fin n => decide (u = p)) (fun u : Fin n => decide (u ∈ y ∨ u = p)) ?_ out
        (hE p hp)
      intro u hu
      have hu2 : u = p := by simpa using hu
      simp [hu2]
    exact hinv out (Nat.lt_succ_self out) hY p1 hp1 p2 hp2 (hup p1 hp1) (hup p2 hp2)
  have h1 : (l.image c).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨p2, hp2, rfl⟩ := Finset.mem_image.mp hb
    exact hsame p1 hp1 p2 hp2
  omega

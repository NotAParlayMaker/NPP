import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1655

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

lemma or_eval (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ e ∈ l, f e = true := by
  simp [GateOp.eval]

lemma and_eval (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ e ∈ l, f e = true := by
  simp [GateOp.eval]

lemma not_eval (a : ℕ) (r : List ℕ) (f : ℕ → Bool) :
    GateOp.not.eval ((a :: r).map f) = !(f a) := by
  simp [GateOp.eval]

end PEqualNP.Outside.L_meta_1655

open PEqualNP.Outside.L_meta_1655

theorem PEqualNP.Outside.L_meta_1655 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    ∀ Sm Dm : Fin N → ℕ → Prop,
    (∀ (t : Fin N) (w : ℕ), Sm t w ↔ ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev w x = true → ∃ v ∈ L t, x v = true) →
    (∀ (t : Fin N) (w : ℕ), Dm t w ↔ (Sm t w ∧ ∀ p ∈ L i0, ev w (fun v : Fin N => decide (v = p)) = true → p ∈ L t)) →
    ∀ Vs : Fin N → ℕ → Fin N → Prop,
    (∀ (t : Fin N) (w : ℕ) (v : Fin N), Vs t w v ↔ ((Dm t w ∧ ev w (fun uu : Fin N => decide (uu = v)) = true) ∨ (¬ Dm t w ∧ v ∉ L i0 ∧ ev w (fun uu : Fin N => decide (uu = v)) = true))) →
    ∀ t : Fin N,
    (∀ (w : ℕ) (v : Fin N), Dm t w → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or → (Sm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Sm t e) ∧ (Dm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Dm t e)) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and → Sm t (N + (g : ℕ)) → ∃ e ∈ (gates.get g).inputs, Sm t e) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → Vs t w v → v ∈ L t) := by
  intro q N L i0 p0 p1 hq hN hcard hint hline hp01 hp0 hp1 gates o j h hops hin hjop huniq hhj hhead hout ev hev he0 he1 heoth hW Sm Dm hSm hDm Vs hVs t
  have hV : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = V gates x w := fun w x => (hev w x).trans rfl
  have hG : ∀ (g : Fin gates.length) (x : Fin N → Bool),
      ev (N + (g : ℕ)) x = (gates.get g).op.eval ((gates.get g).inputs.map fun r => ev r x) := by
    intro g x
    rw [hV, V_gate gates x g.val g.isLt]
    show (gates.get g).op.eval _ = _
    congr 1
    apply List.map_congr_left
    intro r hr
    rw [ite_eq_left (hin g r hr), hV]
  obtain ⟨rr, hrr⟩ := hhead
  have hlt : N + (h : ℕ) < N + (j : ℕ) := hin j _ (by rw [hrr]; simp)
  have hM : ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v, x v = true → y v = true) →
      (∀ v, y v = true → v ∉ L i0) → ev w x = true → ev w y = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro x y hxy hy hx
      by_cases hw : w < N
      · rw [hV] at hx ⊢
        rw [V_input gates _ w hw] at hx ⊢
        exact hxy _ hx
      · by_cases hw2 : w < N + gates.length
        · obtain ⟨g, rfl⟩ : ∃ g : Fin gates.length, w = N + (g : ℕ) :=
            ⟨⟨w - N, by omega⟩, by show w = N + (w - N); omega⟩
          rcases (hops (gates.get g) (List.get_mem _ _)).1 with ho | ho | ho
          · rw [hG, ho] at hx ⊢
            rw [and_eval] at hx ⊢
            intro r hr
            exact ih r (hin g r hr) x y hxy hy (hx r hr)
          · rw [hG, ho] at hx ⊢
            rw [or_eval] at hx ⊢
            obtain ⟨r, hr, hh⟩ := hx
            exact ⟨r, hr, ih r (hin g r hr) x y hxy hy hh⟩
          · have hgj : g = j := huniq g ho
            have hfalse : ev (N + (h : ℕ)) y = false := by
              by_contra hc
              have hc' : ev (N + (h : ℕ)) y = true := by simpa using hc
              have h2 := ih (N + (h : ℕ)) (by rw [hgj]; exact hlt) y (fun v : Fin N => decide (v ∉ L i0))
                (fun v hv => decide_eq_true (hy v hv)) (fun v hv => of_decide_eq_true hv) hc'
              rw [hW] at h2
              cases h2
            rw [hgj, hG, hjop, hrr, not_eval, hfalse]
            rfl
        · rw [hV, V_missing gates x w (by omega)] at hx
          cases hx
  have hand : ∀ l : List ℕ, (∀ e ∈ l, ¬ Sm t e) → ∃ x : Fin N → Bool,
      (∀ v, x v = true → v ∉ L i0) ∧ (∀ e ∈ l, ev e x = true) ∧ ∀ v ∈ L t, x v ≠ true := by
    intro l
    induction l with
    | nil => intro _; exact ⟨fun _ => false, by simp, by simp, by simp⟩
    | cons a l ih =>
      intro hl
      obtain ⟨x1, h1, h2, h3⟩ := ih (fun e he => hl e (List.mem_cons_of_mem _ he))
      have ha : ∃ x2 : Fin N → Bool, (∀ v, x2 v = true → v ∉ L i0) ∧ ev a x2 = true ∧
          ∀ v ∈ L t, x2 v ≠ true := by
        by_contra hc
        apply hl a (by simp)
        rw [hSm]
        intro x hx hex
        by_contra hc2
        exact hc ⟨x, hx, hex, fun v hv hxv => hc2 ⟨v, hv, hxv⟩⟩
      obtain ⟨x2, k1, k2, k3⟩ := ha
      have hsup : ∀ v, (x1 v || x2 v) = true → v ∉ L i0 := by
        intro v hv
        rcases Bool.or_eq_true_iff.1 hv with hv | hv
        · exact h1 v hv
        · exact k1 v hv
      refine ⟨fun v => x1 v || x2 v, hsup, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact hM _ x2 _ (fun v hv => Bool.or_eq_true_iff.2 (Or.inr hv)) hsup k2
        · exact hM _ x1 _ (fun v hv => Bool.or_eq_true_iff.2 (Or.inl hv)) hsup (h2 e he)
      · intro v hv hc
        rcases Bool.or_eq_true_iff.1 hc with hc | hc
        · exact h3 v hv hc
        · exact k3 v hv hc
  have c2 : ∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 →
      ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t := by
    intro w v hs hv he
    obtain ⟨u, hu, hu2⟩ := (hSm t w).1 hs _
      (fun u hu => by have huv : u = v := of_decide_eq_true hu; rw [huv]; exact hv) he
    have huv : u = v := of_decide_eq_true hu2
    rw [← huv]
    exact hu
  have c1 : ∀ (w : ℕ) (v : Fin N), Dm t w →
      ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t := by
    intro w v hd he
    by_cases hv : v ∈ L i0
    · exact ((hDm t w).1 hd).2 v hv he
    · exact c2 w v ((hDm t w).1 hd).1 hv he
  refine ⟨c1, c2, ?_, ?_, ?_⟩
  · intro g ho
    have key : ∀ e ∈ (gates.get g).inputs, ∀ x : Fin N → Bool, ev e x = true →
        ev (N + (g : ℕ)) x = true := by
      intro e he x hx
      rw [hG, ho, or_eval]
      exact ⟨e, he, hx⟩
    have keyS : Sm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Sm t e := by
      intro hs e he
      rw [hSm] at hs ⊢
      intro x hx hex
      exact hs x hx (key e he x hex)
    refine ⟨keyS, fun hd e he => ?_⟩
    rw [hDm] at hd ⊢
    exact ⟨keyS hd.1 e he, fun p hp hep => hd.2 p hp (key e he _ hep)⟩
  · intro g ho hs
    by_contra hc
    obtain ⟨x, h1, h2, h3⟩ := hand (gates.get g).inputs (fun e he hse => hc ⟨e, he, hse⟩)
    obtain ⟨v, hv, hxv⟩ := (hSm t _).1 hs x h1 (by rw [hG, ho]; exact (and_eval _ _).2 h2)
    exact h3 v hv hxv
  · intro w v hs hvs
    rcases (hVs t w v).1 hvs with ⟨hd, he⟩ | ⟨_, hv, he⟩
    · exact c1 w v hd he
    · exact c2 w v hs hv he

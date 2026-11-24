import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1637_aux
open PEqualNP.CircuitLowerBounds
namespace CoWire

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

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

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

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

end CoWire
end PEqualNP.Outside.L_meta_1637_aux

set_option maxHeartbeats 1200000 in
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1637_aux in
theorem PEqualNP.Outside.L_meta_1637 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ TS : Fin N → Fin N → ℕ → Prop,
    (∀ (l m : Fin N) (w : ℕ), TS l m w ↔ (ev w (fun v : Fin N => decide (v ∉ L l)) = false ∧ ev w (fun v : Fin N => decide (v ∉ L m)) = false ∧ (∃ p ∈ L l, ev w (T l p) = true) ∧ ∃ p ∈ L m, ev w (T m p) = true)) →
    ∀ Hg : Fin N → Fin N → Fin gates.length → Prop,
    (∀ (l m : Fin N) (g : Fin gates.length), Hg l m g ↔ (TS l m (N + (g : ℕ)) ∧ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ e ∈ (gates.get g).inputs, ¬ TS l m e)))) →
    ∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      (∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m)) ∧
      (∀ p : Fin N, p ∈ L l → p ∈ L m → (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧ (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p)) ∧
      ∀ w : ℕ, TS l m w → ∃ ν : ℕ, (∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → ν ∈ Zs) ∧
        ((∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ ν = (c : ℕ)) ∨ ∃ h : Fin gates.length, ν = (N + (h : ℕ)) ∧ Hg l m h) ∧
        (∀ s ∈ L l, ev ν (T l s) = true → ev w (T l s) = true) ∧ (∀ s ∈ L m, ev ν (T m s) = true → ev w (T m s) = true) ∧
        (∃ s ∈ L l, ev ν (T l s) = true) ∧ ∃ s ∈ L m, ev ν (T m s) = true := by
  classical
  intro q N L i0 p0 p1 hq hN hcard hinter hpair hp01 hp0 hp1 T hT gates hG hnon hearlier ev hev TS hTS Hg hHg l m hl hm
  have inp (p : Fin N) (x : Fin N → Bool) : ev p x = x p := by
    rw [hev]
    exact CoWire.input_value ⟨gates, p⟩ x p
  have testL (p : Fin N) (hpL : p ∈ L l) (hpM : p ∈ L m) (s : Fin N) :
      ev p (T l s) = true ↔ s = p := by
    have hn : p ≠ p1 := fun h => hl.2 (h ▸ hpL)
    rw [inp, hT]
    simp [hl.1, hl.2, hn, eq_comm]
  have testM (p : Fin N) (hpL : p ∈ L l) (hpM : p ∈ L m) (s : Fin N) :
      ev p (T m s) = true ↔ s = p := by
    have hn : p ≠ p0 := fun h => hm.2 (h ▸ hpM)
    rw [inp, hT]
    simp [hm.1, hm.2, hn, eq_comm]
  have inputTS (p : Fin N) : TS l m p ↔ p ∈ L l ∧ p ∈ L m := by
    constructor
    · intro h
      have hv := (hTS l m p).mp h
      exact ⟨by simpa [inp] using hv.1, by simpa [inp] using hv.2.1⟩
    · rintro ⟨hpL,hpM⟩
      apply (hTS l m p).mpr
      exact ⟨by simp [inp,hpL], by simp [inp,hpM],
        ⟨p,hpL,(testL p hpL hpM p).mpr rfl⟩,
        ⟨p,hpM,(testM p hpL hpM p).mpr rfl⟩⟩
  refine ⟨inputTS, ?_, ?_⟩
  · intro p hpL hpM
    exact ⟨fun s _ => testL p hpL hpM s, fun s _ => testM p hpL hpM s⟩
  · have orLift (g : Fin gates.length) (hop : (gates.get g).op = GateOp.or)
        (e : ℕ) (he : e ∈ (gates.get g).inputs) (x : Fin N → Bool)
        (hx : ev e x = true) : ev (N + g.val) x = true := by
      let D : Circuit := ⟨gates, 0⟩
      have hb : N + g.val < N + D.size := Nat.add_lt_add_left g.isLt N
      have hv := CoWire.gate_value D x (N + g.val) (by omega) hb
      have hv' : ev (N + g.val) x = (gates.get g).op.eval
          ((gates.get g).inputs.map fun r => if r < N + g.val then ev r x else false) := by
        simp only [hev]
        simpa [D, CoWire.value, Circuit.eval, Circuit.wires] using hv
      rw [hv', hop, GateOp.eval, List.any_eq_true]
      refine ⟨true, List.mem_map.mpr ⟨e, he, ?_⟩, rfl⟩
      simp [hearlier g e he, hx]
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      have ht := (hTS l m w).mp hw
      by_cases hin : w < N
      · let c : Fin N := ⟨w,hin⟩
        have hc := (inputTS c).mp hw
        exact ⟨w, fun _ h _ => h, Or.inl ⟨c,hc.1,hc.2,rfl⟩,
          fun _ _ h => h, fun _ _ h => h, ht.2.2.1, ht.2.2.2⟩
      · have hbound : w < N + gates.length := by
          by_contra! hbad
          obtain ⟨s,hs,hv⟩ := ht.2.2.1
          rw [hev] at hv
          have hh := CoWire.missing_value ⟨gates,w⟩ (T l s) w hbad
          change Circuit.eval ⟨gates,w⟩ (List.ofFn (T l s)) = false at hh
          rw [hh] at hv
          contradiction
        let g : Fin gates.length := ⟨w-N,by omega⟩
        have wg : w = N + g.val := by dsimp [g]; omega
        have atg : TS l m (N + g.val) := wg ▸ hw
        have stopHere (hh : Hg l m g) :
            ∃ ν : ℕ, (∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → ν ∈ Zs) ∧
            ((∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ ν = (c : ℕ)) ∨ ∃ h : Fin gates.length, ν = (N + (h : ℕ)) ∧ Hg l m h) ∧
            (∀ s ∈ L l, ev ν (T l s) = true → ev w (T l s) = true) ∧ (∀ s ∈ L m, ev ν (T m s) = true → ev w (T m s) = true) ∧
            (∃ s ∈ L l, ev ν (T l s) = true) ∧ ∃ s ∈ L m, ev ν (T m s) = true := by
          exact ⟨w, fun _ h _ => h, Or.inr ⟨g,wg,hh⟩,
            fun _ _ h => h, fun _ _ h => h, ht.2.2.1, ht.2.2.2⟩
        rcases (hG _ (List.get_mem gates g)).1 with ha | ho
        · exact stopHere ((hHg l m g).mpr ⟨atg,Or.inl ha⟩)
        · by_cases hchild : ∃ e ∈ (gates.get g).inputs, TS l m e
          · obtain ⟨e,he,hte⟩ := hchild
            have hel : e < w := by rw [wg]; exact hearlier g e he
            obtain ⟨ν,hcone,hkind,hleft,hright,hlive,hmive⟩ := ih e hel hte
            refine ⟨ν, ?_, hkind, ?_, ?_, hlive, hmive⟩
            · intro Z hz hclosed
              apply hcone Z (hclosed g (wg ▸ hz) e he) hclosed
            · intro s hs hv
              rw [wg]
              exact orLift g ho e he _ (hleft s hs hv)
            · intro s hs hv
              rw [wg]
              exact orLift g ho e he _ (hright s hs hv)
          · exact stopHere ((hHg l m g).mpr ⟨atg,Or.inr ⟨ho,fun e he h => hchild ⟨e,he,h⟩⟩⟩)

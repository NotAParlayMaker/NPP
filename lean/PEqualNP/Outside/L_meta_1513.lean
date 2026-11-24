import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1513_aux

-- The wire evaluation lemmas and the frontier argument adapt earlier proofs of
-- L_meta_1374 and L_meta_1460 in this repository.

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

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
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

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hm : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, h⟩)
      · simp [h]
    rw [gate_value C x w hn hw] at hx
    rw [gate_value C y w hn hw]
    change g.op.eval _ = true at hx ⊢
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

abbrev Good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def one {n : ℕ} (p : Fin n) (v : Fin n) := decide (v=p)
def co {n : ℕ} (S : Finset (Fin n)) (v : Fin n) := decide (v ∉ S)

def resetGates (gs : List Gate) (j : ℕ) := gs.set j ⟨GateOp.or,[]⟩
def fixed (gs : List Gate) (j : ℕ) : Circuit := ⟨resetGates gs j,0⟩

def strict {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (y : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ a b : ℕ, a<w ∧ b<w ∧ C.gates[w-n]?=some ⟨GateOp.or,[a,b]⟩ ∧
    value C y w=false ∧ ∃ p∈T, ∃ q∈T, p≠q ∧ value C (one p) a=true ∧ value C (one q) b=true

theorem gate_at (C : Circuit) {n : ℕ} (x : Fin n → Bool) (i : Fin C.gates.length) :
    value C x (n+i.val) = (C.gates.get i).op.eval ((C.gates.get i).inputs.map
      (fun r => if r<n+i.val then value C x r else false)) := by
  have h := gate_value C x (n+i.val) (by omega) (by have := i.isLt; unfold Circuit.size; omega)
  simpa only [Nat.add_sub_cancel_left,List.get_eq_getElem] using h

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

def Sv {n : ℕ} {ι : Type*} (C : Circuit) (l : ι → Fin n → Bool) (y : Fin n → Bool)
    (p : ι) (w : ℕ) : Prop :=
  value C (l p) w = true ∧ value C y w = false

def Multi {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ Sv C l y p w ∧ Sv C l y p' w

lemma list_cases (L : List ℕ) (hL : L.length ≤ 2) (Q : ℕ → Prop) :
    (L.length = 2 ∧ ∀ r ∈ L, Q r) ∨ ∃ c, ∀ r ∈ L, Q r → r = c := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · exact Or.inr ⟨0, fun r hr => absurd hr (by simp)⟩
  · exact Or.inr ⟨a, fun r hr _ => by simpa using hr⟩
  · by_cases ha : Q a
    · by_cases hb : Q b
      · refine Or.inl ⟨rfl, fun r hr => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · exact ha
        · exact hb
      · refine Or.inr ⟨a, fun r hr hq => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · rfl
        · exact absurd hq hb
    · refine Or.inr ⟨b, fun r hr hq => ?_⟩
      rcases List.mem_pair.mp hr with rfl | rfl
      · exact absurd hq ha
      · rfl
  · simp at hL

lemma step_cases {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < C.gates.length) (hm : Multi C T l y (n + k)) :
    (∃ r ∈ C.gates[k].inputs, r < n + k ∧ ∀ p ∈ T, Sv C l y p (n + k) → Sv C l y p r) ∨
    (C.gates[k].op = GateOp.or ∧ C.gates[k].inputs.length = 2 ∧
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, r < n + k ∧ value C (l p) r = true) ∧
      ∀ p ∈ T, Sv C l y p (n + k) → ∃ r ∈ C.gates[k].inputs, r < n + k ∧ Sv C l y p r) := by
  obtain ⟨p0, hp0, _, _, _, hs0, _⟩ := hm
  rcases (hC _ (List.getElem_mem hk)).1 with hop | hop
  · left
    have hy := hs0.2
    by_contra hcon
    have hall : ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C y r = true := by
      intro r hr
      by_contra hr2
      apply hcon
      have hlt := ((and_value C k hk hop (l p0)).mp hs0.1 r hr).1
      refine ⟨r, hr, hlt, fun p _ hsp => ⟨((and_value C k hk hop (l p)).mp hsp.1 r hr).2, ?_⟩⟩
      by_contra hne
      exact hr2 ⟨hlt, by simpa using hne⟩
    rw [(and_value C k hk hop y).mpr hall] at hy
    exact Bool.noConfusion hy
  · have hyall : ∀ r ∈ C.gates[k].inputs, r < n + k → value C y r = false := by
      intro r hr hlt
      by_contra h
      have h2 : value C y (n + k) = true :=
        (or_value C k hk hop y).mpr ⟨r, hr, hlt, by simpa using h⟩
      rw [hs0.2] at h2
      exact Bool.noConfusion h2
    have hsv : ∀ p ∈ T, Sv C l y p (n + k) →
        ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C (l p) r = true ∧ Sv C l y p r := by
      intro p _ hsp
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C k hk hop (l p)).mp hsp.1
      exact ⟨r, hr, hlt, hv, hv, hyall r hr hlt⟩
    rcases list_cases C.gates[k].inputs (hC _ (List.getElem_mem hk)).2
      (fun r => ∃ p ∈ T, r < n + k ∧ value C (l p) r = true) with ⟨hlen, hQ⟩ | ⟨c, hc⟩
    · right
      refine ⟨hop, hlen, fun r hr => ?_, fun p hp hsp => ?_⟩
      · exact hQ r hr
      · obtain ⟨r, hr, hlt, _, hs⟩ := hsv p hp hsp
        exact ⟨r, hr, hlt, hs⟩
    · left
      obtain ⟨r, hr, hlt, hv, _⟩ := hsv p0 hp0 hs0
      have hrc := hc r hr ⟨p0, hp0, hlt, hv⟩
      refine ⟨r, hr, hlt, fun p hp hsp => ?_⟩
      obtain ⟨r', hr', hlt', hv', hs'⟩ := hsv p hp hsp
      have hrc' := hc r' hr' ⟨p, hp, hlt', hv'⟩
      rw [hrc, ← hrc']
      exact hs'

lemma frontier {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W : Finset ℕ)
    (hW : ∀ k, ∀ hk : k < C.gates.length, Multi C T l y (n + k) →
      C.gates[k].op = GateOp.or → C.gates[k].inputs.length = 2 →
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, r < n + k ∧ value C (l p) r = true) → n + k ∈ W)
    (hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, Multi C T l y w → w < t)
    (T' : Finset ι) (hT' : T' ⊆ T) (hs : ∀ p ∈ T', ∃ w ∈ F, Sv C l y p w) :
    T'.card ≤ F.card + (W.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    choose! f hfF hfs using hs
    have hinj : Set.InjOn f T' := by
      intro p hp p' hp' e
      by_contra hne
      have hc : Multi C T l y (f p) :=
        ⟨p, hT' hp, p', hT' hp', hne, hfs p hp, by rw [e]; exact hfs p' hp'⟩
      have := hF (f p) (hfF p hp) hc
      omega
    have := Finset.card_le_card_of_injOn f (fun p hp => hfF p hp) hinj
    omega
  | succ t ih =>
    have hle : (W.filter (· < t)).card ≤ (W.filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
          by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases hex : t ∈ F ∧ Multi C T l y t
    · obtain ⟨h1, h2⟩ := hlen t hex.2
      have hk : t - n < C.gates.length := by omega
      have htk : t = n + (t - n) := by omega
      have hm : Multi C T l y (n + (t - n)) := by rw [← htk]; exact hex.2
      have he := Finset.card_erase_add_one hex.1
      rcases step_cases C T l y hC (t - n) hk hm with ⟨r, hr, hlt, hall⟩ | ⟨hop, hlen2, hQ, hsv⟩
      · rw [← htk] at hlt hall
        let F' := insert r (F.erase t)
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_insert.mp hw with hw | hw
          · rw [hw]; exact hlt
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsv⟩ := hs p hp
          by_cases h : w = t
          · subst h
            exact ⟨r, Finset.mem_insert_self _ _, hall p (hT' hp) hsv⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_insert_le r (F.erase t)
        change F'.card ≤ _ at hu
        omega
      · rw [← htk] at hsv
        have htW : t ∈ W := by
          have := hW (t - n) hk hm hop hlen2 hQ
          rwa [← htk] at this
        let P : Finset ℕ := (C.gates[t - n].inputs.filter (· < t)).toFinset
        have hPcard : P.card ≤ 2 := by
          have h1 := List.toFinset_card_le (C.gates[t - n].inputs.filter (· < t))
          have h2 := List.length_filter_le (fun r => decide (r < t)) C.gates[t - n].inputs
          change P.card ≤ _ at h1
          omega
        let F' := F.erase t ∪ P
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_union.mp hw with hw | hw
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
          · have := (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
            simpa using this
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsvp⟩ := hs p hp
          by_cases h : w = t
          · subst h
            obtain ⟨r, hr, hlt, hsr⟩ := hsv p (hT' hp) hsvp
            exact ⟨r, Finset.mem_union_right _ (List.mem_toFinset.mpr
              (List.mem_filter.mpr ⟨hr, by simpa using hlt⟩)), hsr⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hsvp⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_union_le (F.erase t) P
        change F'.card ≤ _ at hu
        have hfilter : W.filter (· < t + 1) = insert t (W.filter (· < t)) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hg, hlt⟩
            by_cases h : w = t
            · exact Or.inl h
            · exact Or.inr ⟨hg, by omega⟩
          · rintro (rfl | ⟨hg, hlt⟩)
            · exact ⟨htW, by omega⟩
            · exact ⟨hg, by omega⟩
        rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
    · have hF' : ∀ w ∈ F, Multi C T l y w → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      have := ih F hF' hs
      omega

lemma family {n : ℕ} {ι : Type*} (gates : List Gate)
    (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T : Finset ι) (l : ι → Fin n → Bool) (y : Fin n → Bool) (o : ℕ)
    (ho : ∀ p ∈ T, Sv ⟨gates, 0⟩ l y p o)
    (hin : ∀ w, w < n → ¬ Multi ⟨gates, 0⟩ T l y w)
    (K : Finset (Fin gates.length))
    (hK : ∀ g : Fin gates.length, Multi ⟨gates, 0⟩ T l y (n + (g : ℕ)) →
      gates[(g : ℕ)].op = GateOp.or → gates[(g : ℕ)].inputs.length = 2 →
      (∀ r ∈ gates[(g : ℕ)].inputs, ∃ p ∈ T, r < n + g.val ∧ value ⟨gates, 0⟩ (l p) r = true) → g ∈ K) :
    T.card ≤ K.card + 1 := by
  classical
  let C : Circuit := ⟨gates, 0⟩
  let W : Finset ℕ := Finset.image (fun g : Fin gates.length => n + (g : ℕ)) K
  have hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length := by
    intro w hc
    refine ⟨Nat.le_of_not_lt fun h => hin w h hc, ?_⟩
    by_contra hge
    obtain ⟨p, _, _, _, _, hsv, _⟩ := hc
    have hm := missing_value C (l p) w (by unfold Circuit.size; omega)
    have h1 := hsv.1
    rw [hm] at h1
    exact Bool.noConfusion h1
  have h := frontier C T l y hC W
    (fun k hk hm hop hl hQ => Finset.mem_image.mpr ⟨(⟨k, hk⟩ : Fin gates.length), hK ⟨k, hk⟩ hm hop hl hQ, rfl⟩)
    hlen (n + C.gates.length) {o}
    (fun w _ hc => (hlen w hc).2) T (Finset.Subset.refl T)
    (fun p hp => ⟨o, Finset.mem_singleton_self o, ho p hp⟩)
  have h1 := Finset.card_filter_le W (· < n + C.gates.length)
  have h2 : W.card ≤ K.card := Finset.card_image_le
  rw [Finset.card_singleton] at h
  omega

theorem simple_paid {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (y : Fin n → Bool)
    (k : ℕ) (hk : k < C.gates.length) (hm : Multi C T one y (n+k))
    (hop : C.gates[k].op=GateOp.or) (len : C.gates[k].inputs.length=2)
    (each : ∀ r ∈ C.gates[k].inputs, ∃ p∈T, r<n+k ∧ value C (one p) r=true) :
    strict C T y (n+k) := by
  obtain ⟨a,b,ab⟩ : ∃ a b, C.gates[k].inputs=[a,b] := by
    rcases hl : C.gates[k].inputs with _|⟨a,_|⟨b,_|⟨c,tl⟩⟩⟩ <;> simp_all
  have ea := each a (by simp [ab])
  have eb := each b (by simp [ab])
  obtain ⟨p,hp,ha,pa⟩ := ea
  obtain ⟨q,hq,hb,qb⟩ := eb
  obtain ⟨u,hu,v,hv,uv,su,sv⟩ := hm
  have gg : C.gates[k] = ⟨GateOp.or,[a,b]⟩ := by
    have η : (⟨C.gates[k].op,C.gates[k].inputs⟩ : Gate) = C.gates[k] := rfl
    rw [← η] at *
    simp_all
  refine ⟨a,b,ha,hb,?_,su.2,?_⟩
  · simp [List.getElem?_eq_getElem hk,gg]
  by_cases ne : p ≠ q
  · exact ⟨p,hp,q,hq,ne,pa,qb⟩
  have eq := Classical.not_not.mp ne
  subst q
  have other : ∃ z ∈ T, z≠p ∧ value C (one z) (n+k)=true := by
    by_cases up : u=p
    · exact ⟨v,hv,fun e => uv (up.trans e.symm),sv.1⟩
    · exact ⟨u,hu,up,su.1⟩
  obtain ⟨z,hz,zp,yes⟩ := other
  obtain ⟨w,mem,_,hot⟩ := (or_value C k hk hop (one z)).mp yes
  rw [ab] at mem
  rcases List.mem_pair.mp mem with rfl|rfl
  · exact ⟨z,hz,p,hp,zp,hot,qb⟩
  · exact ⟨p,hp,z,hz,zp.symm,pa,hot⟩

theorem row_paid {n : ℕ} (gs : List Gate) (T : Finset (Fin n)) (y : Fin n → Bool) (o : ℕ)
    (good : Good ⟨gs,0⟩) (cold : value ⟨gs,0⟩ y o=false)
    (hot : ∀ p∈T, value ⟨gs,0⟩ (one p) o=true)
    (B : Finset (Fin gs.length))
    (charge : ∀ g : Fin gs.length, strict ⟨gs,0⟩ T y (n+g.val) → g∈B) : T.card ≤ B.card+1 := by
  apply family gs good T one y o (fun p hp => ⟨hot p hp,cold⟩) _ B
  · intro g hm hop len ready
    exact charge g (simple_paid _ _ _ _ g.isLt hm hop len ready)
  · intro w lt ⟨p,hp,q,hq,ne,sp,sq⟩
    let v : Fin n := ⟨w,lt⟩
    have vp : v=p := by simpa only [input_value,one,decide_eq_true_eq] using (show value ⟨gs,0⟩ (one p) v=true from sp.1)
    have vq : v=q := by simpa only [input_value,one,decide_eq_true_eq] using (show value ⟨gs,0⟩ (one q) v=true from sq.1)
    exact ne (vp.symm.trans vq)

lemma fixed_size (gs : List Gate) (j : ℕ) : (fixed gs j).size=gs.length := by
  simp [fixed,resetGates,Circuit.size]

lemma fixed_get (gs : List Gate) (j i : Fin gs.length) :
    (fixed gs j).gates[i.val]'(by simpa only [fixed,resetGates,List.length_set] using i.isLt) =
      if j=i then ⟨GateOp.or,[]⟩ else gs.get i := by
  simp [fixed,resetGates,List.getElem_set,Fin.ext_iff,List.get_eq_getElem]

lemma fixed_gate_value {n : ℕ} (gs : List Gate) (j i : Fin gs.length) (x : Fin n → Bool) :
    value (fixed gs j) x (n+i.val)=
      (if j=i then (⟨GateOp.or,[]⟩ : Gate) else gs.get i).op.eval
      ((if j=i then (⟨GateOp.or,[]⟩ : Gate) else gs.get i).inputs.map
        (fun r => if r<n+i.val then value (fixed gs j) x r else false)) := by
  let t : Fin (fixed gs j).gates.length := ⟨i.val,by simpa [fixed,resetGates] using i.isLt⟩
  have h := gate_at (fixed gs j) x t
  change value (fixed gs j) x (n+i.val)= _ at h
  simpa only [t,List.get_eq_getElem,fixed_get] using h

lemma fixed_zero {n : ℕ} (gs : List Gate) (j : Fin gs.length) (x : Fin n → Bool) :
    value (fixed gs j) x (n+j.val)=false := by
  rw [fixed_gate_value]
  simp [GateOp.eval]

lemma fixed_good (gs : List Gate) (j : Fin gs.length)
    (allowed : ∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (sole : ∀ i : Fin gs.length, (gs.get i).op=GateOp.not → i=j) : Good (fixed gs j) := by
  intro g hg
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp hg
  let i : Fin gs.length := ⟨k,by simpa [fixed,resetGates] using hk⟩
  have heq := fixed_get gs j i
  change (fixed gs j).gates[k] = _ at heq
  rw [← eq,heq]
  by_cases same : j=i
  · simp [same]
  · rw [ite_eq_right same]
    obtain ⟨h,small⟩ := allowed _ (List.get_mem gs i)
    refine ⟨h.elim Or.inl (fun hit => ?_),small⟩
    exact hit.elim Or.inr (fun nt => False.elim (same (sole i nt).symm))

lemma fixed_agrees {n : ℕ} (gs : List Gate) (j : Fin gs.length) (x : Fin n → Bool)
    (off : value ⟨gs,0⟩ x (n+j.val)=false) (w : ℕ) :
    value (fixed gs j) x w=value ⟨gs,0⟩ x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<n
    · let v : Fin n := ⟨w,raw⟩
      exact (input_value (fixed gs j) x v).trans (input_value ⟨gs,0⟩ x v).symm
    by_cases valid : w<n+gs.length
    · let i : Fin gs.length := ⟨w-n,by omega⟩
      have eq : n+i.val=w := by dsimp [i];omega
      by_cases same : j=i
      · exact eq ▸ (same ▸ (fixed_zero gs j x).trans off.symm)
      rw [← eq,fixed_gate_value,ite_eq_right same,gate_at (⟨gs,0⟩ : Circuit) x i]
      have read (r : ℕ) : (if r<n+i.val then value (fixed gs j) x r else false)=
          (if r<n+i.val then value ⟨gs,0⟩ x r else false) := by
        split_ifs with lt
        · exact ih r (eq ▸ lt)
        · rfl
      simp only [read]
    · rw [missing_value (fixed gs j) x w (by rw [fixed_size];omega),
        missing_value (⟨gs,0⟩ : Circuit) x w (by change n+gs.length≤w;omega)]

lemma not_is_off {n : ℕ} (gs : List Gate) (j h : Fin gs.length) (hj : h<j)
    (op : (gs.get j).op=GateOp.not) (head : ∃ rest, (gs.get j).inputs=(n+h.val)::rest)
    (x : Fin n → Bool) (lit : value ⟨gs,0⟩ x (n+h.val)=true) :
    value ⟨gs,0⟩ x (n+j.val)=false := by
  obtain ⟨rest,eq⟩ := head
  rw [gate_at (⟨gs,0⟩ : Circuit) x j,op,eq]
  simp [GateOp.eval,Nat.add_lt_add_left hj n,lit]

theorem info {n : ℕ} (gs : List Gate) (j g : Fin gs.length) (T : Finset (Fin n)) (y : Fin n → Bool)
    (z : strict (fixed gs j) T y (n+g.val)) :
    g ≠ j ∧ n+j.val ∉ (gs.get g).inputs ∧ value (fixed gs j) y (n+g.val)=false ∧
    ∃ a b, gs.get g=⟨GateOp.or,[a,b]⟩ ∧ a<n+g.val ∧ b<n+g.val ∧
      ∃ p ∈ T, ∃ q ∈ T, p≠q ∧ value (fixed gs j) (one p) a=true ∧ value (fixed gs j) (one q) b=true := by
  obtain ⟨a,b,ha,hb,get,cold,p,hp,q,hq,pq,pa,qb⟩ := z
  have hidx : g.val < (fixed gs j).gates.length := by simpa [fixed,resetGates] using g.isLt
  simp only [Nat.add_sub_cancel_left,List.getElem?_eq_getElem hidx,Option.some.injEq] at get
  rw [fixed_get gs j g] at get
  by_cases eq : j=g
  · simp [eq] at get
  rw [ite_eq_right eq] at get
  refine ⟨Ne.symm eq,?_,cold,a,b,get,ha,hb,p,hp,q,hq,pq,pa,qb⟩
  rw [get]
  intro mem
  rcases List.mem_pair.mp mem with u|u
  · exact Bool.false_ne_true ((fixed_zero gs j (one p)).symm.trans (u ▸ pa))
  · exact Bool.false_ne_true ((fixed_zero gs j (one q)).symm.trans (u ▸ qb))

theorem strict_separates {n : ℕ} (gs : List Gate) (j g : Fin gs.length) (T : Finset (Fin n))
    (y : Fin n → Bool) (hit : strict (fixed gs j) T y (n+g.val)) :
    ∃ p ∈ T, ∃ q ∈ T, p≠q ∧ value (fixed gs j) (one p) (n+g.val)=true ∧
      value (fixed gs j) (one q) (n+g.val)=true := by
  obtain ⟨ne,_,_,a,b,eq,ha,hb,p,hp,q,hq,pq,pa,qb⟩ := info gs j g T y hit
  refine ⟨p,hp,q,hq,pq,?_,?_⟩
  · rw [fixed_gate_value,ite_eq_right ne.symm,eq]
    simp [GateOp.eval,ha,hb,pa]
  · rw [fixed_gate_value,ite_eq_right ne.symm,eq]
    simp [GateOp.eval,ha,hb,qb]

theorem in_set {n : ℕ} (C : Circuit) (good : Good C) (S : Finset (Fin n)) (w : ℕ)
    (cold : value C (co S) w=false) (p : Fin n) (hot : value C (one p) w=true) : p ∈ S := by
  by_contra h
  have le (v : Fin n) (hv : one p v=true) : co S v=true := by
    have eq : v=p := by simpa [one] using hv
    simpa [co,eq] using h
  exact Bool.false_ne_true (cold.symm.trans (value_mono C good _ _ le w hot))

theorem separate_sets {m n : ℕ} (gs : List Gate) (j g : Fin gs.length) (good : Good (fixed gs j))
    (S T : Fin m → Finset (Fin n)) (sub : ∀ i, T i ⊆ S i)
    (apart : ∀ i k, i≠k → (S i ∩ S k).card≤1) (i k : Fin m)
    (a : strict (fixed gs j) (T i) (co (S i)) (n+g.val))
    (b : strict (fixed gs j) (T k) (co (S k)) (n+g.val)) : i=k := by
  by_contra ne
  have cold := (info gs j g _ _ b).2.2.1
  obtain ⟨p,hp,q,hq,pq,wp,wq⟩ := strict_separates gs j g _ _ a
  have pp : p ∈ S i ∩ S k := Finset.mem_inter.mpr ⟨sub i hp,in_set _ good _ _ cold p wp⟩
  have qq : q ∈ S i ∩ S k := Finset.mem_inter.mpr ⟨sub i hq,in_set _ good _ _ cold q wq⟩
  have small := apart i k ne
  exact (Nat.not_lt_of_ge small) (Finset.one_lt_card.mpr ⟨p,pp,q,qq,pq⟩)

theorem count_parts {q m L : ℕ} (live : Fin m → ℕ) (B : Fin m → Finset (Fin L))
    (R I : Finset (Fin L)) (j h : Fin L) (jh : j≠h)
    (cap : ∀ i, live i ≤ (B i).card+1) (size : ∀ i, live i ≤ q+1)
    (distinct : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint B)
    (clear : ∀ i, ∀ g ∈ B i, g ∉ R ∧ g ≠ j ∧ g ≠ h ∧ g ∉ I)
    (rclear : ∀ g ∈ R, g ≠ j ∧ g ≠ h ∧ g ∉ I) (jc : j ∉ I) (hc : h ∉ I) :
    m*q+R.card+2+I.card ≤ L+∑ i, (q+1-live i) := by
  classical
  let U := Finset.univ.biUnion B
  have part (v) (hv : v ∈ U) : v ∉ R ∧ v ≠ j ∧ v ≠ h ∧ v ∉ I := by
    obtain ⟨i,_,hit⟩ := Finset.mem_biUnion.mp hv
    exact clear i v hit
  have ur : Disjoint U R := Finset.disjoint_left.mpr (fun g hg => (part g hg).1)
  have uj : j ∉ U ∪ R := by
    intro hg
    rcases Finset.mem_union.mp hg with a|a
    · exact (part _ a).2.1 rfl
    · exact (rclear _ a).1 rfl
  have uh : h ∉ insert j (U ∪ R) := by
    intro hg
    rcases Finset.mem_insert.mp hg with eq|hs
    · exact jh eq.symm
    rcases Finset.mem_union.mp hs with a|a
    · exact (part _ a).2.2.1 rfl
    · exact (rclear _ a).2.1 rfl
  have ui : Disjoint (insert h (insert j (U ∪ R))) I := by
    apply Finset.disjoint_left.mpr
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl|hx
    · exact hc
    rcases Finset.mem_insert.mp hx with rfl|hy
    · exact jc
    rcases Finset.mem_union.mp hy with a|a
    · exact (part _ a).2.2.2
    · exact (rclear _ a).2.2
  have total := Finset.card_le_univ (insert h (insert j (U ∪ R)) ∪ I)
  rw [Finset.card_union_of_disjoint ui,Finset.card_insert_of_notMem uh,Finset.card_insert_of_notMem uj,
    Finset.card_union_of_disjoint ur] at total
  have hu : U.card=∑ i, (B i).card := Finset.card_biUnion distinct
  rw [hu,Fintype.card_fin] at total
  have per (i : Fin m) : q ≤ (B i).card+(q+1-live i) := by have := cap i; have := size i; omega
  have bound : m*q ≤ (∑ i, (B i).card)+(∑ i, (q+1-live i)) := by
    calc
      m*q = ∑ _ : Fin m, q := by simp
      _ ≤ ∑ i, ((B i).card+(q+1-live i)) := Finset.sum_le_sum fun i _ => per i
      _ = _ := Finset.sum_add_distrib
  omega

end PEqualNP.Outside.L_meta_1513_aux

open PEqualNP.Outside.L_meta_1513_aux

theorem PEqualNP.Outside.L_meta_1513 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)),
    (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i i' : Fin m, i ≠ i' → (S i ∩ S i').card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ i : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = true) →
    ∀ I : Finset (Fin gates.length),
      (∀ g : Fin gates.length, g ∈ I ↔
        (g ≠ j ∧ g ≠ h ∧ ¬ (j < g ∧ n + (j : ℕ) ∈ (gates.get g).inputs) ∧
         ¬ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ i : Fin m,
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, n + (g : ℕ)⟩
              (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = false ∧
            ∃ (w1 w2 : ℕ), (gates.get g).inputs = [w1, w2] ∧
            ∃ p ∈ S i, ∃ p' ∈ S i, p ≠ p' ∧
              PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, out i⟩ (List.ofFn (fun v : Fin n => decide (v = p))) = true ∧
              PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, out i⟩ (List.ofFn (fun v : Fin n => decide (v = p'))) = true ∧
              PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w1⟩ (List.ofFn (fun v : Fin n => decide (v = p))) = true ∧
              PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w2⟩ (List.ofFn (fun v : Fin n => decide (v = p'))) = true))) →
      m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 + I.card
        ≤ gates.length + ∑ i : Fin m, (q + 1 - ((S i).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, out i⟩
            (List.ofFn (fun v : Fin n => decide (v = p))) = true)).card) := by
  classical
  intro q n m S sizes overlaps gs out j h allowed nt unique earlier source outputs liveH I memI
  let C := fixed gs j
  let T (i : Fin m) := (S i).filter (fun p => value C (one p) (out i)=true)
  let B (i : Fin m) := Finset.univ.filter (fun g : Fin gs.length => strict C (T i) (co (S i)) (n+g.val))
  let R := Finset.univ.filter (fun g : Fin gs.length => j<g ∧ n+j.val ∈ (gs.get g).inputs)
  have hj : h≠j := Fin.ne_of_lt earlier
  have good : Good C := fixed_good gs j allowed unique
  have originalH (i : Fin m) : value ⟨gs,0⟩ (co (S i)) (n+h.val)=true := liveH i
  have agree (i : Fin m) (w : ℕ) : value C (co (S i)) w=value ⟨gs,0⟩ (co (S i)) w :=
    fixed_agrees gs j _ (not_is_off gs j h earlier nt source _ (originalH i)) w
  have cold (i : Fin m) : value C (co (S i)) (out i)=false := by
    rw [agree]
    change Circuit.eval ⟨gs,out i⟩ (List.ofFn (co (S i)))=false
    rw [outputs]
    simp [co]
  have sub (i : Fin m) : T i ⊆ S i := Finset.filter_subset _ _
  have row (i : Fin m) : (T i).card ≤ (B i).card+1 := by
    have target (l : ℕ) (eq : (resetGates gs j).length=l) :
        (T i).card ≤ (Finset.univ.filter (fun g : Fin l => strict C (T i) (co (S i)) (n+g.val))).card+1 := by
      subst l
      apply row_paid (resetGates gs j) (T i) (co (S i)) (out i) good (cold i)
      · exact fun p hp => (Finset.mem_filter.mp hp).2
      · exact fun g hg => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg⟩
    exact target _ (by simp [resetGates])
  have dis : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint B := by
    intro i _ k _ ne
    exact Finset.disjoint_left.mpr fun g a b =>
      ne (separate_sets gs j g good S T sub overlaps i k (Finset.mem_filter.mp a).2 (Finset.mem_filter.mp b).2)
  have clear (i) (g) (hg : g∈B i) : g ∉ R ∧ g≠j ∧ g≠h ∧ g ∉ I := by
    obtain ⟨nj,skip,off,a,b,op,_,_,p,hp,q',hq,pq,pa,qb⟩ := info gs j g (T i) _ (Finset.mem_filter.mp hg).2
    have nh : g≠h := by
      rintro rfl
      exact Bool.false_ne_true (off.symm.trans ((agree i _).trans (originalH i)))
    refine ⟨fun hr => skip (Finset.mem_filter.mp hr).2.2,nj,nh,?_⟩
    intro hi
    apply ((memI g).mp hi).2.2.2
    refine ⟨congrArg Gate.op op,i,off,a,b,congrArg Gate.inputs op,p,(sub i hp),q',(sub i hq),pq,?_,?_,pa,qb⟩
    · exact (Finset.mem_filter.mp hp).2
    · exact (Finset.mem_filter.mp hq).2
  have rc (g) (hg : g ∈ R) : g ≠ j ∧ g ≠ h ∧ g ∉ I := by
    have H := (Finset.mem_filter.mp hg).2
    exact ⟨Ne.symm (Fin.ne_of_lt H.1),fun eq => (not_lt_of_ge (le_of_lt earlier)) (eq ▸ H.1),
      fun hi => ((memI g).mp hi).2.2.1 H⟩
  have hbound := count_parts (fun i => (T i).card) B R I j h hj.symm row
    (fun i => (Finset.card_le_card (sub i)).trans (sizes i).le) dis clear rc
    (fun hi => ((memI j).mp hi).1 rfl) (fun hi => ((memI h).mp hi).2.1 rfl)
  exact hbound

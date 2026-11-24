import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1643.Count

-- Circuit evaluation and monotonicity are adapted from the earlier projective-plane bounds.
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

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

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

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

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
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) ∧
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
      · obtain ⟨p, hp, _, hv⟩ := hQ r hr
        exact ⟨p, hp, hv⟩
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
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) → n + k ∈ W)
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
      (∀ r ∈ gates[(g : ℕ)].inputs, ∃ p ∈ T, value ⟨gates, 0⟩ (l p) r = true) → g ∈ K) :
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

end PEqualNP.Outside.L_meta_1643.Count

namespace PEqualNP.Outside.L_meta_1643
open PEqualNP.Outside.L_meta_1643.Count

-- A chain of q binary OR gates computes one line.
def partialWire {N q : ℕ} (points : Fin N → Fin (q+1) → Fin N) (t : Fin N) (k : ℕ) : ℕ :=
  if k=0 then (points t 0).val else N+(k-1+q*t.val)

def lineGate {N q : ℕ} (points : Fin N → Fin (q+1) → Fin N) (t : Fin N) (k : Fin q) : Gate :=
  ⟨.or,[partialWire points t k.val,(points t k.succ).val]⟩

def grid {N q : ℕ} (points : Fin N → Fin (q+1) → Fin N) : List Gate :=
  List.ofFn fun i : Fin (N*q) => let z := finProdFinEquiv.symm i; lineGate points z.1 z.2

lemma grid_len {N q : ℕ} (points : Fin N → Fin (q+1) → Fin N) : (grid points).length=N*q := by
  simp [grid]

lemma grid_index {N q : ℕ} (points : Fin N → Fin (q+1) → Fin N) (t : Fin N) (k : Fin q) :
    (grid points)[k.val+q*t.val]'(by rw [grid_len];exact (finProdFinEquiv (t,k)).isLt)=lineGate points t k := by
  let i := finProdFinEquiv (t,k)
  change (grid points)[i.val]'(by rw [grid_len];exact i.isLt)=_
  simp only [grid,List.getElem_ofFn]
  change lineGate points (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2=_
  simp [i]

lemma grid_earlier {N q : ℕ} (points : Fin N → Fin (q+1) → Fin N) (t : Fin N) (k : Fin q) :
    ∀ w∈(lineGate points t k).inputs, w<N+(k.val+q*t.val) := by
  intro w hw
  have h0 := (points t 0).isLt
  have h1 := (points t k.succ).isLt
  simp only [lineGate,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl
  · unfold partialWire
    split <;> omega
  · omega

lemma grid_result {N q : ℕ} (points : Fin N → Fin (q+1) → Fin N) (x : Fin N → Bool) (t : Fin N)
    (k : ℕ) (hk : k≤q) :
    value ⟨grid points,0⟩ x (partialWire points t k)=true ↔
      ∃ j : Fin (q+1), j.val≤k ∧ x (points t j)=true := by
  induction k with
  | zero =>
    rw [partialWire,ite_eq_left rfl,input_value]
    constructor
    · intro h
      exact ⟨0,by simp,h⟩
    · rintro ⟨j,hj,h⟩
      have eq : j=0 := Fin.ext (by simpa using hj)
      simpa [eq] using h
  | succ k ih =>
    let a : Fin q := ⟨k,by omega⟩
    let C : Circuit := ⟨grid points,0⟩
    have idx : k+q*t.val<C.gates.length := by rw [show C.gates=grid points from rfl,grid_len];exact (finProdFinEquiv (t,a)).isLt
    have gt : C.gates[k+q*t.val]=lineGate points t a := grid_index points t a
    have rule := or_value C (k+q*t.val) idx (by rw [gt];rfl) x
    rw [gt] at rule
    have below := grid_earlier points t a
    have left := below (partialWire points t k) (by simp [lineGate,a])
    have right := below (points t a.succ).val (by simp [lineGate])
    have pref :=  ih (by omega)
    change value C x (N+(k+q*t.val))=true ↔ _
    rw [rule]
    constructor
    · rintro ⟨w,hw,_,live⟩
      simp only [lineGate,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      · obtain ⟨j,hj,hv⟩ := pref.mp live
        exact ⟨j,by omega,hv⟩
      · exact ⟨a.succ,by simp [a],(input_value C x (points t a.succ)) ▸ live⟩
    · rintro ⟨j,hj,hv⟩
      by_cases small : j.val≤k
      · exact ⟨_,by simp [lineGate,a],left,pref.mpr ⟨j,small,hv⟩⟩
      · have eq : j=a.succ := Fin.ext (by change j.val=k+1;omega)
        subst j
        exact ⟨_,by simp [lineGate],right,(input_value C x (points t a.succ)).symm ▸ hv⟩

lemma upper {q N : ℕ} (L : Fin N → Finset (Fin N)) (card : ∀ t, (L t).card=q+1) :
    ∃ (gates : List Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op=GateOp.and ∨ gt.op=GateOp.or) ∧ gt.inputs.length≤2) ∧
      (∀ i : Fin gates.length, ∀ w∈(gates.get i).inputs, w<N+i.val) ∧
      (∀ (t : Fin N) (x : Fin N → Bool), Circuit.eval ⟨gates,o t⟩ (List.ofFn x)=decide (∃ v∈L t,x v=true)) ∧
      gates.length=N*q := by
  classical
  let p (t : Fin N) := (L t).orderEmbOfFin (card t)
  let points : Fin N → Fin (q+1) → Fin N := fun t j => p t j
  refine ⟨grid points,fun t => partialWire points t q,?_,?_,?_,grid_len _⟩
  · intro gt hg
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
    exact ⟨Or.inr rfl,by simp [lineGate]⟩
  · intro i w hw
    let a : Fin (N*q) := ⟨i.val,by simpa [grid_len] using i.isLt⟩
    obtain ⟨⟨t,k⟩,eq⟩ := finProdFinEquiv.surjective a
    have hi : k.val+q*t.val=i.val := congrArg Fin.val eq
    have read : (grid points).get i=lineGate points t k := by
      change (grid points)[i.val]=_
      simp only [← hi,grid_index]
    rw [read] at hw
    simpa only [←hi] using grid_earlier points t k w hw
  · intro t x
    apply Bool.eq_iff_iff.mpr
    change (value ⟨grid points,0⟩ x (partialWire points t q)=true) ↔ _
    rw [grid_result _ _ _ _ (le_refl _),decide_eq_true_eq]
    constructor
    · rintro ⟨j,_,hj⟩
      exact ⟨points t j,(L t).orderEmbOfFin_mem (card t) j,hj⟩
    · rintro ⟨v,hv,hl⟩
      obtain ⟨j,hj⟩ := ((L t).orderIsoOfFin (card t)).surjective ⟨v,hv⟩
      exact ⟨j,by have := j.isLt;omega,by simpa [points,p,← Finset.coe_orderIsoOfFin_apply,hj] using hl⟩

def domain {N : ℕ} (base : Finset (Fin N)) (a b : Fin N) (x : Fin N → Bool) :=
  x a=true ∨ x b=true ∨ ∀ u, u∉base → x u=true

lemma cotest {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 a b : Fin N)
    (inter : ∀ i j, i≠j → (L i ∩ L j).card=1) (ab : a≠b) (ha : a∈L i0) (hb : b∈L i0)
    (t : Fin N) : domain (L i0) a b (fun v => decide (v∉L t)) := by
  classical
  by_cases eq : t=i0
  · subst t
    exact Or.inr (Or.inr fun u hu => by simpa using hu)
  by_cases at' : a∈L t
  · right;left
    apply decide_eq_true
    intro bt
    have sub : ({a,b} : Finset (Fin N))⊆L t ∩ L i0 := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|h
      · exact Finset.mem_inter.mpr ⟨at',ha⟩
      · rw [Finset.mem_singleton.mp h]
        exact Finset.mem_inter.mpr ⟨bt,hb⟩
    have h := Finset.card_le_card sub
    simp [ab,inter t i0 eq] at h
  · exact Or.inl (by simpa using at')

end PEqualNP.Outside.L_meta_1643

namespace PEqualNP.Outside.L_meta_1643.Rim
open PEqualNP.CircuitLowerBounds

-- Track points on the distinguished line that still require a gate of their own.
def Good {P : Type*} [DecidableEq P] (R D : Finset P) (sens pure : P → Prop) (core : Prop) : Prop :=
  (∀ r ∈ R, r ∉ D → sens r → pure r ∧ ¬ core) ∧
  (∀ r ∈ R, r ∉ D → sens r → ∀ s ∈ R, s ∉ D → sens s → r = s)

lemma Good.mono {P : Type*} [DecidableEq P] {R D E : Finset P} {s p : P → Prop} {c : Prop}
    (h : Good R D s p c) (hDE : D ⊆ E) : Good R E s p c :=
  ⟨fun r hr hd hs => h.1 r hr (fun h => hd (hDE h)) hs,
   fun r hr hd hs t ht he hs' => h.2 r hr (fun h => hd (hDE h)) hs t ht (fun h => he (hDE h)) hs'⟩

abbrev V {N : ℕ} (gs : List Gate) (w : ℕ) (x : Fin N → Bool) : Bool := Circuit.eval ⟨gs,w⟩ (List.ofFn x)
abbrev base {N : ℕ} (M : Finset (Fin N)) : Fin N → Bool := fun v => decide (v ∉ M)
abbrev single {N : ℕ} (r : Fin N) : Fin N → Bool := fun v => decide (v = r)
abbrev rimInput {N : ℕ} (M : Finset (Fin N)) (r : Fin N) : Fin N → Bool := fun v => decide (v ∉ M ∨ v = r)
abbrev S {N : ℕ} (gs : List Gate) (M : Finset (Fin N)) (w : ℕ) (r : Fin N) : Prop := V gs w (rimInput M r) = true
abbrev U {N : ℕ} (gs : List Gate) (w : ℕ) (r : Fin N) : Prop := V gs w (single r) = true
abbrev C {N : ℕ} (gs : List Gate) (T : Finset (Fin N)) (w : ℕ) : Prop := ∃ x ∈ T, U gs w x


lemma twoPoints {N : ℕ} (L : Fin N → Finset (Fin N)) {i t r s : Fin N}
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (ht : t ≠ i) (hr : r ∈ L i) (hs : s ∈ L i) (hrs : r ≠ s) :
    r ∉ L t ∨ s ∉ L t := by
  by_contra! h
  have hsub : ({r,s} : Finset (Fin N)) ⊆ L i ∩ L t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hr, h.1⟩
    · exact Finset.mem_inter.mpr ⟨hs, h.2⟩
  have hle := Finset.card_le_card hsub
  simp [hrs, hinter i t ht.symm] at hle

lemma offOther {N : ℕ} (gates : List Gate) (w : ℕ) (L : Fin N → Finset (Fin N))
    {i r s : Fin N} (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hr : r ∈ L i) (hs : s ∈ L i) (hrs : r ≠ s)
    (h1 : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = r)) = true)
    (h2 : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = s)) = true)
    (t : Fin N) (ht : t ≠ i) :
    Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v ∉ L t)) = true := by
  have lift (p : Fin N) (hp : p ∉ L t)
      (hv : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = p)) = true) :
      Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v ∉ L t)) = true := by
    apply Count.mono ⟨gates,w⟩ hC (fun v : Fin N => decide (v = p)) (fun v => decide (v ∉ L t)) _ w hv
    intro v h
    simp only [decide_eq_true_eq] at h ⊢
    simpa only [h] using hp
  rcases twoPoints L hinter ht hr hs hrs with h | h
  · exact lift r h h1
  · exact lift s h h2

theorem orUpdate {P : Type*} [DecidableEq P] (R D : Finset P) (s₁ s₂ p₁ p₂ : P → Prop)
    (c₁ c₂ Q : Prop) [Decidable Q] (g₁ : Good R D s₁ p₁ c₁) (g₂ : Good R D s₂ p₂ c₂)
    (charge : ((∃ r ∈ R, r ∉ D ∧ s₁ r ∧ c₂) ∨ (∃ r ∈ R, r ∉ D ∧ s₂ r ∧ c₁) ∨
        (∃ r ∈ R, ∃ t ∈ R, r ∉ D ∧ t ∉ D ∧ s₁ r ∧ s₂ t ∧ r ≠ t)) → Q) :
    ∃ E : Finset P, D ⊆ E ∧ E.card ≤ D.card + (if Q then 1 else 0) ∧
      Good R E (fun r => s₁ r ∨ s₂ r) (fun r => p₁ r ∨ p₂ r) (c₁ ∨ c₂) := by
  classical
  let Bad := (∃ r ∈ R, r ∉ D ∧ s₁ r ∧ c₂) ∨ (∃ r ∈ R, r ∉ D ∧ s₂ r ∧ c₁) ∨
             (∃ r ∈ R, ∃ t ∈ R, r ∉ D ∧ t ∉ D ∧ s₁ r ∧ s₂ t ∧ r ≠ t)
  have drop {s p : P → Prop} {c : Prop} (g : Good R D s p c) {a : P}
      (ha : a ∈ R) (hd : a ∉ D) (hs : s a) :
      ∀ z ∈ R, z ∉ insert a D → ¬ s z := by
    intro z hz he hsz
    have eq := g.2 z hz (fun h => he (Finset.mem_insert_of_mem h)) hsz a ha hd hs
    exact he (Finset.mem_insert.mpr (Or.inl eq))
  have vac (E : Finset P) (h : ∀ z ∈ R, z ∉ E → ¬ (s₁ z ∨ s₂ z)) :
      Good R E (fun z => s₁ z ∨ s₂ z) (fun z => p₁ z ∨ p₂ z) (c₁ ∨ c₂) := by
    exact ⟨fun r hr he hs => (h r hr he hs).elim, fun r hr he hs => (h r hr he hs).elim⟩
  by_cases bad : Bad
  · have q : Q := charge bad
    have budget (a : P) : (insert a D).card ≤ D.card + (if Q then 1 else 0) := by
      rw [ite_eq_left q]
      exact Finset.card_insert_le a D
    rcases bad with ⟨a,ha,hd,hs,hc⟩ | ⟨a,ha,hd,hs,hc⟩ | ⟨a,ha,b,hb,hd,_,hs,_,_⟩
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, vac _ ?_⟩
      intro z hz he h
      rcases h with l | r
      · exact drop g₁ ha hd hs z hz he l
      · exact (g₂.1 z hz (fun h => he (Finset.mem_insert_of_mem h)) r).2 hc
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, vac _ ?_⟩
      intro z hz he h
      rcases h with l | r
      · exact (g₁.1 z hz (fun h => he (Finset.mem_insert_of_mem h)) l).2 hc
      · exact drop g₂ ha hd hs z hz he r
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, ?_⟩
      have right : ∀ z ∈ R, z ∉ insert a D → s₁ z ∨ s₂ z → s₂ z :=
        fun z hz he h => h.resolve_left (drop g₁ ha hd hs z hz he)
      have g₂' := g₂.mono (Finset.subset_insert a D)
      constructor
      · intro z hz he h
        have v := g₂'.1 z hz he (right z hz he h)
        exact ⟨Or.inr v.1, fun hC => hC.elim (g₁.1 a ha hd hs).2 v.2⟩
      · intro z hz he h t ht hte hts
        exact g₂'.2 z hz he (right z hz he h) t ht hte (right t ht hte hts)
  · refine ⟨D, Finset.Subset.rfl, Nat.le_add_right _ _, ?_⟩
    have cross {a b : P} (ha : a ∈ R) (hb : b ∈ R) (da : a ∉ D) (db : b ∉ D)
        (sa : s₁ a) (sb : s₂ b) : a = b := by
      by_contra hn
      exact bad (Or.inr (Or.inr ⟨a,ha,b,hb,da,db,sa,sb,hn⟩))
    constructor
    · intro r hr hd hs
      rcases hs with l | r'
      · have v := g₁.1 r hr hd l
        exact ⟨Or.inl v.1, fun c => c.elim v.2 (fun rc => bad (Or.inl ⟨r,hr,hd,l,rc⟩))⟩
      · have v := g₂.1 r hr hd r'
        exact ⟨Or.inr v.1, fun c => c.elim (fun lc => bad (Or.inr (Or.inl ⟨r,hr,hd,r',lc⟩))) v.2⟩
    · intro a ha da hsa b hb db hsb
      rcases hsa with l | r <;> rcases hsb with l' | r'
      · exact g₁.2 a ha da l b hb db l'
      · exact cross ha hb da db l r'
      · exact (cross hb ha db da l' r).symm
      · exact g₂.2 a ha da r b hb db r'

def spare {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T : Finset (Fin N))
    (gs : List Gate) (i : Fin gs.length) : Prop :=
  (gs.get i).op=GateOp.or ∧ V gs (N+i.val) (base (L i0))=false ∧
    (∃ w∈(gs.get i).inputs, ¬C gs T w) ∧ ∀ t, t≠i0 → V gs (N+i.val) (base (L t))=true

def delivering {N : ℕ} (M T : Finset (Fin N)) (gs : List Gate) (i : Fin gs.length) : Prop :=
  (gs.get i).op=GateOp.and ∧ V gs (N+i.val) (base M)=false ∧
    ∃ w∈(gs.get i).inputs, ∃ r∈M \ T, U gs w r

theorem strand_of_rim_only_input {N : ℕ} {L : Fin N → Finset (Fin N)}
    {i0 : Fin N} {T0 : Finset (Fin N)} {gates : List Gate} {Xs : Finset (Fin gates.length)}
    (hXs : ∀ g, spare L i0 T0 gates g → g ∈ Xs)
    {g : Fin gates.length} {a b : ℕ}
    (hop : (gates.get g).op = GateOp.or)
    (hcold : Circuit.eval ⟨gates, N + (g : ℕ)⟩
      (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false)
    (hinputs : (gates.get g).inputs = [a,b] ∨ (gates.get g).inputs = [b,a])
    (hempty : ¬ ∃ x ∈ T0, Circuit.eval ⟨gates, a⟩
      (List.ofFn (fun v : Fin N => decide (v = x))) = true)
    (hother : ∀ t : Fin N, t ≠ i0 → Circuit.eval ⟨gates, N + (g : ℕ)⟩
      (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = true) : g ∈ Xs := by
  refine hXs g ⟨hop,hcold,⟨a,?_,hempty⟩,hother⟩
  rcases hinputs with h|h <;> rw [h] <;> simp

theorem realOrUpdate {N : ℕ} {L : Fin N → Finset (Fin N)} {i0 : Fin N}
    {T : Finset (Fin N)} {gs : List Gate} {Xs : Finset (Fin gs.length)} {D : Finset (Fin N)}
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1) (hTsub : T ⊆ L i0)
    (hXs : ∀ g, spare L i0 T gs g → g ∈ Xs)
    (i : Fin gs.length) (a b : ℕ) (hop : (gs.get i).op = GateOp.or)
    (hinputs : (gs.get i).inputs = [a,b]) (hcold : V gs (N + i.val) (base (L i0)) = false)
    (hor : ∀ x : Fin N → Bool, V gs (N + i.val) x = (V gs a x || V gs b x))
    (ga : Good (L i0 \ T) D (S gs (L i0) a) (U gs a) (C gs T a))
    (gb : Good (L i0 \ T) D (S gs (L i0) b) (U gs b) (C gs T b)) :
    ∃ E : Finset (Fin N), D ⊆ E ∧ E.card ≤ D.card + (if i ∈ Xs then 1 else 0) ∧
      Good (L i0 \ T) E (S gs (L i0) (N + i.val)) (U gs (N + i.val)) (C gs T (N + i.val)) := by
  classical
  have us (r : Fin N) : U gs (N + i.val) r ↔ U gs a r ∨ U gs b r := by
    change V gs (N + i.val) (single r) = true ↔ _
    rw [hor]
    simp only [Bool.or_eq_true, U]
  have ss (r : Fin N) : S gs (L i0) (N + i.val) r ↔ S gs (L i0) a r ∨ S gs (L i0) b r := by
    change V gs (N + i.val) (rimInput (L i0) r) = true ↔ _
    rw [hor]
    simp only [Bool.or_eq_true, S]
  have cs : C gs T (N + i.val) ↔ C gs T a ∨ C gs T b := by
    constructor
    · rintro ⟨x,hx,ux⟩
      rcases (us x).1 ux with ua | ub
      · exact Or.inl ⟨x,hx,ua⟩
      · exact Or.inr ⟨x,hx,ub⟩
    · rintro (⟨x,hx,ua⟩ | ⟨x,hx,ub⟩)
      · exact ⟨x,hx,(us x).2 (Or.inl ua)⟩
      · exact ⟨x,hx,(us x).2 (Or.inr ub)⟩
  have pay {r t : Fin N} (hr : r ∈ L i0) (ht : t ∈ L i0) (hrt : r ≠ t)
      (u₁ : U gs a r) (u₂ : U gs b t) (empty : ¬ C gs T a ∨ ¬ C gs T b) : i ∈ Xs := by
    have every := offOther gs (N + i.val) L hG hinter hr ht hrt
      ((us r).2 (Or.inl u₁)) ((us t).2 (Or.inr u₂))
    rcases empty with ha | hb
    · exact strand_of_rim_only_input hXs hop hcold (Or.inl hinputs) ha every
    · exact strand_of_rim_only_input hXs hop hcold (Or.inr hinputs) hb every
  obtain ⟨E,hDE,hcard,hGood⟩ := orUpdate (L i0 \ T) D _ _ _ _ _ _ (i ∈ Xs) ga gb (by
    rintro (⟨r,hr,hd,sa,t,ht,ub⟩ | ⟨t,ht,hd,sb,r,hr,ua⟩ | ⟨r,hr,t,ht,dr,dt,sa,sb,hrt⟩)
    · obtain ⟨ua,ha⟩ := ga.1 r hr hd sa
      have h := Finset.mem_sdiff.mp hr
      exact pay h.1 (hTsub ht) (fun e => h.2 (e ▸ ht)) ua ub (Or.inl ha)
    · obtain ⟨ub,hb⟩ := gb.1 t ht hd sb
      have h := Finset.mem_sdiff.mp ht
      exact pay (hTsub hr) h.1 (fun e => h.2 (e ▸ hr)) ua ub (Or.inr hb)
    · obtain ⟨ua,ha⟩ := ga.1 r hr dr sa
      obtain ⟨ub,_⟩ := gb.1 t ht dt sb
      exact pay (Finset.mem_sdiff.mp hr).1 (Finset.mem_sdiff.mp ht).1 hrt ua ub (Or.inl ha))
  refine ⟨E,hDE,hcard,?_,?_⟩
  · intro r hr hd sr
    obtain ⟨u,c⟩ := hGood.1 r hr hd ((ss r).1 sr)
    exact ⟨(us r).2 u, fun h => c (cs.1 h)⟩
  · intro r hr hd sr t ht hdt st
    exact hGood.2 r hr hd ((ss r).1 sr) t ht hdt ((ss t).1 st)

lemma andUpdate {P : Type*} [DecidableEq P] (R D : Finset P)
    (sChild pChild sGate pGate : P → Prop) (cChild cGate Q : Prop) [Decidable Q]
    (h : Good R D sChild pChild cChild) (sub : ∀ r, sGate r → sChild r)
    (qual : (∃ r ∈ R, sGate r ∧ pChild r) → Q) :
    ∃ E, D ⊆ E ∧ E.card ≤ D.card + (if Q then 1 else 0) ∧ Good R E sGate pGate cGate := by
  suffices step : ∃ E : Finset P, D ⊆ E ∧ E.card ≤ D.card + (if Q then 1 else 0) ∧
      ∀ r ∈ R, r ∉ E → ¬ sGate r by
    obtain ⟨E, hDE, hcard, no⟩ := step
    exact ⟨E, hDE, hcard, fun r hr he hs => (no r hr he hs).elim,
      fun r hr he hs => (no r hr he hs).elim⟩
  by_cases unpaid : ∃ r ∈ R, r ∉ D ∧ sGate r
  · obtain ⟨r, hr, hd, hs⟩ := unpaid
    have hQ := qual ⟨r, hr, hs,(h.1 r hr hd (sub r hs)).1⟩
    refine ⟨insert r D, Finset.subset_insert _ _, ?_, ?_⟩
    · simp [hd, hQ]
    · intro t ht he hts
      have htd : t ∉ D := fun hmem => he (Finset.mem_insert_of_mem hmem)
      have heq := h.2 t ht htd (sub t hts) r hr hd (sub r hs)
      exact he (Finset.mem_insert.mpr (Or.inl heq))
  · refine ⟨D, Finset.Subset.rfl, Nat.le_add_right _ _, ?_⟩
    exact fun r hr hd hs => unpaid ⟨r, hr, hd, hs⟩

theorem prefixBudget {P : Type*} [DecidableEq P] (N k : ℕ)
    (A Xs : Finset (Fin k)) (G : ℕ → Finset P → Prop)
    (mono : ∀ w D E, D ⊆ E → G w D → G w E)
    (init : ∀ w < N, G w ∅)
    (step : ∀ (i : Fin k) (D : Finset P), (∀ w < N + i.val, G w D) →
      ∃ E, D ⊆ E ∧ E.card ≤ D.card + (if i ∈ A then 1 else 0) +
        (if i ∈ Xs then 1 else 0) ∧ G (N + i.val) E) :
    ∃ D, D.card ≤ A.card + Xs.card ∧ ∀ w < N + k, G w D := by
  let count (S : Finset (Fin k)) (j : ℕ) := (S.filter fun v => v.val < j).card
  have next (S : Finset (Fin k)) (i : Fin k) :
      count S (i.val + 1) = count S i.val + (if i ∈ S then 1 else 0) := by
    have hlt (v : Fin k) : v.val < i.val + 1 ↔ v = i ∨ v.val < i.val := by
      rw [Fin.ext_iff]
      omega
    by_cases hi : i ∈ S
    · have heq : S.filter (fun v => v.val < i.val + 1) =
          insert i (S.filter fun v => v.val < i.val) := by
        ext v
        by_cases hv : v = i
        · subst v
          simp [hi]
        · simp [hlt, hv]
      have hnot : i ∉ S.filter (fun v => v.val < i.val) := by simp
      simp only [count, heq, Finset.card_insert_of_notMem hnot, ite_eq_left hi]
    · have heq : S.filter (fun v => v.val < i.val + 1) =
          S.filter (fun v => v.val < i.val) := by
        ext v
        by_cases hv : v = i
        · subst v
          simp [hi]
        · simp [hlt, hv]
      simp only [count, heq, ite_eq_right hi, Nat.add_zero]
  have prefixBound (j : ℕ) (hj : j ≤ k) :
      ∃ D, D.card ≤ count A j + count Xs j ∧ ∀ w < N + j, G w D := by
    induction j with
    | zero =>
      exact ⟨∅, by simp [count], by simpa using init⟩
    | succ j ih =>
      let i : Fin k := ⟨j, by omega⟩
      obtain ⟨D, hD, hG⟩ := ih (by omega)
      obtain ⟨E, hDE, hE, hGE⟩ := step i D hG
      refine ⟨E, ?_, ?_⟩
      · change E.card ≤ count A (i.val + 1) + count Xs (i.val + 1)
        rw [next A i, next Xs i]
        change D.card ≤ count A i.val + count Xs i.val at hD
        omega
      · intro w hw
        by_cases hprev : w < N + j
        · exact mono w D E hDE (hG w hprev)
        · have hw' : w = N + i.val := by change w = N + j; omega
          exact hw' ▸ hGE
  have last (S : Finset (Fin k)) : count S k = S.card := by
    have heq : S.filter (fun v => v.val < k) = S := by
      ext v
      simp
    simp only [count, heq]
  simpa only [last] using prefixBound k (le_refl k)

lemma primaryGood {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (w : ℕ) (hw : w < N)
    (hc : V gs w (base M) = false) : Good (M \ T) ∅ (S gs M w) (U gs w) (C gs T w) := by
  let p : Fin N := ⟨w, hw⟩
  have eval (x : Fin N → Bool) : V gs w x = x p := Count.input_value ⟨gs,w⟩ x p
  rw [eval] at hc
  have hp : p ∈ M := by simpa [base] using hc
  have sens (r : Fin N) : S gs M w r ↔ p = r := by
    change V gs w (rimInput M r) = true ↔ _
    rw [eval]
    simp [rimInput, hp]
  have purePt (r : Fin N) : U gs w r ↔ p = r := by
    change V gs w (single r) = true ↔ _
    rw [eval]
    simp [single]
  constructor
  · intro r hr _ hs
    refine ⟨(purePt r).mpr ((sens r).mp hs), ?_⟩
    rintro ⟨x, hx, hux⟩
    have heq : r = x := ((sens r).mp hs).symm.trans ((purePt x).mp hux)
    exact (Finset.mem_sdiff.mp hr).2 (heq ▸ hx)
  · intro r _ _ hr s _ _ hs
    exact ((sens r).mp hr).symm.trans ((sens s).mp hs)

lemma missingV {N : ℕ} (gs : List Gate) (w : ℕ) (hw : N + gs.length ≤ w)
    (x : Fin N → Bool) : V gs w x = false :=
  Count.missing_value ⟨gs,w⟩ x w hw

lemma gateCases {N : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < N + i.val) (i : Fin gs.length) :
    (∃ c : Bool, ∀ x : Fin N → Bool, V gs (N + i.val) x = c) ∨
    (∃ a < N + i.val, ∀ x : Fin N → Bool, V gs (N + i.val) x = V gs a x) ∨
    (∃ a < N + i.val, ∃ b < N + i.val, (gs.get i).op = GateOp.and ∧ (gs.get i).inputs = [a,b] ∧
      ∀ x : Fin N → Bool, V gs (N + i.val) x = (V gs a x && V gs b x)) ∨
    (∃ a < N + i.val, ∃ b < N + i.val, (gs.get i).op = GateOp.or ∧
      (gs.get i).inputs = [a, b] ∧
      ∀ x : Fin N → Bool, V gs (N + i.val) x = (V gs a x || V gs b x)) := by
  obtain ⟨hop, hlen⟩ := hG (gs.get i) (List.get_mem gs i)
  have earlier := htop i
  have val (x : Fin N → Bool) :
      V gs (N + i.val) x = (gs.get i).op.eval
        ((gs.get i).inputs.map fun r => if r < N + i.val then V gs r x else false) := by
    let D : Circuit := ⟨gs,0⟩
    have hw : N + i.val < N + D.size := Nat.add_lt_add_left i.isLt N
    have h := Count.gate_value D x (N + i.val) (by omega) hw
    simpa [D, Count.value, V, Circuit.eval, Circuit.wires] using h
  generalize eqg : gs.get i = g at hop hlen earlier val ⊢
  cases ins : g.inputs with
  | nil =>
    left
    exact ⟨g.op.eval [],fun x => by simpa [ins] using val x⟩
  | cons a rest =>
    right
    have ha : a < N + i.val := earlier a (by simp [ins])
    cases rest with
    | nil =>
      refine Or.inl ⟨a, ha, ?_⟩
      intro x
      rcases hop with hop | hop <;> simpa [ins, hop, GateOp.eval, ha] using val x
    | cons b rest =>
      cases rest with
      | nil =>
        have hb : b < N + i.val := earlier b (by simp [ins])
        rcases hop with hop | hop
        · refine Or.inr (Or.inl ⟨a, ha, b, hb, hop, rfl, ?_⟩)
          intro x
          simpa [ins, hop, GateOp.eval, ha, hb] using val x
        · refine Or.inr (Or.inr ⟨a, ha, b, hb, hop, rfl, ?_⟩)
          intro x
          simpa [ins, hop, GateOp.eval, ha, hb] using val x
      | cons c rest => simp [ins] at hlen

set_option maxHeartbeats 1200000 in
lemma rim_budget {q m N : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T : Finset (Fin N))
    (hm : 1 ≤ m) (hsize : ∀ i,(L i).card=q+1) (hinter : ∀ i j,i≠j → (L i ∩ L j).card=1)
    (hTsub : T⊆L i0) (hTm : T.card=m) (gs : List Gate) (o : ℕ)
    (hG : ∀ g∈gs,(g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (htop : ∀ i : Fin gs.length, ∀ a∈(gs.get i).inputs, a<N+i.val)
    (hbase : V gs o (base (L i0))=false) (hsingle : ∀ r∈T,U gs o r)
    (hrim : ∀ r∈L i0 \ T, S gs (L i0) o r)
    (A Xs : Finset (Fin gs.length))
    (hA : ∀ i,delivering (L i0) T gs i → i∈A) (hXs : ∀ i,spare L i0 T gs i → i∈Xs) :
    q+1-m≤A.card+Xs.card := by
  classical
  let M := L i0
  let R := M \ T
  let Inv (w : ℕ) (D : Finset (Fin N)) :=
    V gs w (base M) = false → Good R D (S gs M w) (U gs w) (C gs T w)
  have grow : ∀ w D E, D ⊆ E → Inv w D → Inv w E := by
    intro w D E hDE hw hc
    exact (hw hc).mono hDE
  have init : ∀ w < N, Inv w ∅ := by
    intro w hw hc
    exact primaryGood gs M T w hw hc
  have step (i : Fin gs.length) (D : Finset (Fin N))
      (prev : ∀ w < N + i.val, Inv w D) :
      ∃ E, D ⊆ E ∧ E.card ≤ D.card + (if i ∈ A then 1 else 0) + (if i ∈ Xs then 1 else 0) ∧ Inv (N + i.val) E := by
    by_cases hc : V gs (N+i.val) (base M) = false
    · rcases gateCases gs hG htop i with
        ⟨v, heq⟩ | ⟨a, hlt, heq⟩ | ⟨a, ha, b, hb, hop, hin, heq⟩ | ⟨a, ha, b, hb, hop, hin, heq⟩
      · refine ⟨D,Finset.Subset.rfl,by omega,?_⟩
        intro _
        have hv : v=false := (heq (base M)).symm.trans hc
        have no (r : Fin N) : ¬ S gs M (N+i.val) r := by
          change ¬ V gs (N+i.val) (rimInput M r)=true
          rw [heq,hv]
          decide
        exact ⟨fun r _ _ h => (no r h).elim,fun r _ _ h => (no r h).elim⟩
      · refine ⟨D, fun _ h => h, by omega, ?_⟩
        intro _
        have ca : V gs a (base M) = false := (heq _).symm.trans hc
        have hs : S gs M (N+i.val) = S gs M a := funext fun r =>
          congrArg (fun b : Bool => b = true) (heq (rimInput M r))
        have hu : U gs (N+i.val) = U gs a := funext fun r =>
          congrArg (fun b : Bool => b = true) (heq (single r))
        have hcore : C gs T (N+i.val) = C gs T a := congrArg (fun f : Fin N → Prop => ∃ x ∈ T, f x) hu
        rw [hs, hu, hcore]
        exact prev a hlt ca
      · have forced : ∀ r, S gs M (N+i.val) r → S gs M a r ∧ S gs M b r := by
          intro r hr
          exact Bool.and_eq_true_iff.mp ((heq _).symm.trans hr)
        have coldChoice : ∃ w ∈ (gs.get i).inputs, w < N+i.val ∧ V gs w (base M) = false ∧
            ∀ r, S gs M (N+i.val) r → S gs M w r := by
          by_cases ca : V gs a (base M) = false
          · exact ⟨a, by rw [hin];simp, ha, ca, fun r h => (forced r h).1⟩
          · have cb : V gs b (base M) = false := by
              have h := (heq (base M)).symm.trans hc
              cases h₁ : V gs a (base M) with
              | false => exact (ca h₁).elim
              | true => simpa only [h₁, Bool.true_and] using h
            exact ⟨b, by rw [hin];simp, hb, cb, fun r h => (forced r h).2⟩
        obtain ⟨w, win, hw, cw, sub⟩ := coldChoice
        have qual : (∃ r∈R, S gs M (N+i.val) r ∧ U gs w r) → i∈A := by
          rintro ⟨r,hr,_,hp⟩
          exact hA i ⟨hop,hc,w,win,r,hr,hp⟩
        obtain ⟨E, hDE, hcard, hg⟩ := andUpdate R D (S gs M w) (U gs w)
          (S gs M (N+i.val)) (U gs (N+i.val)) (C gs T w) (C gs T (N+i.val))
          (i ∈ A) (prev w hw cw) sub qual
        exact ⟨E, hDE, by omega, fun _ => hg⟩
      · have ab : V gs a (base M) = false ∧ V gs b (base M) = false := by
          simpa only [Bool.or_eq_false_iff] using (heq (base M)).symm.trans hc
        obtain ⟨E, hDE, hcard, hg⟩ := realOrUpdate hG hinter hTsub hXs i a b hop hin hc heq
          (prev a ha ab.1) (prev b hb ab.2)
        exact ⟨E, hDE, by omega, fun _ => hg⟩
    · exact ⟨D, fun _ h => h, by omega, fun h => (hc h).elim⟩
  obtain ⟨D, hd, hgood⟩ := prefixBudget N gs.length A Xs Inv grow init step
  have tne : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := tne
  have bounded : o < N + gs.length := by
    by_contra! he
    have h := missingV gs o he (single x)
    have p : V gs o (single x) = true := hsingle x hx
    simp [h] at p
  have core : C gs T o := ⟨x, hx, hsingle x hx⟩
  have covered : R ⊆ D := by
    intro r hr
    by_contra hd'
    exact ((hgood o bounded hbase).1 r hr hd' (hrim r hr)).2 core
  have count := (Finset.card_le_card covered).trans hd
  simpa only [R, M, Finset.card_sdiff_of_subset hTsub, hsize, hTm] using count


end PEqualNP.Outside.L_meta_1643.Rim

namespace PEqualNP.Outside.L_meta_1643.Geometry

abbrev Point (n : ℕ) := Fin n
abbrev monoFn {n : ℕ} (f : (Fin n → Bool) → Bool) :=
  ∀ x y, (∀ p, x p=true → y p=true) → f x=true → f y=true

-- A test for an ordinary line can switch on the other distinguished point.
def marker {n : ℕ} (L : Fin n → Finset (Fin n)) (a b t : Fin n) := if a∈L t then b else a

def test {n : ℕ} (L : Fin n → Finset (Fin n)) (a b t p v : Fin n) : Bool :=
  decide (v=p ∨ (p≠a ∧ p≠b ∧ v=marker L a b t))

def co {n : ℕ} (L : Fin n → Finset (Fin n)) (t v : Fin n) : Bool := decide (v∉L t)

def pts {n : ℕ} (L : Fin n → Finset (Fin n)) (a b : Fin n)
    (f : (Fin n → Bool) → Bool) (t : Fin n) : Finset (Fin n) :=
  if f (co L t)=false then (L t).filter fun p => f (test L a b t p)=true else ∅

lemma in_pts {n : ℕ} {L : Fin n → Finset (Fin n)} {a b t p : Fin n} {f : (Fin n → Bool) → Bool} :
    p∈pts L a b f t ↔ f (co L t)=false ∧ p∈L t ∧ f (test L a b t p)=true := by
  by_cases h : f (co L t)=false <;> simp [pts,h]

lemma two_points {n : ℕ} {L : Fin n → Finset (Fin n)} (inter : ∀ i j,i≠j → (L i∩L j).card=1)
    {i j a b : Fin n} (ij : i≠j) (ai : a∈L i) (aj : a∈L j) (bi : b∈L i) (bj : b∈L j) : a=b := by
  by_contra h
  have sub : ({a,b}:Finset (Fin n))⊆L i∩L j := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl|r
    · exact Finset.mem_inter.mpr ⟨ai,aj⟩
    · rw [Finset.mem_singleton.mp r];exact Finset.mem_inter.mpr ⟨bi,bj⟩
  have hle:=Finset.card_le_card sub
  simp [h,inter i j ij] at hle

lemma test_meets {n : ℕ} {L : Fin n → Finset (Fin n)} {a b t u p : Fin n}
    {f : (Fin n → Bool) → Bool} (hm : monoFn f) (cold : f (co L u)=false)
    (h : f (test L a b t p)=true) : p∈L u ∨ (p≠a ∧ p≠b ∧ marker L a b t∈L u) := by
  by_contra hno
  have other := hm (test L a b t p) (co L u) (fun v hv => by
    apply decide_eq_true
    intro hvin
    apply hno
    rcases of_decide_eq_true hv with eq|⟨pa,pb,eq⟩
    · exact Or.inl (eq ▸ hvin)
    · exact Or.inr ⟨pa,pb,eq ▸ hvin⟩) h
  rw [cold] at other;contradiction

lemma multi_marker {n : ℕ} {L : Fin n → Finset (Fin n)} (inter : ∀ i j,i≠j → (L i∩L j).card=1)
    {a b t u : Fin n} {f : (Fin n → Bool) → Bool} (hm : monoFn f) (tu : t≠u)
    (hu : f (co L u)=false) (size : 1<(pts L a b f t).card) : marker L a b t∈L u := by
  by_contra hh
  obtain ⟨p,hp,p',hp',ne⟩:=Finset.one_lt_card.mp size
  have v:=in_pts.mp hp
  have v':=in_pts.mp hp'
  have mem (k : Fin n) (on : f (test L a b t k)=true) : k∈L u := by
    rcases test_meets hm hu on with e|e
    · exact e
    · exact (hh e.2.2).elim
  exact ne (two_points inter tu v.2.1 (mem p v.2.2) v'.2.1 (mem p' v'.2.2))

lemma both_marker {n : ℕ} {L : Fin n → Finset (Fin n)} (inter : ∀ i j,i≠j → (L i∩L j).card=1)
    {a b i0 t : Fin n} (h : t≠i0) (ab : a≠b) (ha : a∈L i0) (hb : b∈L i0)
    (at' : a∈L t) : b∉L t := fun bt => ab (two_points inter h at' ha bt hb)

lemma multi_pair {n : ℕ} {L : Fin n → Finset (Fin n)} (inter : ∀ i j,i≠j → (L i∩L j).card=1)
    {a b i0 t u : Fin n} {f : (Fin n → Bool) → Bool} (hm : monoFn f)
    (_ab : a≠b) (_ha : a∈L i0) (_hb : b∈L i0) (_ti : t≠i0) (_ui : u≠i0) (tu : t≠u)
    (mt : 1<(pts L a b f t).card) (mu : 1<(pts L a b f u).card) :
    (a∈L t ∧ b∈L u) ∨ (a∈L u ∧ b∈L t) := by
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (lt_trans Nat.zero_lt_one mt)
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (lt_trans Nat.zero_lt_one mu)
  have m:=multi_marker inter hm tu (in_pts.mp hz).1 mt
  have m':=multi_marker inter hm tu.symm (in_pts.mp hp).1 mu
  by_cases at' : a∈L t
  · exact Or.inl ⟨at',by simpa [marker,at'] using m⟩
  · have au : a∈L u := by simpa [marker,at'] using m
    exact Or.inr ⟨au,by simpa [marker,au] using m'⟩

lemma other_pencil {n : ℕ} {L : Fin n → Finset (Fin n)} (inter : ∀ i j,i≠j → (L i∩L j).card=1)
    {a b t u s anchor : Fin n} {f : (Fin n → Bool) → Bool} (hm : monoFn f)
    (ts : t≠s) (anchor0 : anchor=a ∨ anchor=b)
    (at' : anchor∈L t) (as' : anchor∈L s) (au : anchor∉L u)
    (ms : marker L a b t∉L s) (cold : f (co L u)=false) (live : (pts L a b f t).Nonempty) :
    f (co L s)=true := by
  obtain ⟨p,hp⟩:=live
  obtain ⟨_,pt,v⟩:=in_pts.mp hp
  have pa : p≠anchor := by
    rintro rfl
    rcases test_meets hm cold v with h|⟨h0,h1,_⟩
    · exact au h
    · exact anchor0.elim h0 h1
  have ps : p∉L s := fun h => pa (two_points inter ts pt h at' as')
  apply hm (test L a b t p) _ _ v
  intro z hz
  apply decide_eq_true
  rcases of_decide_eq_true hz with eq|⟨_,_,eq⟩ <;> subst z <;> assumption

end PEqualNP.Outside.L_meta_1643.Geometry

namespace PEqualNP.Outside.L_meta_1643.Partition
open Finset
variable {P : Type*} [DecidableEq P]

noncomputable def root (a : P) (U : Finset P) : P := if h : U.Nonempty then h.choose else a
noncomputable def ren (a : P) (U : Finset P) (p : P) : P := if p∈U then root a U else p

omit [DecidableEq P] in
lemma root_mem (a : P) (U : Finset P) (h : U.Nonempty) : root a U∈U := by
  simpa [root,h] using h.choose_spec

noncomputable def label (a : P) (S : ℕ → Finset P) : ℕ → P → P
  | 0 => id
  | k+1 => let f:=label a S k; fun p => ren a ((S k).image f) (f p)

noncomputable def colors (a : P) (S : ℕ → Finset P) (k : ℕ) : Finset P :=
  (S k).image (label a S k)

lemma next (a : P) (S : ℕ → Finset P) (k : ℕ) (p : P) :
    label a S (k+1) p=ren a (colors a S k) (label a S k p) := rfl

lemma current_flat (a : P) (S : ℕ → Finset P) (k : ℕ) {p r : P} (hp : p∈S k) (hr : r∈S k) :
    label a S (k+1) p=label a S (k+1) r := by
  simp [next,ren,colors,Finset.mem_image_of_mem _ hp,Finset.mem_image_of_mem _ hr]

lemma flat (a : P) (S : ℕ → Finset P) {j k : ℕ} (early : j<k) {p r : P} (hp : p∈S j) (hr : r∈S j) :
    label a S k p=label a S k r := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp early with h|rfl
    · rw [next,next,ih h]
    · exact current_flat a S _ hp hr

lemma image_ren (a : P) (U V : Finset P) (sub : U⊆V) (ne : U.Nonempty) :
    V.image (ren a U)=insert (root a U) (V \ U) := by
  ext p
  constructor
  · rintro h
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp h
    by_cases inU : v∈U
    · simp [ren,inU]
    · exact Finset.mem_insert_of_mem (by simpa [ren,inU] using Finset.mem_sdiff.mpr ⟨hv,inU⟩)
  · intro h
    rcases Finset.mem_insert.mp h with rfl|hs
    · have hr:=root_mem a U ne
      exact Finset.mem_image.mpr ⟨_,sub hr,by simp [ren,hr]⟩
    · obtain ⟨hv,hU⟩:=Finset.mem_sdiff.mp hs
      exact Finset.mem_image.mpr ⟨p,hv,by simp [ren,hU]⟩

lemma loss (a : P) (U V : Finset P) (sub : U⊆V) (cap : U.card≤2) :
    (V.image (ren a U)).card+(if 1<U.card then 1 else 0)=V.card := by
  rcases U.eq_empty_or_nonempty with rfl|ne
  · have iden : ren a (∅ : Finset P)=id := by funext p;simp [ren]
    simp [iden]
  rw [image_ren a U V sub ne,Finset.card_insert_of_notMem (by simp [root_mem a U ne]),
    Finset.card_sdiff_of_subset sub]
  have h0 := Finset.card_pos.mpr ne
  have h1 := Finset.card_le_card sub
  split <;> omega

lemma mass (a : P) (S : ℕ → Finset P) (T : Finset P) (k : ℕ)
    (sub : ∀ j<k, S j⊆T) (cap : ∀ j<k,(colors a S j).card≤2) :
    (T.image (label a S k)).card+((Finset.range k).filter fun j => 1<(colors a S j).card).card=T.card := by
  induction k with
  | zero => simp [label]
  | succ k ih =>
    have prev:=ih (fun j hj => sub j (by omega)) (fun j hj => cap j (by omega))
    have h:=loss a (colors a S k) (T.image (label a S k))
      (Finset.image_subset_image (sub k (by omega))) (cap k (by omega))
    have im : T.image (label a S (k+1))=(T.image (label a S k)).image (ren a (colors a S k)) := by
      rw [Finset.image_image];rfl
    rw [im,Finset.range_add_one,Finset.filter_insert]
    split <;> rename_i flag
    · rw [Finset.card_insert_of_notMem (by simp)]
      simp only [ite_eq_left flag] at h
      omega
    · simp only [ite_eq_right flag] at h
      omega

end PEqualNP.Outside.L_meta_1643.Partition

namespace PEqualNP.Outside.L_meta_1643.Partition
open Finset
variable {P : Type*} [DecidableEq P]

def raw (B : Finset (P×P)) (S T : ℕ → Finset P) : ℕ → Finset (P×P)
  | 0 => B
  | k+1 => raw B S T k ∪ S k ×ˢ T k

lemma seed_in_raw (B : Finset (P×P)) (S T : ℕ → Finset P) (k : ℕ) : B⊆raw B S T k := by
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih => exact ih.trans Finset.subset_union_left

lemma past_in_raw (B : Finset (P×P)) (S T : ℕ → Finset P) {j k : ℕ} (h : j<k) :
    S j ×ˢ T j ⊆ raw B S T k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h|rfl
    · exact (ih h).trans Finset.subset_union_left
    · exact Finset.subset_union_right

noncomputable def pairLabel (a : P) (S T : ℕ → Finset P) (k : ℕ) (z : P×P) :=
  (label a S k z.1,label a T k z.2)

noncomputable def pairStep (a : P) (S T : ℕ → Finset P) (k : ℕ) (z : P×P) :=
  (ren a (colors a S k) z.1,ren a (colors a T k) z.2)

noncomputable def edges (a : P) (B : Finset (P×P)) (S T : ℕ → Finset P) (k : ℕ) :=
  (raw B S T k).image (pairLabel a S T k)

def inherit (B : Finset (P×P)) (S T : ℕ → Finset P) (k : ℕ) : Prop :=
  ∃ z∈raw B S T k,z∈S k ×ˢ T k

def fresh (B : Finset (P×P)) (S T : ℕ → Finset P) (k : ℕ) : Prop :=
  (S k).Nonempty ∧ (T k).Nonempty ∧ ¬inherit B S T k

def collision (a : P) (B : Finset (P×P)) (S T : ℕ → Finset P) (k : ℕ) : Prop :=
  ∃ z∈raw B S T k, ∃ z'∈raw B S T k, z∈S k ×ˢ T k ∧ z'∈S k ×ˢ T k ∧
    pairLabel a S T k z≠pairLabel a S T k z'

lemma flat_pair (a : P) (S T : ℕ → Finset P) (k : ℕ) {z z' : P×P}
    (hz : z∈S k ×ˢ T k) (hz' : z'∈S k ×ˢ T k) :
    pairLabel a S T (k+1) z=pairLabel a S T (k+1) z' :=
  Prod.ext (current_flat a S k (Finset.mem_product.mp hz).1 (Finset.mem_product.mp hz').1)
    (current_flat a T k (Finset.mem_product.mp hz).2 (Finset.mem_product.mp hz').2)

lemma pair_update (a : P) (B : Finset (P×P)) (S T : ℕ → Finset P) (k : ℕ) :
    edges a B S T (k+1)=(edges a B S T k).image (pairStep a S T k) ∪
      (S k ×ˢ T k).image (pairLabel a S T (k+1)) := by
  unfold edges
  rw [raw,Finset.image_union,Finset.image_image]
  rfl

lemma edge_budget (a : P) (B : Finset (P×P)) (S T : ℕ → Finset P) (k : ℕ)
    (charge : Prop) [Decidable charge] (double : charge → collision a B S T k)
    (pay : Prop) [Decidable pay] (allow : fresh B S T k → pay) :
    (edges a B S T (k+1)).card + (if charge then 1 else 0) ≤
      (edges a B S T k).card + (if pay then 1 else 0) := by
  classical
  let E:=edges a B S T k
  let f:=pairStep a S T k
  let V:=(S k ×ˢ T k).image (pairLabel a S T (k+1))
  have nextE : edges a B S T (k+1)=E.image f ∪ V := pair_update a B S T k
  have cap : V.card≤1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨z',hz',rfl⟩:=Finset.mem_image.mp hy
    exact flat_pair a S T k hz hz'
  have inherited (h : inherit B S T k) : V⊆E.image f := by
    obtain ⟨z,hz,hit⟩:=h
    intro w hw
    obtain ⟨z',hz',rfl⟩:=Finset.mem_image.mp hw
    refine Finset.mem_image.mpr ⟨_,Finset.mem_image_of_mem _ hz,?_⟩
    exact flat_pair a S T k hit hz'
  have le : (E.image f).card≤E.card := Finset.card_image_le
  rw [nextE]
  by_cases h : charge
  · obtain ⟨z,hz,z',hz',hit,hit',ne⟩ := double h
    have hsub:=inherited ⟨z,hz,hit⟩
    have strict : (E.image f).card<E.card := by
      apply lt_of_le_of_ne le
      intro eq
      apply ne
      apply (Finset.card_image_iff.mp eq) (Finset.mem_image_of_mem _ hz) (Finset.mem_image_of_mem _ hz')
      exact flat_pair a S T k hit hit'
    rw [Finset.union_eq_left.mpr hsub,ite_eq_left h]
    change (E.image f).card+1 ≤ E.card+_
    omega
  · rw [ite_eq_right h,Nat.add_zero]
    by_cases old : inherit B S T k
    · rw [Finset.union_eq_left.mpr (inherited old)]
      exact le.trans (Nat.le_add_right _ _)
    by_cases ne : V.Nonempty
    · obtain ⟨v,hv⟩:=ne
      obtain ⟨z,hz,_⟩:=Finset.mem_image.mp hv
      have pp:=Finset.mem_product.mp hz
      have paid:=allow ⟨⟨z.1,pp.1⟩,⟨z.2,pp.2⟩,old⟩
      rw [ite_eq_left paid]
      exact (Finset.card_union_le ..).trans (Nat.add_le_add le cap)
    · rw [Finset.not_nonempty_iff_eq_empty.mp ne,Finset.union_empty]
      exact le.trans (Nat.le_add_right _ _)

-- For two lines, every simultaneous merge consumes a previously created pair.
lemma pair_total (a : P) (B : Finset (P×P)) (S T : ℕ → Finset P) (k : ℕ)
    (one : B.card≤1) (D H : Finset ℕ) (double : ∀ i<k, i∈D → collision a B S T i)
    (pay : ∀ i<k, fresh B S T i → i∈H) :
    ((Finset.range k)∩D).card≤((Finset.range k)∩H).card := by
  classical
  have step (n) (hn : n≤k) : (edges a B S T n).card+((Finset.range n)∩D).card ≤
      B.card+((Finset.range n)∩H).card := by
    induction n with
    | zero =>
      simp only [Finset.range_zero,Finset.empty_inter,Finset.card_empty,Nat.add_zero]
      exact Finset.card_image_le
    | succ n ih =>
      have prev:=ih (by omega)
      have grow:=edge_budget a B S T n (n∈D) (double n (by omega)) (n∈H) (pay n (by omega))
      rw [Finset.range_add_one]
      by_cases hd:n∈D <;> by_cases hh:n∈H <;>
        simp [Finset.insert_inter_of_mem,Finset.insert_inter_of_notMem,hd,hh] at grow ⊢ <;> omega
  have bnd : B.card≤(edges a B S T k).card := by
    rcases B.eq_empty_or_nonempty with rfl|⟨z,hz⟩
    · simp
    · have pos := Finset.card_pos.mpr (show (edges a B S T k).Nonempty from
        ⟨_,Finset.mem_image_of_mem _ (seed_in_raw B S T k hz)⟩)
      omega
  have doneStep:=step k (le_refl _)
  omega

end PEqualNP.Outside.L_meta_1643.Partition

namespace PEqualNP.Outside.L_meta_1643.Wires
open Finset PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1643
variable {N : ℕ}

abbrev supp (L : Fin N → Finset (Fin N)) (a b : Fin N) (gs : List Gate) (t : Fin N) (w : ℕ) :=
  Geometry.pts L a b (Rim.V gs w) t

abbrev seq (L : Fin N → Finset (Fin N)) (a b : Fin N) (gs : List Gate) (t : Fin N) (k : ℕ) :=
  supp L a b gs t (N+k)

noncomputable abbrev labs (L : Fin N → Finset (Fin N)) (a b : Fin N) (gs : List Gate) (t : Fin N) (k : ℕ) :=
  Partition.label a (seq L a b gs t) k

noncomputable abbrev cols (L : Fin N → Finset (Fin N)) (a b : Fin N) (gs : List Gate) (t : Fin N) (k : ℕ) :=
  Partition.colors a (seq L a b gs t) k

abbrev merged (L : Fin N → Finset (Fin N)) (a b : Fin N) (gs : List Gate) (t : Fin N) (k : ℕ) :=
  1<(cols L a b gs t k).card

abbrev okay (gs : List Gate) :=
  ∀ g∈gs,(g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2

abbrev earlier (N : ℕ) (gs : List Gate) :=
  ∀ i : Fin gs.length, ∀ a∈(gs.get i).inputs,a<N+i.val

lemma eval_mono {gs : List Gate} (good : okay gs) (w : ℕ) : Geometry.monoFn (Rim.V (N:=N) gs w) :=
  fun x y h => Count.mono ⟨gs,w⟩ good x y h w

section Circuit
variable {L : Fin N → Finset (Fin N)} {a b t : Fin N} {gs : List Gate}

lemma at_input (p r : Fin N) (h : r∈supp L a b gs t p.val)
    (moff : Geometry.marker L a b t∉L t) : p=r := by
  have e (x : Fin N → Bool) : Rim.V gs p.val x=x p :=
    Count.input_value ⟨gs,p.val⟩ x p
  obtain ⟨cold,_,hit⟩:=Geometry.in_pts.mp h
  rw [e] at cold hit
  have pin : p∈L t := by simpa [Geometry.co] using cold
  rcases of_decide_eq_true hit with eq|⟨_,_,eq⟩
  · exact eq
  · exact (moff (eq ▸ pin)).elim

lemma old_flat {k w : ℕ} (old : w<N+k) (moff : Geometry.marker L a b t∉L t)
    {p r : Fin N} (hp : p∈supp L a b gs t w) (hr : r∈supp L a b gs t w) :
    labs L a b gs t k p=labs L a b gs t k r := by
  by_cases hw : w<N
  · have eq: p=r := (at_input (⟨w,hw⟩ : Fin N) p hp moff).symm.trans (at_input ⟨w,hw⟩ r hr moff)
    rw [eq]
  · have he:w=N+(w-N) := by omega
    rw [he] at hp hr
    exact Partition.flat a (seq L a b gs t) (by omega : w-N<k) hp hr

lemma old_cap {k w : ℕ} (old : w<N+k) (moff : Geometry.marker L a b t∉L t) :
    ((supp L a b gs t w).image (labs L a b gs t k)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro z hz z' hz'
  obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hz
  obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hz'
  exact old_flat old moff hp hr

lemma equal_supp {v w : ℕ} (eq : ∀ x : Fin N → Bool,Rim.V gs v x=Rim.V gs w x) :
    supp L a b gs t v=supp L a b gs t w := congrArg (fun f => Geometry.pts L a b f t) (funext eq)

lemma constant_empty {v : ℕ} {c : Bool} (eq : ∀ x : Fin N → Bool,Rim.V gs v x=c) :
    supp L a b gs t v=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨cold,_,hit⟩:=Geometry.in_pts.mp hp
  rw [eq] at cold hit
  exact Bool.noConfusion (cold.symm.trans hit)

lemma and_subset {v u w : ℕ} (eq : ∀ x : Fin N → Bool,Rim.V gs v x=(Rim.V gs u x && Rim.V gs w x)) :
    supp L a b gs t v⊆supp L a b gs t u ∨ supp L a b gs t v⊆supp L a b gs t w := by
  by_cases cu : Rim.V gs u (Geometry.co L t)=false
  · left
    intro p h
    obtain ⟨_,pt,on⟩:=Geometry.in_pts.mp h
    exact Geometry.in_pts.mpr ⟨cu,pt,(Bool.and_eq_true_iff.mp ((eq _).symm.trans on)).1⟩
  · right
    intro p h
    obtain ⟨cv,pt,on⟩:=Geometry.in_pts.mp h
    have uu : Rim.V gs u (Geometry.co L t)=true := by simpa using cu
    rw [eq,uu,Bool.true_and] at cv
    exact Geometry.in_pts.mpr ⟨cv,pt,(Bool.and_eq_true_iff.mp ((eq _).symm.trans on)).2⟩

lemma or_union {v u w : ℕ} (eq : ∀ x : Fin N → Bool,Rim.V gs v x=(Rim.V gs u x || Rim.V gs w x))
    (live : (supp L a b gs t v).Nonempty) :
    supp L a b gs t v=supp L a b gs t u∪supp L a b gs t w := by
  obtain ⟨p,hp⟩:=live
  have cv:=(Geometry.in_pts.mp hp).1
  have cc:=Bool.or_eq_false_iff.mp ((eq _).symm.trans cv)
  ext r
  simp only [Finset.mem_union,Geometry.in_pts,cv,cc.1,cc.2,true_and,eq _ ,Bool.or_eq_true]
  tauto

lemma split_merge {k u w : ℕ} (hu : u<N+k) (hw : w<N+k) (moff : Geometry.marker L a b t∉L t)
    (eq : ∀ x : Fin N → Bool,Rim.V gs (N+k) x=(Rim.V gs u x || Rim.V gs w x))
    (merge : merged L a b gs t k) :
    ∃ p∈supp L a b gs t u,∃ r∈supp L a b gs t w,labs L a b gs t k p≠labs L a b gs t k r := by
  obtain ⟨z,hz,z',hz',ne⟩:=Finset.one_lt_card.mp merge
  obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hz
  obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hz'
  have un:=or_union eq (show (supp L a b gs t (N+k)).Nonempty from ⟨p,hp⟩)
  change p∈supp L a b gs t (N+k) at hp
  change r∈supp L a b gs t (N+k) at hr
  rw [un] at hp hr
  rcases Finset.mem_union.mp hp with pu|pw <;> rcases Finset.mem_union.mp hr with ru|rw
  · exact (ne (old_flat hu moff pu ru)).elim
  · exact ⟨p,pu,r,rw,ne⟩
  · exact ⟨r,ru,p,pw,Ne.symm ne⟩
  · exact (ne (old_flat hw moff pw rw)).elim

lemma merged_nonempty {k : ℕ} (merge : merged L a b gs t k) : (supp L a b gs t (N+k)).Nonempty := by
  have c:=Finset.card_image_le (s:=seq L a b gs t k) (f:=labs L a b gs t k)
  exact Finset.card_pos.mp (lt_trans Nat.zero_lt_one (lt_of_lt_of_le merge c))

lemma colors_cap (good : okay gs) (top : earlier N gs) (moff : Geometry.marker L a b t∉L t)
    (k : Fin gs.length) : (cols L a b gs t k.val).card≤2 := by
  change ((supp L a b gs t (N+k.val)).image (labs L a b gs t k.val)).card≤2
  rcases Rim.gateCases gs good top k with ⟨c,eq⟩|⟨u,hu,eq⟩|⟨u,hu,w,hw,_,_,eq⟩|⟨u,hu,w,hw,_,_,eq⟩
  · rw [constant_empty eq];simp
  · rw [equal_supp eq];exact (old_cap hu moff).trans (by decide)
  · rcases and_subset (L:=L) (a:=a) (b:=b) (t:=t) eq with h|h
    · exact (Finset.card_le_card (Finset.image_subset_image h)).trans ((old_cap hu moff).trans (by decide))
    · exact (Finset.card_le_card (Finset.image_subset_image h)).trans ((old_cap hw moff).trans (by decide))
  · rcases (supp L a b gs t (N+k.val)).eq_empty_or_nonempty with he|ne
    · rw [he];simp
    rw [or_union eq ne,Finset.image_union]
    have l:=Finset.card_union_le ((supp L a b gs t u).image (labs L a b gs t k)) ((supp L a b gs t w).image (labs L a b gs t k))
    have l1:=old_cap (a:=a) (b:=b) (gs:=gs) hu moff
    have l2:=old_cap (a:=a) (b:=b) (gs:=gs) hw moff
    omega

end Circuit
end PEqualNP.Outside.L_meta_1643.Wires

namespace PEqualNP.Outside.L_meta_1643.Wires
open Finset PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1643
variable {N : ℕ}

def seed (L : Fin N → Finset (Fin N)) (t s : Fin N) := (L t ∩ L s).image fun p => (p,p)
abbrev history (L : Fin N → Finset (Fin N)) (a b : Fin N) (gs : List Gate) (t s : Fin N) (k : ℕ) :=
  Partition.raw (seed L t s) (seq L a b gs t) (seq L a b gs s) k
abbrev born (L : Fin N → Finset (Fin N)) (a b : Fin N) (gs : List Gate) (t s : Fin N) (k : ℕ) :=
  Partition.fresh (seed L t s) (seq L a b gs t) (seq L a b gs s) k

section Circuit
variable {L : Fin N → Finset (Fin N)} {a b t s : Fin N} {gs : List Gate}

lemma wire_pair {k w : ℕ} (early : w<N+k) (mt : Geometry.marker L a b t∉L t) (ms : Geometry.marker L a b s∉L s)
    {p r : Fin N} (hp : p∈supp L a b gs t w) (hr : r∈supp L a b gs s w) :
    (p,r)∈history L a b gs t s k := by
  by_cases h : w<N
  · let z : Fin N:=⟨w,h⟩
    have ep : z=p:=at_input z p hp mt
    have er : z=r:=at_input z r hr ms
    apply Partition.seed_in_raw
    exact Finset.mem_image.mpr ⟨z,Finset.mem_inter.mpr ⟨ep.symm ▸ (Geometry.in_pts.mp hp).2.1,er.symm ▸ (Geometry.in_pts.mp hr).2.1⟩,Prod.ext ep er⟩
  · have eq : w=N+(w-N) := by omega
    rw [eq] at hp hr
    apply Partition.past_in_raw _ _ _ (by omega : w-N<k)
    exact Finset.mem_product.mpr ⟨hp,hr⟩

lemma merge_gate (good : okay gs) (top : earlier N gs) (mt : Geometry.marker L a b t∉L t)
    {k : Fin gs.length} (mg : merged L a b gs t k) :
    ∃ u<N+k.val,∃ w<N+k.val,(gs.get k).op=GateOp.or ∧ (gs.get k).inputs=[u,w] ∧
      ∀ x : Fin N → Bool,Rim.V gs (N+k.val) x=(Rim.V gs u x || Rim.V gs w x) := by
  have ne:=merged_nonempty mg
  have monoCap {w : ℕ} (hw:w<N+k.val) (h : seq L a b gs t k ⊆ supp L a b gs t w) : False := by
    have bd := (Finset.card_le_card (Finset.image_subset_image (f:=labs L a b gs t k) h)).trans (old_cap hw mt)
    exact (Nat.not_lt_of_le bd) mg
  rcases Rim.gateCases gs good top k with ⟨c,eq⟩|⟨u,hu,eq⟩|⟨u,hu,w,hw,_,_,eq⟩|h
  · exact (ne.ne_empty (constant_empty eq)).elim
  · exact (monoCap hu (equal_supp eq).le).elim
  · rcases and_subset (L:=L) (a:=a) (b:=b) (t:=t) eq with h|h
    · exact (monoCap hu h).elim
    · exact (monoCap hw h).elim
  · exact h

lemma double_collision (good : okay gs) (top : earlier N gs)
    (mt : Geometry.marker L a b t∉L t) (ms : Geometry.marker L a b s∉L s)
    {k : Fin gs.length} (gt : merged L a b gs t k) (gt' : merged L a b gs s k) :
    Partition.collision a (seed L t s) (seq L a b gs t) (seq L a b gs s) k := by
  obtain ⟨u,hu,w,hw,_,_,eq⟩:=merge_gate good top mt gt
  obtain ⟨p,pu,p',pw,ne⟩:=split_merge hu hw mt eq gt
  obtain ⟨r,ru,r',rw,_⟩:=split_merge hu hw ms eq gt'
  have ut:=or_union eq (merged_nonempty gt)
  have us:=or_union eq (merged_nonempty gt')
  refine ⟨(p,r),wire_pair hu mt ms pu ru,(p',r'),wire_pair hw mt ms pw rw,?_,?_,?_⟩
  · apply Finset.mem_product.mpr
    exact ⟨ut.ge (Finset.mem_union_left _ pu),us.ge (Finset.mem_union_left _ ru)⟩
  · apply Finset.mem_product.mpr
    exact ⟨ut.ge (Finset.mem_union_right _ pw),us.ge (Finset.mem_union_right _ rw)⟩
  · exact fun h => ne (congrArg Prod.fst h)

lemma merge_inherits (good : okay gs) (top : earlier N gs) (mt : Geometry.marker L a b t∉L t)
    (ms : Geometry.marker L a b s∉L s) {k : Fin gs.length} (gt : merged L a b gs t k)
    (vs : (seq L a b gs s k).Nonempty) :
    Partition.inherit (seed L t s) (seq L a b gs t) (seq L a b gs s) k := by
  obtain ⟨u,hu,w,hw,_,_,eq⟩:=merge_gate good top mt gt
  obtain ⟨p,pu,p',pw,_⟩:=split_merge hu hw mt eq gt
  have ut:=or_union eq (merged_nonempty gt)
  have us:=or_union eq vs
  obtain ⟨r,hr⟩:=vs
  have mem : r∈supp L a b gs s u ∪ supp L a b gs s w := us ▸ hr
  rcases Finset.mem_union.mp mem with ru|rw
  · exact ⟨(p,r),wire_pair hu mt ms pu ru,Finset.mem_product.mpr ⟨ut.ge (Finset.mem_union_left _ pu),hr⟩⟩
  · exact ⟨(p',r),wire_pair hw mt ms pw rw,Finset.mem_product.mpr ⟨ut.ge (Finset.mem_union_right _ pw),hr⟩⟩

lemma swap_history (p : Fin N × Fin N) (k : ℕ) :
    p.swap∈history L a b gs s t k ↔ p∈history L a b gs t s k := by
  induction k with
  | zero =>
    change p.swap∈seed L s t ↔ p∈seed L t s
    obtain ⟨x,y⟩:=p
    simp [seed,Finset.mem_image,Prod.ext_iff,Finset.inter_comm,eq_comm, and_comm]
  | succ k ih =>
    change p.swap∈Partition.raw _ _ _ k ∪ _ ↔ p∈Partition.raw _ _ _ k ∪ _
    simp only [Finset.mem_union,Finset.mem_product]
    change (p.swap∈history L a b gs s t k ∨ p.2∈_ ∧ p.1∈_) ↔
      (p∈history L a b gs t s k ∨ p.1∈_ ∧ p.2∈_)
    rw [ih];tauto

lemma swap_birth {k : ℕ} (fresh : born L a b gs t s k) : born L a b gs s t k := by
  refine ⟨fresh.2.1,fresh.1,?_⟩
  rintro ⟨z,hz,hit⟩
  apply fresh.2.2
  exact ⟨z.swap,(swap_history z k).mpr hz,Finset.mem_product.mpr ⟨(Finset.mem_product.mp hit).2,(Finset.mem_product.mp hit).1⟩⟩

lemma no_merge_at_birth (good : okay gs) (top : earlier N gs)
    (mt : Geometry.marker L a b t∉L t) (ms : Geometry.marker L a b s∉L s)
    {k : Fin gs.length} (h : born L a b gs t s k) :
    ¬merged L a b gs t k ∧ ¬merged L a b gs s k :=
  ⟨fun e=>h.2.2 (merge_inherits good top mt ms e h.2.1),
   fun e=>(swap_birth h).2.2 (merge_inherits good top ms mt e h.1)⟩

end Circuit
end PEqualNP.Outside.L_meta_1643.Wires

namespace PEqualNP.Outside.L_meta_1643
open Finset PEqualNP.CircuitLowerBounds

def exempt {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 a b : Fin N) (gs : List Gate) (k : Fin gs.length) :=
  Rim.delivering (L i0) {a,b} gs k ∨ ((gs.get k).op=GateOp.or ∧ ∀ t,t≠i0 → Rim.V gs (N+k.val) (Rim.base (L t))=true)

noncomputable def reserve {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 a b : Fin N) (gs : List Gate) :
    Finset (Fin gs.length) := by classical exact Finset.univ.filter (exempt L i0 a b gs)

lemma in_reserve {N : ℕ} {L : Fin N → Finset (Fin N)} {i0 a b : Fin N} {gs : List Gate} {k : Fin gs.length} :
    k∈reserve L i0 a b gs ↔ exempt L i0 a b gs k := by classical simp [reserve]

lemma reserve_budget {N q : ℕ} (L : Fin N → Finset (Fin N)) (i0 a b : Fin N) (ab : a≠b)
    (ha : a∈L i0) (hb : b∈L i0) (hq : 3≤q) (card : ∀ i,(L i).card=q+1)
    (inter : ∀ i j,i≠j → (L i∩L j).card=1)
    (gs : List Gate) (out : Fin N → ℕ)
    (good : ∀ g∈gs,(g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (top : ∀ i : Fin gs.length, ∀ w∈(gs.get i).inputs,w<N+i.val)
    (correct : ∀ t x,domain (L i0) a b x → Circuit.eval ⟨gs,out t⟩ (List.ofFn x)=decide (∃ v∈L t,x v=true)) :
    q≤(reserve L i0 a b gs).card := by
  classical
  let T : Finset (Fin N) := {a,b}
  let A := Finset.univ.filter (Rim.delivering (L i0) T gs)
  let X := Finset.univ.filter (Rim.spare L i0 T gs)
  let E := reserve L i0 a b gs
  have sub : T⊆L i0 := by intro r hr;rcases Finset.mem_insert.mp hr with rfl|h;exact ha;simpa [Finset.mem_singleton.mp h] using hb
  have tc : T.card=2 := by simp [T,ab]
  have neg : Rim.V gs (out i0) (Rim.base (L i0))=false := by
    have h:=correct i0 _ (cotest L i0 a b inter ab ha hb i0)
    exact h.trans (by simp)
  have single (r) (hr : r∈T) : Rim.U gs (out i0) r := by
    have hD : domain (L i0) a b (Rim.single r) := by
      rcases Finset.mem_insert.mp hr with rfl|h
      · exact Or.inl (by simp [Rim.single])
      · rw [Finset.mem_singleton.mp h]
        exact Or.inr (Or.inl (by simp [Rim.single]))
    have yes : ∃ v∈L i0,Rim.single r v=true := ⟨r,sub hr,by simp [Rim.single]⟩
    exact (correct i0 _ hD).trans (decide_eq_true yes)
  have rim (r) (hr : r∈L i0 \ T) : Rim.S gs (L i0) (out i0) r := by
    let x:=Rim.rimInput (L i0) r
    have hD : domain (L i0) a b x := Or.inr (Or.inr (fun u hu => by simp [x,hu]))
    have yes : ∃ v∈L i0,x v=true := ⟨r,(Finset.mem_sdiff.mp hr).1,by simp [x]⟩
    exact (correct i0 x hD).trans (decide_eq_true yes)
  have rbound:=Rim.rim_budget L i0 T (by decide : 1≤2) card inter sub tc gs (out i0) good top neg single rim A X
    (by simp [A]) (by simp [X])
  have dis : Disjoint A X := by
    apply Finset.disjoint_left.mpr
    intro g hg hx
    have hg':= (Finset.mem_filter.mp hg).2
    have hx':= (Finset.mem_filter.mp hx).2
    exact (show GateOp.and≠GateOp.or by intro h;cases h) (hg'.1.symm.trans hx'.1)
  have incl : A∪X ⊆ E := by
    intro k hk
    apply in_reserve.mpr
    rcases Finset.mem_union.mp hk with h|h
    · exact Or.inl (Finset.mem_filter.mp h).2
    · have e:=(Finset.mem_filter.mp h).2
      exact Or.inr ⟨e.1,e.2.2.2⟩
  let K:=E \ (A∪X)
  have bound:=Count.family gs good T Rim.single (Rim.base (L i0)) (out i0)
    (fun p hp => ⟨single p hp,neg⟩) (by
      intro w hw h
      obtain ⟨p,_,r,_,ne,hp,hr⟩:=h
      let z : Fin N:=⟨w,hw⟩
      have eq (k : Fin N) (live : Count.value ⟨gs,0⟩ (Rim.single k) w=true) : z=k := by
        change Count.value ⟨gs,0⟩ (Rim.single k) z.val=true at live
        rw [Count.input_value] at live
        exact of_decide_eq_true live
      exact ne ((eq p hp.1).symm.trans (eq r hr.1))) K (by
      intro g hg hop _ children
      obtain ⟨p,hp,r,hr,ne,sp,sr⟩:=hg
      have all:=Rim.offOther gs (N+g.val) L good inter (sub hp) (sub hr) ne sp.1 sr.1
      apply Finset.mem_sdiff.mpr
      refine ⟨in_reserve.mpr (Or.inr ⟨hop,all⟩),?_⟩
      intro h
      rcases Finset.mem_union.mp h with h|h
      · exact (show GateOp.and≠GateOp.or by intro h;cases h) ((Finset.mem_filter.mp h).2.1.symm.trans hop)
      · obtain ⟨w,hw,none⟩:=(Finset.mem_filter.mp h).2.2.2.1
        exact none (children w hw))
  have sz : K.card=E.card-(A.card+X.card) := by
    rw [show K=E \ (A∪X) from rfl,Finset.card_sdiff_of_subset incl,Finset.card_union_of_disjoint dis]
  change q≤E.card
  omega

end PEqualNP.Outside.L_meta_1643

namespace PEqualNP.Outside.L_meta_1643.Wires
open Finset PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1643
variable {N q : ℕ} {L : Fin N → Finset (Fin N)} {a b i0 : Fin N} {gs : List Gate}

abbrev ordinary (i : Fin N) : Finset (Fin N) := Finset.univ.erase i
abbrev lefts (L : Fin N → Finset (Fin N)) (i0 a : Fin N) := (ordinary i0).filter fun t => a∈L t
abbrev rights (L : Fin N → Finset (Fin N)) (i0 b : Fin N) := (ordinary i0).filter fun t => b∈L t
abbrev gridPairs (L : Fin N → Finset (Fin N)) (i0 a b : Fin N) := lefts L i0 a ×ˢ rights L i0 b

lemma mark_off (inter : ∀ i j,i≠j → (L i∩L j).card=1) (ab : a≠b)
    (ha : a∈L i0) (hb : b∈L i0) {t : Fin N} (ordinary : t≠i0) : Geometry.marker L a b t∉L t := by
  by_cases at' : a∈L t
  · simpa [Geometry.marker,at'] using Geometry.both_marker inter ordinary ab ha hb at'
  · simp [Geometry.marker,at']

lemma line_mass (inter : ∀ i j,i≠j → (L i∩L j).card=1) (ab : a≠b)
    (ha : a∈L i0) (hb : b∈L i0) (card : ∀ t,(L t).card=q+1)
    (good : okay gs) (top : earlier N gs) {out : Fin N → ℕ}
    (correct : ∀ t x,domain (L i0) a b x → Circuit.eval ⟨gs,out t⟩ (List.ofFn x)=decide (∃ v∈L t,x v=true))
    {t : Fin N} (to' : t≠i0) :
    ((Finset.range gs.length).filter fun k => merged L a b gs t k).card=q := by
  classical
  have mt:=mark_off inter ab ha hb to'
  have ok : supp L a b gs t (out t)=L t := by
    ext p
    constructor
    · exact fun h=>(Geometry.in_pts.mp h).2.1
    · intro hp
      have cold : Rim.V gs (out t) (Geometry.co L t)=false :=
        (correct t _ (cotest L i0 a b inter ab ha hb t)).trans (by simp)
      have pos : domain (L i0) a b (Geometry.test L a b t p) := by
        by_cases p0 : p=a
        · exact Or.inl (by simp [Geometry.test,p0])
        by_cases p1 : p=b
        · exact Or.inr (Or.inl (by simp [Geometry.test,p1]))
        by_cases at' : a∈L t
        · exact Or.inr (Or.inl (by simp [Geometry.test,Geometry.marker,at',p0,p1]))
        · exact Or.inl (by simp [Geometry.test,Geometry.marker,at',p0,p1])
      exact Geometry.in_pts.mpr ⟨cold,hp,(correct t _ pos).trans (decide_eq_true ⟨p,hp,by simp [Geometry.test]⟩)⟩
  have non : (L t).Nonempty:=Finset.card_pos.mp (by rw [card];omega)
  obtain ⟨p,hp⟩:=non
  have reach : out t<N+gs.length := by
    by_contra! h
    have seed:=(Geometry.in_pts.mp (ok.ge hp)).2.2
    have no:=Rim.missingV gs (out t) h (Geometry.test L a b t p)
    rw [no] at seed;contradiction
  have last : ((L t).image (labs L a b gs t gs.length)).card=1 := by
    apply Nat.le_antisymm
    · apply Finset.card_le_one.mpr
      intro y hy z hz
      obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hy
      obtain ⟨s,hs,rfl⟩:=Finset.mem_image.mp hz
      exact old_flat reach mt (ok.ge hr) (ok.ge hs)
    · exact Finset.card_pos.mpr ⟨_,Finset.mem_image_of_mem _ hp⟩
  have m:=Partition.mass a (seq L a b gs t) (L t) gs.length (fun j _ p hp => (Geometry.in_pts.mp hp).2.1)
    (fun j hj => colors_cap good top mt ⟨j,hj⟩)
  change ((L t).image (labs L a b gs t gs.length)).card+_= (L t).card at m
  rw [last,card] at m
  change 1+((Finset.range gs.length).filter fun k => merged L a b gs t k).card=q+1 at m
  omega

lemma pair_bounds {p : Fin N × Fin N} (mem : p∈gridPairs L i0 a b) :
    p.1≠i0 ∧ a∈L p.1 ∧ p.2≠i0 ∧ b∈L p.2 := by
  obtain ⟨left,right⟩:=Finset.mem_product.mp mem
  obtain ⟨lo,la⟩:=Finset.mem_filter.mp left
  obtain ⟨ro,rb⟩:=Finset.mem_filter.mp right
  exact ⟨(Finset.mem_erase.mp lo).1,la,(Finset.mem_erase.mp ro).1,rb⟩

lemma only_lines (inter : ∀ i j,i≠j → (L i∩L j).card=1) (ab : a≠b)
    (ha : a∈L i0) (hb : b∈L i0) (good : okay gs) {l m : Fin N} (pair : (l,m)∈gridPairs L i0 a b)
    {w : ℕ} (ll : (supp L a b gs l w).Nonempty) (lm : (supp L a b gs m w).Nonempty) :
    (∀ i∈lefts L i0 a, i≠l → Rim.V gs w (Geometry.co L i)=true) ∧
    (∀ j∈rights L i0 b, j≠m → Rim.V gs w (Geometry.co L j)=true) ∧
    ∀ t, t≠i0 → 1<(supp L a b gs t w).card → t=l ∨ t=m := by
  obtain ⟨li,al,mi,bm⟩:=pair_bounds pair
  have bl:=Geometry.both_marker inter li ab ha hb al
  have am:=Geometry.both_marker inter mi ab.symm hb ha bm
  obtain ⟨v,hv⟩:=ll
  obtain ⟨z,hz⟩:=lm
  have cl:=(Geometry.in_pts.mp hv).1
  have cm:=(Geometry.in_pts.mp hz).1
  have left (i) (hi : i∈lefts L i0 a) (il : i≠l) : Rim.V gs w (Geometry.co L i)=true := by
    obtain ⟨io,ai⟩:=Finset.mem_filter.mp hi
    have bi := Geometry.both_marker inter (Finset.mem_erase.mp io).1 ab ha hb ai
    exact Geometry.other_pencil inter (eval_mono good w) il.symm (Or.inl rfl) al ai am (by simpa [Geometry.marker,al] using bi) cm ⟨v,hv⟩
  have right (j) (hj : j∈rights L i0 b) (jm : j≠m) : Rim.V gs w (Geometry.co L j)=true := by
    obtain ⟨jo,bj⟩:=Finset.mem_filter.mp hj
    have aj:=Geometry.both_marker inter (Finset.mem_erase.mp jo).1 ab.symm hb ha bj
    exact Geometry.other_pencil inter (eval_mono good w) jm.symm (Or.inr rfl) bm bj bl (by simpa [Geometry.marker,am] using aj) cl ⟨z,hz⟩
  refine ⟨left,right,?_⟩
  intro t to' many
  by_contra! bad
  have mm:=Geometry.multi_marker inter (eval_mono good w) bad.2 cm many
  obtain ⟨x,hx⟩:=Finset.card_pos.mp (lt_trans Nat.zero_lt_one many)
  have ct:=(Geometry.in_pts.mp hx).1
  by_cases at' : a∈L t
  · have hot:=left t (by simp [lefts,ordinary,to',at']) bad.1
    rw [hot] at ct;contradiction
  · exact am (by simpa [Geometry.marker,at'] using mm)

end PEqualNP.Outside.L_meta_1643.Wires

namespace PEqualNP.Outside.L_meta_1643.Wires
open Finset PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1643
variable {N : ℕ} {L : Fin N → Finset (Fin N)} {a b i0 l m : Fin N} {gs : List Gate}

lemma merged_many {t : Fin N} {k : ℕ} (h : merged L a b gs t k) : 1<(seq L a b gs t k).card :=
  lt_of_lt_of_le h Finset.card_image_le

lemma parent_inherit {k w : ℕ} (early : w<N+k)
    (ml : Geometry.marker L a b l∉L l) (mm : Geometry.marker L a b m∉L m)
    (fl : (seq L a b gs l k).Nonempty) (fm : (seq L a b gs m k).Nonempty)
    (s1 : seq L a b gs l k ⊆ supp L a b gs l w) (s2 : seq L a b gs m k ⊆ supp L a b gs m w) :
    Partition.inherit (seed L l m) (seq L a b gs l) (seq L a b gs m) k := by
  obtain ⟨p,hp⟩:=fl
  obtain ⟨r,hr⟩:=fm
  exact ⟨(p,r),wire_pair early ml mm (s1 hp) (s2 hr),Finset.mem_product.mpr ⟨hp,hr⟩⟩

lemma cold_child {u v z : ℕ} {t : Fin N}
    (ev : ∀ x : Fin N → Bool,Rim.V gs z x= (Rim.V gs u x && Rim.V gs v x))
    (hot : Rim.V gs u (Geometry.co L t)=true) : supp L a b gs t z⊆supp L a b gs t v := by
  intro p hp
  obtain ⟨c,pt,on⟩:=Geometry.in_pts.mp hp
  rw [ev,hot,Bool.true_and] at c
  exact Geometry.in_pts.mpr ⟨c,pt,(Bool.and_eq_true_iff.mp ((ev _).symm.trans on)).2⟩

lemma birth_not_exempt (inter : ∀ i j,i≠j → (L i∩L j).card=1) (ab : a≠b)
    (ha : a∈L i0) (hb : b∈L i0) (good : okay gs) (top : earlier N gs)
    (pair : (l,m)∈gridPairs L i0 a b) {k : Fin gs.length} (birth : born L a b gs l m k) :
    ¬ exempt L i0 a b gs k := by
  obtain ⟨li,al,mi,bm⟩:=pair_bounds pair
  have ml:=mark_off inter ab ha hb li
  have mm:=mark_off inter ab ha hb mi
  obtain ⟨p,hp⟩:=birth.1
  obtain ⟨r,hr⟩:=birth.2.1
  rintro (delivery|⟨_,all⟩)
  · obtain ⟨andOp,_,w,win,j,hj,live⟩:=delivery
    obtain ⟨ji,un⟩:=Finset.mem_sdiff.mp hj
    have ja : j≠a := fun h=>un (h ▸ Finset.mem_insert_self ..)
    have jb : j≠b := fun h=>un (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have outsideL : j∉L l := fun h => ja (Geometry.two_points inter li h ji al ha)
    have outsideM : j∉L m := fun h => jb (Geometry.two_points inter mi h ji bm hb)
    have hot {t : Fin N} (out : j∉L t) : Rim.V gs w (Geometry.co L t)=true := by
      apply eval_mono good w (Rim.single j) _ _ live
      intro z h
      exact decide_eq_true ((of_decide_eq_true h).symm ▸ out)
    rcases Rim.gateCases gs good top k with ⟨c,eq⟩|⟨u,hu,eq⟩|⟨u,hu,v,hv,_,ins,eq⟩|⟨_,_,_,_,op,_⟩
    · exact birth.1.ne_empty (constant_empty eq)
    · exact birth.2.2 (parent_inherit hu ml mm birth.1 birth.2.1 (equal_supp eq).le (equal_supp eq).le)
    · rw [ins] at win
      rcases List.mem_pair.mp win with h|h
      · subst w
        exact birth.2.2 (parent_inherit hv ml mm birth.1 birth.2.1 (cold_child eq (hot outsideL)) (cold_child eq (hot outsideM)))
      · subst w
        have rev (x) : Rim.V gs (N+k.val) x=(Rim.V gs v x && Rim.V gs u x) := (eq x).trans (Bool.and_comm ..)
        exact birth.2.2 (parent_inherit hu ml mm birth.1 birth.2.1 (cold_child rev (hot outsideL)) (cold_child rev (hot outsideM)))
    · exact (show GateOp.and≠GateOp.or by intro h;cases h) (andOp.symm.trans op)
  · have c:=(Geometry.in_pts.mp hp).1
    have h:=all l li
    exact Bool.noConfusion (c.symm.trans h)

lemma birth_not_merged (inter : ∀ i j,i≠j → (L i∩L j).card=1) (ab : a≠b)
    (ha : a∈L i0) (hb : b∈L i0) (good : okay gs) (top : earlier N gs)
    (pair : (l,m)∈gridPairs L i0 a b) {k : Fin gs.length} (birth : born L a b gs l m k)
    {t : Fin N} (ti : t≠i0) : ¬ merged L a b gs t k := by
  intro on
  obtain ⟨li,_,mi,_⟩:=pair_bounds pair
  have only:=only_lines inter ab ha hb good pair birth.1 birth.2.1
  have no:=no_merge_at_birth good top (mark_off inter ab ha hb li) (mark_off inter ab ha hb mi) birth
  rcases only.2.2 t ti (merged_many on) with rfl|rfl
  · exact no.1 on
  · exact no.2 on

lemma birth_unique (inter : ∀ i j,i≠j → (L i∩L j).card=1) (ab : a≠b)
    (ha : a∈L i0) (hb : b∈L i0) (good : okay gs)
    {x y : Fin N × Fin N} (hx : x∈gridPairs L i0 a b) (hy : y∈gridPairs L i0 a b)
    {k : ℕ} (fx : born L a b gs x.1 x.2 k) (fy : born L a b gs y.1 y.2 k) : x=y := by
  have only:=only_lines inter ab ha hb good hx fx.1 fx.2.1
  obtain ⟨p,hp⟩:=fy.1
  obtain ⟨r,hr⟩:=fy.2.1
  apply Prod.ext
  · by_contra ne
    have hot:=only.1 y.1 (Finset.mem_product.mp hy).1 (Ne.symm ne)
    exact Bool.noConfusion ((Geometry.in_pts.mp hp).1.symm.trans hot)
  · by_contra ne
    have hot:=only.2.1 y.2 (Finset.mem_product.mp hy).2 (Ne.symm ne)
    exact Bool.noConfusion ((Geometry.in_pts.mp hr).1.symm.trans hot)

lemma merge_not_exempt (inter : ∀ i j,i≠j → (L i∩L j).card=1) (ab : a≠b)
    (ha : a∈L i0) (hb : b∈L i0) (good : okay gs) (top : earlier N gs)
    {t : Fin N} (ti : t≠i0) {k : Fin gs.length} (mg : merged L a b gs t k) : ¬ exempt L i0 a b gs k := by
  obtain ⟨_,_,_,_,op,_⟩:=merge_gate good top (mark_off inter ab ha hb ti) mg
  obtain ⟨p,hp⟩:=merged_nonempty mg
  rintro (a|⟨_,h⟩)
  · exact (show GateOp.and≠GateOp.or by intro h;cases h) (a.1.symm.trans op)
  · exact Bool.noConfusion ((Geometry.in_pts.mp hp).1.symm.trans (h t ti))

end PEqualNP.Outside.L_meta_1643.Wires

namespace PEqualNP.Outside.L_meta_1643.Account
open Finset
variable {W T I : Type*} [DecidableEq W] [DecidableEq T] [DecidableEq I]

omit [DecidableEq T] in
lemma transpose_sum (U : Finset W) (O : Finset T) (M : T → Finset W)
    (sub : ∀ t∈O,M t⊆U) :
    (∑ k∈U,(O.filter fun t => k∈M t).card)=∑ t∈O,(M t).card := by
  classical
  calc
    _ = ∑ k∈U, ∑ t∈O, (if k∈M t then 1 else 0 : ℕ) := by simp
    _ = ∑ t∈O, ∑ k∈U, (if k∈M t then 1 else 0 : ℕ) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      simp [Finset.inter_eq_right.mpr (sub t ht)]

lemma tally (U : Finset W) (O : Finset T) (P : Finset I) (M : T → Finset W)
    (D H : I → Finset W) (E : Finset W) (q : ℕ)
    (em : E⊆U) (ms : ∀ t∈O,M t⊆U) (ds : ∀ p∈P,D p⊆U) (hs : ∀ p∈P,H p⊆U)
    (mcount : ∀ t∈O,(M t).card=q) (paid : ∀ p∈P,(D p).card≤(H p).card)
    (step : ∀ k∈U,(O.filter (fun t => k∈M t)).card+(P.filter (fun p => k∈H p)).card+
      (if k∈E then 1 else 0) ≤ 1+(P.filter (fun p=>k∈D p)).card) :
    O.card*q+E.card≤U.card := by
  classical
  have bound:=Finset.sum_le_sum step
  simp only [Finset.sum_add_distrib] at bound
  rw [transpose_sum U O M ms,transpose_sum U P H hs,transpose_sum U P D ds] at bound
  have cost := Finset.sum_le_sum paid
  rw [Finset.sum_congr rfl mcount] at bound
  simp [Finset.inter_eq_right.mpr em] at bound
  omega

end PEqualNP.Outside.L_meta_1643.Account

namespace PEqualNP.Outside.L_meta_1643.Wires
open Finset PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1643
variable {N : ℕ} {L : Fin N → Finset (Fin N)} {a b i0 : Fin N} {gs : List Gate}

open Classical in
-- A gate that creates a new pair can be assigned to only one pair of lines.
lemma step_count (inter : ∀ i j,i≠j → (L i∩L j).card=1) (ab : a≠b)
    (ha : a∈L i0) (hb : b∈L i0) (good : okay gs) (top : earlier N gs) (g : Fin gs.length) :
    ((ordinary i0).filter (fun t=>merged L a b gs t g)).card+
    ((gridPairs L i0 a b).filter (fun p=>born L a b gs p.1 p.2 g)).card+
    (if exempt L i0 a b gs g then 1 else 0) ≤
    1+((gridPairs L i0 a b).filter (fun p=>merged L a b gs p.1 g ∧ merged L a b gs p.2 g)).card := by
  classical
  let B := (ordinary i0).filter (fun t=>merged L a b gs t g)
  let F := (gridPairs L i0 a b).filter (fun p=>born L a b gs p.1 p.2 g)
  let Z := (gridPairs L i0 a b).filter (fun p=>merged L a b gs p.1 g ∧ merged L a b gs p.2 g)
  change B.card+F.card+_≤1+Z.card
  have getB {t} (h : t∈B) : t≠i0 ∧ merged L a b gs t g := by
    obtain ⟨h₁,h₂⟩:=Finset.mem_filter.mp h
    exact ⟨(Finset.mem_erase.mp h₁).1,h₂⟩
  have one : F.card≤1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨px,fx⟩:=Finset.mem_filter.mp hx
    obtain ⟨py,fy⟩:=Finset.mem_filter.mp hy
    exact birth_unique inter ab ha hb good px py fx fy
  by_cases active : F.Nonempty
  · obtain ⟨p,hp⟩:=active
    obtain ⟨pair,fb⟩:=Finset.mem_filter.mp hp
    have ne:=birth_not_exempt inter ab ha hb good top pair fb
    have em : B=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨ti,mg⟩:=getB ht
      exact birth_not_merged inter ab ha hb good top pair fb ti mg
    simp only [em,Finset.card_empty,Nat.zero_add,ite_eq_right ne,Nat.add_zero]
    omega
  have fe : F=∅ := Finset.not_nonempty_iff_eq_empty.mp active
  rw [fe,Finset.card_empty,Nat.add_zero]
  by_cases ex : exempt L i0 a b gs g
  · have em : B=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨ti,mg⟩:=getB ht
      exact merge_not_exempt inter ab ha hb good top ti mg ex
    simp [em,ex]
  rw [ite_eq_right ex,Nat.add_zero]
  by_cases few : B.card≤1
  · omega
  obtain ⟨t,ht,u,hu,tu⟩:=Finset.one_lt_card.mp (Nat.lt_of_not_ge few)
  obtain ⟨ti,gt⟩:=getB ht
  obtain ⟨ui,gu⟩:=getB hu
  have orient:=Geometry.multi_pair inter (eval_mono good (N+g.val)) ab ha hb ti ui tu (merged_many gt) (merged_many gu)
  have nz : Z.Nonempty := by
    rcases orient with ⟨at',bu⟩|⟨au,bt⟩
    · exact ⟨(t,u),Finset.mem_filter.mpr ⟨by simp [gridPairs,lefts,rights,ordinary,ti,ui,at',bu],gt,gu⟩⟩
    · exact ⟨(u,t),Finset.mem_filter.mpr ⟨by simp [gridPairs,lefts,rights,ordinary,ti,ui,au,bt],gu,gt⟩⟩
  obtain ⟨p,hp⟩:=nz
  obtain ⟨pair,gl,gm⟩:=Finset.mem_filter.mp hp
  have only:=only_lines inter ab ha hb good pair (merged_nonempty gl) (merged_nonempty gm)
  have sub : B⊆{p.1,p.2} := by
    intro s hs
    obtain ⟨si,mg⟩:=getB hs
    simpa only [Finset.mem_insert,Finset.mem_singleton] using only.2.2 s si (merged_many mg)
  have two : B.card≤2 := (Finset.card_le_card sub).trans (by
    by_cases h : p.1=p.2 <;> simp [h])
  have pos:=Finset.card_pos.mpr (show Z.Nonempty from ⟨p,hp⟩)
  omega

end PEqualNP.Outside.L_meta_1643.Wires

namespace PEqualNP.Outside.L_meta_1643.Wires
open Finset PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1643

-- Sum over ordinary lines, cancel double charges, and add the distinguished line.
lemma lower {N q : ℕ} (L : Fin N → Finset (Fin N)) (i0 a b : Fin N) (ab : a≠b)
    (ha : a∈L i0) (hb : b∈L i0) (hq : 3≤q) (card : ∀ t,(L t).card=q+1)
    (inter : ∀ i j,i≠j → (L i∩L j).card=1)
    (gs : List Gate) (out : Fin N → ℕ) (good : okay gs) (top : earlier N gs)
    (correct : ∀ t x,domain (L i0) a b x → Circuit.eval ⟨gs,out t⟩ (List.ofFn x)=decide (∃ v∈L t,x v=true)) :
    N*q≤gs.length := by
  classical
  let O:=ordinary i0
  let P:=gridPairs L i0 a b
  let U:=Finset.range gs.length
  let M (t : Fin N):=U.filter (merged L a b gs t)
  let D (p : Fin N × Fin N):=M p.1 ∩ M p.2
  let H (p : Fin N × Fin N):=U.filter (born L a b gs p.1 p.2)
  let E:=(reserve L i0 a b gs).image (fun i : Fin gs.length=>i.val)
  have em : E⊆U := by
    intro k hk
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hk
    exact Finset.mem_range.mpr i.isLt
  have ms (t : Fin N) : M t⊆U := Finset.filter_subset ..
  have ds (p : Fin N × Fin N) : D p⊆U := Finset.inter_subset_left.trans (ms p.1)
  have hs (p : Fin N × Fin N) : H p⊆U := Finset.filter_subset ..
  have paid (p) (hp : p∈P) : (D p).card≤(H p).card := by
    obtain ⟨li,al,mi,bm⟩:=pair_bounds hp
    have ne : p.1≠p.2 := fun h=>Geometry.both_marker inter li ab ha hb al (h ▸ bm)
    have one : (seed L p.1 p.2).card≤1 := Finset.card_image_le.trans (inter _ _ ne).le
    have bound:=Partition.pair_total a (seed L p.1 p.2) (seq L a b gs p.1) (seq L a b gs p.2) gs.length one (D p) (H p) (by
      intro k hk hd
      obtain ⟨lh,rh⟩:=Finset.mem_inter.mp hd
      exact double_collision good top (mark_off inter ab ha hb li) (mark_off inter ab ha hb mi)
        (k:=⟨k,hk⟩) (Finset.mem_filter.mp lh).2 (Finset.mem_filter.mp rh).2) (by
      intro k hk birth
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,birth⟩)
    change (U∩D p).card≤(U∩H p).card at bound
    rwa [Finset.inter_eq_right.mpr (ds p),Finset.inter_eq_right.mpr (hs p)] at bound
  have step (k) (hk : k∈U) :
      (O.filter (fun t=>k∈M t)).card+(P.filter (fun p=>k∈H p)).card+(if k∈E then 1 else 0) ≤
      1+(P.filter (fun p=>k∈D p)).card := by
    let g : Fin gs.length:=⟨k,Finset.mem_range.mp hk⟩
    have eq : k∈E ↔ exempt L i0 a b gs g := by
      constructor
      · intro h
        obtain ⟨i,hi,hv⟩:=Finset.mem_image.mp h
        have ig : i=g:=Fin.ext hv
        exact in_reserve.mp (ig ▸ hi)
      · intro h
        exact Finset.mem_image.mpr ⟨g,in_reserve.mpr h,rfl⟩
    simpa only [M,D,H,Finset.mem_inter,Finset.mem_filter,hk,true_and,eq] using
      (step_count inter ab ha hb good top g)
  have tot:=Account.tally U O P M D H E q em (fun t _=>ms t) (fun p _=>ds p) (fun p _=>hs p)
    (fun t ht=>line_mass inter ab ha hb card good top correct (Finset.mem_erase.mp ht).1) paid step
  have ec : E.card=(reserve L i0 a b gs).card:=Finset.card_image_of_injective _ Fin.val_injective
  have res:=reserve_budget L i0 a b ab ha hb hq card inter gs out good top correct
  have oc : O.card+1=N := by
    simpa [O,ordinary] using Finset.card_erase_add_one (s:=Finset.univ) (Finset.mem_univ i0)
  calc
    N*q=(O.card+1)*q := by rw [oc]
    _=O.card*q+q := by simp [Nat.add_mul]
    _≤O.card*q+E.card := Nat.add_le_add_left (ec.symm ▸ res) _
    _≤gs.length := by simpa [U] using tot
end PEqualNP.Outside.L_meta_1643.Wires

theorem PEqualNP.Outside.L_meta_1643 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
      N * q ≤ gates.length) ∧
    ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) ∧
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) ∧
      (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) ∧
      gates.length = N * q := by
  intro q N L i0 a b hq _ card inter _ ab ha hb
  exact ⟨fun gs out good top correct =>
    PEqualNP.Outside.L_meta_1643.Wires.lower L i0 a b ab ha hb hq card inter gs out good top correct,
    PEqualNP.Outside.L_meta_1643.upper L card⟩

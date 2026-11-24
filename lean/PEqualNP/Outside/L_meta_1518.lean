import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1518

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

abbrev Valid (C : Circuit) :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

abbrev Cold {n : ℕ} (C : Circuit) (mark : ℕ) (x : Fin n → Bool) :=
  value C x mark = false

lemma parents {n : ℕ} (C : Circuit) (valid : Valid C) (j : Fin C.size)
    (unique : ∀ i : Fin C.size, (C.gates.get i).op = GateOp.not → i = j)
    (w : ℕ) (hn : n ≤ w) (hw : w < n+C.size) :
    let i : Fin C.size := ⟨w-n,by omega⟩
    ∃ P : Finset ℕ, P.card ≤ 2 ∧
      (n+j.val ∈ (C.gates.get i).inputs → P.card ≤ 1) ∧ (∀ r ∈ P, r<w) ∧
      ∀ x y : Fin n → Bool, Cold C (n+j.val) x → Cold C (n+j.val) y →
        (∀ r ∈ P, value C x r=true → value C y r=true) →
        value C x w=true → value C y w=true := by
  let i : Fin C.size := ⟨w-n,by omega⟩
  let g := C.gates.get i
  obtain ⟨hop,hlen⟩ := valid g (List.get_mem ..)
  let mark := n+j.val
  let P := (g.inputs.toFinset.erase mark).filter (· < w)
  have bound := (Finset.card_filter_le (g.inputs.toFinset.erase mark) (· < w))
  have max := List.toFinset_card_le g.inputs |>.trans hlen
  refine ⟨P,bound.trans ((Finset.card_le_card (Finset.erase_subset ..)).trans max),?_,?_,?_⟩
  · intro read
    have h : mark ∈ g.inputs.toFinset := List.mem_toFinset.mpr read
    have e := Finset.card_erase_add_one h
    change P.card ≤ 1
    change P.card ≤ _ at bound
    omega
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y cx cy step hx
    rcases hop with hop|hop|hop
    all_goals try
      have same : w = n+j.val := by
        have e := congrArg Fin.val (unique i hop)
        change w-n=j.val at e
        omega
      rw [same] at hx
      exact (Bool.false_ne_true (cx.symm.trans hx)).elim
    all_goals
      have hr (r : ℕ) (hin : r ∈ g.inputs) :
          (if r < w then value C x r else false)=true →
          (if r < w then value C y r else false)=true := by
        by_cases lt : r < w
        · by_cases eq : r = mark
          · subst r; simp [lt,mark,cx]
          · simpa only [ite_eq_left lt] using step r
              (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨eq,List.mem_toFinset.mpr hin⟩,lt⟩)
        · simp [lt]
      have gx := gate_value C x w hn hw
      have gy := gate_value C y w hn hw
      change value C x w = g.op.eval _ at gx
      change value C y w = g.op.eval _ at gy
      rw [gx] at hx
      rw [gy]
    · simp only [hop,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at hx ⊢
      exact fun z hz => hr z hz (hx z hz)
    · simp only [hop,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at hx ⊢
      obtain ⟨z,hz,yes⟩ := hx
      exact ⟨z,hz,hr z hz yes⟩

lemma mono {n : ℕ} (C : Circuit) (valid : Valid C) (j : Fin C.size)
    (unique : ∀ i : Fin C.size, (C.gates.get i).op = GateOp.not → i=j)
    (x y : Fin n → Bool) (cx : Cold C (n+j.val) x) (cy : Cold C (n+j.val) y)
    (le : ∀ p, x p=true → y p=true) (w : ℕ) : value C x w=true → value C y w=true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases small : w<n
    · let p : Fin n := ⟨w,small⟩
      change value C x p=true → value C y p=true
      simpa only [input_value] using le p
    by_cases end' : w<n+C.size
    · obtain ⟨P,_,_,lt,step⟩ := parents C valid j unique w (by omega) end'
      exact step x y cx cy fun r hr => ih r (lt r hr)
    · simp [missing_value C x w (by omega)]

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
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ p ∈ T, ∀ k, ∀ hk : k < C.gates.length, C.gates[k].op = GateOp.not → value C (l p) (n + k) = false)
    (k : ℕ) (hk : k < C.gates.length) (hm : Multi C T l y (n + k)) :
    (∃ r ∈ C.gates[k].inputs, r < n + k ∧ ∀ p ∈ T, Sv C l y p (n + k) → Sv C l y p r) ∨
    (C.gates[k].op = GateOp.or ∧ C.gates[k].inputs.length = 2 ∧
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) ∧
      ∀ p ∈ T, Sv C l y p (n + k) → ∃ r ∈ C.gates[k].inputs, r < n + k ∧ Sv C l y p r) := by
  obtain ⟨p0, hp0, _, _, _, hs0, _⟩ := hm
  rcases (hC _ (List.getElem_mem hk)).1 with hop | hop | hop
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
  · exfalso
    have hf := hnot p0 hp0 k hk hop
    rw [hs0.1] at hf
    exact Bool.noConfusion hf

lemma frontier {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ p ∈ T, ∀ k, ∀ hk : k < C.gates.length, C.gates[k].op = GateOp.not → value C (l p) (n + k) = false)
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
      rcases step_cases C T l y hC hnot (t - n) hk hm with ⟨r, hr, hlt, hall⟩ | ⟨hop, hlen2, hQ, hsv⟩
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

lemma family {n : ℕ} {ι : Type*} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (T : Finset ι) (l : ι → Fin n → Bool) (y : Fin n → Bool) (o : ℕ)
    (hnot : ∀ p ∈ T, ∀ k, ∀ hk : k < C.gates.length, C.gates[k].op = GateOp.not → value C (l p) (n + k) = false)
    (ho : ∀ p ∈ T, Sv C l y p o)
    (hin : ∀ w, w < n → ¬ Multi C T l y w)
    (K : Finset (Fin C.gates.length))
    (hK : ∀ g : Fin C.gates.length, Multi C T l y (n + (g : ℕ)) →
      C.gates[(g : ℕ)].op = GateOp.or → C.gates[(g : ℕ)].inputs.length = 2 →
      (∀ r ∈ C.gates[(g : ℕ)].inputs, ∃ p ∈ T, value C (l p) r = true) → g ∈ K) :
    T.card ≤ K.card + 1 := by
  classical
  let W : Finset ℕ := Finset.image (fun g : Fin C.gates.length => n + (g : ℕ)) K
  have hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length := by
    intro w hc
    refine ⟨Nat.le_of_not_lt fun h => hin w h hc, ?_⟩
    by_contra hge
    obtain ⟨p, _, _, _, _, hsv, _⟩ := hc
    have hm := missing_value C (l p) w (by unfold Circuit.size; omega)
    have h1 := hsv.1
    rw [hm] at h1
    exact Bool.noConfusion h1
  have h := frontier C T l y hC hnot W
    (fun k hk hm hop hl hQ => Finset.mem_image.mpr ⟨(⟨k, hk⟩ : Fin C.gates.length), hK ⟨k, hk⟩ hm hop hl hQ, rfl⟩)
    hlen (n + C.gates.length) {o}
    (fun w _ hc => (hlen w hc).2) T (Finset.Subset.refl T)
    (fun p hp => ⟨o, Finset.mem_singleton_self o, ho p hp⟩)
  have h1 := Finset.card_filter_le W (· < n + C.gates.length)
  have h2 : W.card ≤ K.card := Finset.card_image_le
  rw [Finset.card_singleton] at h
  omega

theorem paid_card {n : ℕ} (gates : List Gate) (j h : Fin gates.length) (earlier : h < j)
    (paid : Finset (Fin gates.length)) (hj : j ∉ paid) (hh : h ∉ paid)
    (noReader : ∀ i ∈ paid, j < i → n+j.val ∉ (gates.get i).inputs) :
    paid.card + (Finset.univ.filter (fun i : Fin gates.length =>
      j < i ∧ n+j.val ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  classical
  let rs := Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n+j.val∈(gates.get i).inputs)
  have dis : Disjoint paid rs := Finset.disjoint_left.mpr fun i hi hr =>
    noReader i hi (Finset.mem_filter.mp hr).2.1 (Finset.mem_filter.mp hr).2.2
  have outJ : j ∉ paid∪rs := by
    simp [rs,hj]
  have outH : h ∉ insert j (paid∪rs) := by
    simp [rs,hh,earlier.ne,not_lt_of_gt earlier]
  have cap := Finset.card_le_univ (insert h (insert j (paid∪rs)))
  rw [Finset.card_insert_of_notMem outH,Finset.card_insert_of_notMem outJ,
    Finset.card_union_of_disjoint dis,Fintype.card_fin] at cap
  change paid.card+rs.card+2 ≤ gates.length
  omega

lemma not_value {n : ℕ} (C : Circuit) (j h : ℕ) (hj : j < C.gates.length)
    (op : C.gates[j].op = GateOp.not) (hlt : h < j)
    (hin : ∃ r : List ℕ, C.gates[j].inputs = (n + h) :: r)
    (x : Fin n → Bool) (hx : value C x (n + h) = true) :
    value C x (n + j) = false := by
  obtain ⟨r, hr⟩ := hin
  have hw : n + j < n + C.size := by unfold Circuit.size; omega
  have hg := gate_value C x (n + j) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hg
  rw [hg, op, hr]
  have hlt' : n + h < n + j := by omega
  simp [GateOp.eval, hlt', hx]

lemma walk {n : ℕ} {ι : Type*} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (j : ℕ)
    (unique : ∀ k, ∀ hk : k < C.gates.length, C.gates[k].op = GateOp.not → k = j)
    (z : ι → Fin n → Bool) (f : ι → Bool)
    (cold : ∀ s, value C (z s) (n + j) = false)
    (s1 : ι) (hs1 : f s1 = true)
    (hvar : ∀ v : Fin n, ∃ s, z s v ≠ f s)
    (w : ℕ) (hw : ∀ s, value C (z s) w = f s) :
    ∃ k, ∃ hk : k < C.gates.length, ¬ (j < k ∧ n + j ∈ C.gates[k].inputs) ∧ k ≠ j ∧
      ∀ s, value C (z s) (n + k) = f s := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · exfalso
      obtain ⟨s, hs⟩ := hvar ⟨w, hn⟩
      apply hs
      rw [← hw s]
      exact (input_value C (z s) ⟨w, hn⟩).symm
    by_cases hlen : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      have h1 : value C (z s1) w = true := by rw [hw s1, hs1]
      by_cases hread : j < w - n ∧ n + j ∈ C.gates[w - n].inputs
      · rcases (hC _ (List.getElem_mem hk)).1 with hop | hop | hop
        · exfalso
          have e := and_value C (w - n) hk hop (z s1)
          rw [← hwk] at e
          have h2 := (e.mp h1 (n + j) hread.2).2
          rw [cold s1] at h2
          exact Bool.noConfusion h2
        · obtain ⟨u, hu1, hu2⟩ : ∃ u, (∀ r ∈ C.gates[w - n].inputs, r = n + j ∨ r = u) ∧
              (u = n + j ∨ u ∈ C.gates[w - n].inputs) := by
            have hl := (hC _ (List.getElem_mem hk)).2
            have hm := hread.2
            generalize C.gates[w - n].inputs = L at hl hm
            rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
            · simp at hm
            · refine ⟨n + j, fun r hr => ?_, Or.inl rfl⟩
              have hra : r = a := by simpa using hr
              have haj : n + j = a := by simpa using hm
              left
              omega
            · rcases List.mem_pair.mp hm with h | h
              · refine ⟨b, fun r hr => ?_, Or.inr (by simp)⟩
                rcases List.mem_pair.mp hr with e | e
                · left; omega
                · right; exact e
              · refine ⟨a, fun r hr => ?_, Or.inr (by simp)⟩
                rcases List.mem_pair.mp hr with e | e
                · right; exact e
                · left; omega
            · simp at hl
          have key : ∀ s, value C (z s) w = true ↔ (u < w ∧ value C (z s) u = true) := by
            intro s
            have e := or_value C (w - n) hk hop (z s)
            rw [← hwk] at e
            rw [e]
            constructor
            · rintro ⟨r, hr, hlt, hv⟩
              rcases hu1 r hr with e1 | e1
              · rw [e1, cold s] at hv
                exact Bool.noConfusion hv
              · rw [e1] at hlt hv
                exact ⟨hlt, hv⟩
            · rintro ⟨hlt, hv⟩
              rcases hu2 with e1 | hu
              · rw [e1, cold s] at hv
                exact Bool.noConfusion hv
              · exact ⟨u, hu, hlt, hv⟩
          have huw : u < w := ((key s1).mp h1).1
          apply ih u huw
          intro s
          rw [← hw s, Bool.eq_iff_iff, key s]
          exact ⟨fun hh => ⟨huw, hh⟩, fun hh => hh.2⟩
        · exfalso
          have := unique (w - n) hk hop
          omega
      · refine ⟨w - n, hk, hread, ?_, ?_⟩
        · intro e
          have h2 : value C (z s1) (n + (w - n)) = true := by rw [← hwk]; exact h1
          rw [e, cold s1] at h2
          exact Bool.noConfusion h2
        · intro s
          rw [← hwk]
          exact hw s
    · exfalso
      have hmiss := missing_value C (z s1) w (by unfold Circuit.size; omega)
      rw [hw s1, hs1] at hmiss
      exact Bool.noConfusion hmiss

def tst {n m : ℕ} (B : Fin m → Fin n → Finset (Fin n)) (t : Fin m) (p : Fin n) : Fin n → Bool :=
  fun v => decide (v = p ∨ v ∈ B t p)

def coY {n m : ℕ} (L : Fin m → Finset (Fin n)) (t : Fin m) : Fin n → Bool :=
  fun v => decide (v ∉ L t)

def InK {n m : ℕ} (C : Circuit) (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (t : Fin m) (g : Fin C.gates.length) : Prop :=
  Multi C (L t) (tst B t) (coY L t) (n + (g : ℕ)) ∧ C.gates[(g : ℕ)].op = GateOp.or ∧
    ∀ r ∈ C.gates[(g : ℕ)].inputs, ∃ p ∈ L t, value C (tst B t p) r = true

theorem core {n m : ℕ} (L : Fin m → Finset (Fin n))
    (card4 : ∀ t, (L t).card = 4)
    (thin : ∀ t t', t ≠ t' → (L t ∩ L t').card ≤ 1)
    (hsub : ∀ t s, s ≠ t → ∃ v ∈ L t, v ∉ L s)
    (hpt : ∀ t v, v ∈ L t → ∃ s, s ≠ t ∧ v ∈ L s)
    (hne : ∀ t : Fin m, ∃ s, s ≠ t)
    (C : Circuit) (o : Fin m → ℕ) (j h : Fin C.gates.length)
    (valid : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (op : (C.gates.get j).op = GateOp.not)
    (unique : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i = j)
    (hlt : h < j) (hin : ∃ r : List ℕ, (C.gates.get j).inputs = (n + (h : ℕ)) :: r)
    (computes : ∀ (t : Fin m) (x : Fin n → Bool), value C x (o t) = decide (∃ v ∈ L t, x v = true))
    (hco : ∀ t : Fin m, value C (fun v : Fin n => decide (v ∉ L t)) (n + (h : ℕ)) = true)
    (Lam : Finset (Fin m)) (B : Fin m → Fin n → Finset (Fin n))
    (hB : ∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧
      value C (fun v : Fin n => decide (v = p ∨ v ∈ B t p)) (n + (h : ℕ)) = true)
    (separated : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty)))
    (I : Finset (Fin C.gates.length))
    (hI : ∀ g ∈ I, (C.gates.get g).op = GateOp.and ∧ g < h) :
    (Finset.univ.filter (fun i : Fin C.gates.length => j < i ∧ n + (j : ℕ) ∈ (C.gates.get i).inputs)).card + 2 +
      3 * Lam.card + max (m - Lam.card) I.card ≤ C.gates.length := by
  classical
  have hjlen : j.val < C.gates.length := j.isLt
  have opj : C.gates[j.val].op = GateOp.not := op
  have hinj : ∃ r : List ℕ, C.gates[j.val].inputs = (n + h.val) :: r := hin
  have hlt' : h.val < j.val := Fin.lt_def.mp hlt
  have coldNo : ∀ t, value C (coY L t) (n + j.val) = false := fun t =>
    not_value C j.val h.val hjlen opj hlt' hinj (coY L t) (hco t)
  have coldL : ∀ t ∈ Lam, ∀ p ∈ L t, value C (tst B t p) (n + j.val) = false := fun t ht p hp =>
    not_value C j.val h.val hjlen opj hlt' hinj (tst B t p) (hB t ht p hp).2
  have uniq' : ∀ k, ∀ hk : k < C.gates.length, C.gates[k].op = GateOp.not → k = j.val :=
    fun k hk hop => congrArg Fin.val (unique ⟨k, hk⟩ hop)
  let K : Fin m → Finset (Fin C.gates.length) := fun t => Finset.univ.filter (InK C L B t)
  have hKmem : ∀ t g, g ∈ K t → InK C L B t g := fun t g hg => (Finset.mem_filter.mp hg).2
  have hK3 : ∀ t ∈ Lam, 3 ≤ (K t).card := by
    intro t ht
    have hfam := family (n := n) C valid (L t) (tst B t) (coY L t) (o t)
      (fun p hp k hk hop => by
        have e := uniq' k hk hop
        rw [e]
        exact coldL t ht p hp)
      (fun p hp => ⟨(computes t (tst B t p)).trans
          (decide_eq_true ⟨p, hp, decide_eq_true (Or.inl rfl)⟩),
        (computes t (coY L t)).trans (decide_eq_false (by
          rintro ⟨v, hv, hy⟩
          exact (of_decide_eq_true hy) hv))⟩)
      (fun w hw hc => by
        obtain ⟨p, hp, p', hp', hpp, hs1, hs2⟩ := hc
        have e : ∀ a ∈ L t, Sv C (tst B t) (coY L t) a w → (⟨w, hw⟩ : Fin n) = a := by
          intro a ha hsa
          have h1 : value C (tst B t a) ((⟨w, hw⟩ : Fin n) : ℕ) = true := hsa.1
          have h2 : value C (coY L t) ((⟨w, hw⟩ : Fin n) : ℕ) = false := hsa.2
          rw [input_value] at h1 h2
          simp only [tst, coY, decide_eq_true_eq, decide_eq_false_iff_not, not_not] at h1 h2
          rcases h1 with h1 | h1
          · exact h1
          · exfalso
            have h3 : (⟨w, hw⟩ : Fin n) ∈ B t a ∩ L t := Finset.mem_inter.mpr ⟨h1, h2⟩
            rw [(hB t ht a ha).1] at h3
            simp at h3
        exact hpp ((e p hp hs1).symm.trans (e p' hp' hs2)))
      (K t)
      (fun g hm hop _ hQ => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hm, hop, hQ⟩)
    have := card4 t
    omega
  have kill : ∀ t ∈ Lam, ∀ t', t ≠ t' → (¬ ∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) →
      ∀ w, Multi C (L t) (tst B t) (coY L t) w → value C (coY L t') w = false → False := by
    intro t ht t' hne' hnA w hi hj
    obtain ⟨p, hp, p', hp', hpp, hs, hs'⟩ := hi
    have key : ∀ a ∈ L t, a ∉ L t' → value C (tst B t a) w = true → False := by
      intro a ha haj hv
      have hle : ∀ v, tst B t a v = true → coY L t' v = true := by
        intro v hv'
        simp only [tst, coY, decide_eq_true_eq] at hv' ⊢
        intro hvj
        rcases hv' with hv' | hv'
        · rw [hv'] at hvj
          exact haj hvj
        · exact hnA ⟨a, Finset.mem_sdiff.mpr ⟨ha, haj⟩, ⟨v, Finset.mem_inter.mpr ⟨hv', hvj⟩⟩⟩
      have hm := mono C valid j unique (tst B t a) (coY L t') (coldL t ht a ha) (coldNo t') hle w hv
      rw [hj] at hm
      exact Bool.noConfusion hm
    by_cases hpj : p ∈ L t'
    · by_cases hpj' : p' ∈ L t'
      · exact hpp (Finset.card_le_one.mp (thin t t' hne') p (Finset.mem_inter.mpr ⟨hp, hpj⟩) p'
          (Finset.mem_inter.mpr ⟨hp', hpj'⟩))
      · exact key p' hp' hpj' hs'.1
    · exact key p hp hpj hs.1
  have hKfalse : ∀ t g, g ∈ K t → value C (coY L t) (n + g.val) = false := by
    intro t g hg
    obtain ⟨p, _, _, _, _, hs, _⟩ := (hKmem t g hg).1
    exact hs.2
  have Kdisj : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → Disjoint (K t) (K t') := by
    intro t ht t' ht' hne'
    refine Finset.disjoint_left.mpr fun g hgt hgt' => ?_
    by_cases hA : ∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty
    · have hB' : ¬ ∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty :=
        fun hB' => separated t ht t' ht' hne' ⟨hA, hB'⟩
      exact kill t' ht' t hne'.symm hB' _ (hKmem t' g hgt').1 (hKfalse t g hgt)
    · exact kill t ht t' hne' hA _ (hKmem t g hgt).1 (hKfalse t' g hgt')
  have hUcard : 3 * Lam.card ≤ (Lam.biUnion K).card := by
    rw [Finset.card_biUnion Kdisj]
    have hsum := Finset.sum_le_sum (s := Lam) (f := fun _ => 3) (g := fun t => (K t).card)
      (fun t ht => hK3 t ht)
    rw [Finset.sum_const, smul_eq_mul] at hsum
    omega
  have hU : ∀ g ∈ Lam.biUnion K, ∃ t ∈ Lam, C.gates[g.val].op = GateOp.or ∧
      value C (coY L t) (n + g.val) = false ∧ ¬ (j < g ∧ n + j.val ∈ C.gates[g.val].inputs) := by
    intro g hg
    obtain ⟨t, ht, hgt⟩ := Finset.mem_biUnion.mp hg
    refine ⟨t, ht, (hKmem t g hgt).2.1, hKfalse t g hgt, ?_⟩
    rintro ⟨_, hmem⟩
    obtain ⟨p, hp, hv⟩ := (hKmem t g hgt).2.2 _ hmem
    rw [coldL t ht p hp] at hv
    exact Bool.noConfusion hv
  have jU : j ∉ Lam.biUnion K := by
    intro hj
    obtain ⟨t, _, hop, _, _⟩ := hU j hj
    rw [opj] at hop
    exact GateOp.noConfusion hop
  have hU' : h ∉ Lam.biUnion K := by
    intro hh
    obtain ⟨t, _, _, hf, _⟩ := hU h hh
    have ht : value C (coY L t) (n + h.val) = true := hco t
    rw [hf] at ht
    exact Bool.noConfusion ht
  have walk1 : ∀ t : Fin m, ∃ k, ∃ hk : k < C.gates.length,
      ¬ (j.val < k ∧ n + j.val ∈ C.gates[k].inputs) ∧ k ≠ j.val ∧
      ∀ s, value C (coY L s) (n + k) = decide (s ≠ t) := by
    intro t
    obtain ⟨s1, hs1⟩ := hne t
    refine walk C valid j.val uniq' (fun s => coY L s) (fun s => decide (s ≠ t)) coldNo s1
      (decide_eq_true hs1) ?_ (o t) ?_
    · intro v
      by_cases hv : v ∈ L t
      · obtain ⟨s, hs, hvs⟩ := hpt t v hv
        refine ⟨s, ?_⟩
        have e1 : coY L s v = false := decide_eq_false (fun hh => hh hvs)
        have e2 : decide (s ≠ t) = true := decide_eq_true hs
        rw [e1, e2]
        exact Bool.noConfusion
      · refine ⟨t, ?_⟩
        have e1 : coY L t v = true := decide_eq_true hv
        have e2 : decide (t ≠ t) = false := decide_eq_false (fun hh => hh rfl)
        rw [e1, e2]
        exact Bool.noConfusion
    · intro s
      by_cases hs : s = t
      · have e2 : decide (s ≠ t) = false := decide_eq_false (fun hh => hh hs)
        rw [e2, hs]
        exact (computes t (coY L t)).trans (decide_eq_false (by
          rintro ⟨v, hv, hy⟩
          exact (of_decide_eq_true hy) hv))
      · obtain ⟨v, hv, hvs⟩ := hsub t s hs
        exact ((computes t (coY L s)).trans (decide_eq_true ⟨v, hv, decide_eq_true hvs⟩)).trans
          (decide_eq_true hs).symm
  choose gk hgk hread hnej hval using walk1
  let gf : Fin m → Fin C.gates.length := fun t => ⟨gk t, hgk t⟩
  have gf_inj : Function.Injective gf := by
    intro t t' e
    by_contra hne'
    have e' : gk t = gk t' := congrArg Fin.val e
    have h1 := hval t t
    have h2 := hval t' t
    rw [e'] at h1
    rw [h1] at h2
    have e3 : decide (t ≠ t) = false := decide_eq_false (fun hh => hh rfl)
    have e4 : decide (t ≠ t') = true := decide_eq_true hne'
    rw [e3, e4] at h2
    exact Bool.noConfusion h2
  let G0 : Finset (Fin C.gates.length) := Lamᶜ.image gf
  have hG0card : G0.card = m - Lam.card := by
    change (Lamᶜ.image gf).card = m - Lam.card
    rw [Finset.card_image_of_injective _ gf_inj, Finset.card_compl, Fintype.card_fin]
  have hG0 : ∀ g ∈ G0, ∃ t, t ∉ Lam ∧ g.val = gk t := by
    intro g hg
    obtain ⟨t, ht, e⟩ := Finset.mem_image.mp hg
    exact ⟨t, Finset.mem_compl.mp ht, (congrArg Fin.val e).symm⟩
  have disj1 : Disjoint (Lam.biUnion K) G0 := by
    refine Finset.disjoint_left.mpr fun g hg hg0 => ?_
    obtain ⟨t, ht, _, hf, _⟩ := hU g hg
    obtain ⟨t', ht', e⟩ := hG0 g hg0
    have h2 := hval t' t
    rw [← e, hf] at h2
    have e4 : decide (t ≠ t') = true := decide_eq_true (fun hh => ht' (hh ▸ ht))
    rw [e4] at h2
    exact Bool.noConfusion h2
  have cap1 := paid_card (n := n) C.gates j h hlt (Lam.biUnion K ∪ G0)
    (by
      intro hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact jU hj
      · obtain ⟨t, _, e⟩ := hG0 j hj
        exact hnej t e.symm)
    (by
      intro hh
      rcases Finset.mem_union.mp hh with hh | hh
      · exact hU' hh
      · obtain ⟨t, _, e⟩ := hG0 h hh
        have h2 := hval t t
        rw [← e] at h2
        have ht : value C (coY L t) (n + h.val) = true := hco t
        rw [ht] at h2
        have e3 : decide (t ≠ t) = false := decide_eq_false (fun hh => hh rfl)
        rw [e3] at h2
        exact Bool.noConfusion h2)
    (by
      intro i hi hji hmem
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨t, _, _, _, hnr⟩ := hU i hi
        exact hnr ⟨hji, hmem⟩
      · obtain ⟨t, _, e⟩ := hG0 i hi
        have hr := hread t
        apply hr
        constructor
        · have : j.val < i.val := Fin.lt_def.mp hji
          omega
        · have hi' : i = ⟨gk t, hgk t⟩ := Fin.ext e
          rw [hi'] at hmem
          exact hmem)
  have disj2 : Disjoint (Lam.biUnion K) I := by
    refine Finset.disjoint_left.mpr fun g hg hgI => ?_
    obtain ⟨t, _, hop, _, _⟩ := hU g hg
    have hand : C.gates[g.val].op = GateOp.and := (hI g hgI).1
    rw [hand] at hop
    exact GateOp.noConfusion hop
  have cap2 := paid_card (n := n) C.gates j h hlt (Lam.biUnion K ∪ I)
    (by
      intro hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact jU hj
      · have := Fin.lt_def.mp (hI j hj).2
        omega)
    (by
      intro hh
      rcases Finset.mem_union.mp hh with hh | hh
      · exact hU' hh
      · have := Fin.lt_def.mp (hI h hh).2
        omega)
    (by
      intro i hi hji hmem
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨t, _, _, _, hnr⟩ := hU i hi
        exact hnr ⟨hji, hmem⟩
      · have h1 := Fin.lt_def.mp (hI i hi).2
        have h2 := Fin.lt_def.mp hji
        omega)
  rw [Finset.card_union_of_disjoint disj1, hG0card] at cap1
  rw [Finset.card_union_of_disjoint disj2] at cap2
  rcases le_total (m - Lam.card) I.card with hle | hle
  · rw [max_eq_right hle]
    omega
  · rw [max_eq_left hle]
    omega


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

theorem low_mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool)
    (hxy : ∀ v, x v = true → y v = true) (m : ℕ)
    (hm : ∀ k, ∀ hk : k < C.gates.length, k < m →
      (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or))
    (w : ℕ) (hwm : w < n + m) : value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hm (w - n) hk (by omega)) x y
        fun r _ hlt => ih r (by omega) (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

theorem inter_card : ∀ a b : Fin 13, a ≠ b →
    (({a, a + 1, a + 3, a + 9} : Finset (Fin 13)) ∩ {b, b + 1, b + 3, b + 9}).card ≤ 1 := by
  decide

theorem two (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (a b : Fin 13) (hab : a ≠ b) (x y : Fin 13) (hxy : x ≠ y)
    (hxa : x ∈ L a) (hya : y ∈ L a) (hxb : x ∈ L b) (hyb : y ∈ L b) : False := by
  have h1 : (L a ∩ L b).card ≤ 1 := by
    rw [hL a, hL b]
    exact inter_card a b hab
  have h2 : 1 < (L a ∩ L b).card :=
    Finset.one_lt_card.mpr ⟨x, Finset.mem_inter.mpr ⟨hxa, hxb⟩, y, Finset.mem_inter.mpr ⟨hya, hyb⟩, hxy⟩
  omega

theorem choice (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (s t u v : Fin 13) (hts : t ∈ L s) (hus : u ∈ L s) (hvs : v ∈ L s)
    (htu : t ≠ u) (huv : u ≠ v) (htv : t ≠ v) :
    ∃ c : Fin 13 → Fin 13,
      (∀ s' : Fin 13, s' ≠ s → c s' ∉ L s' ∧ (c s' = t ∨ c s' = u ∨ c s' = v)) ∧
      (∀ s' s'' : Fin 13, s' ≠ s → s'' ≠ s → ¬ (c s' ∈ L s'' ∧ c s'' ∈ L s')) := by
  refine ⟨fun s' => if t ∈ L s' then u else if u ∈ L s' then v else t, ?_, ?_⟩
  · intro s' hs'
    dsimp only
    split_ifs with h1 h2
    · exact ⟨fun hu => two L hL s' s hs' t u htu h1 hu hts hus, Or.inr (Or.inl rfl)⟩
    · exact ⟨fun hv => two L hL s' s hs' u v huv h2 hv hus hvs, Or.inr (Or.inr rfl)⟩
    · exact ⟨h1, Or.inl rfl⟩
  · intro s' s'' hs' hs'' hboth
    obtain ⟨h1, h2⟩ := hboth
    by_cases a1 : t ∈ L s'
    · simp only [a1, ↓reduceIte] at h1
      have b1 : t ∉ L s'' := fun hb => two L hL s'' s hs'' t u htu hb h1 hts hus
      simp only [b1, h1, ↓reduceIte] at h2
      exact two L hL s' s hs' t v htv a1 h2 hts hvs
    · by_cases a2 : u ∈ L s'
      · simp only [a1, a2, ↓reduceIte] at h1
        have b1 : t ∉ L s'' := fun hb => two L hL s'' s hs'' t v htv hb h1 hts hvs
        have b2 : u ∉ L s'' := fun hb => two L hL s'' s hs'' u v huv hb h1 hus hvs
        simp only [b1, b2, ↓reduceIte] at h2
        exact a1 h2
      · simp only [a1, a2, ↓reduceIte] at h1
        simp only [h1, ↓reduceIte] at h2
        exact a2 h2

theorem step10 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
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
  intro L hL gates o j h valid op unique hlt hin computes hco Lam B hB separated I hI
  have hLe : L = fun t : Fin 13 => {t, t + 1, t + 3, t + 9} := funext hL
  subst hLe
  refine core (n := 13) (m := 13)
    (fun t : Fin 13 => {t, t + 1, t + 3, t + 9}) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨gates, 0⟩ o j h valid op unique hlt hin computes hco Lam B hB separated I ?_
  intro g hg
  obtain ⟨hop, hT⟩ := hI g hg
  refine ⟨hop, ?_⟩
  have hmem := hT (Finset.univ.filter (fun i => i < h)) (fun i g' hi _ hlt' => by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hi with hi | hi
    · rw [hi] at hlt'
      exact hlt'
    · exact lt_trans hlt' (Finset.mem_filter.mp hi).2)
  exact (Finset.mem_filter.mp hmem).2

end PEqualNP.Outside.L_meta_1518

theorem PEqualNP.Outside.L_meta_1518 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ (s t u v : Fin 13), t ∈ L s → u ∈ L s → v ∈ L s → t ≠ u → u ≠ v → t ≠ v →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = t))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = u))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = v))) = true →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      38 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + max 1 I.card ≤ gates.length := by
  intro L hL gates o j h hg hj huniq hhj hin hout hco s t u v hts hus hvs htu huv htv ht hu hv I hI
  obtain ⟨c, hc1, hc2⟩ := PEqualNP.Outside.L_meta_1518.choice L hL s t u v hts hus hvs htu huv htv
  have hLam : (Finset.univ.erase s).card = 12 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ, Fintype.card_fin]
  have hmono : ∀ (a : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩
        (List.ofFn (fun y : Fin 13 => decide (y = a))) = true → x a = true →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn x) = true := by
    intro a x ha hxa
    refine PEqualNP.Outside.L_meta_1518.low_mono ⟨gates, 13 + (h : ℕ)⟩
      (fun y : Fin 13 => decide (y = a)) x ?_ ((h : ℕ) + 1) ?_ (13 + (h : ℕ)) (by omega) ha
    · intro w hw
      have hwa : w = a := by simpa using hw
      rw [hwa]
      exact hxa
    · intro k hk hkm
      have hk' : k < gates.length := hk
      have hgk := (hg (gates[k]'hk') (List.getElem_mem hk')).1
      rcases hgk with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exfalso
        have hkj : (⟨k, hk'⟩ : Fin gates.length) = j := huniq ⟨k, hk'⟩ h1
        have hkj' : k = (j : ℕ) := congrArg Fin.val hkj
        have hhj' : (h : ℕ) < (j : ℕ) := hhj
        omega
  have c1 : ∀ s' ∈ Finset.univ.erase s, ∀ p ∈ L s',
      ({c s'} : Finset (Fin 13)) ∩ L s' = ∅ ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩
        (List.ofFn (fun w : Fin 13 => decide (w = p ∨ w ∈ ({c s'} : Finset (Fin 13))))) = true := by
    intro s' hs' p _
    obtain ⟨hn, hcase⟩ := hc1 s' (Finset.mem_erase.mp hs').1
    refine ⟨Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_singleton_left.mpr hn), ?_⟩
    rcases hcase with e | e | e
    · exact hmono t _ ht (by simp [e])
    · exact hmono u _ hu (by simp [e])
    · exact hmono v _ hv (by simp [e])
  have c2 : ∀ s' ∈ Finset.univ.erase s, ∀ s'' ∈ Finset.univ.erase s, s' ≠ s'' →
      ¬ ((∃ p ∈ L s' \ L s'', (({c s'} : Finset (Fin 13)) ∩ L s'').Nonempty) ∧
        (∃ p ∈ L s'' \ L s', (({c s''} : Finset (Fin 13)) ∩ L s').Nonempty)) := by
    intro s' hs' s'' hs'' _ hboth
    obtain ⟨⟨p, _, x, hx⟩, ⟨q, _, y, hy⟩⟩ := hboth
    rw [Finset.mem_inter, Finset.mem_singleton] at hx hy
    exact hc2 s' s'' (Finset.mem_erase.mp hs').1 (Finset.mem_erase.mp hs'').1
      ⟨hx.1 ▸ hx.2, hy.1 ▸ hy.2⟩
  have key := PEqualNP.Outside.L_meta_1518.step10 L hL gates o j h hg hj huniq hhj hin hout hco
    (Finset.univ.erase s) (fun s' _ => {c s'}) c1 c2 I hI
  rw [hLam] at key
  change _ + 2 + 3 * 12 + max 1 I.card ≤ _ at key
  generalize max 1 I.card = M at key ⊢
  omega

import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1648

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

lemma hmono (N : ℕ) (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) (hw : w < N + (j : ℕ)) :
    value ⟨gates, 0⟩ x w = true → value ⟨gates, 0⟩ y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < N
    · let p : Fin N := ⟨w, hn⟩
      change value ⟨gates, 0⟩ x p = true → value ⟨gates, 0⟩ y p = true
      simpa only [input_value] using hxy p
    · have hk : w - N < gates.length := by
        have := j.isLt
        omega
      have hwk : w = N + (w - N) := by omega
      rw [hwk]
      have hop : gates[w - N].op = GateOp.and ∨ gates[w - N].op = GateOp.or := by
        rcases (hg _ (List.getElem_mem hk)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have h1 := hone ⟨w - N, hk⟩ h
          have h2 : w - N = (j : ℕ) := congrArg Fin.val h1
          omega
      exact gate_mono (n := N) ⟨gates, 0⟩ (w - N) hk hop x y fun r _ hlt => ih r (by omega) (by omega)

def Many {α : Type*} (R : α → ℕ → Prop) (w : ℕ) : Prop :=
  ∃ a b, a ≠ b ∧ R a w ∧ R b w

lemma count_front {α : Type*} (T : Finset α) (R : α → ℕ → Prop) (K : Finset ℕ)
    (step : ∀ w, Many R w → ∃ P : Finset ℕ,
      (∀ r ∈ P, r < w) ∧ P.card ≤ 1 + (if w ∈ K then 1 else 0) ∧
      ∀ p, R p w → ∃ r ∈ P, R p r)
    (t : ℕ) (F : Finset ℕ) (lim : ∀ w ∈ F, Many R w → w < t)
    (cover : ∀ p ∈ T, ∃ w ∈ F, R p w) :
    T.card ≤ F.card + (K.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    choose! f hf hR using cover
    have inj : Set.InjOn f T := by
      intro a ha b hb he
      by_contra hn
      have := lim (f a) (hf a ha) ⟨a,b,hn,hR a ha,he ▸ hR b hb⟩
      omega
    have := Finset.card_le_card_of_injOn f (fun a ha => hf a ha) inj
    omega
  | succ t ih =>
    have inc : (K.filter (· < t)).card ≤ (K.filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hw).1, Nat.lt_succ_of_lt (Finset.mem_filter.mp hw).2⟩
    by_cases use : t ∈ F ∧ Many R t
    · obtain ⟨P, hP, sz, cov⟩ := step t use.2
      let F' := F.erase t ∪ P
      have hlim : ∀ w ∈ F', Many R w → w < t := by
        intro w hw hm
        rcases Finset.mem_union.mp hw with hw | hw
        · obtain ⟨hne, mem⟩ := Finset.mem_erase.mp hw
          have := lim w mem hm
          omega
        · exact hP w hw
      have hc := ih F' hlim (by
        intro p hp
        obtain ⟨w, hw, hr⟩ := cover p hp
        by_cases he : w = t
        · subst w
          obtain ⟨r, hin, hr⟩ := cov p hr
          exact ⟨r, Finset.mem_union_right _ hin, hr⟩
        · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hw⟩), hr⟩)
      have he := Finset.card_erase_add_one use.1
      have hu : F'.card ≤ (F.erase t).card + P.card := Finset.card_union_le _ _
      by_cases ht : t ∈ K
      · have eq : K.filter (· < t + 1) = insert t (K.filter (· < t)) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hk, hl⟩
            by_cases h : w = t
            · exact Or.inl h
            · exact Or.inr ⟨hk, by omega⟩
          · rintro (rfl | ⟨hk, hl⟩)
            · exact ⟨ht, by omega⟩
            · exact ⟨hk, by omega⟩
        rw [eq, Finset.card_insert_of_notMem (by simp)]
        simp [ht] at sz
        omega
      · simp [ht] at sz
        omega
    · have hc := ih F (fun w hw hm => by
          have := lim w hw hm
          have hn : w ≠ t := fun he => use (he ▸ ⟨hw,hm⟩)
          omega) cover
      omega

def one {N : ℕ} (p v : Fin N) : Bool := decide (v = p)

def tier {N : ℕ} (M : Finset (Fin N)) (a b p : Fin N) : ℕ :=
  if p ∉ M then 0 else if p = a ∨ p = b then 2 else 1

def seen {N : ℕ} (C : Circuit) (S M : Finset (Fin N)) (a b p : Fin N) (w : ℕ) : Prop :=
  p ∈ S ∧ value C (one p) w = true ∧
  value C (fun v => decide (v ∉ M ∧ v ∉ S)) w = false ∧
  ∀ u, tier M a b u ≤ tier M a b p → value C (one u) w = true → u ∈ S

lemma many_disjoint {N : ℕ} (C : Circuit) (S T M : Finset (Fin N)) (a b : Fin N)
    (hST : (S ∩ T).card ≤ 1) (w : ℕ) :
    Many (seen C S M a b) w → ¬ Many (seen C T M a b) w := by
  have outsider (A B : Finset (Fin N)) (hAB : (A ∩ B).card ≤ 1)
      (hm : Many (seen C A M a b) w) : ∃ p, seen C A M a b p w ∧ p ∉ B := by
    obtain ⟨p,r,hn,hp,hr⟩ := hm
    by_cases h : p ∈ B
    · exact ⟨r,hr,fun hh => hn (Finset.card_le_one.mp hAB p
        (Finset.mem_inter.mpr ⟨hp.1,h⟩) r (Finset.mem_inter.mpr ⟨hr.1,hh⟩))⟩
    · exact ⟨p,hp,h⟩
  intro hs ht
  obtain ⟨p,hp,hn⟩ := outsider S T hST hs
  obtain ⟨r,hr,hm⟩ := outsider T S (by rwa [Finset.inter_comm]) ht
  rcases le_total (tier M a b p) (tier M a b r) with h | h
  · exact hn (hr.2.2.2 p h hp.2.1)
  · exact hm (hp.2.2.2 r h hr.2.1)

lemma input_seen {N : ℕ} (C : Circuit) (S M : Finset (Fin N)) (a b p : Fin N)
    (hp : p ∈ S) : seen C S M a b p p := by
  refine ⟨hp, by simp [input_value, one], by simp [input_value, hp], ?_⟩
  intro u _ hv
  have e : p = u := by simpa [input_value, one] using hv
  exact e ▸ hp

lemma pair_cover (l : List ℕ) (hl : l.length ≤ 2) (r z : ℕ)
    (hr : r ∈ l) (hz : z ∈ l) (hne : r ≠ z) : ∀ u ∈ l, u = r ∨ u = z := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · simp at hr
  · simp_all
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at *
    grind
  · simp at hl

def used {N : ℕ} (C : Circuit) (S M : Finset (Fin N)) (a b : Fin N) (j : ℕ)
    (g : Fin C.gates.length) : Prop :=
  Many (seen C S M a b) (N + g.val) ∧ g.val ≠ j ∧ N + j ∉ (C.gates.get g).inputs

lemma gate_step {N : ℕ} (C : Circuit) (S M : Finset (Fin N)) (a b : Fin N)
    (ha : a ∈ M) (hb : b ∈ M) (hgeom : S = M ∨ (S ∩ M).card ≤ 1)
    (j : ℕ) (k : Fin C.gates.length)
    (ops : (C.gates.get k).op = GateOp.and ∨ (C.gates.get k).op = GateOp.or ∨
      (C.gates.get k).op = GateOp.not)
    (hlen : (C.gates.get k).inputs.length ≤ 2)
    (wf : ∀ r ∈ (C.gates.get k).inputs, r < N + k.val)
    (hnot : (C.gates.get k).op = GateOp.not → k.val = j)
    (hz : value C (fun v => decide (v ∉ M ∧ v ∉ S)) (N + j) = true)
    (hzp : ∀ p, value C (one p) (N + j) = decide (p ≠ a ∧ p ≠ b))
    (hsafe : ∀ r u, value C (fun v => decide (v ∉ M ∧ v ∉ S)) r = false →
      u ∉ M → value C (one u) r = true → u ∈ S)
    (hm : Many (seen C S M a b) (N + k.val)) :
    ∃ P : Finset ℕ, (∀ r ∈ P, r < N + k.val) ∧
      P.card ≤ 1 + (if N + j ∈ (C.gates.get k).inputs then 0 else 1) ∧
      ∀ p, seen C S M a b p (N + k.val) → ∃ r ∈ P, seen C S M a b p r := by
  classical
  let y := fun v => decide (v ∉ M ∧ v ∉ S)
  obtain ⟨p', _, _, hp', _⟩ := hm
  have hy : value C y (N + k.val) = false := hp'.2.2.1
  have hkj : k.val ≠ j := by
    intro e
    rw [e] at hy
    exact Bool.false_ne_true (hy.symm.trans hz)
  rcases ops with hand | hor | hbad
  · have handv := and_value (n := N) C k.val k.isLt hand
    have hex : ∃ r ∈ (C.gates.get k).inputs, value C y r = false := by
      by_contra! hf
      have hon := (handv y).2 (fun r hr => ⟨wf r hr, by simpa using hf r hr⟩)
      exact Bool.false_ne_true (hy.symm.trans hon)
    obtain ⟨r,hr,hry⟩ := hex
    have wr := wf r hr
    have singletonCase (hc : ∀ p, seen C S M a b p (N + k.val) → seen C S M a b p r) :
        ∃ P : Finset ℕ, (∀ u ∈ P, u < N + k.val) ∧
        P.card ≤ 1 + (if N + j ∈ (C.gates.get k).inputs then 0 else 1) ∧
        ∀ p, seen C S M a b p (N + k.val) → ∃ u ∈ P, seen C S M a b p u := by
      exact ⟨{r}, by simpa, by simp, fun p hp => ⟨r,by simp,hc p hp⟩⟩
    by_cases readz : N + j ∈ (C.gates.get k).inputs
    · apply singletonCase
      have hrz : r ≠ N + j := fun e => Bool.false_ne_true ((e ▸ hry).symm.trans hz)
      have hc := pair_cover _ hlen r (N + j) hr readz hrz
      intro p hp
      have inds := (handv (one p)).1 hp.2.1
      have pz := (inds _ readz).2
      rw [hzp] at pz
      obtain ⟨hpa,hpb⟩ := of_decide_eq_true pz
      refine ⟨hp.1, (inds _ hr).2, hry, ?_⟩
      intro u hu huv
      have hsmall : tier M a b p ≤ 1 := by
        unfold tier
        split <;> simp_all
      have hbig : u ≠ a ∧ u ≠ b := by
        constructor
        · intro eq
          rw [eq] at hu
          rw [show tier M a b a = 2 by simp [tier,ha]] at hu
          omega
        · intro eq
          rw [eq] at hu
          rw [show tier M a b b = 2 by simp [tier,hb]] at hu
          omega
      apply hp.2.2.2 u hu
      apply (handv (one u)).2
      intro d hd
      refine ⟨wf d hd, ?_⟩
      rcases hc d hd with rfl | rfl
      · exact huv
      · rw [hzp]
        exact decide_eq_true hbig
    · have lift (p : Fin N) (hp : seen C S M a b p (N + k.val)) (off : p ∉ M ∨ S = M) :
          seen C S M a b p r := by
        refine ⟨hp.1, ((handv (one p)).1 hp.2.1 _ hr).2, hry, ?_⟩
        intro u hu hv
        by_cases huM : u ∈ M
        · rcases off with h | e
          · simp [tier,h,huM] at hu
            split at hu <;> omega
          · exact e ▸ huM
        · exact hsafe r u hry huM hv
      by_cases allSeen : ∀ p, seen C S M a b p (N + k.val) → seen C S M a b p r
      · exact singletonCase allSeen
      · push_neg at allSeen
        obtain ⟨c,hc,hcn⟩ := allSeen
        have cm : c ∈ M := by_contra fun hn => hcn (lift c hc (Or.inl hn))
        have hsize : (S ∩ M).card ≤ 1 :=
          hgeom.resolve_left (fun e => hcn (lift c hc (Or.inr e)))
        refine ⟨{r,(c : ℕ)}, ?_, ?_, ?_⟩
        · intro d hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl
          · exact wr
          · have := c.isLt
            omega
        · simp only [if_neg readz]
          have hcsize := Finset.card_insert_le r ({(c : ℕ)} : Finset ℕ)
          simpa using hcsize
        · intro p hp
          by_cases inM : p ∈ M
          · have e := Finset.card_le_one.mp hsize p (Finset.mem_inter.mpr ⟨hp.1,inM⟩)
              c (Finset.mem_inter.mpr ⟨hc.1,cm⟩)
            subst p
            exact ⟨c,by simp,input_seen C S M a b c hc.1⟩
          · exact ⟨r,by simp,lift p hp (Or.inl inM)⟩
  · have horv := or_value (n := N) C k.val k.isLt hor
    have neg (r : ℕ) (hr : r ∈ (C.gates.get k).inputs) : value C y r = false := by
      by_contra! h
      have hv := (horv y).2 ⟨r,hr,wf r hr,by simpa using h⟩
      exact Bool.false_ne_true (hy.symm.trans hv)
    have notread : N + j ∉ (C.gates.get k).inputs :=
      fun hin => Bool.false_ne_true ((neg _ hin).symm.trans hz)
    refine ⟨(C.gates.get k).inputs.toFinset, fun r hr => wf r (List.mem_toFinset.mp hr), ?_, ?_⟩
    · rw [if_neg notread]
      exact le_trans (List.toFinset_card_le _) hlen
    · intro p hp
      obtain ⟨r,hr,_,hv⟩ := (horv (one p)).1 hp.2.1
      exact ⟨r,List.mem_toFinset.mpr hr,hp.1,hv,neg r hr,fun u hu hv =>
        hp.2.2.2 u hu ((horv (one u)).2 ⟨r,hr,wf r hr,hv⟩)⟩
  · exact False.elim (hkj (hnot hbad))

lemma mono_at_fixed {N : ℕ} (C : Circuit) (j : ℕ)
    (ops : ∀ i : Fin C.gates.length, i.val ≠ j →
      (C.gates.get i).op = GateOp.and ∨ (C.gates.get i).op = GateOp.or)
    (x y : Fin N → Bool) (le : ∀ p, x p = true → y p = true)
    (fixed : value C x (N+j) = true → value C y (N+j) = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < N
    · let p : Fin N := ⟨w,hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using le p
    by_cases hw : w < N + C.gates.length
    · have hk : w-N < C.gates.length := by omega
      have e : w = N + (w-N) := by omega
      by_cases h : w-N = j
      · have e' : w = N+j := by omega
        rwa [e']
      rw [e]
      exact gate_mono C (w-N) hk (ops ⟨w-N,hk⟩ h) x y (fun r _ hr => ih r (by omega))
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

lemma not_value {N : ℕ} (C : Circuit) (j h : Fin C.gates.length)
    (op : (C.gates.get j).op = GateOp.not) (hj : h < j)
    (hin : ∃ r : List ℕ, (C.gates.get j).inputs = (N+h.val) :: r) (x : Fin N → Bool) :
    value C x (N+j.val) = !value C x (N+h.val) := by
  have g := gate_value C x (N+j.val) (by omega) (by unfold Circuit.size; have := j.isLt; omega)
  simp only [Nat.add_sub_cancel_left] at g
  obtain ⟨r,hr⟩ := hin
  change C.gates[j.val].inputs = _ at hr
  change C.gates[j.val].op = _ at op
  have hj' : h.val < j.val := hj
  have lt : N+h.val < N+j.val := by omega
  simpa [op,hr,GateOp.eval,lt] using g


lemma union_count {N m q : ℕ} (K : Fin m → Finset (Fin N)) (hq : ∀ i, q ≤ (K i).card)
    (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)) : m * q ≤ (Finset.univ.biUnion K).card := by
  rw [Finset.card_biUnion (fun i _ j _ hij => hd i j hij)]
  have h2 : ∑ _i : Fin m, q ≤ ∑ i : Fin m, (K i).card := Finset.sum_le_sum fun i _ => hq i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  exact h2

end PEqualNP.Outside.L_meta_1648

open PEqualNP.Outside.L_meta_1648

theorem PEqualNP.Outside.L_meta_1648 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p0))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p1))) = true →
    (∀ p : Fin N, p ≠ p0 → p ≠ p1 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p))) = false) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length := by
  classical
  intro q N L i0 a b hq hN card inter line hab ha hb gates o j h ops wf jop uniq hj jin out va vb vrest voff
  let C : Circuit := ⟨gates,0⟩
  let M := L i0
  let K := fun t => Finset.univ.filter (used C (L t) M a b j.val)
  let W := fun t => (K t).image (fun k : Fin gates.length => N+k.val)
  let y := fun (t v : Fin N) => decide (v ∉ M ∧ v ∉ L t)
  have hlt : N+h.val < N+j.val := by have : h.val < j.val := hj; omega
  have zprobe (p : Fin N) : value C (one p) (N+j.val) = decide (p ≠ a ∧ p ≠ b) := by
    rw [not_value C j h jop hj jin]
    by_cases e : p = a
    · subst p
      change Circuit.eval ⟨gates,N+h.val⟩ (List.ofFn (one a)) = true at va
      change value C (one a) (N+h.val) = true at va
      simp [va]
    by_cases e' : p = b
    · subst p
      change value C (one b) (N+h.val) = true at vb
      simp [vb]
    have hh : value C (one p) (N+h.val) = false := vrest p e e'
    simp [hh,e,e']
  have zy (t : Fin N) : value C (y t) (N+j.val) = true := by
    rw [not_value C j h jop hj jin]
    have hh : value C (y t) (N+h.val) = false := by
      by_contra! hon
      have bad := hmono N gates j ops uniq (y t) (fun v => decide (v ∉ M))
        (fun v hv => decide_eq_true (of_decide_eq_true hv).1) _ hlt (by simpa using hon)
      change value C (fun v => decide (v ∉ M)) (N+h.val) = true at bad
      change value C (fun v => decide (v ∉ M)) (N+h.val) = false at voff
      exact Bool.false_ne_true (voff.symm.trans bad)
    simp [hh]
  have monoOps (k : Fin C.gates.length) (hne : k.val ≠ j.val) :
      (C.gates.get k).op = GateOp.and ∨ (C.gates.get k).op = GateOp.or := by
    rcases (ops _ (List.get_mem gates k)).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hne (congrArg Fin.val (uniq k h)))
  have low (t : Fin N) (r : ℕ) (u : Fin N) (hr : value C (y t) r = false)
      (hu : u ∉ M) (hv : value C (one u) r = true) : u ∈ L t := by
    by_contra hout
    have v := mono_at_fixed C j.val monoOps (one u) (y t) (by
      intro p hp
      have eq : p = u := of_decide_eq_true hp
      subst p
      exact decide_eq_true ⟨hu,hout⟩) (fun _ => zy t) r hv
    exact Bool.false_ne_true (hr.symm.trans v)
  have bound (t : Fin N) : q ≤ (K t).card := by
    let R := seen C (L t) M a b
    have inrange (w : ℕ) (hm : Many R w) : N ≤ w ∧ w < N+gates.length := by
      obtain ⟨p,s,hne,hp,hs⟩ := hm
      constructor
      · by_contra! hw
        let u : Fin N := ⟨w,hw⟩
        have h1 : value C (one p) u = true := hp.2.1
        have h2 : value C (one s) u = true := hs.2.1
        rw [input_value] at h1 h2
        exact hne ((of_decide_eq_true h1).symm.trans (of_decide_eq_true h2))
      · by_contra! hw
        have f := missing_value C (one p) w (by exact hw)
        exact Bool.false_ne_true (f.symm.trans hp.2.1)
    have step (w : ℕ) (hm : Many R w) : ∃ P : Finset ℕ,
        (∀ r ∈ P, r < w) ∧ P.card ≤ 1 + (if w ∈ W t then 1 else 0) ∧
        ∀ p, R p w → ∃ r ∈ P, R p r := by
      obtain ⟨hn,hw⟩ := inrange w hm
      let k : Fin gates.length := ⟨w-N, by omega⟩
      have eq : w = N+k.val := by dsimp [k]; omega
      rw [eq] at hm ⊢
      have kj : k.val ≠ j.val := by
        intro he
        obtain ⟨p,_,_,hp,_⟩ := hm
        have f : value C (y t) (N+k.val) = false := hp.2.2.1
        rw [he] at f
        exact Bool.false_ne_true (f.symm.trans (zy t))
      have g := ops _ (List.get_mem gates k)
      have geom : L t = M ∨ (L t ∩ M).card ≤ 1 := by
        by_cases e : t = i0
        · exact Or.inl (congrArg L e)
        · exact Or.inr (inter t i0 e).le
      obtain ⟨P,hP,sz,cov⟩ := gate_step C (L t) M a b ha hb geom j.val k g.1 g.2 (wf k)
        (fun hop => congrArg Fin.val (uniq k hop)) (zy t) zprobe (low t) hm
      refine ⟨P,hP,?_,cov⟩
      by_cases hread : N+j.val ∈ (gates.get k).inputs
      · rw [if_pos hread] at sz
        split <;> omega
      · have mem : N+k.val ∈ W t := Finset.mem_image.mpr
          ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm,kj,hread⟩,rfl⟩
        rw [if_pos mem]
        rw [if_neg hread] at sz
        exact sz
    have hcover (p : Fin N) (hp : p ∈ L t) : R p (o t) := by
      have ev (x : Fin N → Bool) : value C x (o t) = decide (∃ v ∈ L t, x v = true) := out t x
      refine ⟨hp, (ev _).trans (decide_eq_true ⟨p,hp,by simp [one]⟩), ?_, ?_⟩
      · apply (ev _).trans
        apply decide_eq_false
        rintro ⟨v,hv,hx⟩
        exact (of_decide_eq_true hx).2 hv
      · intro u _ hu
        rw [ev] at hu
        obtain ⟨v,hv,hvu⟩ := of_decide_eq_true hu
        exact (of_decide_eq_true hvu) ▸ hv
    have hcount := count_front (L t) R (W t) step (N+gates.length) {o t}
      (fun w _ hm => (inrange w hm).2) (fun p hp => ⟨o t,by simp,hcover p hp⟩)
    have f := Finset.card_filter_le (W t) (· < N+gates.length)
    have im : (W t).card ≤ (K t).card := Finset.card_image_le
    rw [card t,Finset.card_singleton] at hcount
    omega
  have dis (t u : Fin N) (hne : t ≠ u) : Disjoint (K t) (K u) := by
    refine Finset.disjoint_left.mpr fun k h1 h2 => ?_
    have m1 := (Finset.mem_filter.mp h1).2
    have m2 := (Finset.mem_filter.mp h2).2
    exact many_disjoint C (L t) (L u) M a b (inter t u hne).le _ m1.1 m2.1
  let U := Finset.univ.biUnion K
  let B := Finset.univ.filter (fun k : Fin gates.length => N+j.val ∈ (gates.get k).inputs)
  have tot : N*q ≤ U.card := union_count K bound dis
  have ds : Disjoint U B := by
    refine Finset.disjoint_left.mpr fun k hk hb => ?_
    obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hk
    have hu : used C (L t) M a b j.val k := (Finset.mem_filter.mp ht).2
    exact hu.2.2 (Finset.mem_filter.mp hb).2
  have nj : j ∉ U ∪ B := by
    intro mem
    rcases Finset.mem_union.mp mem with mem | mem
    · obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp mem
      have hu : used C (L t) M a b j.val j := (Finset.mem_filter.mp ht).2
      exact hu.2.1 rfl
    · exact (Nat.lt_irrefl _) (wf j _ (Finset.mem_filter.mp mem).2)
  have fin := Finset.card_le_univ (insert j (U ∪ B))
  rw [Finset.card_insert_of_notMem nj,Finset.card_union_of_disjoint ds,Fintype.card_fin] at fin
  change U.card+B.card+1 ≤ gates.length at fin
  exact le_trans (Nat.add_le_add_right (Nat.add_le_add_right tot B.card) 1) fin

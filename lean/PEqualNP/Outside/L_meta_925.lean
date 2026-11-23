import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925
open PEqualNP.CircuitLowerBounds

-- Expanding one active binary gate adds at most one wire to the boundary.
theorem closure (d : Finset ℕ) (child : ℕ → Finset ℕ)
    (hcard : ∀ j, (child j).card ≤ 2) (hlt : ∀ j z, z ∈ child j → z < j) :
    ∀ live : Finset ℕ, ∃ exits : Finset ℕ,
      exits.card ≤ live.card + d.card ∧ Disjoint exits d ∧
      (∀ z ∈ exits, z ∈ live ∨ ∃ j ∈ d, z ∈ child j) ∧
      ∀ P : ℕ → Prop, (∀ j ∈ d, (∀ z ∈ child j, P z) → P j) →
      (∀ z ∈ exits, P z) → ∀ z ∈ live, P z := by
  induction d using Finset.induction_on_max with
  | empty =>
    intro live
    exact ⟨live, by simp, by simp, fun z hz => Or.inl hz, fun _ _ h => h⟩
  | insert w d hmax ih =>
    intro live
    have hw : w ∉ d := fun h => (Nat.lt_irrefl w) (hmax w h)
    by_cases hwl : w ∈ live
    · let next := (live.erase w) ∪ child w
      obtain ⟨ex, hsize, hdis, hsource, hprop⟩ := ih next
      refine ⟨ex, ?_, ?_, ?_, ?_⟩
      · have hu : next.card ≤ (live.erase w).card + (child w).card := Finset.card_union_le ..
        have he := Finset.card_erase_add_one hwl
        have hc := hcard w
        rw [Finset.card_insert_of_notMem hw]
        omega
      · rw [Finset.disjoint_left] at hdis ⊢
        intro z hz hzw
        rcases Finset.mem_insert.mp hzw with eq | hd
        · subst z
          rcases hsource w hz with hn | ⟨j,hj,he⟩
          · rcases Finset.mem_union.mp hn with h | h
            · exact (Finset.ne_of_mem_erase h) rfl
            · exact (Nat.lt_irrefl w) (hlt w w h)
          · exact (Nat.lt_irrefl w) ((hlt j w he).trans (hmax j hj))
        · exact hdis hz hd
      · intro z hz
        rcases hsource z hz with hn | ⟨j,hj,he⟩
        · rcases Finset.mem_union.mp hn with hl | hs
          · exact Or.inl (Finset.mem_of_mem_erase hl)
          · exact Or.inr ⟨w,Finset.mem_insert_self ..,hs⟩
        · exact Or.inr ⟨j,Finset.mem_insert_of_mem hj,he⟩
      · intro P step hex z hz
        have hnext := hprop P (fun j hj => step j (Finset.mem_insert_of_mem hj)) hex
        by_cases eq : z=w
        · subst z
          exact step w (Finset.mem_insert_self ..) (fun a ha => hnext a (Finset.mem_union_right _ ha))
        · exact hnext z (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hz⟩))
    · obtain ⟨ex, hsize, hdis, hsource, hprop⟩ := ih live
      refine ⟨ex, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hw]
        omega
      · rw [Finset.disjoint_left] at hdis ⊢
        intro z hz hzw
        rcases Finset.mem_insert.mp hzw with eq | hd
        · subst z
          rcases hsource w hz with hl | ⟨j,hj,hz⟩
          · exact hwl hl
          · exact (Nat.lt_irrefl w) ((hlt j w hz).trans (hmax j hj))
        · exact hdis hz hd
      · intro z hz
        rcases hsource z hz with h | ⟨j,hj,he⟩
        · exact Or.inl h
        · exact Or.inr ⟨j,Finset.mem_insert_of_mem hj,he⟩
      · intro P step
        exact hprop P (fun j hj => step j (Finset.mem_insert_of_mem hj))

-- Each additional set meets an earlier set, so it adds at most q new points.
theorem unionBound {α : Type} [DecidableEq α] (F : Finset (Finset α)) (q : ℕ)
    (hne : F.Nonempty) (hcard : ∀ A ∈ F, A.card ≤ q+1)
    (hi : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) :
    (F.biUnion id).card ≤ q * F.card + 1 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp at hne
  | @insert a f ha ih =>
    by_cases h : f.Nonempty
    · obtain ⟨b,hb⟩ := h
      have ih' := ih ⟨b,hb⟩ (fun s hs => hcard s (Finset.mem_insert_of_mem hs))
        (fun s hs t ht => hi s (Finset.mem_insert_of_mem hs) t (Finset.mem_insert_of_mem ht))
      obtain ⟨v,hv⟩ := hi a (Finset.mem_insert_self ..) b (Finset.mem_insert_of_mem hb)
      have hv2 : v ∈ a ∩ f.biUnion id :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,Finset.mem_biUnion.mpr ⟨b,hb,(Finset.mem_inter.mp hv).2⟩⟩
      have hpos := Finset.card_pos.mpr (show (a ∩ f.biUnion id).Nonempty from ⟨v,hv2⟩)
      have hsum := Finset.card_union_add_card_inter a (f.biUnion id)
      have ha' := hcard a (Finset.mem_insert_self ..)
      rw [Finset.biUnion_insert, Finset.card_insert_of_notMem ha, Nat.mul_add]
      simp only [id_eq,Nat.mul_one]
      omega
    · have e := Finset.not_nonempty_iff_eq_empty.mp h
      subst f
      simpa using hcard a (Finset.mem_insert_self ..)

-- Too few boundary wires would let an input missing part of S w switch the output on.
theorem useExits {m n : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m) (q K c : ℕ)
    (sz : ∀ j, (S j).card=q+1) (inter : ∀ i j, i ≠ j → (S i ∩ S j).card=1)
    (hc : c ≤ q) (hK : c*q < K)
    (ex : Finset ℕ) (degree : ℕ)
    (hsize : ex.card ≤ 1+degree)
    (val : Finset (Fin n) → ℕ → Prop) (out : ℕ)
    (suff : ∀ X, (∀ z ∈ ex, val X z) → val X out)
    (promise : ∀ X, X.card ≤ K → val X out → S w ⊆ X)
    (supply : ∀ z ∈ ex, ∃ B : Finset (Fin n),
      ((B.card ≤ 1) ∨ ∃ v, v ≠ w ∧ B=S v) ∧
      ∀ X, B ⊆ X → val X z) : c ≤ degree := by
  classical
  by_contra! small
  have qpos0 : 1 ≤ q := by omega
  by_cases Ksmall : K < q+1
  · have : c=0 := by
      by_contra! h
      have z := Nat.mul_le_mul_right q (show 1 ≤ c by omega)
      simp only [one_mul] at z
      omega
    omega
  let B (z : {z // z ∈ ex}) := Classical.choose (supply z z.property)
  have good (z : {z // z ∈ ex}) : ((B z).card ≤ 1 ∨ ∃ v, v ≠ w ∧ B z=S v) ∧ (∀ X, B z ⊆ X → val X z) := Classical.choose_spec (supply z z.property)
  let inputs := ex.attach.image B
  let X := inputs.biUnion id
  have count : inputs.card ≤ c := by
    have a : inputs.card ≤ ex.attach.card := Finset.card_image_le
    simp only [Finset.card_attach] at a
    omega
  have structureB (A) (h : A∈inputs) : A.card ≤ 1 ∨ ∃ v, v ≠ w ∧ A=S v := by
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp h
    exact (good z).1
  have on : ∀ z ∈ ex, val X z := by
    intro z hz
    let t : {z // z ∈ ex} := ⟨z,hz⟩
    apply (good t).2
    intro p hp
    exact Finset.mem_biUnion.mpr ⟨B t,Finset.mem_image.mpr ⟨t,Finset.mem_attach ..,rfl⟩,hp⟩
  have smallcap (A) (h : A ∈ inputs) : (S w ∩ A).card ≤ 1 := by
    rcases structureB A h with ha | ⟨j,hj,rfl⟩
    · exact (Finset.card_le_card Finset.inter_subset_right).trans ha
    · exact (inter w j (Ne.symm hj)).le
  have misses : ¬ S w ⊆ X := by
    intro sub
    have cap : S w ⊆ inputs.biUnion (fun A => S w ∩ A) := by
      intro x hx
      obtain ⟨A,hA,hxA⟩ := Finset.mem_biUnion.mp (sub hx)
      exact Finset.mem_biUnion.mpr ⟨A,hA,Finset.mem_inter.mpr ⟨hx,hxA⟩⟩
    have hcard : (S w).card ≤ inputs.card := by
      calc
        _ ≤ (inputs.biUnion (fun A => S w ∩ A)).card := Finset.card_le_card cap
        _ ≤ ∑ A ∈ inputs,(S w ∩ A).card := Finset.card_biUnion_le
        _ ≤ ∑ _A ∈ inputs,1 := Finset.sum_le_sum smallcap
        _ = inputs.card := by simp
    have := sz w
    omega
  let big := inputs.filter (fun A => 1 < A.card)
  have coverBig (A) (h : A ∈ big) : ∃ v, v ≠ w ∧ A=S v := by
    obtain ⟨hm,hs⟩ := Finset.mem_filter.mp h
    exact (structureB A hm).resolve_left (by omega)
  have hull : X.card ≤ q * inputs.card + 1 := by
    by_cases nonempty : big.Nonempty
    · have Vsize := unionBound big q nonempty (by
        intro A ha
        obtain ⟨i,_,rfl⟩ := coverBig A ha
        exact (sz i).le) (by
        intro A ha C hd
        obtain ⟨i,_,rfl⟩ := coverBig A ha
        obtain ⟨j,_,rfl⟩ := coverBig C hd
        by_cases h : i=j
        · subst j
          simp only [Finset.inter_self]
          exact Finset.card_pos.mp (by rw [sz];omega)
        · exact Finset.card_pos.mp (by rw [inter i j h];decide))
      have hsmall (A) (ha : A ∈ inputs \ big) : A.card ≤ 1 := by
        obtain ⟨hi,hb⟩ := Finset.mem_sdiff.mp ha
        by_contra! h
        exact hb (Finset.mem_filter.mpr ⟨hi,h⟩)
      have smallSum : ((inputs \ big).biUnion id).card ≤ (inputs \ big).card := by
        calc
          _ ≤ ∑ A ∈ inputs \ big, A.card := Finset.card_biUnion_le
          _ ≤ ∑ _A ∈ inputs \ big, 1 := Finset.sum_le_sum hsmall
          _ = _ := by simp
      have whole : X ⊆ (big.biUnion id) ∪ ((inputs \ big).biUnion id) := by
        intro z hz
        obtain ⟨A,hA,hz⟩ := Finset.mem_biUnion.mp hz
        by_cases h : A ∈ big
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨A,h,hz⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨A,Finset.mem_sdiff.mpr ⟨hA,h⟩,hz⟩)
      have hsum := (Finset.card_le_card whole).trans (Finset.card_union_le ..)
      have bsub : big ⊆ inputs := Finset.filter_subset ..
      have hboth := Finset.card_sdiff_add_card_eq_card bsub
      have qpos : 1 ≤ q := by omega
      have m := Nat.mul_le_mul_right (inputs \ big).card qpos
      rw [one_mul] at m
      rw [← hboth, Nat.mul_add]
      omega
    · have few (A) (hA : A ∈ inputs) : A.card ≤ 1 := by
        by_contra! many
        exact nonempty ⟨A,Finset.mem_filter.mpr ⟨hA,many⟩⟩
      have hle : X.card ≤ inputs.card := by
        calc
          _ ≤ ∑ A ∈ inputs, A.card := Finset.card_biUnion_le
          _ ≤ ∑ _A ∈ inputs,1 := Finset.sum_le_sum few
          _ = _ := by simp
      have qpos : 1 ≤ q := by omega
      have m := Nat.mul_le_mul_right inputs.card qpos
      rw [one_mul] at m
      omega
  have mul := Nat.mul_le_mul_left q count
  rw [Nat.mul_comm c q] at hK
  exact misses (promise X (by omega) (suff X on))


-- A gate appends one wire to the list of input and intermediate values.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem gate_force (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : ℕ → Bool) (hf : g.op.eval (g.inputs.map f) = true) :
    ∃ ids : Finset ℕ, ids.card ≤ 2 ∧ (∀ j ∈ ids, f j = true) ∧
    (∀ j ∈ ids, j ∈ g.inputs) ∧ ∀ u : ℕ → Bool, (∀ j ∈ ids, u j = true) →
      g.op.eval (g.inputs.map u) = true := by
  classical
  rcases h with hp|hp
  · refine ⟨g.inputs.toFinset,g.inputs.toFinset_card_le.trans hlen,?_,by simp,?_⟩
    · intro j hj
      have ok : (g.inputs.map f).all id = true := by simpa [hp,GateOp.eval] using hf
      exact List.all_eq_true.mp ok (f j) (List.mem_map.mpr ⟨j,List.mem_toFinset.mp hj,rfl⟩)
    · intro u hu
      simp only [hp,GateOp.eval,List.all_eq_true]
      intro z hz
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
      exact hu j (List.mem_toFinset.mpr hj)
  · have help : (g.inputs.map f).any id = true := by simpa [hp,GateOp.eval] using hf
    obtain ⟨z,hz,hv⟩ := List.any_eq_true.mp help
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
    refine ⟨{j},by simp,by simpa using hv,by simpa using hj,?_⟩
    intro u hu
    simp only [hp,GateOp.eval,List.any_eq_true]
    exact ⟨u j,List.mem_map.mpr ⟨j,hj,rfl⟩,hu j (Finset.mem_singleton_self _)⟩

theorem network (n : ℕ) (gs : List Gate) (base : List Bool) (length_base : base.length = n)
    (HG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ child : ℕ → Finset ℕ, (∀ w, (child w).card ≤ 2) ∧
    (∀ w z, z ∈ child w → z < w) ∧
    ∀ w, n ≤ w → (gs.foldl step base).getD w false = true →
      (∀ z ∈ child w, (gs.foldl step base).getD z false = true) ∧
      ∀ x : List Bool, x.length = n → (∀ z ∈ child w, (gs.foldl step x).getD z false = true) →
        (gs.foldl step x).getD w false = true := by
  classical
  have get (w : ℕ) (hn : n ≤ w) (tr : (gs.foldl step base).getD w false = true) :
      ∃ kids : Finset ℕ, kids.card ≤ 2 ∧ (∀ j ∈ kids, j < w) ∧
      (∀ j ∈ kids, (gs.foldl step base).getD j false = true) ∧
      ∀ x : List Bool, x.length = n → (∀ z ∈ kids, (gs.foldl step x).getD z false = true) →
        (gs.foldl step x).getD w false = true := by
    let t := w-n
    have hw : w = n+t := by dsimp [t]; omega
    have ht : t < gs.length := by
      by_contra! h
      have b : (gs.foldl step base).length ≤ w := by rw [foldl_step_length,length_base,hw];omega
      rw [getD_of_length_le _ _ b] at tr
      contradiction
    let g := gs[t]
    have hg := HG g (List.getElem_mem ht)
    have hpre (x : List Bool) (hx : x.length=n) :
        ((gs.take t).foldl step x).length = w := by
      simp [foldl_step_length,hx,List.length_take,Nat.min_eq_left ht.le,hw]
    have hop (x : List Bool) (hx : x.length=n) : (gs.foldl step x).getD w false =
        g.op.eval (g.inputs.map (fun z => ((gs.take t).foldl step x).getD z false)) := by
      rw [show w=x.length+t by rw [hx,← hw]]
      exact foldl_step_getD_gate gs x t ht
    rw [hop _ length_base] at tr
    obtain ⟨kids, hwidth, htr, _, hsafe⟩ := gate_force g hg.1 hg.2 _ tr
    have hlt : ∀ z ∈ kids, z < w := by
      intro z hz
      by_contra! large
      have v := htr z hz
      rw [getD_of_length_le _ _ (by rw [hpre _ length_base];exact large)] at v
      contradiction
    refine ⟨kids,hwidth,hlt,?_,?_⟩
    · intro z hz
      rw [foldl_take_getD gs base t z (by rw [hpre _ length_base];exact hlt z hz)]
      exact htr z hz
    · intro x hx hc
      rw [hop _ hx]
      exact hsafe _ (fun z hz => by
        rw [← foldl_take_getD gs x t z (by rw [hpre _ hx];exact hlt z hz)]
        exact hc z hz)
  let child := fun w => if h : n ≤ w ∧ (gs.foldl step base).getD w false = true
                      then Classical.choose (get w h.1 h.2) else ∅
  refine ⟨child, ?_, ?_, ?_⟩
  · intro w
    by_cases h : n ≤ w ∧ (gs.foldl step base).getD w false = true
    · simpa only [child, dite_eq_left h] using (Classical.choose_spec (get w h.1 h.2)).1
    · simp only [child,dite_eq_right h]
      simp
  · intro w z
    by_cases h : n ≤ w ∧ (gs.foldl step base).getD w false = true
    · simpa only [child, dite_eq_left h] using (Classical.choose_spec (get w h.1 h.2)).2.1 z
    · simp only [child,dite_eq_right h]
      simp
  · intro w hw hv
    have h := And.intro hw hv
    simpa only [child, dite_eq_left h] using (Classical.choose_spec (get w hw hv)).2.2


end PEqualNP.Outside.L_meta_925

open PEqualNP.Outside.L_meta_925

theorem PEqualNP.Outside.L_meta_925 :
  ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hsize hinter gates out hg hcorrect c hc hK
  by_cases hzero : c=0
  · simp [hzero]
  have hcpos : 1 ≤ c := by omega
  have wholeSmall : q + 1 ≤ K := by
    have z := Nat.mul_le_mul_right q hcpos
    rw [one_mul] at z
    omega
  let bits (X : Finset (Fin n)) (a : Fin n) := decide (a ∈ X)
  let val (X : Finset (Fin n)) (z : ℕ) := (gates.foldl step (List.ofFn (bits X))).getD z false = true
  let wires := Finset.Ico n (n+gates.length)
  -- Charge to each output the gates active on its set alone among the listed sets.
  let d (w : Fin m) := wires.filter (fun z => val (S w) z ∧ ∀ v, v ≠ w → ¬val (S v) z)
  have exactOn (X : Finset (Fin n)) (w : Fin m) (hX : X.card ≤ K) : val X (out w) ↔ S w ⊆ X := by
    have support : (Finset.univ.filter (fun a : Fin n => bits X a = true))=X := by
      ext a
      simp [bits]
    have h := hcorrect w (bits X) (by simpa [support] using hX)
    change (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates,out w⟩ (List.ofFn (bits X)) = true) ↔ _
    rw [h,decide_eq_true_eq]
    simp only [bits,decide_eq_true_eq,Finset.subset_iff]
  have output (w : Fin m) : val (S w) (out w) :=
    (exactOn (S w) w (by rw [hsize];exact wholeSmall)).mpr (Finset.Subset.refl _)
  have monotone (X Y : Finset (Fin n)) (sub : X ⊆ Y) (z : ℕ) : val X z → val Y z := by
    have hw (j : ℕ) : val X j → val Y j := by
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hv
        by_cases hj : j < n
        · have h1 : ∀ Z : Finset (Fin n), val Z j ↔ (⟨j,hj⟩ : Fin n) ∈ Z := by
            intro Z
            unfold val
            rw [foldl_step_getD gates _ _ (by simpa using hj)]
            simp [List.getD_eq_getElem?_getD, hj, bits]
          exact (h1 Y).mpr (sub ((h1 X).mp hv))
        · obtain ⟨kids,_,hlt,hs⟩ := network n gates (List.ofFn (bits X)) (by simp) hg
          obtain ⟨hon, hprop⟩ := hs j (by omega) hv
          exact hprop (List.ofFn (bits Y)) (by simp) (fun k hk => ih k (hlt j k hk) (hon k hk))
    exact hw z
  have one (w : Fin m) : c ≤ (d w).card := by
    obtain ⟨kid, width, below, hnet⟩ := network n gates (List.ofFn (bits (S w))) (by simp) hg
    obtain ⟨ex, hcard, hdis, hsource, hprop⟩ := closure (d w) kid width below {out w}
    have hdval (j) (h : j ∈ d w) : val (S w) j := (Finset.mem_filter.mp h).2.1
    have hlow (j) (h : j ∈ d w) : n ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp h).1).1
    have active (z) (hz : z ∈ ex) : val (S w) z := by
      rcases hsource z hz with hout | ⟨j,hj,hc⟩
      · have e := Finset.mem_singleton.mp hout
        simpa [e] using output w
      · exact (hnet j (hlow j hj) (hdval j hj)).1 z hc
    apply useExits S w q K c hsize hinter hc hK ex (d w).card
      (by simpa using hcard) val (out w)
    · intro X hx
      have certify (j : ℕ) (hj : j ∈ d w) (hk : ∀ z ∈ kid j, val X z) : val X j := by
        exact (hnet j (hlow j hj) (hdval j hj)).2 (List.ofFn (bits X)) (by simp) hk
      exact hprop (val X) certify hx (out w) (Finset.mem_singleton_self _)
    · intro X hX
      exact (exactOn X w hX).mp
    · intro z hz
      by_cases hin : z < n
      · let a : Fin n := ⟨z,hin⟩
        refine ⟨{a},Or.inl (by simp),?_⟩
        intro X hx
        have ha := hx (Finset.mem_singleton_self a)
        unfold val
        rw [foldl_step_getD gates _ _ (by simpa using hin)]
        simpa [bits,List.getD_eq_getElem?_getD,hin,a] using ha
      · have htrue := active z hz
        have hl : z < n+gates.length := by
          by_contra! hge
          unfold val at htrue
          rw [getD_of_length_le _ _ (by simpa [foldl_step_length] using hge)] at htrue
          contradiction
        have oth : ∃ v, v ≠ w ∧ val (S v) z := by
          by_contra! no
          have mem : z ∈ d w := Finset.mem_filter.mpr
            ⟨Finset.mem_Ico.mpr ⟨by omega,hl⟩,htrue,no⟩
          exact (Finset.disjoint_left.mp hdis) hz mem
        obtain ⟨v,hvw,hon⟩ := oth
        exact ⟨S v,Or.inr ⟨v,hvw,rfl⟩,fun X hX => monotone _ X hX z hon⟩
  have pairwise : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (d i) (d j) := by
    intro i _ j _ h
    rw [Finset.disjoint_left]
    intro z hzi hzj
    exact (Finset.mem_filter.mp hzi).2.2 j (Ne.symm h) (Finset.mem_filter.mp hzj).2.1
  calc
    m*c = ∑ _i : Fin m,c := by simp
    _ ≤ ∑ i : Fin m,(d i).card := Finset.sum_le_sum (fun i _ => one i)
    _ = (Finset.univ.biUnion d).card := (Finset.card_biUnion pairwise).symm
    _ ≤ wires.card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨w,_,h⟩ := Finset.mem_biUnion.mp hz
      exact (Finset.mem_filter.mp h).1
    _ = gates.length := by simp [wires]

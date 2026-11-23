import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782


open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem val_oob {n : ℕ} (gs : List Gate) (x : Fin n → Bool) {w : ℕ}
    (h : n + gs.length ≤ w) : val gs x w = false := by
  unfold val
  apply List.getD_eq_default
  simpa [fold_length] using h

theorem val_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) {w : ℕ}
    (h : w < n) : val gs x w = x ⟨w,h⟩ := by
  induction gs using List.reverseRecOn with
  | nil => simp [val_nil,h]
  | append_singleton gs g ih => rw [val_snoc, ite_eq_right (by omega), ih]

theorem gate_diff (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hl : g.inputs.length = 2) (f q : ℕ → Bool)
    (hf : g.op.eval (g.inputs.map f) = true) (hq : g.op.eval (g.inputs.map q) = false) :
    ∃ w ∈ g.inputs, f w = true ∧ q w = false := by
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp hl
  rcases h with h | h <;>
    cases ha : f a <;> cases hb : f b <;> cases hc : q a <;> cases hd : q b <;>
    simp_all [GateOp.eval]

theorem circuitChildren (n : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∃ child : ℕ → Finset ℕ, (∀ j, (child j).card ≤ 2) ∧
    (∀ j z, z ∈ child j → z < j) ∧
    ∀ (x y : Fin n → Bool) (w : ℕ), n ≤ w → val gs x w = true → val gs y w = false →
      ∃ z ∈ child w, val gs x z = true ∧ val gs y z = false := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun _ => ∅, by simp, by simp, ?_⟩
    intro x y w hw hp
    simp [val_nil, Nat.not_lt_of_ge hw] at hp
  | append_singleton gs g ih =>
    obtain ⟨old, bound, below, walk⟩ := ih (fun g' h => hg g' (by simp [h]))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    let k := n + gs.length
    let ins := g.inputs.toFinset.filter (fun z => z < k)
    let child := fun w => if w = k then ins else old w
    refine ⟨child, ?_, ?_, ?_⟩
    · intro w
      by_cases hw : w=k
      · simp only [child, hw, ite_true]
        exact (Finset.card_filter_le ..).trans (g.inputs.toFinset_card_le.trans hlen.le)
      · simpa [child,hw] using bound w
    · intro w z
      by_cases hw : w=k
      · simp only [child, hw, ite_true, ins, Finset.mem_filter]
        exact fun h => h.2
      · simpa [child,hw] using below w z
    · intro x y w hn hp hq
      by_cases he : w=k
      · subst w
        rw [val_snoc, ite_eq_left rfl] at hp hq
        obtain ⟨z,hz,tx,ty⟩ := gate_diff g hop hlen _ _ hp hq
        have hlt : z < k := by
          by_contra! hge
          rw [val_oob gs x hge] at tx
          contradiction
        refine ⟨z, ?_, ?_, ?_⟩
        · simpa [child,ins] using And.intro hz hlt
        · rwa [val_snoc, ite_eq_right (ne_of_lt hlt)]
        · rwa [val_snoc, ite_eq_right (ne_of_lt hlt)]
      · rw [val_snoc, ite_eq_right he] at hp hq
        obtain ⟨z,hz,tx,ty⟩ := walk x y w hn hp hq
        have hlt : w < k := by
          by_contra! hge
          rw [val_oob gs x hge] at hp
          contradiction
        have hne := ne_of_lt ((below w z hz).trans hlt)
        exact ⟨z, by simpa [child,he] using hz,
          by rwa [val_snoc, ite_eq_right hne], by rwa [val_snoc, ite_eq_right hne]⟩


def expand (w : ℕ) (children live : Finset ℕ) : Finset ℕ :=
  if w ∈ live then (live.erase w) ∪ children else live

theorem expand_le (w : ℕ) (children live : Finset ℕ) (hb : children.card ≤ 2) :
    (expand w children live).card ≤ live.card + 1 := by
  by_cases h : w ∈ live
  · rw [expand, ite_eq_left h]
    have hu := Finset.card_union_le (live.erase w) children
    have he := Finset.card_erase_add_one h
    omega
  · simp [expand, h]

theorem expand_witness {w : ℕ} {children live : Finset ℕ} {P : ℕ → Prop}
    (h : ∃ z ∈ live, P z)
    (step : P w → ∃ z ∈ children, P z) : ∃ z ∈ expand w children live, P z := by
  by_cases hw : w ∈ live
  · rw [expand, ite_eq_left hw]
    obtain ⟨z, hz, hP⟩ := h
    by_cases hzw : z = w
    · subst z
      obtain ⟨v, hv, hpv⟩ := step hP
      exact ⟨v, Finset.mem_union_right _ hv, hpv⟩
    · exact ⟨z, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzw, hz⟩), hP⟩
  · simpa [expand, hw] using h

theorem expand_earlier {j : ℕ} {children live : Finset ℕ}
    (hsmall : ∀ z ∈ children, z < j) :
    ∀ z ∈ expand j children live, j ≤ z → z ∈ live ∧ z ≠ j := by
  intro z hz hle
  by_cases hj : j ∈ live
  · rw [expand, ite_eq_left hj, Finset.mem_union] at hz
    rcases hz with hz | hz
    · exact ⟨Finset.mem_of_mem_erase hz, Finset.ne_of_mem_erase hz⟩
    · exact ((Nat.not_lt_of_ge hle) (hsmall z hz)).elim
  · rw [expand, ite_eq_right hj] at hz
    exact ⟨hz, fun h => hj (h ▸ hz)⟩

theorem makeClosure (d : Finset ℕ) (child : ℕ → Finset ℕ)
    (hcard : ∀ j, (child j).card ≤ 2) (hlt : ∀ j z, z ∈ child j → z < j) :
    ∀ live : Finset ℕ, ∃ exits : Finset ℕ,
      exits.card ≤ live.card + d.card ∧ Disjoint exits d ∧
      (∀ z ∈ exits, z ∈ live ∨ ∃ j ∈ d, z ∈ child j) ∧
      ∀ P : ℕ → Prop, (∀ j ∈ d, P j → ∃ z ∈ child j, P z) →
      (∃ z ∈ live, P z) → ∃ z ∈ exits, P z := by
  induction d using Finset.induction_on_max with
  | empty =>
    intro live
    exact ⟨live, by simp, by simp, fun z hz => Or.inl hz, fun _ _ h => h⟩
  | insert w d hmax ih =>
    intro live
    obtain ⟨exits, hsize, hdisj, hsource, hprop⟩ := ih (expand w (child w) live)
    have hw : w ∉ d := fun h => (Nat.lt_irrefl w) (hmax w h)
    refine ⟨exits, ?_, ?_, ?_, ?_⟩
    · have he := expand_le w (child w) live (hcard w)
      rw [Finset.card_insert_of_notMem hw]
      omega
    · rw [Finset.disjoint_left] at hdisj ⊢
      intro z hz hz'
      rcases Finset.mem_insert.mp hz' with heq | hzd
      · subst z
        rcases hsource w hz with he | ⟨j,hj,hwj⟩
        · exact (expand_earlier (hlt w) w he (Nat.le_refl _)).2 rfl
        · exact (Nat.lt_irrefl w) ((hlt j w hwj).trans (hmax j hj))
      · exact hdisj hz hzd
    · intro z hz
      rcases hsource z hz with he | ⟨j,hj,hzj⟩
      · by_cases hwl : w ∈ live
        · rw [expand, ite_eq_left hwl, Finset.mem_union] at he
          rcases he with he | he
          · exact Or.inl (Finset.mem_of_mem_erase he)
          · exact Or.inr ⟨w, Finset.mem_insert_self .., he⟩
        · exact Or.inl (by simpa [expand, hwl] using he)
      · exact Or.inr ⟨j, Finset.mem_insert_of_mem hj, hzj⟩
    · intro P hstep hlive
      exact hprop P (fun j hj => hstep j (Finset.mem_insert_of_mem hj))
        (expand_witness hlive (hstep w (Finset.mem_insert_self ..)))

theorem output_bound {α : Type} [Fintype α] [DecidableEq α]
    (s : Finset α) (support : ℕ → Finset α) (off : Finset α → ℕ → Prop)
    (d : Finset ℕ) (child : ℕ → Finset ℕ) (out c k : ℕ)
    (width : ∀ j, (child j).card ≤ 2) (earlier : ∀ j z, z ∈ child j → z < j)
    (in_d : ∀ z, support z ⊆ s → 2 ≤ (support z).card → z ∈ d)
    (separates : ∀ (x : Finset α) (p : α) (j : ℕ), j ∈ d →
      p ∈ support j → off x j → ∃ v ∈ child j, p ∈ support v ∧ off x v)
    (mono : ∀ (x : Finset α) (p : α) j, p ∈ x → p ∈ support j → ¬off x j)
    (promise : ∀ x, x.card ≤ k → Disjoint x s → off x out)
    (hc : c ≤ k) (hlarge : c + 1 ≤ (support out).card) : c ≤ d.card := by
  classical
  by_contra! hsmall
  obtain ⟨exits, hcnt, hdisj, _, htrace⟩ := makeClosure d child width earlier {out}
  simp only [Finset.card_singleton] at hcnt
  let bad := exits.filter (fun z => ¬ support z ⊆ s)
  have outside (j : {z // z ∈ bad}) : ∃ p ∈ support j.val, p ∉ s := by
    have hh := (Finset.mem_filter.mp j.property).2
    exact Finset.not_subset.mp hh
  let pick (j : {z // z ∈ bad}) := Classical.choose (outside j)
  let x := bad.attach.image pick
  have hcardx : x.card ≤ k := by
    calc
      x.card ≤ bad.attach.card := Finset.card_image_le
      _ = bad.card := Finset.card_attach
      _ ≤ exits.card := Finset.card_filter_le ..
      _ ≤ k := by omega
  have hxs : Disjoint x s := by
    rw [Finset.disjoint_left]
    intro p hp hs
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hp
    rw [← he] at hs
    exact (Classical.choose_spec (outside j)).2 hs
  have hxoff := promise x hcardx hxs
  let good := exits.filter (fun z => support z ⊆ s)
  have small (z : ℕ) (hz : z ∈ good) : (support z).card ≤ 1 := by
    obtain ⟨he, hsub⟩ := Finset.mem_filter.mp hz
    by_contra! hmany
    exact Finset.disjoint_left.mp hdisj he (in_d z hsub hmany)
  have hcovers : support out ⊆ good.biUnion support := by
    intro p hp
    obtain ⟨z, hz, hpz, hxz⟩ := htrace (fun j => p ∈ support j ∧ off x j)
      (fun j hj h => separates x p j hj h.1 h.2) ⟨out, by simp, hp, hxoff⟩
    by_cases hsub : support z ⊆ s
    · exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hsub⟩, hpz⟩
    · let j : {z // z ∈ bad} := ⟨z, Finset.mem_filter.mpr ⟨hz, hsub⟩⟩
      have hmem : pick j ∈ x := Finset.mem_image.mpr ⟨j, Finset.mem_attach .., rfl⟩
      exact False.elim ((mono x (pick j) z hmem (Classical.choose_spec (outside j)).1) hxz)
  have hu : (support out).card ≤ exits.card := by
    calc
      _ ≤ (good.biUnion support).card := Finset.card_le_card hcovers
      _ ≤ ∑ z ∈ good, (support z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ good, 1 := Finset.sum_le_sum small
      _ = good.card := by simp
      _ ≤ exits.card := Finset.card_filter_le ..
  omega

end PEqualNP.Outside.L_meta_782

open PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 :
  ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c hinter _ hgate _ hpromise hc hlarge
  let pts (p : Fin n) := fun q : Fin n => decide (q = p)
  let ind (x : Finset (Fin n)) := fun q : Fin n => decide (q ∈ x)
  let supp (z : ℕ) := Finset.univ.filter (fun p : Fin n => val C.gates (pts p) z = true)
  let off (x : Finset (Fin n)) z := val C.gates (ind x) z = false
  let wires := Finset.Ico n (n + C.gates.length)
  let d (i : Fin m) := wires.filter (fun z => supp z ⊆ S i ∧ 2 ≤ (supp z).card)
  obtain ⟨child, hwidth, hlt, hstep⟩ := circuitChildren n C.gates hgate
  have inRange (j : ℕ) (hj : 2 ≤ (supp j).card) : j ∈ wires := by
    apply Finset.mem_Ico.mpr
    constructor
    · by_contra! h
      have small : (supp j).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro u hu v hv
        have hu' := (Finset.mem_filter.mp hu).2
        have hv' := (Finset.mem_filter.mp hv).2
        change val C.gates (pts u) j = true at hu'
        change val C.gates (pts v) j = true at hv'
        rw [val_input C.gates _ h] at hu' hv'
        exact (of_decide_eq_true hu').symm.trans (of_decide_eq_true hv')
      omega
    · by_contra! h
      have hz : supp j = ∅ := by
        ext p
        simp [supp, val_oob C.gates _ h]
      simp [hz] at hj
  have mono (x : Finset (Fin n)) (p : Fin n) (j : ℕ) (hpx : p ∈ x) :
      p ∈ supp j → ¬off x j := by
    have aux (w : ℕ) : val C.gates (pts p) w = true → val C.gates (ind x) w ≠ false := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hp hx
        by_cases hl : w < n
        · rw [val_input C.gates _ hl] at hp hx
          have hh : (⟨w,hl⟩ : Fin n) = p := of_decide_eq_true hp
          change decide ((⟨w,hl⟩ : Fin n) ∈ x) = false at hx
          simp [hh,hpx] at hx
        · obtain ⟨z, hz, hpz, hxz⟩ := hstep _ _ w (by omega) hp hx
          exact ih z (hlt w z hz) hpz hxz
    intro hp
    exact aux j (Finset.mem_filter.mp hp).2
  have count (i : Fin m) : c i ≤ (d i).card := by
    apply output_bound (S i) supp off (d i) child (o i) (c i) k hwidth hlt
    · intro z hsub htwo
      exact Finset.mem_filter.mpr ⟨inRange z htwo, hsub, htwo⟩
    · intro x p j hj hp hx
      have hr := Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1
      obtain ⟨z,hz,hpz,hxz⟩ := hstep (pts p) (ind x) j hr.1 (Finset.mem_filter.mp hp).2 hx
      exact ⟨z,hz,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpz⟩,hxz⟩
    · exact mono
    · intro x hx hdisj
      apply hpromise i (ind x)
      · simpa [ind] using hx
      · intro q hqs
        have hqx : q ∉ x := fun h => Finset.disjoint_left.mp hdisj h hqs
        simp [ind,hqx]
    · exact hc i
    · exact hlarge i
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (d i) (d j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro w hi hj
    obtain ⟨_, hsi, htwo⟩ := Finset.mem_filter.mp hi
    obtain ⟨_, hsj, _⟩ := Finset.mem_filter.mp hj
    have sub : supp w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hsi hp,hsj hp⟩
    have h1 := Finset.card_le_card sub
    have h2 := hinter i j hij
    omega
  calc
    ∑ i, c i ≤ ∑ i, (d i).card := Finset.sum_le_sum fun i _ => count i
    _ = (Finset.univ.biUnion d).card := (Finset.card_biUnion hd).symm
    _ ≤ wires.card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    _ = C.size := by simp [wires,PEqualNP.CircuitLowerBounds.Circuit.size]

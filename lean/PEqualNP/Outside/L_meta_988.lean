import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_988_aux

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
  · rw [ite_eq_left (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f f' : ℕ → Bool) (hff : ∀ j, f j = true → f' j = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h b hb
    obtain ⟨j, hj, rfl⟩ := hb
    exact hff j (h (f j) ⟨j, hj, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    intro h
    obtain ⟨_, ⟨j, hj, rfl⟩, hfj⟩ := h
    exact ⟨f' j, ⟨j, hj, rfl⟩, hff j hfj⟩

theorem val_mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hxx : ∀ t : Fin n, x t = true → x' t = true) :
    ∀ i, val gs x i = true → val gs x' i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    rw [val_nil] at hi ⊢
    split_ifs at hi ⊢ with h
    exact hxx ⟨i, h⟩ hi
  | append_singleton gs g ih =>
    have hg1 : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (List.mem_append_left _ hg')
    have hg2 : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      hg g (List.mem_append_right _ (List.mem_singleton_self g))
    have hih := ih hg1
    intro i hi
    rw [val_snoc] at hi ⊢
    split_ifs at hi ⊢ with h
    · exact eval_mono g.op hg2.1 g.inputs (val gs x) (val gs x') hih hi
    · exact hih i hi

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eofY {n : ℕ} (Y : Finset (Fin n)) (u : Fin n) : Fin n → Bool :=
  fun c => decide (c ∈ Y ∨ c = u)

def Inv {n : ℕ} (S Y : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eofY Y u) i = true →
    val gs (eofY Y v) i = true → u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S Y : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (eofY Y u) i = true ∧ val gs (eofY Y v) i = true

open Classical in
noncomputable def Dset {n : ℕ} (S Y : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt S Y gs i

theorem Dset_mono {n : ℕ} (S Y : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    Dset S Y gs ⊆ Dset S Y (gs ++ [g]) := by
  classical
  intro i hi
  simp only [Dset, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, ?_, ?_⟩
  · rw [val_snoc, ite_eq_right (fun h => False.elim (hne h))]; exact hz
  · rw [val_snoc, ite_eq_right (fun h => False.elim (hne h))]; exact hu
  · rw [val_snoc, ite_eq_right (fun h => False.elim (hne h))]; exact hv

theorem main_inv {n : ℕ} (S Y : Finset (Fin n)) (hdisj : Disjoint Y S) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S Y gs l ∧ S.card ≤ (S.image l).card + (Dset S Y gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, ?_⟩
    · intro i u v hz hu hv
      rw [val_nil] at hz hu hv
      split_ifs at hz hu hv with hi
      simp only [Zof, decide_eq_false_iff_not, not_not] at hz
      simp only [eofY, decide_eq_true_eq] at hu hv
      have hnotY : (⟨i, hi⟩ : Fin n) ∉ Y := Finset.disjoint_right.mp hdisj hz
      have hpu : (⟨i, hi⟩ : Fin n) = u := hu.resolve_left hnotY
      have hpv : (⟨i, hi⟩ : Fin n) = v := hv.resolve_left hnotY
      subst hpu
      exact ⟨hz, hpv⟩
    · simp
  | append_singleton gs g ih =>
    have hg1 : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (List.mem_append_left _ hg')
    have hg2 : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      hg g (List.mem_append_right _ (List.mem_singleton_self g))
    obtain ⟨l, hinv, hcard⟩ := ih hg1
    set N := n + gs.length
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = g.op.eval (g.inputs.map fun j => val gs x j) := by
      intro x
      rw [val_snoc]; simp [N]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, ite_eq_right (fun h => False.elim (hi h))]
    rcases gate_cases g hg2.1 hg2.2 (val gs) (Zof S) with hall | ⟨a, b, hab⟩
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew, hall] at hiu
          simp at hiu
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (Dset_mono S Y gs g)
        omega
    · have key : g.op.eval (g.inputs.map fun j => val gs (Zof S) j) = false →
          ∀ u, g.op.eval (g.inputs.map fun j => val gs (eofY Y u) j) = true →
            u ∈ S ∧ (val gs (eofY Y u) a = true ∨ val gs (eofY Y u) b = true) := by
        intro hz u hu
        obtain ⟨hza, hzb, hor⟩ := hab hz
        rcases hor (eofY Y u) hu with hua | hub
        · exact ⟨(hinv a u u hza hua hua).1, Or.inl hua⟩
        · exact ⟨(hinv b u u hzb hub hub).1, Or.inr hub⟩
      by_cases hm : g.op.eval (g.inputs.map fun j => val gs (Zof S) j) = false ∧
          ∃ u0 v0, g.op.eval (g.inputs.map fun j => val gs (eofY Y u0) j) = true ∧
            g.op.eval (g.inputs.map fun j => val gs (eofY Y v0) j) = true ∧ l u0 ≠ l v0
      · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
        obtain ⟨hza, hzb, hor⟩ := hab hz
        have hcol : ∀ u, g.op.eval (g.inputs.map fun j => val gs (eofY Y u) j) = true →
            l u = l u0 ∨ l u = l v0 := by
          intro u hu
          rcases hor (eofY Y u0) hu0 with ha0 | hb0 <;>
            rcases hor (eofY Y v0) hv0 with ha1 | hb1
          · exact False.elim (hne (hinv a u0 v0 hza ha0 ha1).2)
          · rcases hor (eofY Y u) hu with hau | hbu
            · exact Or.inl (hinv a u u0 hza hau ha0).2
            · exact Or.inr (hinv b u v0 hzb hbu hb1).2
          · rcases hor (eofY Y u) hu with hau | hbu
            · exact Or.inr (hinv a u v0 hza hau ha1).2
            · exact Or.inl (hinv b u u0 hzb hbu hb0).2
          · exact False.elim (hne (hinv b u0 v0 hzb hb0 hb1).2)
        refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
        · intro i u v hiz hiu hiv
          by_cases hi : i = N
          · subst hi
            rw [hnew] at hiz hiu hiv
            refine ⟨(key hiz u hiu).1, ?_⟩
            rcases hcol u hiu with h1 | h1 <;> rcases hcol v hiv with h2 | h2
            · simp [h1, h2, hne]
            · simp [h1, h2, hne]
            · simp [h1, h2, hne]
            · simp [h1, h2]
          · rw [hold _ _ hi] at hiz hiu hiv
            obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
            refine ⟨huS, ?_⟩
            dsimp only
            rw [hl]
        · have himg : S.image l ⊆
              insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
            intro y hy
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
            by_cases h : l w = l v0
            · rw [h]; exact Finset.mem_insert_self _ _
            · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
              rw [ite_eq_right (fun hc => False.elim (h hc))]
          have h1 : (S.image l).card ≤
              (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
            (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
          have hNin : N ∈ Dset S Y (gs ++ [g]) := by
            simp only [Dset, Finset.mem_filter, Finset.mem_Ico, List.length_append,
              List.length_cons, List.length_nil]
            refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, ?_, ?_⟩
            · rw [hnew]; exact hz
            · intro h; exact hne (by rw [h])
            · rw [hnew]; exact hu0
            · rw [hnew]; exact hv0
          have hNnot : N ∉ Dset S Y gs := by
            simp only [Dset, Finset.mem_filter, Finset.mem_Ico]
            intro h
            omega
          have h2 : (Dset S Y gs).card + 1 ≤ (Dset S Y (gs ++ [g])).card := by
            rw [← Finset.card_insert_of_notMem hNnot]
            apply Finset.card_le_card
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact hNin
            · exact Dset_mono S Y gs g hi
          omega
      · refine ⟨l, ?_, ?_⟩
        · intro i u v hiz hiu hiv
          by_cases hi : i = N
          · subst hi
            rw [hnew] at hiz hiu hiv
            obtain ⟨huS, -⟩ := key hiz u hiu
            refine ⟨huS, ?_⟩
            by_contra hne'
            exact hm ⟨hiz, u, v, hiu, hiv, hne'⟩
          · rw [hold _ _ hi] at hiz hiu hiv
            exact hinv i u v hiz hiu hiv
        · have := Finset.card_le_card (Dset_mono S Y gs g)
          omega

end PEqualNP.Outside.L_meta_988_aux

open PEqualNP.Outside.L_meta_988_aux in
theorem PEqualNP.Outside.L_meta_988 : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  classical
  intro n m D S y C o hS hDisj hGates hBelow hFire hShare
  have hZ : ∀ i, val C.gates (Zof (S i)) (o i) = false := by
    intro i
    cases h : val C.gates (Zof (S i)) (o i)
    · rfl
    · obtain ⟨p, hpS, hpZ⟩ := hBelow i (Zof (S i)) h
      simp only [Zof, decide_eq_true_eq] at hpZ
      exact False.elim (hpZ hpS)
  have hE : ∀ i, ∀ p ∈ S i, val C.gates (eofY (y i) p) (o i) = true := by
    intro i p hp
    exact hFire i p hp
  choose l hinv hcard using fun i => main_inv (S i) (y i) (hDisj i) C.gates hGates
  have hbound : ∀ i : Fin m, (S i).card ≤ (Dset (S i) (y i) C.gates).card + 1 := by
    intro i
    have h1 : ((S i).image (l i)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv i (o i) u v (hZ i) (hE i u hu) (hE i v hv)).2
    have := hcard i
    omega
  have hJ : ∀ w ∈ Finset.Ico n (n + C.gates.length),
      ((Finset.univ : Finset (Fin m)).filter fun i => w ∈ Dset (S i) (y i) C.gates).card ≤ D := by
    intro w hw
    apply hShare
    intro i hi j hj hij hdy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Dset, Finset.mem_Ico] at hi hj
    obtain ⟨hzi, u, v, huv, hu, hv⟩ := hi.2
    obtain ⟨hzj, -⟩ := hj.2
    have huSi : u ∈ S i := (hinv i w u u hzi hu hu).1
    have hvSi : v ∈ S i := (hinv i w v v hzi hv hv).1
    have hnotboth : ¬ (u ∈ S j ∧ v ∈ S j) := by
      intro hboth
      have hsub : ({u, v} : Finset (Fin n)) ⊆ S i ∩ S j := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with htu | htv
        · rw [htu]; exact Finset.mem_inter.mpr ⟨huSi, hboth.1⟩
        · rw [htv]; exact Finset.mem_inter.mpr ⟨hvSi, hboth.2⟩
      have h2 : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
      have := Finset.card_le_card hsub
      have := hS i j hij
      omega
    have hstep : ∀ a, a ∉ S j → val C.gates (eofY (y i) a) w = true → False := by
      intro a haNot haVal
      have hle : ∀ t : Fin n, eofY (y i) a t = true → Zof (S j) t = true := by
        intro t ht
        simp only [eofY, decide_eq_true_eq] at ht
        simp only [Zof, decide_eq_true_eq]
        rcases ht with hty | hta
        · exact Finset.disjoint_left.mp hdy hty
        · rw [hta]
          exact haNot
      have htrue := val_mono C.gates hGates (eofY (y i) a) (Zof (S j)) hle w haVal
      rw [hzj] at htrue
      simp at htrue
    by_cases huj : u ∈ S j
    · exact hstep v (fun hvj => hnotboth ⟨huj, hvj⟩) hv
    · exact hstep u huj hu
  have hsumD : ∑ i : Fin m, (Dset (S i) (y i) C.gates).card ≤ D * C.gates.length := by
    have hrewrite : ∀ i : Fin m, (Dset (S i) (y i) C.gates).card =
        ∑ w ∈ Finset.Ico n (n + C.gates.length), if w ∈ Dset (S i) (y i) C.gates then 1 else 0 := by
      intro i
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1
      ext w
      simp only [Finset.mem_filter, Dset]
      constructor
      · intro h; exact ⟨h.1, h⟩
      · intro h; exact h.2
    calc ∑ i : Fin m, (Dset (S i) (y i) C.gates).card
        = ∑ i : Fin m, ∑ w ∈ Finset.Ico n (n + C.gates.length),
            if w ∈ Dset (S i) (y i) C.gates then 1 else 0 := Finset.sum_congr rfl fun i _ => hrewrite i
      _ = ∑ w ∈ Finset.Ico n (n + C.gates.length), ∑ i : Fin m,
            if w ∈ Dset (S i) (y i) C.gates then 1 else 0 := Finset.sum_comm
      _ = ∑ w ∈ Finset.Ico n (n + C.gates.length),
            ((Finset.univ : Finset (Fin m)).filter fun i => w ∈ Dset (S i) (y i) C.gates).card := by
            apply Finset.sum_congr rfl
            intro w _
            rw [Finset.sum_boole, Nat.cast_id]
      _ ≤ ∑ _w ∈ Finset.Ico n (n + C.gates.length), D := Finset.sum_le_sum hJ
      _ = D * C.gates.length := by
            rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.add_sub_cancel_left, mul_comm]
  calc ∑ i : Fin m, (S i).card
      ≤ ∑ i : Fin m, ((Dset (S i) (y i) C.gates).card + 1) := Finset.sum_le_sum fun i _ => hbound i
    _ = (∑ i : Fin m, (Dset (S i) (y i) C.gates).card) + m := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul, mul_one]
    _ ≤ D * C.gates.length + m := Nat.add_le_add_right hsumD m

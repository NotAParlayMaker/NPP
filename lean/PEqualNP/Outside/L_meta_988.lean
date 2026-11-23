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
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

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

def eof {n : ℕ} (Y : Finset (Fin n)) (u : Fin n) : Fin n → Bool := fun c => decide (c ∈ Y ∨ c = u)

def Inv {n : ℕ} (S Y : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eof Y u) i = true → val gs (eof Y v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S Y : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ val gs (eof Y u) i = true ∧ val gs (eof Y v) i = true

open Classical in
noncomputable def D {n : ℕ} (S Y : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt S Y gs i

theorem D_mono {n : ℕ} (S Y : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S Y gs ⊆ D S Y (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, hus, hvs, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, hus, hvs, huv, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

theorem main_inv {n : ℕ} (S Y : Finset (Fin n)) (hdis : Disjoint Y S) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S Y gs l ∧ S.card ≤ (S.image l).card + (D S Y gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      have notY := Finset.disjoint_right.mp hdis hz
      replace hu := hu.resolve_left notY
      replace hv := hv.resolve_left notY
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    -- facts about the new wire from the old invariant
    have key : P (Zof S) = false → ∀ u, P (eof Y u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof Y w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof S) with hall | ⟨a, b, hab⟩
      · have := hall (eof Y u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (eof Y w) a = true, fun w => val gs (eof Y w) b = true,
          fun w hw => hy (eof Y w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof Y u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P (Zof S) = false ∧ ∃ u v, P (eof Y u) = true ∧ P (eof Y v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (eof Y w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inr (hA w v0 h h1)
            · exact absurd (hB u0 v0 h0 h1) hne
            · exact absurd (hA u0 v0 h0 h1) hne
            · exact Or.inr (hB w v0 h h1)
            · exact Or.inl (hB w u0 h h0)
            · exact Or.inl (hB w u0 h h0)
          have red : ∀ w, P (eof Y w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hw
            rcases two w hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [if_pos h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hiu, red v hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [if_neg h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S Y (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, (key hz u0 hu0).1, (key hz v0 hv0).1, ?_, ?_, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D S Y gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S Y gs).card + 1 ≤ (D S Y (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S Y gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono S Y gs g)
        omega

theorem row_bound {n : ℕ} (S Y : Finset (Fin n)) (gs : List Gate) (out : ℕ)
    (hdis : Disjoint Y S)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hZ : val gs (Zof S) out = false)
    (hE : ∀ p ∈ S, val gs (eof Y p) out = true) : S.card ≤ (D S Y gs).card + 1 := by
  classical
  obtain ⟨l,hi,hs⟩ := main_inv S Y hdis gs hg
  have hc : (S.image l).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    exact (hi out u v hZ (hE u hu) (hE v hv)).2
  omega

end PEqualNP.Outside.L_meta_988_aux
namespace PEqualNP.Outside.L_meta_988_aux
open CircuitLowerBounds
theorem point_mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ q, x q = true → y q = true) :
    ∀ j, val gs x j = true → val gs y j = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro j h
    rw [val_nil] at h ⊢
    split at h <;> simp_all
  | append_singleton gs g ih =>
    have hi := ih (fun g hg' => hg g (List.mem_append_left _ hg'))
    intro j h
    rw [val_snoc] at h ⊢
    by_cases he : j = n + gs.length
    · simp only [he,ite_true] at h ⊢
      obtain hor | hor := (hg g (by simp)).1
      · simp [hor,GateOp.eval] at h ⊢
        exact fun a ha => hi a (h a ha)
      · simp [hor,GateOp.eval] at h ⊢
        obtain ⟨a,ha,hw⟩ := h
        exact ⟨_,ha,hi a hw⟩
    · simpa only [if_neg he] using hi j (by simpa only [if_neg he] using h)
theorem count_split {m : ℕ} (G : Finset ℕ) (A : Fin m → Finset ℕ) (cap : ℕ)
    (inside : ∀ i, A i ⊆ G) (limit : ∀ z ∈ G, (Finset.univ.filter fun i => z ∈ A i).card ≤ cap) :
    ∑ i, (A i).card ≤ cap * G.card := by
  classical
  have hc (i : Fin m) : (A i).card = ∑ z ∈ G, (if z ∈ A i then 1 else 0) := by
    rw [Finset.sum_boole]
    congr 1
    ext z
    simp [and_iff_right_of_imp (fun hz => inside i hz)]
  calc
    _ = ∑ i, ∑ z ∈ G, (if z ∈ A i then 1 else 0) := Finset.sum_congr rfl (fun i _ => hc i)
    _ = ∑ z ∈ G, (Finset.univ.filter fun i => z ∈ A i).card := by
      rw [Finset.sum_comm]
      simp
    _ ≤ ∑ _ ∈ G, cap := Finset.sum_le_sum limit
    _ = _ := by simp [Nat.mul_comm]
end PEqualNP.Outside.L_meta_988_aux
open PEqualNP.Outside.L_meta_988_aux PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_988 : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  classical
  intro n m cap S Y C o hpair hdis hmono himplies hfire hmax
  let A (i : Fin m) := D (S i) (Y i) C.gates
  let G := Finset.Ico n (n+C.gates.length)
  have hsub (i : Fin m) : A i ⊆ G := Finset.filter_subset _ _
  have hrow (i : Fin m) : (S i).card ≤ (A i).card + 1 := by
    apply row_bound (S i) (Y i) C.gates (o i) (hdis i) hmono
    · by_contra! h
      have ht : val C.gates (Zof (S i)) (o i) = true := by
        cases he : val C.gates (Zof (S i)) (o i) <;> simp_all
      obtain ⟨p,hp,hz⟩ := himplies i _ ht
      simp [Zof,hp] at hz
    · exact hfire i
  have hlim (w : ℕ) (_ : w ∈ G) : (Finset.univ.filter fun i => w ∈ A i).card ≤ cap := by
    apply hmax
    intro i hi j hj hne hy
    obtain ⟨_,hzi,u,v,hu,hv,huv,htu,htv⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hi).2
    have hz := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).2).2.1
    have shared (t : Fin n) (ht : val C.gates (eof (Y i) t) w = true) : t ∈ S j := by
      by_contra hn
      have hle (p : Fin n) (h : eof (Y i) t p = true) : Zof (S j) p = true := by
        simp only [eof,decide_eq_true_eq] at h
        rcases h with h | rfl
        · exact decide_eq_true (Finset.disjoint_left.mp hy h)
        · exact decide_eq_true hn
      have hbad := point_mono C.gates hmono _ _ hle w ht
      rw [hz] at hbad
      contradiction
    have hs : ({u,v} : Finset (Fin n)) ⊆ S i ∩ S j := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact Finset.mem_inter.mpr ⟨hu,shared _ htu⟩
      · obtain rfl := Finset.mem_singleton.mp hp
        exact Finset.mem_inter.mpr ⟨hv,shared _ htv⟩
    have := Finset.card_le_card hs
    rw [Finset.card_pair huv] at this
    have := hpair i j hne
    omega
  have hc := count_split G A cap hsub hlim
  calc
    _ ≤ ∑ i, ((A i).card + 1) := Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ i, (A i).card) + m := by simp [Finset.sum_add_distrib]
    _ ≤ _ := by simpa [G] using Nat.add_le_add_right hc m

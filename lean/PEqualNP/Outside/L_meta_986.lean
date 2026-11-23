import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_986

open PEqualNP.CircuitLowerBounds

-- The partition count adapts johnpascoe43's proof of L-meta-529 to masked inputs.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mask {n : ℕ} (K : Finset (Fin n)) (x : Fin n → Bool) (v : Fin n) : Bool := x v && decide (v ∈ K)

def val {n : ℕ} (K : Finset (Fin n)) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn (mask K x))).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (K : Finset (Fin n)) (x : Fin n → Bool) (i : ℕ) :
    val K [] x i = if h : i < n then mask K x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (K : Finset (Fin n)) (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val K (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val K gs x j)
      else val K gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn (mask K x))).length = n + gs.length := by
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

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (K : Finset (Fin n)) (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val K gs (Zof S) i = false → val K gs (eof u) i = true → val K gs (eof v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (K : Finset (Fin n)) (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val K gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val K gs (eof u) i = true ∧ val K gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (K : Finset (Fin n)) (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt K S gs i

theorem D_mono {n : ℕ} (K : Finset (Fin n)) (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D K S gs ⊆ D K S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

theorem main_inv {n : ℕ} (K : Finset (Fin n)) (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv K S gs l ∧ S.card ≤ (S.image l).card + (D K S gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · have eu : (⟨i,h⟩ : Fin n) = u ∧ (⟨i,h⟩ : Fin n) ∈ K := by simpa [h,mask,eof] using hu
      have ev : (⟨i,h⟩ : Fin n) = v ∧ (⟨i,h⟩ : Fin n) ∈ K := by simpa [h,mask,eof] using hv
      have eS : (⟨i,h⟩ : Fin n) ∈ S := by
        simpa [h,mask,Zof,eu.2] using hz
      exact ⟨eu.1 ▸ eS,congrArg id (eu.1.symm.trans ev.1)⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val K gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val K (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val K (gs ++ [g]) x i = val K gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    -- facts about the new wire from the old invariant
    have key : P (Zof S) = false → ∀ u, P (eof u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val K gs x j) (Zof S) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val K gs (eof w) a = true, fun w => val K gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P (Zof S) = false ∧ ∃ u v, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
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
          have red : ∀ w, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
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
        have hNin : N ∈ D K S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, ?_, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D K S gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D K S gs).card + 1 ≤ (D K S (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono K S gs g hi
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
      · have := Finset.card_le_card (D_mono K S gs g)
        omega


def raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

-- Replacing the unique negation by a constant one preserves every positive singleton witness.
def force (g : Gate) : Gate :=
  match g.op with
  | .not => ⟨.and,[]⟩
  | _ => g

def valid (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem force_valid (g : Gate) (h : valid g) :
    ((force g).op = GateOp.and ∨ (force g).op = GateOp.or) ∧ (force g).inputs.length ≤ 2 := by
  rcases g with ⟨op,ins⟩
  rcases h with ⟨h,sz⟩
  change op = .and ∨ op = .or ∨ op = .not at h
  rcases h with rfl|rfl|rfl
  · exact ⟨Or.inl rfl,sz⟩
  · exact ⟨Or.inr rfl,sz⟩
  · exact ⟨Or.inl rfl,by change 0 ≤ 2; decide⟩

theorem fold_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem raw_take {n : ℕ} (gs : List Gate) (k : ℕ) (hk : k ≤ gs.length) (x : Fin n → Bool)
    (j : ℕ) (hj : j < n+k) : raw gs x j = raw (gs.take k) x j := by
  unfold raw
  conv_lhs => rw [← List.take_append_drop k gs,List.foldl_append]
  apply fold_old
  simpa [fold_length,Nat.min_eq_left hk] using hj

theorem raw_gate {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) (x : Fin n → Bool) :
    raw gs x (n+j) = gs[j].op.eval (gs[j].inputs.map fun i => raw (gs.take j) x i) := by
  rw [raw_take gs (j+1) (by omega) x (n+j) (by omega),List.take_succ_eq_append_getElem hj]
  unfold raw
  rw [List.foldl_append]
  let b := (gs.take j).foldl step (List.ofFn x)
  have hl : b.length = n+j := by simp [b,fold_length,Nat.min_eq_left (Nat.le_of_lt hj)]
  change (b ++ [_]).getD (n+j) false = _
  rw [←hl]
  simp

theorem gate_up (g : Gate) (hg : valid g) (a b : ℕ → Bool)
    (h : ∀ i, a i = true → b i = true) :
    g.op.eval (g.inputs.map a) = true → (force g).op.eval ((force g).inputs.map b) = true := by
  rcases g with ⟨op,ins⟩
  rcases hg with ⟨hop,sz⟩
  change op = .and ∨ op = .or ∨ op = .not at hop
  rcases hop with rfl|rfl|rfl
  · change (ins.map a).all id = true → (ins.map b).all id = true
    simp only [List.all_map,Function.id_comp,List.all_eq_true]
    exact fun ha i hi => h i (ha _ hi)
  · change (ins.map a).any id = true → (ins.map b).any id = true
    simp only [List.any_map,Function.id_comp,List.any_eq_true]
    rintro ⟨i,hi,ha⟩
    exact ⟨i,hi,h i ha⟩
  · intro _
    rfl

def Dom (a b : List Bool) : Prop :=
  a.length=b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

theorem step_up (g : Gate) (hg : valid g) (a b : List Bool) (hd : Dom a b) :
    Dom (step a g) (step b (force g)) := by
  obtain ⟨len,hd⟩ := hd
  refine ⟨by simp [step,len],?_⟩
  intro i
  rcases Nat.lt_trichotomy i a.length with lo|eq|hi
  · simpa only [step,List.getD_append _ _ _ _ lo,List.getD_append _ _ _ _ (len ▸ lo)] using hd i
  · have lastread (L : List Bool) (v : Bool) (j : ℕ) (hj : j=L.length) :
        (L++[v]).getD j false = v := by simp [hj,List.getD_eq_getElem?_getD]
    simp only [step,lastread a _ i eq,lastread b _ i (eq.trans len)]
    exact gate_up g hg _ _ hd
  · simp only [step,List.getD_eq_default _ _ (show (a ++ [_]).length ≤ i by simp; omega),
      List.getD_eq_default _ _ (show (b ++ [_]).length ≤ i by simp; omega)]
    simp

theorem fold_up (gs : List Gate) (a b : List Bool) (hg : ∀ g ∈ gs, valid g) (hd : Dom a b) :
    Dom (gs.foldl step a) ((gs.map force).foldl step b) := by
  induction gs generalizing a b with
  | nil => exact hd
  | cons g gs ih =>
    exact ih _ _ (fun k hk => hg k (by simp [hk])) (step_up g (hg _ (by simp)) _ _ hd)

theorem raw_up {n : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs, valid g) (x : Fin n → Bool) (i : ℕ) :
    raw gs x i = true → raw (gs.map force) x i = true :=
  (fold_up gs (List.ofFn x) _ hg ⟨rfl,fun _ h => h⟩).2 i

theorem forced_same {n : ℕ} (gs : List Gate) (x : Fin n → Bool)
    (hc : ∀ j (hj : j < gs.length), gs[j].op = GateOp.not →
      gs[j].op.eval (gs[j].inputs.map fun i => raw (gs.take j) x i) = true) :
    (gs.map force).foldl step (List.ofFn x) = gs.foldl step (List.ofFn x) := by
  have initial (k : ℕ) (hk : k ≤ gs.length) : ((gs.take k).map force).foldl step (List.ofFn x) =
      (gs.take k).foldl step (List.ofFn x) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have lt : k < gs.length := by omega
      rw [List.take_succ_eq_append_getElem lt,List.map_append,List.foldl_append,List.foldl_append,ih (by omega)]
      let w := (gs.take k).foldl step (List.ofFn x)
      change step w (force gs[k]) = step w gs[k]
      cases hop : gs[k].op with
      | not =>
        have hv := hc k lt hop
        change gs[k].op.eval (gs[k].inputs.map fun i => w.getD i false) = true at hv
        simp [step,force,hop,GateOp.eval] at hv ⊢
        exact hv
      | _ => simp [force,hop]
  simpa using initial gs.length (Nat.le_refl _)

theorem same_on_zero {n : ℕ} (gs : List Gate) (i0 : Fin gs.length) (hw : ℕ) (x : Fin n → Bool)
    (uniq : ∀ j : Fin gs.length, (gs.get j).op = GateOp.not → j=i0)
    (head : (gs.get i0).inputs.head? = some hw) (earlier : hw < n+i0.val)
    (zero : raw gs x hw = false) :
    ∀ i, raw (gs.map force) x i = raw gs x i := by
  have eq := forced_same gs x (by
    intro j hj hop
    have ji : j=i0.val := congrArg Fin.val (uniq ⟨j,hj⟩ hop)
    subst j
    have hef := (raw_take gs i0.val (Nat.le_of_lt i0.isLt) x hw earlier).symm.trans zero
    have hhead : gs[i0.val].inputs.head? = some hw := head
    cases hs : gs[i0.val].inputs with
    | nil => simp [hs] at hhead
    | cons k ks =>
      have kh : k = hw := by simpa [hs] using hhead
      simpa [hop,hs,kh,hef,GateOp.eval])
  intro i
  simp only [raw,eq]

theorem forced_wire {n : ℕ} (gs : List Gate) (i0 : Fin gs.length) (hop : (gs.get i0).op = GateOp.not)
    (x : Fin n → Bool) : raw (gs.map force) x (n+i0.val) = true := by
  rw [raw_gate _ _ (by simpa using i0.isLt)]
  simp [List.getElem_map,force,show gs[i0.val].op = GateOp.not from hop,GateOp.eval]

def rest {n : ℕ} (S T : Finset (Fin n)) (t0 : Fin n) := S \ T.erase t0

-- Rows keep the distinguished point exactly when it lies in their target set.
def allow {n : ℕ} (S T : Finset (Fin n)) (t0 : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun u => u ∉ T ∨ (u = t0 ∧ t0 ∈ S)

theorem kept {n : ℕ} {A B T : Finset (Fin n)} {u t0 : Fin n} (h : u ∈ rest A T t0)
    (ord : t0 ∈ A → t0 ∈ B) : u ∈ allow B T t0 := by
  obtain ⟨ha,hno⟩ := Finset.mem_sdiff.mp h
  by_cases ht : u ∈ T
  · have e : u = t0 := by
      by_contra ne
      exact hno (Finset.mem_erase.mpr ⟨ne,ht⟩)
    subst u
    simp [allow,ord ha]
  · simp [allow,ht]

theorem mask_eof {n : ℕ} (K : Finset (Fin n)) (u : Fin n) (hu : u ∈ K) :
    mask K (eof u) = eof u := by
  funext v
  by_cases e : v=u <;> simp [mask,eof,e,hu]

theorem zero_T {n : ℕ} (S T : Finset (Fin n)) (t0 v : Fin n) (hv : v ∈ T) :
    mask (allow S T t0) (Zof (rest S T t0)) v = false := by
  by_cases e : v=t0
  · subst v
    by_cases hs : t0 ∈ S <;> simp [mask,allow,Zof,rest,hv,hs]
  · simp [mask,allow,Zof,rest,hv,e]

theorem zero_S {n : ℕ} (S T : Finset (Fin n)) (t0 v : Fin n) (hv : v ∈ S) :
    mask (allow S T t0) (Zof (rest S T t0)) v = false := by
  by_cases h : v ∈ T
  · exact zero_T _ _ _ _ h
  · simp [mask,allow,Zof,rest,hv,h]

theorem disjoint_charges {n m : ℕ} (S : Fin m → Finset (Fin n)) (T : Finset (Fin n))
    (t0 : Fin n) (M : List Gate) (l : Fin m → Fin n → Fin n)
    (inv : ∀ w, Inv (allow (S w) T t0) (rest (S w) T t0) M (l w))
    (meet : ∀ a b : Fin m, a ≠ b → (S a ∩ S b).card ≤ 1) :
    ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)), a ≠ b →
      Disjoint (D (allow (S a) T t0) (rest (S a) T t0) M)
               (D (allow (S b) T t0) (rest (S b) T t0) M) := by
  classical
  let R := fun w => rest (S w) T t0
  let K := fun w => allow (S w) T t0
  -- Compare the row with the smaller set of allowed singleton tests to the other row.
  have go (a b : Fin m) (ne : a ≠ b) (ord : t0 ∈ S a → t0 ∈ S b) (i : ℕ)
      (ha : i ∈ D (K a) (R a) M) (hb : i ∈ D (K b) (R b) M) : False := by
    obtain ⟨za,u,v,uv,pu,pv⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨zb,_⟩ := (Finset.mem_filter.mp hb).2
    have ua : u ∈ R a := (inv a i u u za pu pu).1
    have va : v ∈ R a := (inv a i v v za pv pv).1
    have transfer (p : Fin n) (hp : p ∈ R a) :
        val (K a) M (eof p) i = val (K b) M (eof p) i := by
      change raw M (mask (K a) (eof p)) i = raw M (mask (K b) (eof p)) i
      rw [mask_eof _ p (kept hp id),mask_eof _ p (kept hp ord)]
    have uq := (transfer u ua).symm.trans pu
    have vq := (transfer v va).symm.trans pv
    have ub := (inv b i u u zb uq uq).1
    have vb := (inv b i v v zb vq vq).1
    apply uv
    exact Finset.card_le_one.mp (meet a b ne) u
      (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp ua).1,(Finset.mem_sdiff.mp ub).1⟩) v
      (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp va).1,(Finset.mem_sdiff.mp vb).1⟩)
  intro a _ b _ ne
  apply Finset.disjoint_left.mpr
  intro i ha hb
  by_cases ord : t0 ∈ S a → t0 ∈ S b
  · exact go a b ne ord i ha hb
  · exact go b a ne.symm (by tauto) i hb ha

theorem incidence {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin n)) :
    ∑ s : Fin m, (S s ∩ U).card =
      ∑ u ∈ U, (Finset.univ.filter (fun s : Fin m => u ∈ S s)).card := by
  classical
  calc
    _ = ∑ s : Fin m, ∑ u ∈ U, if u ∈ S s then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.sum_filter]
      simp [Finset.filter_mem_eq_inter,Finset.inter_comm]
    _ = ∑ u ∈ U, ∑ s : Fin m, if u ∈ S s then 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [← Finset.sum_filter]
      simp

end PEqualNP.Outside.L_meta_986

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_986 in
theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  intro n m S gates out i0 hw T t0 _ meet legal uniq notGate head earlier correct clause _ _
  let U := T.erase t0
  let R := fun w => rest (S w) T t0
  let K := fun w => allow (S w) T t0
  let M := gates.map force
  have mono : ∀ g ∈ M, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨src,hs,rfl⟩ := List.mem_map.mp hg
    exact force_valid src (legal src hs)
  -- On each zero input every point of T is absent, so the replacement preserves that output.
  have zero (w : Fin m) : val (K w) M (Zof (R w)) (out w) = false := by
    let x := mask (K w) (Zof (R w))
    have hx : raw gates x hw = false := clause x (fun v hv => zero_T (S w) T t0 v hv)
    have eq := same_on_zero gates i0 hw x uniq head earlier hx (out w)
    have outEq : raw gates x (out w) = decide (∃ v ∈ S w, x v = true) := correct w x
    have none : ¬ ∃ v ∈ S w, x v = true := by
      rintro ⟨v,hv,p⟩
      have z : x v = false := zero_S (S w) T t0 v hv
      rw [z] at p
      contradiction
    change raw M x (out w) = false
    simpa only [M,none,decide_false] using eq.trans outEq
  have single (w : Fin m) (u : Fin n) (hr : u ∈ R w) : val (K w) M (eof u) (out w) = true := by
    change raw M (mask (K w) (eof u)) (out w) = true
    rw [mask_eof _ u (kept hr id)]
    apply raw_up gates legal
    have h : raw gates (eof u) (out w) = _ := correct w (eof u)
    rw [h,decide_eq_true_eq]
    exact ⟨u,(Finset.mem_sdiff.mp hr).1,by simp [eof]⟩
  choose l inv count using fun w => main_inv (K w) (R w) M mono
  let C := fun w => D (K w) (R w) M
  have per (w : Fin m) : (R w).card - 1 ≤ (C w).card := by
    have one : ((R w).image (l w)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
      exact (inv w (out w) u v (zero w) (single w u hu) (single w v hv)).2
    have h := count w
    change (R w).card ≤ ((R w).image (l w)).card + (C w).card at h
    omega
  have disjoint := disjoint_charges S T t0 M l inv meet
  have summed : (∑ w, ((R w).card - 1)) ≤ (Finset.univ.biUnion C).card := by
    calc
      _ ≤ ∑ w, (C w).card := Finset.sum_le_sum (fun w _ => per w)
      _ = _ := (Finset.card_biUnion disjoint).symm
  let I := Finset.Ico n (n+gates.length)
  have contains : n+i0.val ∈ I := Finset.mem_Ico.mpr ⟨by omega,by have z:=i0.isLt; omega⟩
  -- The constant gate cannot belong to a charged set, as a charged wire must be false on its zero input.
  have all : Finset.univ.biUnion C ⊆ I.erase (n+i0.val) := by
    intro i hi
    obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨inside,hcnt⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_erase.mpr
    refine ⟨?_,?_⟩
    · intro eq
      have z := hcnt.1
      change raw M (mask (K w) (Zof (R w))) i = false at z
      rw [eq,forced_wire gates i0 notGate] at z
      contradiction
    · simpa [I,M] using inside
  have limited := summed.trans (Finset.card_le_card all)
  have miss := Finset.card_erase_of_mem contains
  have sz : I.card = gates.length := by simp [I]
  have lower (w : Fin m) : (S w).card - 1 ≤ ((R w).card - 1) + (S w ∩ U).card := by
    have split := Finset.card_sdiff_add_card_inter (S w) U
    change (R w).card + (S w ∩ U).card = (S w).card at split
    omega
  have agg := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun w _ => lower w)
  rw [Finset.sum_add_distrib,incidence] at agg
  change 1 + (∑ w : Fin m, ((S w).card - 1)) ≤ gates.length +
    ∑ u ∈ U, (Finset.univ.filter (fun w : Fin m => u ∈ S w)).card
  have nonempty := i0.isLt
  omega

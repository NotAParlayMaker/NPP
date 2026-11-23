import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_726

-- Wire representation and extension follow L-meta-669.

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [ite_eq_left ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [ite_eq_right ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, ite_eq_right hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, Or.inl rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, ite_eq_left rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, Or.inr rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, ite_eq_left rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

lemma input_value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (v : Fin n) :
    (W gs x).getD v.val false = x v := by
  induction gs using List.reverseRecOn with
  | nil =>
    change (List.ofFn x).getD v.val false = _
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  | append_singleton gs g ih =>
    rw [W_val, ite_eq_right (by have := v.isLt; omega), ih]

lemma fixed_gate {n : ℕ} (old new : List Gate) (v : Fin n) (bit : Bool)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or)
    (hlen : l.length ≤ 2) (reads : v.val ∈ l)
    (h : ∀ t, Rep new (fun x => (W old (Function.update x v bit)).getD t false)) :
    Rep new (fun x => op.eval (l.map fun i => (W old (Function.update x v bit)).getD i false)) := by
  have hv (x : Fin n → Bool) : (W old (Function.update x v bit)).getD v.val false = bit := by
    rw [input_value, Function.update_self]
  rcases l with _ | ⟨a, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩
  · simp at reads
  · rcases hop with rfl | rfl <;> exact rep_congr (fun x => by simp [GateOp.eval]) (h a)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at reads
    rcases reads with rfl | rfl <;> cases bit <;> rcases hop with rfl | rfl
    all_goals simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      List.any_cons, List.any_nil, id_eq, hv, Bool.and_false, Bool.and_true, Bool.false_and,
      Bool.true_and, Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or]
    all_goals first | exact h _ | exact Or.inl ⟨_, fun _ => rfl⟩
  · simp only [List.length_cons] at hlen
    omega

def Invariant {n : ℕ} (v : Fin n) (bit : Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧
    new.length + old.countP (fun g => decide (v.val ∈ g.inputs)) ≤ old.length ∧
    ∀ t, Rep new (fun x => (W old (Function.update x v bit)).getD t false)

lemma extend {n : ℕ} (v : Fin n) (bit : Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (ih : Invariant v bit old) : Invariant v bit (old ++ [g]) := by
  obtain ⟨new, hfan, hsize, hrep⟩ := ih
  have next : ∃ new', Ext new new' ∧ (v.val ∈ g.inputs → new' = new) ∧
      Rep new' (fun x => g.op.eval (g.inputs.map fun i =>
        (W old (Function.update x v bit)).getD i false)) := by
    by_cases h : v.val ∈ g.inputs
    · exact ⟨new, Or.inl rfl, fun _ => rfl, fixed_gate old new v bit _ _ hop hlen h hrep⟩
    · obtain ⟨out, he, hr⟩ := gate_rep (fun x => Function.update x v bit) old new _ _ hop hlen hrep
      exact ⟨out, he, fun hm => (h hm).elim, hr⟩
  obtain ⟨out, he, unchanged, hr⟩ := next
  refine ⟨out, ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · exact (List.mem_singleton.mp hq) ▸ hk
  · by_cases h : v.val ∈ g.inputs
    · rw [unchanged h]
      simp [List.countP_append, h, ← Nat.add_assoc, hsize]
    · rcases he with rfl | ⟨k, rfl, _⟩ <;> simp [List.countP_append, h] <;> omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by rw [W_val, ite_eq_left ht]) hr
    · exact rep_congr (fun x => by rw [W_val, ite_eq_right ht]) (rep_mono he _ (hrep t))

lemma build {n : ℕ} (v : Fin n) (bit : Bool) (gs : List Gate)
    (mono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Invariant v bit gs := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], by simp, by simp, rep_input (fun x => Function.update x v bit) ?_⟩
    intro i
    by_cases hi : i = v
    · subst i
      exact Or.inl ⟨bit, fun x => Function.update_self ..⟩
    · exact Or.inr (fun x => Function.update_of_ne hi ..)
  | append_singleton gs g ih =>
    have hg := mono g (by simp)
    exact extend v bit gs g hg.1 hg.2 (ih (fun k hk => mono k (by simp [hk])))

lemma reader_count {n : ℕ} (v : Fin n) (gs : List Gate) :
    gs.countP (fun g => decide (v.val ∈ g.inputs)) =
      (Finset.univ.filter (fun i : Fin gs.length => v.val ∈ (gs.get i).inputs)).card := by
  let vec : List.Vector Gate gs.length := ⟨gs, rfl⟩
  calc
    _ = (Finset.univ.filter (fun i : Fin gs.length =>
      decide (v.val ∈ (gs.get i).inputs) = true)).card :=
      List.Vector.countP_toList (fun g : Gate => decide (v.val ∈ g.inputs)) vec
    _ = _ := by congr 1 <;> ext i <;> simp

end PEqualNP.Outside.L_meta_726

open PEqualNP.Outside.L_meta_726 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_726 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool), PEqualNP.MetaComplexity.Monotone2 C → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + (Finset.univ.filter (fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs)).card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b)) := by
  intro n C v bit hmono hfalse
  obtain ⟨gs, fan, bound, represents⟩ := build v bit C.gates (fun g hg =>
    ⟨(hmono g hg).1, (hmono g hg).2⟩)
  rw [reader_count] at bound
  have output : ∃ o : ℕ, ∀ x : Fin n → Bool, (W gs x).getD o false =
      C.eval (List.ofFn (Function.update x v bit)) := by
    rcases represents C.output with ⟨val, eq⟩ | ⟨o, _, eq⟩
    · obtain ⟨y, hy⟩ := hfalse
      have hc : val = false := (eq y).symm.trans hy
      refine ⟨n + gs.length, fun x => ?_⟩
      rw [List.getD_eq_default _ _ (by rw [W_len])]
      exact hc.symm.trans (eq x).symm
    · exact ⟨o, eq⟩
  obtain ⟨o, ho⟩ := output
  exact ⟨⟨gs, o⟩, fun g hg => ⟨(fan g hg).1, (fan g hg).2.le⟩, bound, ho⟩

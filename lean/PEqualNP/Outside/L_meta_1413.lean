import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1413

open PEqualNP.CircuitLowerBounds

def ValidOp (op : GateOp) : Prop :=
  op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not

def ValidGate (g : Gate) : Prop :=
  ValidOp g.op ∧ g.inputs.length ≤ 2

def ValidCircuit (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, ValidGate g

def Computes (n : ℕ) (C : Circuit) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

def HasCircuitSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, ValidCircuit C ∧ C.size ≤ s ∧ Computes n C f

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wireVal (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def effInputs (g : Gate) (limit : ℕ) : List ℕ :=
  (match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs).filter (· < limit)

def IsConstOn (C : Circuit) (n : ℕ) (P : (Fin n → Bool) → Prop) (w : ℕ) : Prop :=
  ∀ y z : Fin n → Bool, P y → P z → wireVal C n y w = wireVal C n z w

def IsElim (C : Circuit) (n : ℕ) (P : (Fin n → Bool) → Prop) (j : ℕ) : Prop :=
  IsConstOn C n P (n + j) ∨
    ∃ w < n + j, ∀ u : Fin n → Bool, P u → wireVal C n u (n + j) = wireVal C n u w

noncomputable def elimSet (C : Circuit) (n : ℕ) (P : (Fin n → Bool) → Prop) : Finset (Fin C.size) := by
  classical
  exact Finset.univ.filter fun j => IsElim C n P j.val

def IsDead (C : Circuit) (n : ℕ) (j : ℕ) : Prop :=
  C.output ≠ n + j ∧
    ∀ k : ℕ, (hk : k < C.size) → j < k → n + j ∉ effInputs (C.gates[k]'hk) (n + k)

-- ============================================================================
-- Part 1: Basic wire evaluation lemmas
-- ============================================================================

theorem getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem foldl_step_len (gs : List Gate) (W : List Bool) :
    (gs.foldl step W).length = W.length + gs.length := by
  induction gs generalizing W with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [step]
    omega

theorem foldl_step_prefix (gs : List Gate) (W : List Bool) (i : ℕ) (hi : i < W.length) :
    (gs.foldl step W).getD i false = W.getD i false := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (step W g).length := by simp [step]; omega
    rw [ih (step W g) hi']
    simp only [step]
    exact List.getD_append _ _ _ _ hi

theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

theorem wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  rw [wires_eq_foldl, foldl_step_len]
  rfl

theorem wireVal_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    wireVal C n x i.val = x i := by
  unfold wireVal
  rw [wires_eq_foldl, foldl_step_prefix _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem wireVal_oob (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : n + C.size ≤ w) :
    wireVal C n x w = false := by
  unfold wireVal
  apply List.getD_eq_default
  rw [wires_len]
  simp
  omega

theorem wireVal_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (hj : j < C.size) :
    wireVal C n x (n + j) =
      (C.gates[j]'hj).op.eval
        ((C.gates[j]'hj).inputs.map fun i => if i < n + j then wireVal C n x i else false) := by
  unfold wireVal
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]'hj] ++ C.gates.drop (j + 1) := by
    have h1 := (List.take_append_drop j C.gates).symm
    have h2 : C.gates.drop j = C.gates[j]'hj :: C.gates.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1
  set Wj := (C.gates.take j).foldl step (List.ofFn x) with hWj_def
  have hWj_len : Wj.length = n + j := by
    rw [hWj_def, foldl_step_len, List.length_ofFn, List.length_take]
    have : j ≤ C.gates.length := Nat.le_of_lt hj
    omega
  have hW_eq : C.wires (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step Wj (C.gates[j]'hj)) := by
    calc
      C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
      _ = (C.gates.take j ++ [C.gates[j]'hj] ++ C.gates.drop (j + 1)).foldl step (List.ofFn x) :=
            congrArg (fun gs => gs.foldl step (List.ofFn x)) hsplit
      _ = (C.gates.drop (j + 1)).foldl step (step Wj (C.gates[j]'hj)) := by
            rw [List.foldl_append, List.foldl_append]
            rfl
  have hstep_len : (step Wj (C.gates[j]'hj)).length = n + j + 1 := by
    simp only [step, List.length_append, List.length_singleton, hWj_len]
  have hpref_all : ∀ i < n + j, Wj.getD i false = (C.wires (List.ofFn x)).getD i false := by
    intro i hi
    symm
    rw [hW_eq, foldl_step_prefix _ _ _ (by omega)]
    simp only [step]
    rw [List.getD_append _ _ _ _ (by omega)]
  have hmap : ((C.gates[j]'hj).inputs.map fun i => Wj.getD i false) =
      ((C.gates[j]'hj).inputs.map fun i =>
        if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < n + j
    · simp only [hi, ite_true]
      exact hpref_all i hi
    · simp only [hi, ite_false]
      exact List.getD_eq_default _ _ (by omega)
  conv_lhs =>
    rw [hW_eq, foldl_step_prefix _ _ _ (by omega)]
    simp only [step]
    rw [← hWj_len, getD_snoc_eq, hmap]

theorem wireVal_gate_congr (C : Circuit) (n : ℕ) (x y : Fin n → Bool) (j : ℕ) (hj : j < C.size)
    (hvalid : ValidOp (C.gates[j]'hj).op)
    (heq : ∀ w ∈ effInputs (C.gates[j]'hj) (n + j), wireVal C n x w = wireVal C n y w) :
    wireVal C n x (n + j) = wireVal C n y (n + j) := by
  rw [wireVal_gate C n x j hj, wireVal_gate C n y j hj]
  set g := C.gates[j]'hj
  rcases hvalid with hop | hop | hop
  · rw [hop]
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hlt : i < n + j
    · simp only [hlt, ite_true]
      apply heq
      simp [effInputs, hop, hi, hlt]
    · simp only [hlt, ite_false]
  · rw [hop]
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hlt : i < n + j
    · simp only [hlt, ite_true]
      apply heq
      simp [effInputs, hop, hi, hlt]
    · simp only [hlt, ite_false]
  · rw [hop]
    simp only [GateOp.eval]
    cases h_in : g.inputs with
    | nil => rfl
    | cons a rest =>
      simp only [List.map_cons, List.headD_cons]
      by_cases hlt : a < n + j
      · simp only [hlt, ite_true]
        congr 1
        apply heq
        simp [effInputs, hop, h_in, hlt]
      · simp only [hlt, ite_false]

-- ============================================================================
-- Part 2: Non-eliminated gate structure and elimination lemma
-- ============================================================================

theorem not_elim_gate_shape (C : Circuit) (n : ℕ) (P : (Fin n → Bool) → Prop)
    (hC : ValidCircuit C) (j : ℕ) (hj : j < C.size) (hnot : ¬ IsElim C n P j) :
    (∃ y0 : Fin n → Bool, P y0) ∧
    match (C.gates[j]'hj).op with
    | GateOp.not =>
        ∃ a < n + j, (C.gates[j]'hj).inputs.head? = some a ∧
          effInputs (C.gates[j]'hj) (n + j) = [a] ∧
          ¬ IsConstOn C n P a ∧
          ∀ x, wireVal C n x (n + j) = !(wireVal C n x a)
    | GateOp.and =>
        ∃ a b : ℕ, a < n + j ∧ b < n + j ∧ a ≠ b ∧
          (C.gates[j]'hj).inputs = [a, b] ∧
          effInputs (C.gates[j]'hj) (n + j) = [a, b] ∧
          ¬ IsConstOn C n P a ∧ ¬ IsConstOn C n P b ∧
          ∀ x, wireVal C n x (n + j) = (wireVal C n x a && wireVal C n x b)
    | GateOp.or =>
        ∃ a b : ℕ, a < n + j ∧ b < n + j ∧ a ≠ b ∧
          (C.gates[j]'hj).inputs = [a, b] ∧
          effInputs (C.gates[j]'hj) (n + j) = [a, b] ∧
          ¬ IsConstOn C n P a ∧ ¬ IsConstOn C n P b ∧
          ∀ x, wireVal C n x (n + j) = (wireVal C n x a || wireVal C n x b)
    | _ => False := by
  have hex : ∃ y0 : Fin n → Bool, P y0 := by
    by_contra hne
    push Not at hne
    apply hnot
    exact Or.inl fun y _ hy => False.elim (hne y hy)
  obtain ⟨y0, hy0⟩ := hex
  refine ⟨⟨y0, hy0⟩, ?_⟩
  have hvg : ValidGate (C.gates[j]'hj) := hC _ (List.getElem_mem hj)
  obtain ⟨hop, hlen⟩ := hvg
  set g := C.gates[j]'hj with hg_def
  rcases hop with h_op | h_op | h_op
  · rw [h_op]
    match hin : g.inputs with
    | [] =>
      exfalso; apply hnot; left; intro y z _ _
      rw [wireVal_gate C n y j hj, wireVal_gate C n z j hj, ← hg_def, h_op, hin]
      rfl
    | [a] =>
      exfalso; apply hnot
      by_cases ha : a < n + j
      · right; refine ⟨a, ha, fun u _ => ?_⟩
        rw [wireVal_gate C n u j hj, ← hg_def, h_op, hin]
        simp [GateOp.eval, ha]
      · left; intro y z _ _
        rw [wireVal_gate C n y j hj, wireVal_gate C n z j hj, ← hg_def, h_op, hin]
        simp [GateOp.eval, ha]
    | [a, b] =>
      have ha : a < n + j := by
        by_contra hna; apply hnot; left; intro y z _ _
        rw [wireVal_gate C n y j hj, wireVal_gate C n z j hj, ← hg_def, h_op, hin]
        simp [GateOp.eval, hna]
      have hb : b < n + j := by
        by_contra hnb; apply hnot; left; intro y z _ _
        rw [wireVal_gate C n y j hj, wireVal_gate C n z j hj, ← hg_def, h_op, hin]
        simp [GateOp.eval, hnb]
      have heval : ∀ x, wireVal C n x (n + j) = (wireVal C n x a && wireVal C n x b) := by
        intro x
        rw [wireVal_gate C n x j hj, ← hg_def, h_op, hin]
        simp [GateOp.eval, ha, hb]
      have hab : a ≠ b := by
        intro heq; subst heq; apply hnot; right; refine ⟨a, ha, fun u _ => ?_⟩
        rw [heval u]; simp
      have hnca : ¬ IsConstOn C n P a := by
        intro hca
        cases hval : wireVal C n y0 a
        · apply hnot; left; intro y z hy hz
          rw [heval y, heval z, hca y y0 hy hy0, hca z y0 hz hy0, hval]; simp
        · apply hnot; right; refine ⟨b, hb, fun u hu => ?_⟩
          rw [heval u, hca u y0 hu hy0, hval]; simp
      have hncb : ¬ IsConstOn C n P b := by
        intro hcb
        cases hval : wireVal C n y0 b
        · apply hnot; left; intro y z hy hz
          rw [heval y, heval z, hcb y y0 hy hy0, hcb z y0 hz hy0, hval]; simp
        · apply hnot; right; refine ⟨a, ha, fun u hu => ?_⟩
          rw [heval u, hcb u y0 hu hy0, hval]; simp
      exact ⟨a, b, ha, hb, hab, rfl, by simp [effInputs, h_op, hin, ha, hb], hnca, hncb, heval⟩
    | _ :: _ :: _ :: _ =>
      rw [hin] at hlen; simp at hlen
  · rw [h_op]
    match hin : g.inputs with
    | [] =>
      exfalso; apply hnot; left; intro y z _ _
      rw [wireVal_gate C n y j hj, wireVal_gate C n z j hj, ← hg_def, h_op, hin]
      rfl
    | [a] =>
      exfalso; apply hnot
      by_cases ha : a < n + j
      · right; refine ⟨a, ha, fun u _ => ?_⟩
        rw [wireVal_gate C n u j hj, ← hg_def, h_op, hin]
        simp [GateOp.eval, ha]
      · left; intro y z _ _
        rw [wireVal_gate C n y j hj, wireVal_gate C n z j hj, ← hg_def, h_op, hin]
        simp [GateOp.eval, ha]
    | [a, b] =>
      have ha : a < n + j := by
        by_contra hna; apply hnot
        by_cases hb : b < n + j
        · right; refine ⟨b, hb, fun u _ => ?_⟩
          rw [wireVal_gate C n u j hj, ← hg_def, h_op, hin]
          simp [GateOp.eval, hna, hb]
        · left; intro y z _ _
          rw [wireVal_gate C n y j hj, wireVal_gate C n z j hj, ← hg_def, h_op, hin]
          simp [GateOp.eval, hna, hb]
      have hb : b < n + j := by
        by_contra hnb; apply hnot; right; refine ⟨a, ha, fun u _ => ?_⟩
        rw [wireVal_gate C n u j hj, ← hg_def, h_op, hin]
        simp [GateOp.eval, ha, hnb]
      have heval : ∀ x, wireVal C n x (n + j) = (wireVal C n x a || wireVal C n x b) := by
        intro x
        rw [wireVal_gate C n x j hj, ← hg_def, h_op, hin]
        simp [GateOp.eval, ha, hb]
      have hab : a ≠ b := by
        intro heq; subst heq; apply hnot; right; refine ⟨a, ha, fun u _ => ?_⟩
        rw [heval u]; simp
      have hnca : ¬ IsConstOn C n P a := by
        intro hca
        cases hval : wireVal C n y0 a
        · apply hnot; right; refine ⟨b, hb, fun u hu => ?_⟩
          rw [heval u, hca u y0 hu hy0, hval]; simp
        · apply hnot; left; intro y z hy hz
          rw [heval y, heval z, hca y y0 hy hy0, hca z y0 hz hy0, hval]; simp
      have hncb : ¬ IsConstOn C n P b := by
        intro hcb
        cases hval : wireVal C n y0 b
        · apply hnot; right; refine ⟨a, ha, fun u hu => ?_⟩
          rw [heval u, hcb u y0 hu hy0, hval]; simp
        · apply hnot; left; intro y z hy hz
          rw [heval y, heval z, hcb y y0 hy hy0, hcb z y0 hz hy0, hval]; simp
      exact ⟨a, b, ha, hb, hab, rfl, by simp [effInputs, h_op, hin, ha, hb], hnca, hncb, heval⟩
    | _ :: _ :: _ :: _ =>
      rw [hin] at hlen; simp at hlen
  · rw [h_op]
    match hin : g.inputs with
    | [] =>
      exfalso; apply hnot; left; intro y z _ _
      rw [wireVal_gate C n y j hj, wireVal_gate C n z j hj, ← hg_def, h_op, hin]
      rfl
    | a :: rest =>
      have ha : a < n + j := by
        by_contra hna; apply hnot; left; intro y z _ _
        rw [wireVal_gate C n y j hj, wireVal_gate C n z j hj, ← hg_def, h_op, hin]
        simp [GateOp.eval, hna]
      have heval : ∀ x, wireVal C n x (n + j) = !(wireVal C n x a) := by
        intro x
        rw [wireVal_gate C n x j hj, ← hg_def, h_op, hin]
        simp [GateOp.eval, ha]
      have hnca : ¬ IsConstOn C n P a := by
        intro hca; apply hnot; left; intro y z hy hz
        rw [heval y, heval z, hca y z hy hz]
      exact ⟨a, ha, rfl, by simp [effInputs, h_op, hin, ha], hnca, heval⟩

theorem elim_of_const_effInput (C : Circuit) (n : ℕ) (P : (Fin n → Bool) → Prop)
    (hC : ValidCircuit C) (j : ℕ) (hj : j < C.size) (w : ℕ)
    (hw : w ∈ effInputs (C.gates[j]'hj) (n + j)) (hconst : IsConstOn C n P w) :
    IsElim C n P j := by
  by_contra hnot
  have hsh := (not_elim_gate_shape C n P hC j hj hnot).2
  have hop := (hC _ (List.getElem_mem hj)).1
  rcases hop with h_op | h_op | h_op
  · rw [h_op] at hsh
    obtain ⟨a, b, _, _, _, _, heff, hnca, hncb, _⟩ := hsh
    rw [heff] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hnca hconst
    · exact hncb hconst
  · rw [h_op] at hsh
    obtain ⟨a, b, _, _, _, _, heff, hnca, hncb, _⟩ := hsh
    rw [heff] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hnca hconst
    · exact hncb hconst
  · rw [h_op] at hsh
    obtain ⟨a, _, _, heff, hnca, _⟩ := hsh
    rw [heff] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    exact hnca hconst

theorem rep_exists (C : Circuit) (n : ℕ) (P : (Fin n → Bool) → Prop) :
    ∀ w : ℕ, w < n + C.size → ¬ IsConstOn C n P w →
      ∃ r ≤ w, (r < n ∨ ∃ j : Fin C.size, r = n + j.val ∧ ¬ IsElim C n P j.val) ∧
        ∀ u : Fin n → Bool, P u → wireVal C n u r = wireVal C n u w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hnc
    by_cases hlt : w < n
    · exact ⟨w, le_rfl, Or.inl hlt, fun _ _ => rfl⟩
    · set j : Fin C.size := ⟨w - n, by omega⟩
      have hwj : w = n + j.val := by simp [j]; omega
      by_cases hel : IsElim C n P j.val
      · rcases hel with hc | ⟨w', hw', heq⟩
        · rw [← hwj] at hc
          exact absurd hc hnc
        · have hnc' : ¬ IsConstOn C n P w' := by
            intro hc'
            apply hnc
            intro y z hy hz
            rw [hwj, heq y hy, heq z hz]
            exact hc' y z hy hz
          obtain ⟨r, hrw', hrkind, hreq⟩ := ih w' (by omega) (by omega) hnc'
          refine ⟨r, by omega, hrkind, fun u hu => ?_⟩
          rw [hreq u hu, hwj, heq u hu]
      · exact ⟨w, le_rfl, Or.inr ⟨j, hwj, hel⟩, fun _ _ => rfl⟩

theorem wireVal_indep_of_unused (C : Circuit) (n : ℕ) (hC : ValidCircuit C)
    (p : Fin n) (hunused : ∀ k : ℕ, (hk : k < C.size) → p.val ∉ effInputs (C.gates[k]'hk) (n + k))
    (x y : Fin n → Bool) (hagree : ∀ i : Fin n, i ≠ p → x i = y i) :
    ∀ w : ℕ, w ≠ p.val → wireVal C n x w = wireVal C n y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hne
    by_cases hw : w < n
    · have h1 := wireVal_input C n x ⟨w, hw⟩
      have h2 := wireVal_input C n y ⟨w, hw⟩
      dsimp at h1 h2
      rw [h1, h2]
      exact hagree ⟨w, hw⟩ (by intro heq; apply hne; exact congrArg Fin.val heq)
    · by_cases hlt : w < n + C.size
      · set j := w - n
        have hj : j < C.size := by omega
        have hwj : w = n + j := by omega
        rw [hwj]
        apply wireVal_gate_congr C n x y j hj (hC _ (List.getElem_mem hj)).1
        intro u hu
        have hult : u < n + j := by
          unfold effInputs at hu
          exact (List.mem_filter.mp hu).2 |> of_decide_eq_true
        have hune : u ≠ p.val := fun heq => hunused j hj (heq ▸ hu)
        exact ih u (by omega) hune
      · rw [wireVal_oob C n x w (by omega), wireVal_oob C n y w (by omega)]

theorem elim_circuit (C : Circuit) (n : ℕ) (P : (Fin n → Bool) → Prop)
    (hC : ValidCircuit C)
    (hnc_out : ∃ y z : Fin n → Bool, P y ∧ P z ∧ C.eval (List.ofFn y) ≠ C.eval (List.ofFn z)) :
    ∃ C' : Circuit, ValidCircuit C' ∧ C'.size = C.size - (elimSet C n P).card ∧
      (∀ u : Fin n → Bool, P u → C'.eval (List.ofFn u) = C.eval (List.ofFn u)) ∧
      (∀ p : Fin n, IsConstOn C n P p.val →
        C'.output ≠ p.val ∧
        ∀ k : ℕ, (hk : k < C'.size) → p.val ∉ effInputs (C'.gates[k]'hk) (n + k)) := by
  classical
  let S := elimSet C n P
  let kept : List (Fin C.size) := (List.finRange C.size).filter fun j => decide (¬ IsElim C n P j.val)
  have hkept_nodup : kept.Nodup := (List.nodup_finRange C.size).filter _
  have hkept_mem : ∀ j : Fin C.size, j ∈ kept ↔ ¬ IsElim C n P j.val := by
    intro j
    simp [kept]
  have hkept_sorted : kept.Pairwise (· < ·) := by
    apply List.Pairwise.filter
    exact List.pairwise_lt_finRange C.size
  have hkept_len : kept.length = C.size - S.card := by
    have h1 : kept.toFinset = Finset.univ.filter fun j : Fin C.size => ¬ IsElim C n P j.val := by
      ext j
      simp [hkept_mem]
    have h2 : kept.length = kept.toFinset.card := (List.toFinset_card_of_nodup hkept_nodup).symm
    have h3 : (Finset.univ.filter fun j : Fin C.size => ¬ IsElim C n P j.val).card + S.card = C.size := by
      have hdisj : Disjoint (Finset.univ.filter fun j : Fin C.size => ¬ IsElim C n P j.val) S := by
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, S, elimSet] at hj1 hj2
        exact hj1 hj2
      have hunion : (Finset.univ.filter fun j : Fin C.size => ¬ IsElim C n P j.val) ∪ S = Finset.univ := by
        ext j
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, S, elimSet]
        by_cases h : IsElim C n P j.val
        · exact Or.inr h
        · exact Or.inl h
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    rw [h2, h1]
    omega
  let newIdx (w : ℕ) : ℕ :=
    if w < n then w
    else n + (Finset.univ.filter fun i : Fin C.size => i.val < w - n ∧ ¬ IsElim C n P i.val).card
  have hnewIdx_kept : ∀ (k : ℕ) (hk : k < kept.length),
      newIdx (n + (kept[k]'hk).val) = n + k := by
    intro k hk
    have hnotlt : ¬ (n + (kept[k]'hk).val < n) := by omega
    simp only [newIdx, hnotlt, ite_false]
    have hsub : n + (kept[k]'hk).val - n = (kept[k]'hk).val := by omega
    rw [hsub]
    congr 1
    have htake_nodup : (kept.take k).Nodup := hkept_nodup.sublist (List.take_sublist k kept)
    have htake_len : (kept.take k).length = k := by simp [Nat.le_of_lt hk]
    have hset_eq : (Finset.univ.filter fun i : Fin C.size =>
        i.val < (kept[k]'hk).val ∧ ¬ IsElim C n P i.val) = (kept.take k).toFinset := by
      ext i
      simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hilt, hnotel⟩
        have hmem : i ∈ kept := (hkept_mem i).mpr hnotel
        obtain ⟨m, hm, hmi⟩ := List.mem_iff_getElem.mp hmem
        have hmk : m < k := by
          by_contra hge
          have hkm : k ≤ m := by omega
          rcases eq_or_lt_of_le hkm with rfl | hlt'
          · rw [hmi] at hilt; exact Nat.lt_irrefl _ hilt
          · have hlt2 := (List.pairwise_iff_getElem.mp hkept_sorted) k m hk hm hlt'
            rw [hmi] at hlt2
            exact Nat.lt_asymm hilt hlt2
        rw [List.mem_iff_getElem]
        exact ⟨m, by rw [List.length_take]; omega, by simpa [List.getElem_take] using hmi⟩
      · intro hi
        obtain ⟨m, hm, hmi⟩ := List.mem_iff_getElem.mp hi
        have hmk : m < k := by rw [List.length_take] at hm; omega
        have hm_kept : m < kept.length := by omega
        have hget : kept[m]'hm_kept = i := by
          simpa [List.getElem_take] using hmi
        refine ⟨?_, (hkept_mem i).mp (hget ▸ List.getElem_mem hm_kept)⟩
        rw [← hget]
        exact (List.pairwise_iff_getElem.mp hkept_sorted) m k hm_kept hk hmk
    rw [hset_eq, List.toFinset_card_of_nodup htake_nodup, htake_len]
  have hnewIdx_lt : ∀ (r : ℕ) (k : ℕ) (hk : k < kept.length),
      r < n + (kept[k]'hk).val →
      (r < n ∨ ∃ j : Fin C.size, r = n + j.val ∧ ¬ IsElim C n P j.val) →
      newIdx r < n + k := by
    intro r k hk hr hkind
    rcases hkind with hrn | ⟨j, rfl, hnotel⟩
    · simp only [newIdx, hrn, ite_true]; omega
    · have hjmem : j ∈ kept := (hkept_mem j).mpr hnotel
      obtain ⟨m, hm, hmj⟩ := List.mem_iff_getElem.mp hjmem
      have hmk : m < k := by
        by_contra hge
        have hkm : k ≤ m := by omega
        rcases eq_or_lt_of_le hkm with rfl | hlt'
        · rw [hmj] at hr; omega
        · have hlt2 := (List.pairwise_iff_getElem.mp hkept_sorted) k m hk hm hlt'
          rw [hmj] at hlt2
          omega
      rw [← hmj, hnewIdx_kept m hm]
      omega
  -- Choose canonical representative for non-constant wires < n + C.size
  let rep (w : ℕ) : ℕ :=
    if h : w < n + C.size ∧ ¬ IsConstOn C n P w then
      Classical.choose (rep_exists C n P w h.1 h.2)
    else 0
  have hrep_spec : ∀ w, w < n + C.size → ¬ IsConstOn C n P w →
      rep w ≤ w ∧
      (rep w < n ∨ ∃ j : Fin C.size, rep w = n + j.val ∧ ¬ IsElim C n P j.val) ∧
      (∀ u : Fin n → Bool, P u → wireVal C n u (rep w) = wireVal C n u w) := by
    intro w hw hnc
    have hcond : w < n + C.size ∧ ¬ IsConstOn C n P w := ⟨hw, hnc⟩
    simp only [rep, hcond]
    exact Classical.choose_spec (rep_exists C n P w hw hnc)
  let canon (w : ℕ) : ℕ := newIdx (rep w)
  have hcanon_ne_const : ∀ (w : ℕ) (p : Fin n),
      w < n + C.size → ¬ IsConstOn C n P w → IsConstOn C n P p.val → canon w ≠ p.val := by
    intro w p hw hnc hpconst
    obtain ⟨_, hkind, heq⟩ := hrep_spec w hw hnc
    have hrep_ne : rep w ≠ p.val := by
      intro hpeq
      apply hnc
      intro y z hy hz
      rw [← heq y hy, ← heq z hz, hpeq]
      exact hpconst y z hy hz
    rcases hkind with hrn | ⟨j, hjr, _⟩
    · simp only [canon, newIdx, hrn, ite_true]
      exact hrep_ne
    · have hnotlt : ¬ (rep w < n) := by omega
      simp only [canon, newIdx, hnotlt, ite_false]
      have := p.isLt
      omega
  let mkGate (j : Fin C.size) : Gate :=
    let g := C.gates[j.val]'j.isLt
    let raw := match g.op with
      | GateOp.not => g.inputs.take 1
      | _ => g.inputs
    ⟨g.op, raw.map canon⟩
  let C' : Circuit := ⟨kept.map mkGate, canon C.output⟩
  have hC'_size : C'.size = C.size - S.card := by
    change (kept.map mkGate).length = C.size - S.card
    rw [List.length_map, hkept_len]
  have hC'_valid : ValidCircuit C' := by
    intro g' hg'
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg'
    have hvg := hC _ (List.getElem_mem j.isLt)
    have hlen : (C.gates[j.val]'j.isLt).inputs.length ≤ 2 := hvg.2
    refine ⟨hvg.1, ?_⟩
    simp only [mkGate, List.length_map]
    cases (C.gates[j.val]'j.isLt).op <;> simp [List.length_take] <;> omega
  have hC'_wire : ∀ (u : Fin n → Bool), P u →
      ∀ (k : ℕ) (hk : k < kept.length),
        wireVal C' n u (n + k) = wireVal C n u (n + (kept[k]'hk).val) := by
    intro u hu k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have hk' : k < C'.size := by
        change k < (kept.map mkGate).length
        rw [List.length_map]
        exact hk
      set j : Fin C.size := kept[k]'hk
      have hnotel : ¬ IsElim C n P j.val := (hkept_mem j).mp (List.getElem_mem hk)
      have hsh := (not_elim_gate_shape C n P hC j.val j.isLt hnotel).2
      have hgate_eq : C'.gates[k]'hk' = mkGate j := List.getElem_map _
      have hval_canon : ∀ a : ℕ, a < n + j.val → ¬ IsConstOn C n P a →
          canon a < n + k ∧ wireVal C' n u (canon a) = wireVal C n u a := by
        intro a ha hnca
        obtain ⟨hrle, hrkind, hreq⟩ := hrep_spec a (by omega) hnca
        have hlt : canon a < n + k := hnewIdx_lt (rep a) k hk (by omega) hrkind
        refine ⟨hlt, ?_⟩
        rcases hrkind with hrn | ⟨j0, hj0, hnotel0⟩
        · have hca : canon a = rep a := by simp [canon, newIdx, hrn]
          rw [hca]
          have h1 := wireVal_input C' n u ⟨rep a, hrn⟩
          have h2 := wireVal_input C n u ⟨rep a, hrn⟩
          dsimp at h1 h2
          rw [h1, ← h2, hreq u hu]
        · have hj0_mem : j0 ∈ kept := (hkept_mem j0).mpr hnotel0
          obtain ⟨m, hm, hmj0⟩ := List.mem_iff_getElem.mp hj0_mem
          have hca : canon a = n + m := by
            simp only [canon, hj0, ← hmj0]
            exact hnewIdx_kept m hm
          have hmk : m < k := by omega
          rw [hca, ih m hmk hm, hmj0, ← hj0, hreq u hu]
      have hop := (hC _ (List.getElem_mem j.isLt)).1
      rw [wireVal_gate C' n u k hk', hgate_eq]
      rcases hop with h_op | h_op | h_op
      · rw [h_op] at hsh
        obtain ⟨a, b, ha, hb, _, hin, _, hnca, hncb, heval⟩ := hsh
        obtain ⟨hca_lt, hca_val⟩ := hval_canon a ha hnca
        obtain ⟨hcb_lt, hcb_val⟩ := hval_canon b hb hncb
        simp only [mkGate, h_op, hin, List.map_cons, List.map_nil, GateOp.eval]
        simp only [hca_lt, hcb_lt, ite_true, hca_val, hcb_val, List.all_cons, List.all_nil, id_eq,
          Bool.and_true]
        exact (heval u).symm
      · rw [h_op] at hsh
        obtain ⟨a, b, ha, hb, _, hin, _, hnca, hncb, heval⟩ := hsh
        obtain ⟨hca_lt, hca_val⟩ := hval_canon a ha hnca
        obtain ⟨hcb_lt, hcb_val⟩ := hval_canon b hb hncb
        simp only [mkGate, h_op, hin, List.map_cons, List.map_nil, GateOp.eval]
        simp only [hca_lt, hcb_lt, ite_true, hca_val, hcb_val, List.any_cons, List.any_nil, id_eq,
          Bool.or_false]
        exact (heval u).symm
      · rw [h_op] at hsh
        obtain ⟨a, ha, hhead, _, hnca, heval⟩ := hsh
        obtain ⟨hca_lt, hca_val⟩ := hval_canon a ha hnca
        cases h_in : (C.gates[j.val]'j.isLt).inputs with
        | nil => rw [h_in] at hhead; simp at hhead
        | cons a0 rest =>
          rw [h_in] at hhead
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst hhead
          simp only [mkGate, h_op, h_in, List.take_succ_cons, List.take_zero, List.map_cons,
            List.map_nil, GateOp.eval, List.headD_cons]
          simp only [hca_lt, ite_true, hca_val]
          exact (heval u).symm
  have hout_lt : C.output < n + C.size := by
    by_contra hge
    obtain ⟨y, z, hy, hz, hne⟩ := hnc_out
    apply hne
    change wireVal C n y C.output = wireVal C n z C.output
    rw [wireVal_oob C n y C.output (by omega), wireVal_oob C n z C.output (by omega)]
  have hout_nc : ¬ IsConstOn C n P C.output := by
    intro hco
    obtain ⟨y, z, hy, hz, hne⟩ := hnc_out
    exact hne (hco y z hy hz)
  refine ⟨C', hC'_valid, hC'_size, ?_, ?_⟩
  · intro u hu
    change wireVal C' n u (canon C.output) = wireVal C n u C.output
    obtain ⟨_, hrkind, hreq⟩ := hrep_spec C.output hout_lt hout_nc
    rcases hrkind with hrn | ⟨j0, hj0, hnotel0⟩
    · have hca : canon C.output = rep C.output := by simp [canon, newIdx, hrn]
      rw [hca]
      have h1 := wireVal_input C' n u ⟨rep C.output, hrn⟩
      have h2 := wireVal_input C n u ⟨rep C.output, hrn⟩
      dsimp at h1 h2
      rw [h1, ← h2, hreq u hu]
    · have hj0_mem : j0 ∈ kept := (hkept_mem j0).mpr hnotel0
      obtain ⟨m, hm, hmj0⟩ := List.mem_iff_getElem.mp hj0_mem
      have hca : canon C.output = n + m := by
        simp only [canon, hj0, ← hmj0]
        exact hnewIdx_kept m hm
      rw [hca, hC'_wire u hu m hm, hmj0, ← hj0, hreq u hu]
  · intro p hpconst
    refine ⟨hcanon_ne_const C.output p hout_lt hout_nc hpconst, ?_⟩
    intro k hk hmem
    have hk_kept : k < kept.length := by
      have hk1 : k < (kept.map mkGate).length := hk
      rw [List.length_map] at hk1
      exact hk1
    set j : Fin C.size := kept[k]'hk_kept
    have hnotel : ¬ IsElim C n P j.val := (hkept_mem j).mp (List.getElem_mem hk_kept)
    have hsh := (not_elim_gate_shape C n P hC j.val j.isLt hnotel).2
    have hgate_eq : C'.gates[k]'hk = mkGate j := List.getElem_map _
    rw [hgate_eq] at hmem
    have hop := (hC _ (List.getElem_mem j.isLt)).1
    rcases hop with h_op | h_op | h_op
    · rw [h_op] at hsh
      obtain ⟨a, b, ha, hb, _, hin, _, hnca, hncb, _⟩ := hsh
      simp only [effInputs, mkGate, h_op, hin, List.map_cons, List.map_nil, List.mem_filter,
        List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem.1 with h1 | h2
      · exact hcanon_ne_const a p (by omega) hnca hpconst h1.symm
      · exact hcanon_ne_const b p (by omega) hncb hpconst h2.symm
    · rw [h_op] at hsh
      obtain ⟨a, b, ha, hb, _, hin, _, hnca, hncb, _⟩ := hsh
      simp only [effInputs, mkGate, h_op, hin, List.map_cons, List.map_nil, List.mem_filter,
        List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem.1 with h1 | h2
      · exact hcanon_ne_const a p (by omega) hnca hpconst h1.symm
      · exact hcanon_ne_const b p (by omega) hncb hpconst h2.symm
    · rw [h_op] at hsh
      obtain ⟨a, ha, hhead, _, hnca, _⟩ := hsh
      cases h_in : (C.gates[j.val]'j.isLt).inputs with
      | nil => rw [h_in] at hhead; simp at hhead
      | cons a0 rest =>
        rw [h_in] at hhead
        simp only [List.head?_cons, Option.some.injEq] at hhead
        simp only [effInputs, mkGate, h_op, h_in, List.take_succ_cons, List.take_zero,
          List.map_cons, List.map_nil, List.mem_filter, List.mem_cons, List.not_mem_nil,
          or_false] at hmem
        exact hcanon_ne_const a0 p (by omega) (hhead ▸ hnca) hpconst hmem.1.symm

-- ============================================================================
-- Part 3: Dead-gate elimination
-- ============================================================================

theorem elim_dead_gate (C : Circuit) (n : ℕ) (hC : ValidCircuit C) (j : ℕ) (hj : j < C.size)
    (hdead : IsDead C n j) :
    ∃ C' : Circuit, ValidCircuit C' ∧ C'.size = C.size - 1 ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let shift (w : ℕ) : ℕ :=
    if w < n + j then w else if w = n + j then n + C.size else w - 1
  let sg (g : Gate) : Gate := ⟨g.op, g.inputs.map shift⟩
  let gs' : List Gate := (C.gates.take j ++ C.gates.drop (j + 1)).map sg
  let C' : Circuit := ⟨gs', shift C.output⟩
  have hCsz : C.size = C.gates.length := rfl
  have hgs'_len : gs'.length = C.size - 1 := by
    simp only [gs', List.length_map, List.length_append, List.length_take, List.length_drop]
    omega
  have hC'_valid : ValidCircuit C' := by
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    have hgC : g ∈ C.gates := by
      rcases List.mem_append.mp hg with h1 | h2
      · exact List.mem_of_mem_take h1
      · exact List.mem_of_mem_drop h2
    exact ⟨(hC g hgC).1, by simpa [sg] using (hC g hgC).2⟩
  have hget_lt : ∀ (k : ℕ) (hk' : k < C'.size) (hk : k < j),
      C'.gates[k]'hk' = sg (C.gates[k]'(by omega)) := by
    intro k hk' hk
    have h1 : k < (C.gates.take j).length := by rw [List.length_take]; omega
    have hk_map : k < (List.map sg (List.take j C.gates ++ List.drop (j + 1) C.gates)).length := hk'
    change (List.map sg (List.take j C.gates ++ List.drop (j + 1) C.gates))[k]'hk_map = sg (C.gates[k]'(by omega))
    rw [List.getElem_map, List.getElem_append_left h1, List.getElem_take]
  have hget_ge : ∀ (k : ℕ) (hk' : k < C'.size) (hk : j ≤ k) (hk1 : k + 1 < C.size),
      C'.gates[k]'hk' = sg (C.gates[k + 1]'hk1) := by
    intro k hk' hk hk1
    have hlen_take : (C.gates.take j).length = j := by rw [List.length_take]; omega
    have hk_map : k < (List.map sg (List.take j C.gates ++ List.drop (j + 1) C.gates)).length := hk'
    change (List.map sg (List.take j C.gates ++ List.drop (j + 1) C.gates))[k]'hk_map = sg (C.gates[k + 1]'hk1)
    rw [List.getElem_map, List.getElem_append_right (by omega : (C.gates.take j).length ≤ k),
      List.getElem_drop]
    congr 2
    omega
  have hwire : ∀ (x : Fin n → Bool) (k : ℕ), k < C.size - 1 →
      wireVal C' n x (n + k) =
        if k < j then wireVal C n x (n + k) else wireVal C n x (n + (k + 1)) := by
    intro x k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have hk' : k < C'.size := by change k < gs'.length; omega
      rw [wireVal_gate C' n x k hk']
      by_cases hkj : k < j
      · simp only [hkj, ite_true]
        rw [hget_lt k hk' hkj, wireVal_gate C n x k (by omega)]
        simp only [sg, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        simp only [Function.comp_apply]
        by_cases ha : a < n + k
        · have hsh : shift a = a := by simp only [shift, show a < n + j by omega, ite_true]
          rw [hsh]
          simp only [ha, ite_true]
          by_cases han : a < n
          · have h1 := wireVal_input C' n x ⟨a, han⟩
            have h2 := wireVal_input C n x ⟨a, han⟩
            dsimp at h1 h2; rw [h1, h2]
          · set m := a - n
            have hm : m < k := by omega
            have ha_eq : a = n + m := by omega
            rw [ha_eq, ih m hm (by omega)]
            simp [show m < j by omega]
        · have hsh_ge : n + k ≤ shift a := by
            simp only [shift]
            split_ifs <;> omega
          simp only [ha, ite_false, show ¬ (shift a < n + k) by omega]
      · simp only [hkj, ite_false]
        have hjk : j ≤ k := by omega
        have hk1 : k + 1 < C.size := by omega
        rw [hget_ge k hk' hjk hk1, wireVal_gate C n x (k + 1) hk1]
        have hnot_in : n + j ∉ effInputs (C.gates[k + 1]'hk1) (n + (k + 1)) :=
          hdead.2 (k + 1) hk1 (by omega)
        have hval_a : ∀ a : ℕ, a ≠ n + j →
            (if shift a < n + k then wireVal C' n x (shift a) else false) =
            (if a < n + (k + 1) then wireVal C n x a else false) := by
          intro a hane
          by_cases ha_lt : a < n + j
          · have hsh : shift a = a := by simp only [shift, ha_lt, ite_true]
            rw [hsh]
            simp only [show a < n + k by omega, show a < n + (k + 1) by omega, ite_true]
            by_cases han : a < n
            · have h1 := wireVal_input C' n x ⟨a, han⟩
              have h2 := wireVal_input C n x ⟨a, han⟩
              dsimp at h1 h2; rw [h1, h2]
            · set m := a - n
              have ha_eq : a = n + m := by omega
              rw [ha_eq, ih m (by omega) (by omega)]
              simp [show m < j by omega]
          · have hsh : shift a = a - 1 := by
              simp only [shift, ha_lt, hane, ite_false]
            rw [hsh]
            by_cases ha_lt2 : a < n + (k + 1)
            · simp only [ha_lt2, show a - 1 < n + k by omega, ite_true]
              set m := a - 1 - n
              have hm_ge : ¬ (m < j) := by omega
              have ha1 : a - 1 = n + m := by omega
              have ha2 : a = n + (m + 1) := by omega
              rw [ha1, ih m (by omega) (by omega)]
              simp only [hm_ge, ite_false, ← ha2]
            · simp only [ha_lt2, show ¬ (a - 1 < n + k) by omega, ite_false]
        set g := C.gates[k + 1]'hk1
        change n + j ∉ effInputs g (n + (k + 1)) at hnot_in
        have hop : ValidOp g.op := (hC _ (List.getElem_mem hk1)).1
        rcases hop with h_op | h_op | h_op
        · simp only [sg, List.map_map]
          congr 1
          apply List.map_congr_left
          intro a ha
          apply hval_a
          intro heq
          subst heq
          apply hnot_in
          simp only [effInputs, h_op, List.mem_filter, decide_eq_true_eq]
          exact ⟨ha, by omega⟩
        · simp only [sg, List.map_map]
          congr 1
          apply List.map_congr_left
          intro a ha
          apply hval_a
          intro heq
          subst heq
          apply hnot_in
          simp only [effInputs, h_op, List.mem_filter, decide_eq_true_eq]
          exact ⟨ha, by omega⟩
        · simp only [sg, List.map_map]
          change g.op.eval _ = g.op.eval _
          rw [h_op]
          simp only [GateOp.eval]
          cases hin : g.inputs with
          | nil => rfl
          | cons a rest =>
            simp only [List.map_cons, List.headD_cons, Function.comp_apply]
            congr 1
            apply hval_a
            intro heq
            subst heq
            apply hnot_in
            simp only [effInputs, h_op, hin, List.take_succ_cons, List.take_zero, List.mem_filter,
              List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq]
            exact ⟨trivial, by omega⟩
  refine ⟨C', hC'_valid, hgs'_len, fun x => ?_⟩
  change wireVal C' n x (shift C.output) = wireVal C n x C.output
  have hne : C.output ≠ n + j := hdead.1
  by_cases ho1 : C.output < n + j
  · have hsh : shift C.output = C.output := by simp only [shift, ho1, ite_true]
    rw [hsh]
    by_cases hon : C.output < n
    · have h1 := wireVal_input C' n x ⟨C.output, hon⟩
      have h2 := wireVal_input C n x ⟨C.output, hon⟩
      dsimp at h1 h2; rw [h1, h2]
    · set m := C.output - n
      have heq : C.output = n + m := by omega
      rw [heq, hwire x m (by omega)]
      simp [show m < j by omega]
  · have hsh : shift C.output = C.output - 1 := by simp only [shift, ho1, hne, ite_false]
    rw [hsh]
    by_cases ho2 : C.output < n + C.size
    · set m := C.output - 1 - n
      have h1 : C.output - 1 = n + m := by omega
      have h2 : C.output = n + (m + 1) := by omega
      rw [h1, hwire x m (by omega)]
      simp only [show ¬ (m < j) by omega, ite_false, ← h2]
    · rw [wireVal_oob C' n x (C.output - 1) (by rw [show C'.size = C.size - 1 from hgs'_len]; omega),
          wireVal_oob C n x C.output (by omega)]

-- ============================================================================
-- Part 4: Minimal circuits, renameing, dep_lower, gate_elim_at, and G_lower
-- ============================================================================

theorem exists_minimal_circuit (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ C : Circuit, ValidCircuit C ∧ C.size ≤ s ∧ Computes n C f ∧
      (∀ C' : Circuit, ValidCircuit C' → Computes n C' f → C.size ≤ C'.size) := by
  classical
  have hex : ∃ k : ℕ, ∃ C : Circuit, ValidCircuit C ∧ C.size = k ∧ Computes n C f := by
    obtain ⟨C, h1, _, h3⟩ := h
    exact ⟨C.size, C, h1, rfl, h3⟩
  let m := Nat.find hex
  obtain ⟨C, h1, h2, h3⟩ := Nat.find_spec hex
  refine ⟨C, h1, ?_, h3, ?_⟩
  · obtain ⟨C0, h01, h02, h03⟩ := h
    have hle : m ≤ C0.size := Nat.find_min' hex ⟨C0, h01, rfl, h03⟩
    omega
  · intro C' h1' h3'
    have hle : m ≤ C'.size := Nat.find_min' hex ⟨C', h1', rfl, h3'⟩
    omega

theorem minimal_no_dead (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hC : ValidCircuit C) (hcomp : Computes n C f)
    (hmin : ∀ C', ValidCircuit C' → Computes n C' f → C.size ≤ C'.size)
    (j : ℕ) (hj : j < C.size) : ¬ IsDead C n j := by
  intro hdead
  obtain ⟨C', hC', hsz', hev'⟩ := elim_dead_gate C n hC j hj hdead
  have hle := hmin C' hC' (fun x => by rw [hev' x, hcomp x])
  omega

theorem minimal_no_elim (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hC : ValidCircuit C) (hcomp : Computes n C f)
    (hmin : ∀ C', ValidCircuit C' → Computes n C' f → C.size ≤ C'.size)
    (hnc : ∃ y z : Fin n → Bool, f y ≠ f z)
    (j : ℕ) (hj : j < C.size) : ¬ IsElim C n (fun _ => True) j := by
  intro hel
  have hnc_out : ∃ y z : Fin n → Bool, True ∧ True ∧ C.eval (List.ofFn y) ≠ C.eval (List.ofFn z) := by
    obtain ⟨y, z, hne⟩ := hnc
    exact ⟨y, z, trivial, trivial, by rw [hcomp y, hcomp z]; exact hne⟩
  obtain ⟨C', hC', hsz', hev', _⟩ := elim_circuit C n (fun _ => True) hC hnc_out
  have hcard : 1 ≤ (elimSet C n (fun _ => True)).card := by
    classical
    apply Finset.card_pos.mpr
    refine ⟨⟨j, hj⟩, ?_⟩
    simp [elimSet, hel]
  have hle := hmin C' hC' (fun x => by rw [hev' x trivial, hcomp x])
  omega

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def rename (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem rename_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨rename n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [rename, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

theorem dep_lower (N : ℕ) (f : (Fin N → Bool) → Bool)
    (hdep : ∀ p : Fin N, ∃ x : Fin N → Bool, f (Function.update x p (!x p)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize N f s) : N ≤ s + 1 := by
  by_cases hN2 : N < 2
  · omega
  obtain ⟨C, hC, hsz, hcomp, hmin⟩ := exists_minimal_circuit N f s h
  have hout_lt : C.output < N + C.size := by
    by_contra hge
    obtain ⟨x, hx⟩ := hdep ⟨0, by omega⟩
    apply hx
    rw [← hcomp, ← hcomp]
    change wireVal C N _ C.output = wireVal C N _ C.output
    rw [wireVal_oob C N _ C.output (by omega), wireVal_oob C N _ C.output (by omega)]
  have hcover : (Finset.range (N + C.size)).erase C.output ⊆
      Finset.univ.biUnion fun k : Fin C.size => (effInputs (C.gates[k.val]'k.isLt) (N + k.val)).toFinset := by
    intro w hw
    simp only [Finset.mem_erase, Finset.mem_range] at hw
    obtain ⟨hwne, hwlt⟩ := hw
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset]
    by_cases hwn : w < N
    · by_contra hnone
      push Not at hnone
      obtain ⟨x, hx⟩ := hdep ⟨w, hwn⟩
      apply hx
      rw [← hcomp, ← hcomp]
      apply wireVal_indep_of_unused C N hC ⟨w, hwn⟩ (fun k hk => hnone ⟨k, hk⟩)
      · intro i hi
        simp [Function.update_of_ne hi]
      · exact hwne.symm
    · set j := w - N
      have hj : j < C.size := by omega
      have hnd := minimal_no_dead N f C hC hcomp hmin j hj
      have hwj : w = N + j := by omega
      rw [hwj] at hwne ⊢
      by_contra hnone
      push Not at hnone
      apply hnd
      refine ⟨hwne.symm, fun k hk _ => hnone ⟨k, hk⟩⟩
  have hcard1 : ((Finset.range (N + C.size)).erase C.output).card = N + C.size - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hout_lt), Finset.card_range]
  have hcard2 : ((Finset.range (N + C.size)).erase C.output).card ≤
      ∑ k : Fin C.size, ((effInputs (C.gates[k.val]'k.isLt) (N + k.val)).toFinset).card :=
    le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
  have hcard3 : ∑ k : Fin C.size, ((effInputs (C.gates[k.val]'k.isLt) (N + k.val)).toFinset).card ≤
      2 * C.size := by
    calc
      ∑ k : Fin C.size, ((effInputs (C.gates[k.val]'k.isLt) (N + k.val)).toFinset).card
          ≤ ∑ _k : Fin C.size, 2 := by
            apply Finset.sum_le_sum
            intro k _
            have hle1 : ((effInputs (C.gates[k.val]'k.isLt) (N + k.val)).toFinset).card ≤
                (effInputs (C.gates[k.val]'k.isLt) (N + k.val)).length := List.toFinset_card_le _
            have hle2 : (effInputs (C.gates[k.val]'k.isLt) (N + k.val)).length ≤ 2 := by
              set g := C.gates[k.val]'k.isLt
              have hlen : g.inputs.length ≤ 2 := (hC _ (List.getElem_mem k.isLt)).2
              unfold effInputs
              have hf := List.length_filter_le (· < N + k.val)
                (match g.op with
                | GateOp.not => g.inputs.take 1
                | _ => g.inputs)
              cases hg : g.op <;> simp only [hg, List.length_take] at hf ⊢ <;> omega
            omega
      _ = 2 * C.size := by simp [Nat.mul_comm]
  omega

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ b : Bool, ∃ s' : ℕ, s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  obtain ⟨C, hC, hsz, hcomp, hmin⟩ := exists_minimal_circuit (n + 1) f s h
  have hnc_global : ∃ y z : Fin (n + 1) → Bool, f y ≠ f z := by
    obtain ⟨x, hx⟩ := hdep
    exact ⟨Function.update x p (!x p), x, hx⟩
  have hout_ne_p : C.output ≠ p.val := by
    intro heq
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← hcomp, ← hcomp]
    change wireVal C (n + 1) _ C.output = wireVal C (n + 1) _ C.output
    rw [heq, wireVal_input, wireVal_input]
    simp
  have hp_used : ∃ j : Fin C.size, p.val ∈ effInputs (C.gates[j.val]'j.isLt) (n + 1 + j.val) := by
    by_contra hnone
    push Not at hnone
    obtain ⟨x, hx⟩ := hdep
    apply hx
    rw [← hcomp, ← hcomp]
    apply wireVal_indep_of_unused C (n + 1) hC p (fun k hk => hnone ⟨k, hk⟩)
    · intro i hi; simp [Function.update_of_ne hi]
    · exact hout_ne_p
  obtain ⟨j, hjmem⟩ := hp_used
  have hnotel_j := minimal_no_elim (n + 1) f C hC hcomp hmin hnc_global j.val j.isLt
  have hsh := (not_elim_gate_shape C (n + 1) (fun _ => True) hC j.val j.isLt hnotel_j).2
  have hop := (hC _ (List.getElem_mem j.isLt)).1
  have hchoose : ∃ b : Bool, IsConstOn C (n + 1) (fun x => x p = b) (n + 1 + j.val) := by
    rcases hop with h_op | h_op | h_op
    · rw [h_op] at hsh
      obtain ⟨a, b0, _, _, _, _, heff, _, _, heval⟩ := hsh
      rw [heff] at hjmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hjmem
      refine ⟨false, fun y z hy hz => ?_⟩
      rw [heval y, heval z]
      rcases hjmem with rfl | rfl
      · rw [wireVal_input C (n + 1) y p, wireVal_input C (n + 1) z p, hy, hz]; simp
      · rw [wireVal_input C (n + 1) y p, wireVal_input C (n + 1) z p, hy, hz]; simp
    · rw [h_op] at hsh
      obtain ⟨a, b0, _, _, _, _, heff, _, _, heval⟩ := hsh
      rw [heff] at hjmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hjmem
      refine ⟨true, fun y z hy hz => ?_⟩
      rw [heval y, heval z]
      rcases hjmem with rfl | rfl
      · rw [wireVal_input C (n + 1) y p, wireVal_input C (n + 1) z p, hy, hz]; simp
      · rw [wireVal_input C (n + 1) y p, wireVal_input C (n + 1) z p, hy, hz]; simp
    · rw [h_op] at hsh
      obtain ⟨a, _, _, heff, _, heval⟩ := hsh
      rw [heff] at hjmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hjmem
      subst hjmem
      refine ⟨false, fun y z hy hz => ?_⟩
      rw [heval y, heval z, wireVal_input C (n + 1) y p, wireVal_input C (n + 1) z p, hy, hz]
  obtain ⟨b, hconst_j⟩ := hchoose
  have hnc_P : ∃ y z : Fin (n + 1) → Bool,
      y p = b ∧ z p = b ∧ C.eval (List.ofFn y) ≠ C.eval (List.ofFn z) := by
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨Function.update x p b, Function.update y p b, by simp, by simp, ?_⟩
    rw [hcomp, hcomp]
    exact hxy
  have hout_ne_j : C.output ≠ n + 1 + j.val := by
    intro heq
    obtain ⟨y, z, hy, hz, hne⟩ := hnc_P
    apply hne
    change wireVal C (n + 1) y C.output = wireVal C (n + 1) z C.output
    rw [heq]
    exact hconst_j y z hy hz
  have hnd_j := minimal_no_dead (n + 1) f C hC hcomp hmin j.val j.isLt
  have hk_ex : ∃ k : Fin C.size, j.val < k.val ∧
      n + 1 + j.val ∈ effInputs (C.gates[k.val]'k.isLt) (n + 1 + k.val) := by
    by_contra hnone
    push Not at hnone
    exact hnd_j ⟨hout_ne_j, fun k hk hlt => hnone ⟨k, hk⟩ hlt⟩
  obtain ⟨k, hjk, hkmem⟩ := hk_ex
  have hel_j : IsElim C (n + 1) (fun x => x p = b) j.val := Or.inl hconst_j
  have hel_k : IsElim C (n + 1) (fun x => x p = b) k.val :=
    elim_of_const_effInput C (n + 1) (fun x => x p = b) hC k.val k.isLt (n + 1 + j.val) hkmem hconst_j
  have hcard2 : 2 ≤ (elimSet C (n + 1) (fun x => x p = b)).card := by
    classical
    have hsub : ({j, k} : Finset (Fin C.size)) ⊆ elimSet C (n + 1) (fun x => x p = b) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hi with rfl | rfl
      · exact hel_j
      · exact hel_k
    have hne : j ≠ k := fun heq => Nat.lt_irrefl j.val (heq ▸ hjk)
    calc 2 = ({j, k} : Finset (Fin C.size)).card := (Finset.card_pair hne).symm
      _ ≤ (elimSet C (n + 1) (fun x => x p = b)).card := Finset.card_le_card hsub
  obtain ⟨C', hC', hsz', hev', hunused'⟩ := elim_circuit C (n + 1) (fun x => x p = b) hC hnc_P
  have hpconst : IsConstOn C (n + 1) (fun x => x p = b) p.val := by
    intro y z hy hz
    rw [wireVal_input C (n + 1) y p, wireVal_input C (n + 1) z p, hy, hz]
  obtain ⟨hout', hpu'⟩ := hunused' p hpconst
  refine ⟨b, C'.size, by omega, C', hC', le_rfl, fun x => ?_⟩
  have hupd_eq : C'.eval (List.ofFn x) = C'.eval (List.ofFn (Function.update x p b)) := by
    apply wireVal_indep_of_unused C' (n + 1) hC' p hpu'
    · intro i hi; simp [Function.update_of_ne hi]
    · exact hout'
  rw [hupd_eq, hev' (Function.update x p b) (by simp), hcomp]

def G (N k : ℕ) (x : Fin N → Bool) : Bool :=
  decide ((∃ i : Fin N, i.val < k ∧ x i = true) ∨
    (∃ i j : Fin N, k ≤ i.val ∧ i.val + 1 = j.val ∧ x i = true ∧ x j = true))

def ext {N : ℕ} (x : Fin N → Bool) (j : ℕ) : Bool := if h : j < N then x ⟨j, h⟩ else false

theorem ext_fin {N : ℕ} (x : Fin N → Bool) (i : Fin N) : ext x i.val = x i := by
  simp [ext]

theorem ext_lt {N : ℕ} {x : Fin N → Bool} {j : ℕ} (h : ext x j = true) : j < N := by
  unfold ext at h
  split at h
  · assumption
  · simp at h

theorem ext_fn {N : ℕ} (Q : ℕ → Bool) (j : ℕ) :
    ext (fun i : Fin N => Q i.val) j = (decide (j < N) && Q j) := by
  unfold ext
  by_cases hj : j < N <;> simp [hj]

theorem ext_update {N : ℕ} (x : Fin N → Bool) (p : Fin N) (b : Bool) (j : ℕ) :
    ext (Function.update x p b) j = if j = p.val then b else ext x j := by
  unfold ext
  by_cases hj : j < N
  · simp [hj, Function.update_apply, Fin.ext_iff]
  · have : j ≠ p.val := by have := p.2; omega
    simp [hj, this]

theorem G_iff (N k : ℕ) (x : Fin N → Bool) : G N k x = true ↔
    ((∃ i, i < k ∧ ext x i = true) ∨ (∃ i, k ≤ i ∧ ext x i = true ∧ ext x (i + 1) = true)) := by
  unfold G
  rw [decide_eq_true_iff]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, j, hi, hij, hx, hy⟩)
    · exact Or.inl ⟨i, hi, by rw [ext_fin]; exact hx⟩
    · refine Or.inr ⟨i, hi, by rw [ext_fin]; exact hx, ?_⟩
      rw [hij, ext_fin]; exact hy
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · have hl := ext_lt hx
      refine Or.inl ⟨⟨i, hl⟩, hi, ?_⟩
      rw [← ext_fin x ⟨i, hl⟩]; exact hx
    · have hl := ext_lt hy
      refine Or.inr ⟨⟨i, by omega⟩, ⟨i + 1, hl⟩, hi, rfl, ?_, ?_⟩
      · rw [← ext_fin x ⟨i, by omega⟩]; exact hx
      · rw [← ext_fin x ⟨i + 1, hl⟩]; exact hy

def del (n k : ℕ) (hk : k < n) : Fin (n + 1) → Fin n :=
  fun i => ⟨if i.val ≤ k then i.val else i.val - 1, by have := i.2; split <;> omega⟩

theorem ext_del (n k : ℕ) (hk : k < n) (y : Fin n → Bool) (b : Bool) (j : ℕ) :
    ext (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ b) j
      = if j = k then b else if j < k then ext y j else ext y (j - 1) := by
  rw [ext_update]
  by_cases hjk : j = k
  · simp [hjk]
  · simp only [hjk, ite_false]
    unfold ext
    by_cases hj : j < n + 1
    · simp only [hj, dite_true]
      by_cases hjk' : j < k
      · simp only [hjk', ite_true, show j < n by omega, dite_true]
        simp [del, show j ≤ k by omega]
      · simp only [hjk', ite_false, show j - 1 < n by omega, dite_true]
        simp [del, show ¬ j ≤ k by omega]
    · simp only [hj, dite_false, show ¬ j < k by omega, ite_false,
        show ¬ j - 1 < n by omega, dite_false]

theorem G_del_false (n k : ℕ) (hk : k < n) (y : Fin n → Bool) :
    G (n + 1) k (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ false) = G n k y := by
  rw [Bool.eq_iff_iff, G_iff, G_iff]
  simp only [ext_del]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · simp only [show i ≠ k by omega, ite_false, hi, ite_true] at hx
      exact Or.inl ⟨i, hi, hx⟩
    · by_cases hik : i = k
      · simp only [hik, ite_true] at hx; exact absurd hx (by simp)
      · simp only [hik, show ¬ i < k by omega, ite_false] at hx
        simp only [show i + 1 ≠ k by omega, show ¬ i + 1 < k by omega, ite_false] at hy
        refine Or.inr ⟨i - 1, by omega, hx, ?_⟩
        rwa [show i - 1 + 1 = i + 1 - 1 by omega]
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · refine Or.inl ⟨i, hi, ?_⟩
      simp only [show i ≠ k by omega, ite_false, hi, ite_true]; exact hx
    · refine Or.inr ⟨i + 1, by omega, ?_, ?_⟩
      · simp only [show i + 1 ≠ k by omega, show ¬ i + 1 < k by omega, ite_false]; simpa using hx
      · simp only [show i + 1 + 1 ≠ k by omega, show ¬ i + 1 + 1 < k by omega, ite_false]; simpa using hy

theorem G_del_true (n k : ℕ) (hk : k < n) (y : Fin n → Bool) :
    G (n + 1) k (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ true) = G n (k + 1) y := by
  rw [Bool.eq_iff_iff, G_iff, G_iff]
  simp only [ext_del]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · simp only [show i ≠ k by omega, ite_false, hi, ite_true] at hx
      exact Or.inl ⟨i, by omega, hx⟩
    · by_cases hik : i = k
      · simp only [show i + 1 ≠ k by omega, show ¬ i + 1 < k by omega, ite_false] at hy
        refine Or.inl ⟨k, by omega, ?_⟩
        rwa [show k = i + 1 - 1 by omega]
      · by_cases hik1 : i = k + 1
        · simp only [show i ≠ k by omega, show ¬ i < k by omega, ite_false] at hx
          refine Or.inl ⟨k, by omega, ?_⟩
          rwa [show k = i - 1 by omega]
        · simp only [hik, show ¬ i < k by omega, ite_false] at hx
          simp only [show i + 1 ≠ k by omega, show ¬ i + 1 < k by omega, ite_false] at hy
          refine Or.inr ⟨i - 1, by omega, hx, ?_⟩
          rwa [show i - 1 + 1 = i + 1 - 1 by omega]
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · by_cases hik : i < k
      · refine Or.inl ⟨i, hik, ?_⟩
        simp only [show i ≠ k by omega, ite_false, hik, ite_true]; exact hx
      · have e : i = k := by omega
        subst e
        refine Or.inr ⟨i, le_rfl, by simp, ?_⟩
        simp only [show i + 1 ≠ i by omega, show ¬ i + 1 < i by omega, ite_false]; simpa using hx
    · refine Or.inr ⟨i + 1, by omega, ?_, ?_⟩
      · simp only [show i + 1 ≠ k by omega, show ¬ i + 1 < k by omega, ite_false]; simpa using hx
      · simp only [show i + 1 + 1 ≠ k by omega, show ¬ i + 1 + 1 < k by omega, ite_false]; simpa using hy

theorem G_dep (N k : ℕ) (hd : k + 2 ≤ N) (p : Fin N) :
    ∃ x : Fin N → Bool, G N k (Function.update x p (!x p)) ≠ G N k x := by
  by_cases hp : p.val < k
  · refine ⟨fun _ => false, ?_⟩
    have h1 : G N k (Function.update (fun _ => false) p (!false)) = true := by
      rw [G_iff]
      refine Or.inl ⟨p.val, hp, ?_⟩
      rw [ext_update]; simp
    have h0 : G N k (fun _ => false) = false := by
      rw [← Bool.not_eq_true, G_iff]
      rintro (⟨i, _, hx⟩ | ⟨i, _, hx, _⟩) <;> simp [ext] at hx
    rw [h1, h0]; simp
  · set q : ℕ := if p.val + 1 < N then p.val + 1 else p.val - 1 with hq
    have hqN : q < N := by rw [hq]; split <;> omega
    have hqk : k ≤ q := by have := p.2; rw [hq]; split <;> omega
    have hpq : p.val ≠ q := by rw [hq]; split <;> omega
    refine ⟨fun i : Fin N => decide (i.val = q), ?_⟩
    have hxp : (fun i : Fin N => decide (i.val = q)) p = false := by simp [hpq]
    rw [hxp]
    have h1 : G N k (Function.update (fun i : Fin N => decide (i.val = q)) p (!false)) = true := by
      rw [G_iff]
      right
      by_cases hc : p.val + 1 < N
      · have hqv : q = p.val + 1 := by simp [hq, hc]
        refine ⟨p.val, by omega, ?_, ?_⟩
        · rw [ext_update]; simp
        · rw [ext_update]
          simp only [show p.val + 1 ≠ p.val by omega, ite_false,
            ext_fn (fun j => decide (j = q))]
          simp [hqv, hc]
      · have hqv : q = p.val - 1 := by simp [hq, hc]
        refine ⟨q, hqk, ?_, ?_⟩
        · rw [ext_update]
          simp only [show q ≠ p.val by omega, ite_false, ext_fn (fun j => decide (j = q))]
          simp [hqN]
        · rw [ext_update]
          simp [show q + 1 = p.val by omega]
    have h0 : G N k (fun i : Fin N => decide (i.val = q)) = false := by
      rw [← Bool.not_eq_true, G_iff]
      rintro (⟨i, hi, hx⟩ | ⟨i, _, hx, hy⟩)
      · rw [ext_fn (fun j => decide (j = q))] at hx
        simp at hx; omega
      · rw [ext_fn (fun j => decide (j = q))] at hx hy
        simp at hx hy; omega
    rw [h1, h0]; simp

theorem G_lower : ∀ d : ℕ, 2 ≤ d → ∀ k N s : ℕ, N = k + d →
    HasCircuitSize N (G N k) s → N + d / 2 ≤ s + 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd k N s hN h
    by_cases hd4 : d < 4
    · have := dep_lower N (G N k) (G_dep N k (by omega)) s h
      have : d / 2 ≤ 1 := by omega
      omega
    · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      have hk : k < n := by omega
      set p : Fin (n + 1) := ⟨k, by omega⟩ with hp
      have hdep := G_dep (n + 1) k (by omega) p
      have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
          G (n + 1) k (Function.update x p b) ≠ G (n + 1) k (Function.update y p b) := by
        intro b
        refine ⟨fun _ => false, fun i : Fin (n + 1) => decide (i.val = k + 2 ∨ i.val = k + 3), ?_⟩
        have h0 : G (n + 1) k (Function.update (fun _ => false) p b) = false := by
          rw [← Bool.not_eq_true, G_iff]
          rintro (⟨i, hi, hx⟩ | ⟨i, _, hx, hy⟩)
          · rw [ext_update] at hx
            simp only [show i ≠ p.val by simp [hp]; omega, ite_false] at hx
            simp [ext] at hx
          · rw [ext_update] at hy
            simp only [show i + 1 ≠ p.val by simp [hp]; omega, ite_false] at hy
            simp [ext] at hy
        have h1 : G (n + 1) k (Function.update
            (fun i : Fin (n + 1) => decide (i.val = k + 2 ∨ i.val = k + 3)) p b) = true := by
          rw [G_iff]
          refine Or.inr ⟨k + 2, by omega, ?_, ?_⟩
          · rw [ext_update]
            simp only [show k + 2 ≠ p.val by simp [hp], ite_false,
              ext_fn (fun j => decide (j = k + 2 ∨ j = k + 3))]
            simp; omega
          · rw [ext_update]
            simp only [show k + 2 + 1 ≠ p.val by simp [hp]; omega, ite_false,
              ext_fn (fun j => decide (j = k + 2 ∨ j = k + 3))]
            simp; omega
        rw [h0, h1]; simp
      obtain ⟨b, s', hs, h'⟩ := gate_elim_at n (G (n + 1) k) p s hdep hnc h
      have h'' := rename_size (del n k hk) _ s' h'
      cases b with
      | false =>
        have e : (fun y : Fin n → Bool =>
            (fun x => G (n + 1) k (Function.update x p false)) (y ∘ del n k hk)) = G n k := by
          funext y; exact G_del_false n k hk y
        rw [e] at h''
        have := ih (d - 1) (by omega) (by omega) k n s' (by omega) h''
        omega
      | true =>
        have e : (fun y : Fin n → Bool =>
            (fun x => G (n + 1) k (Function.update x p true)) (y ∘ del n k hk)) = G n (k + 1) := by
          funext y; exact G_del_true n k hk y
        rw [e] at h''
        have := ih (d - 2) (by omega) (by omega) (k + 1) n s' (by omega) h''
        omega

-- ============================================================================
-- Part 5: 7-cycle properties, fanout dichotomy, and size >= 10
-- ============================================================================

def fC7 (x : Fin 7 → Bool) : Bool :=
  decide (∃ i : Fin 7, x i = true ∧ x (i + 1) = true)

theorem fC7_dep_after_fix (p1 p2 : Fin 7) (b1 : Bool) (hne : p1 ≠ p2) :
    ∃ x : Fin 7 → Bool, x p1 = b1 ∧ fC7 (Function.update x p2 (!x p2)) ≠ fC7 x := by
  by_cases hb1 : b1 = true
  · subst hb1
    by_cases hadj : p2 = p1 + 1 ∨ p1 = p2 + 1
    · refine ⟨fun i => decide (i = p1), by simp, ?_⟩
      have hxp2 : (fun i : Fin 7 => decide (i = p1)) p2 = false := by
        simp [hne.symm]
      rw [hxp2]
      have h0 : fC7 (fun i : Fin 7 => decide (i = p1)) = false := by
        rw [← Bool.not_eq_true]
        unfold fC7
        rw [decide_eq_true_iff]
        rintro ⟨i, h1, h2⟩
        simp only [decide_eq_true_eq] at h1 h2
        rw [h1] at h2
        have : (1 : Fin 7) = 0 := by simpa using congrArg (fun t => t - p1) h2
        exact absurd this (by decide)
      have h1 : fC7 (Function.update (fun i : Fin 7 => decide (i = p1)) p2 (!false)) = true := by
        unfold fC7
        rw [decide_eq_true_iff]
        rcases hadj with h12 | h21
        · refine ⟨p1, ?_, ?_⟩
          · rw [Function.update_of_ne hne]; simp
          · rw [← h12, Function.update_self]; rfl
        · refine ⟨p2, ?_, ?_⟩
          · rw [Function.update_self]; rfl
          · rw [← h21, Function.update_of_ne hne]; simp
      rw [h0, h1]; simp
    · push Not at hadj
      set q : Fin 7 := if p2 + 1 ≠ p1 + 1 ∧ p2 + 1 ≠ p1 - 1 then p2 + 1 else p2 - 1 with hq
      have hq_props : (q = p2 + 1 ∨ p2 = q + 1) ∧ q ≠ p1 ∧ q ≠ p2 ∧ q ≠ p1 + 1 ∧ p1 ≠ q + 1 := by
        revert p1 p2
        decide
      obtain ⟨hq_adj, hqp1, hqp2, hq_n1, hq_n2⟩ := hq_props
      refine ⟨fun i => decide (i = p1 ∨ i = q), by simp, ?_⟩
      have hxp2 : (fun i : Fin 7 => decide (i = p1 ∨ i = q)) p2 = false := by
        simp [hne.symm, hqp2.symm]
      rw [hxp2]
      have h0 : fC7 (fun i : Fin 7 => decide (i = p1 ∨ i = q)) = false := by
        rw [← Bool.not_eq_true]
        unfold fC7
        rw [decide_eq_true_iff]
        rintro ⟨i, h1, h2⟩
        simp only [decide_eq_true_eq] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · rw [h1] at h2
          exact absurd (by simpa using congrArg (fun t => t - p1) h2 : (1 : Fin 7) = 0) (by decide)
        · rw [h1] at h2; exact hq_n1 h2.symm
        · rw [h1] at h2; exact hq_n2 h2.symm
        · rw [h1] at h2
          exact absurd (by simpa using congrArg (fun t => t - q) h2 : (1 : Fin 7) = 0) (by decide)
      have h1 : fC7 (Function.update (fun i : Fin 7 => decide (i = p1 ∨ i = q)) p2 (!false)) = true := by
        unfold fC7
        rw [decide_eq_true_iff]
        rcases hq_adj with hq1 | hq2
        · refine ⟨p2, by rw [Function.update_self]; rfl, ?_⟩
          rw [← hq1, Function.update_of_ne hqp2]; simp
        · refine ⟨q, ?_, ?_⟩
          · rw [Function.update_of_ne hqp2]; simp
          · rw [← hq2, Function.update_self]; rfl
      rw [h0, h1]; simp
  · have hb1f : b1 = false := Bool.eq_false_iff.mpr hb1
    subst hb1f
    set q : Fin 7 := if p2 + 1 ≠ p1 then p2 + 1 else p2 - 1 with hq
    have hq_props : (q = p2 + 1 ∨ p2 = q + 1) ∧ q ≠ p1 ∧ q ≠ p2 := by
      revert p1 p2
      decide
    obtain ⟨hq_adj, hqp1, hqp2⟩ := hq_props
    refine ⟨fun i => decide (i = q), by simp [hqp1.symm], ?_⟩
    have hxp2 : (fun i : Fin 7 => decide (i = q)) p2 = false := by simp [hqp2.symm]
    rw [hxp2]
    have h0 : fC7 (fun i : Fin 7 => decide (i = q)) = false := by
      rw [← Bool.not_eq_true]
      unfold fC7
      rw [decide_eq_true_iff]
      rintro ⟨i, h1, h2⟩
      simp only [decide_eq_true_eq] at h1 h2
      rw [h1] at h2
      exact absurd (by simpa using congrArg (fun t => t - q) h2 : (1 : Fin 7) = 0) (by decide)
    have h1 : fC7 (Function.update (fun i : Fin 7 => decide (i = q)) p2 (!false)) = true := by
      unfold fC7
      rw [decide_eq_true_iff]
      rcases hq_adj with hq1 | hq2
      · refine ⟨p2, by rw [Function.update_self]; rfl, ?_⟩
        rw [← hq1, Function.update_of_ne hqp2]; simp
      · refine ⟨q, ?_, ?_⟩
        · rw [Function.update_of_ne hqp2]; simp
        · rw [← hq2, Function.update_self]; rfl
    rw [h0, h1]; simp

theorem fC7_nc (p : Fin 7) (b : Bool) :
    ∃ y z : Fin 7 → Bool, y p = b ∧ z p = b ∧ fC7 y ≠ fC7 z := by
  have hne : p ≠ p + 1 := by revert p; decide
  obtain ⟨x, hxp, hxne⟩ := fC7_dep_after_fix p (p + 1) b hne
  exact ⟨Function.update x (p + 1) (!x (p + 1)), x,
    by rw [Function.update_of_ne hne]; exact hxp, hxp, hxne⟩

theorem exists_third_fin7 (a b : Fin 7) : ∃ c : Fin 7, c ≠ a ∧ c ≠ b := by
  revert a b; decide

theorem fC7_not_unary_on_fix (p1 q : Fin 7) (b1 : Bool) (h : Bool → Bool) :
    ¬ (∀ x : Fin 7 → Bool, x p1 = b1 → fC7 x = h (x q)) := by
  intro hall
  obtain ⟨p3, hp31, hp3q⟩ := exists_third_fin7 p1 q
  obtain ⟨x, hxp1, hxne⟩ := fC7_dep_after_fix p1 p3 b1 hp31.symm
  have h1 := hall (Function.update x p3 (!x p3)) (by rw [Function.update_of_ne hp31.symm]; exact hxp1)
  have h2 := hall x hxp1
  rw [Function.update_of_ne hp3q.symm] at h1
  exact hxne (h1.trans h2.symm)

def piFalse (p : Fin 7) (i : Fin 7) : Fin 6 :=
  let d := ((i - p : Fin 7) : ℕ)
  if h : 1 ≤ d ∧ d ≤ 6 then ⟨d - 1, by omega⟩ else ⟨0, by omega⟩

def piTrue (p : Fin 7) (i : Fin 7) : Fin 6 :=
  let d := ((i - p : Fin 7) : ℕ)
  if d = 1 then ⟨0, by omega⟩
  else if d = 6 then ⟨1, by omega⟩
  else if h : 2 ≤ d ∧ d ≤ 5 then ⟨d, by omega⟩
  else ⟨0, by omega⟩

theorem fin7_add_ne (p d : Fin 7) (hd : d ≠ 0) : p + d ≠ p := by
  revert p d; decide

theorem fC7_del_false (p : Fin 7) (y : Fin 6 → Bool) :
    fC7 (Function.update (y ∘ piFalse p) p false) = G 6 0 y := by
  rw [Bool.eq_iff_iff]
  unfold fC7 G
  rw [decide_eq_true_iff, decide_eq_true_iff]
  have hval : ∀ (k : Fin 6),
      Function.update (y ∘ piFalse p) p false (p + ⟨k.val + 1, by omega⟩) = y k := by
    intro k
    have hne : p + (⟨k.val + 1, by omega⟩ : Fin 7) ≠ p :=
      fin7_add_ne p ⟨k.val + 1, by omega⟩ (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    rw [Function.update_of_ne hne, Function.comp_apply]
    congr 1
    simp only [piFalse, add_sub_cancel_left]
    have h1 : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ 6 := by omega
    simp only [h1, and_self, dite_true]
    ext; simp
  constructor
  · rintro ⟨i, h1, h2⟩
    right
    have hi_eq : i = p + (i - p) := (add_sub_cancel p i).symm
    generalize hd : i - p = d at hi_eq
    fin_cases d
    · have hi' : i = p := by simpa using hi_eq
      rw [hi', Function.update_self] at h1; simp at h1
    · have hi' : i = p + 1 := hi_eq
      have hi1' : i + 1 = p + ⟨(1 : Fin 6).val + 1, by omega⟩ := by rw [hi', add_assoc]; rfl
      rw [hi'] at h1; rw [hi1'] at h2
      have h1' : y 0 = true := by simpa using (hval 0).symm.trans h1
      have h2' : y 1 = true := (hval 1).symm.trans h2
      exact ⟨0, 1, Nat.zero_le _, rfl, h1', h2'⟩
    · have hi' : i = p + 2 := hi_eq
      have hi1' : i + 1 = p + ⟨(2 : Fin 6).val + 1, by omega⟩ := by rw [hi', add_assoc]; rfl
      rw [hi'] at h1; rw [hi1'] at h2
      have h1' : y 1 = true := by simpa using (hval 1).symm.trans h1
      have h2' : y 2 = true := (hval 2).symm.trans h2
      exact ⟨1, 2, Nat.zero_le _, rfl, h1', h2'⟩
    · have hi' : i = p + 3 := hi_eq
      have hi1' : i + 1 = p + ⟨(3 : Fin 6).val + 1, by omega⟩ := by rw [hi', add_assoc]; rfl
      rw [hi'] at h1; rw [hi1'] at h2
      have h1' : y 2 = true := by simpa using (hval 2).symm.trans h1
      have h2' : y 3 = true := (hval 3).symm.trans h2
      exact ⟨2, 3, Nat.zero_le _, rfl, h1', h2'⟩
    · have hi' : i = p + 4 := hi_eq
      have hi1' : i + 1 = p + ⟨(4 : Fin 6).val + 1, by omega⟩ := by rw [hi', add_assoc]; rfl
      rw [hi'] at h1; rw [hi1'] at h2
      have h1' : y 3 = true := by simpa using (hval 3).symm.trans h1
      have h2' : y 4 = true := (hval 4).symm.trans h2
      exact ⟨3, 4, Nat.zero_le _, rfl, h1', h2'⟩
    · have hi' : i = p + 5 := hi_eq
      have hi1' : i + 1 = p + ⟨(5 : Fin 6).val + 1, by omega⟩ := by rw [hi', add_assoc]; rfl
      rw [hi'] at h1; rw [hi1'] at h2
      have h1' : y 4 = true := by simpa using (hval 4).symm.trans h1
      have h2' : y 5 = true := (hval 5).symm.trans h2
      exact ⟨4, 5, Nat.zero_le _, rfl, h1', h2'⟩
    · have hi' : i = p + 6 := hi_eq
      have h0 : i + 1 = p := by rw [hi', add_assoc]; simp
      rw [h0, Function.update_self] at h2; simp at h2
  · rintro (⟨i, hi, _⟩ | ⟨i, j, _, hij, h1, h2⟩)
    · omega
    · refine ⟨p + ⟨i.val + 1, by omega⟩, ?_, ?_⟩
      · rw [hval i]; exact h1
      · have hnext : p + (⟨i.val + 1, by omega⟩ : Fin 7) + 1 = p + ⟨j.val + 1, by omega⟩ := by
          rw [add_assoc]
          congr 1
          ext
          simp [Fin.val_add, ← hij]
          omega
        rw [hnext, hval j]; exact h2

theorem fC7_del_true (p : Fin 7) (y : Fin 6 → Bool) :
    fC7 (Function.update (y ∘ piTrue p) p true) = G 6 2 y := by
  rw [Bool.eq_iff_iff]
  unfold fC7 G
  rw [decide_eq_true_iff, decide_eq_true_iff]
  have hval0 : Function.update (y ∘ piTrue p) p true (p + 1) = y 0 := by
    rw [Function.update_of_ne (fin7_add_ne p 1 (by decide)), Function.comp_apply]
    congr 1; simp [piTrue]
  have hval1 : Function.update (y ∘ piTrue p) p true (p + 6) = y 1 := by
    rw [Function.update_of_ne (fin7_add_ne p 6 (by decide)), Function.comp_apply]
    congr 1; simp [piTrue]
  have hval_mid : ∀ (k : Fin 6), 2 ≤ k.val →
      Function.update (y ∘ piTrue p) p true (p + ⟨k.val, by omega⟩) = y k := by
    intro k hk
    have hne : p + (⟨k.val, by omega⟩ : Fin 7) ≠ p :=
      fin7_add_ne p ⟨k.val, by omega⟩ (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    rw [Function.update_of_ne hne, Function.comp_apply]
    congr 1
    simp only [piTrue, add_sub_cancel_left]
    have hne1 : k.val ≠ 1 := by omega
    have hne6 : k.val ≠ 6 := by omega
    have h25 : 2 ≤ k.val ∧ k.val ≤ 5 := by omega
    simp only [hne1, hne6, ite_false, h25, and_self, dite_true]
  constructor
  · rintro ⟨i, h1, h2⟩
    have hi_eq : i = p + (i - p) := (add_sub_cancel p i).symm
    generalize hd : i - p = d at hi_eq
    fin_cases d
    · left
      have hi' : i = p := by simpa using hi_eq
      rw [hi', hval0] at h2
      exact ⟨0, by decide, h2⟩
    · left
      have hi' : i = p + 1 := hi_eq
      rw [hi', hval0] at h1
      exact ⟨0, by decide, h1⟩
    · right
      have hi' : i = p + 2 := hi_eq
      have hi1' : i + 1 = p + ⟨(3 : Fin 6).val, by omega⟩ := by rw [hi', add_assoc]; rfl
      rw [hi'] at h1; rw [hi1'] at h2
      have h1' : y 2 = true := by simpa using (hval_mid 2 (by decide)).symm.trans h1
      have h2' : y 3 = true := (hval_mid 3 (by decide)).symm.trans h2
      exact ⟨2, 3, le_rfl, rfl, h1', h2'⟩
    · right
      have hi' : i = p + 3 := hi_eq
      have hi1' : i + 1 = p + ⟨(4 : Fin 6).val, by omega⟩ := by rw [hi', add_assoc]; rfl
      rw [hi'] at h1; rw [hi1'] at h2
      have h1' : y 3 = true := by simpa using (hval_mid 3 (by decide)).symm.trans h1
      have h2' : y 4 = true := (hval_mid 4 (by decide)).symm.trans h2
      exact ⟨3, 4, by decide, rfl, h1', h2'⟩
    · right
      have hi' : i = p + 4 := hi_eq
      have hi1' : i + 1 = p + ⟨(5 : Fin 6).val, by omega⟩ := by rw [hi', add_assoc]; rfl
      rw [hi'] at h1; rw [hi1'] at h2
      have h1' : y 4 = true := by simpa using (hval_mid 4 (by decide)).symm.trans h1
      have h2' : y 5 = true := (hval_mid 5 (by decide)).symm.trans h2
      exact ⟨4, 5, by decide, rfl, h1', h2'⟩
    · left
      have hi' : i = p + 5 := hi_eq
      have hstep : i + 1 = p + 6 := by rw [hi', add_assoc]; rfl
      rw [hstep, hval1] at h2
      exact ⟨1, by decide, h2⟩
    · left
      have hi' : i = p + 6 := hi_eq
      rw [hi', hval1] at h1
      exact ⟨1, by decide, h1⟩
  · rintro (⟨i, hi, hy⟩ | ⟨i, j, hi, hij, h1, h2⟩)
    · have h01 : i = 0 ∨ i = 1 := by
        rcases eq_or_lt_of_le (Nat.zero_le i.val) with h0 | hpos
        · left; ext; exact h0.symm
        · right; ext; change i.val = 1; omega
      rcases h01 with rfl | rfl
      · refine ⟨p, by rw [Function.update_self], ?_⟩
        rw [hval0]; exact hy
      · refine ⟨p + 6, ?_, ?_⟩
        · rw [hval1]; exact hy
        · have : p + (6 : Fin 7) + 1 = p := by rw [add_assoc]; simp
          rw [this, Function.update_self]
    · refine ⟨p + ⟨i.val, by omega⟩, ?_, ?_⟩
      · rw [hval_mid i hi]; exact h1
      · have hnext : p + (⟨i.val, by omega⟩ : Fin 7) + 1 = p + ⟨j.val, by omega⟩ := by
          rw [add_assoc]
          congr 1
          ext
          simp [Fin.val_add, ← hij]
          omega
        rw [hnext, hval_mid j (by omega)]; exact h2

theorem fanout_tight (C : Circuit) (hC : ValidCircuit C) (hcomp : Computes 7 C fC7)
    (hnodead : ∀ j : ℕ, (hj : j < C.size) → ¬ IsDead C 7 j)
    (hnoelim : ∀ j : ℕ, (hj : j < C.size) → ¬ IsElim C 7 (fun _ => True) j) :
    ∃ (p : Fin 7) (b : Bool),
      (if b = true then 4 else 3) ≤ (elimSet C 7 (fun x => x p = b)).card := by
  classical
  have hconst_next : ∀ (p : Fin 7) (b : Bool) (j : Fin C.size),
      IsConstOn C 7 (fun x => x p = b) (7 + j.val) →
      ∃ k : Fin C.size, j < k ∧
        7 + j.val ∈ effInputs (C.gates[k.val]'k.isLt) (7 + k.val) ∧
        k ∈ elimSet C 7 (fun x => x p = b) := by
    intro p b j hconst
    have hout : C.output ≠ 7 + j.val := by
      intro heq
      obtain ⟨y, z, hy, hz, hne⟩ := fC7_nc p b
      apply hne
      rw [← hcomp y, ← hcomp z]
      change wireVal C 7 y C.output = wireVal C 7 z C.output
      rw [heq]
      exact hconst y z hy hz
    have hnd := hnodead j.val j.isLt
    have hex : ∃ k : Fin C.size, j < k ∧
        7 + j.val ∈ effInputs (C.gates[k.val]'k.isLt) (7 + k.val) := by
      by_contra hnone
      push Not at hnone
      exact hnd ⟨hout, fun k hk hlt => hnone ⟨k, hk⟩ hlt⟩
    obtain ⟨k, hjk, hkmem⟩ := hex
    refine ⟨k, hjk, hkmem, ?_⟩
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact elim_of_const_effInput C 7 (fun x => x p = b) hC k.val k.isLt (7 + j.val) hkmem hconst
  have hp_in_elim : ∀ (p : Fin 7) (b : Bool) (j : Fin C.size),
      p.val ∈ effInputs (C.gates[j.val]'j.isLt) (7 + j.val) →
      j ∈ elimSet C 7 (fun x => x p = b) := by
    intro p b j hmem
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    apply elim_of_const_effInput C 7 (fun x => x p = b) hC j.val j.isLt p.val hmem
    intro y z hy hz
    rw [wireVal_input C 7 y p, wireVal_input C 7 z p, hy, hz]
  -- Case 1: Some input p feeds two distinct gates j1 < j2
  by_cases hCase1 : ∃ (p : Fin 7) (j1 j2 : Fin C.size), j1 < j2 ∧
      p.val ∈ effInputs (C.gates[j1.val]'j1.isLt) (7 + j1.val) ∧
      p.val ∈ effInputs (C.gates[j2.val]'j2.isLt) (7 + j2.val)
  · obtain ⟨p, j1, j2, h12, hm1, hm2⟩ := hCase1
    have hsh1 := (not_elim_gate_shape C 7 (fun _ => True) hC j1.val j1.isLt (hnoelim j1.val j1.isLt)).2
    have hsh2 := (not_elim_gate_shape C 7 (fun _ => True) hC j2.val j2.isLt (hnoelim j2.val j2.isLt)).2
    have hop1 := (hC _ (List.getElem_mem j1.isLt)).1
    have hop2 := (hC _ (List.getElem_mem j2.isLt)).1
    -- Helper: if gate j has op = and or not and reads p, then j is const on x p = false
    have hconst_false : ∀ (j : Fin C.size),
        p.val ∈ effInputs (C.gates[j.val]'j.isLt) (7 + j.val) →
        ((C.gates[j.val]'j.isLt).op = GateOp.and ∨ (C.gates[j.val]'j.isLt).op = GateOp.not) →
        IsConstOn C 7 (fun x => x p = false) (7 + j.val) := by
      intro j hmj hopj
      have hshj := (not_elim_gate_shape C 7 (fun _ => True) hC j.val j.isLt (hnoelim j.val j.isLt)).2
      rcases hopj with h_op | h_op
      · rw [h_op] at hshj
        obtain ⟨a, b, _, _, _, _, heff, _, _, heval⟩ := hshj
        rw [heff] at hmj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmj
        intro y z hy hz
        rw [heval y, heval z]
        rcases hmj with rfl | rfl
        · rw [wireVal_input C 7 y p, wireVal_input C 7 z p, hy, hz]; simp
        · rw [wireVal_input C 7 y p, wireVal_input C 7 z p, hy, hz]; simp
      · rw [h_op] at hshj
        obtain ⟨a, _, _, heff, _, heval⟩ := hshj
        rw [heff] at hmj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmj
        subst hmj
        intro y z hy hz
        rw [heval y, heval z, wireVal_input C 7 y p, wireVal_input C 7 z p, hy, hz]
    -- Helper: if gate j has op = or and reads p, then wireVal (7+j) = true on x p = true
    have hval_or_true : ∀ (j : Fin C.size),
        p.val ∈ effInputs (C.gates[j.val]'j.isLt) (7 + j.val) →
        (C.gates[j.val]'j.isLt).op = GateOp.or →
        ∀ u : Fin 7 → Bool, u p = true → wireVal C 7 u (7 + j.val) = true := by
      intro j hmj h_op u hu
      have hshj := (not_elim_gate_shape C 7 (fun _ => True) hC j.val j.isLt (hnoelim j.val j.isLt)).2
      rw [h_op] at hshj
      obtain ⟨a, b, _, _, _, _, heff, _, _, heval⟩ := hshj
      rw [heff] at hmj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmj
      rw [heval u]
      rcases hmj with rfl | rfl
      · rw [wireVal_input C 7 u p, hu]; simp
      · rw [wireVal_input C 7 u p, hu]; simp
    by_cases h2an : (C.gates[j2.val]'j2.isLt).op = GateOp.and ∨ (C.gates[j2.val]'j2.isLt).op = GateOp.not
    · -- Subcase 1a: j2 is AND or NOT
      obtain ⟨k2, h2k2, _, hk2el⟩ := hconst_next p false j2 (hconst_false j2 hm2 h2an)
      refine ⟨p, false, ?_⟩
      simp only [Bool.false_eq_true, ite_false]
      have hsub : ({j1, j2, k2} : Finset (Fin C.size)) ⊆ elimSet C 7 (fun x => x p = false) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with hi | hi | hi
        · rw [hi]; exact hp_in_elim p false j1 hm1
        · rw [hi]; exact hp_in_elim p false j2 hm2
        · rw [hi]; exact hk2el
      have hne12 : j1 ≠ j2 := ne_of_lt h12
      have hne1k : j1 ≠ k2 := ne_of_lt (lt_trans h12 h2k2)
      have hne2k : j2 ≠ k2 := ne_of_lt h2k2
      have hcard : ({j1, j2, k2} : Finset (Fin C.size)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hne12, hne1k]), Finset.card_pair hne2k]
      rw [← hcard]
      exact Finset.card_le_card hsub
    · -- j2 must be OR
      have h2or : (C.gates[j2.val]'j2.isLt).op = GateOp.or := by
        rcases hop2 with h | h | h
        · exact absurd (Or.inl h) h2an
        · exact h
        · exact absurd (Or.inr h) h2an
      by_cases h1an : (C.gates[j1.val]'j1.isLt).op = GateOp.and ∨ (C.gates[j1.val]'j1.isLt).op = GateOp.not
      · -- Subcase 1b: j1 is AND or NOT, j2 is OR
        obtain ⟨k1, h1k1, hk1mem, hk1el⟩ := hconst_next p false j1 (hconst_false j1 hm1 h1an)
        have hk1_ne_j2 : k1 ≠ j2 := by
          intro heq
          rw [heq] at hk1mem
          rw [h2or] at hsh2
          obtain ⟨a2, b2, _, _, hab2, _, heff2, _, _, heval2⟩ := hsh2
          rw [heff2] at hm2 hk1mem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2 hk1mem
          have hpair : ∀ u : Fin 7 → Bool,
              wireVal C 7 u (7 + j2.val) = (u p || wireVal C 7 u (7 + j1.val)) := by
            intro u
            rw [heval2 u]
            have hne_p_j1 : p.val ≠ 7 + j1.val := by have := p.isLt; omega
            rcases hm2 with rfl | rfl <;> rcases hk1mem with h | h
            · exact absurd h.symm hne_p_j1
            · subst h; rw [wireVal_input C 7 u p]
            · subst h; rw [wireVal_input C 7 u p, Bool.or_comm]
            · exact absurd h.symm hne_p_j1
          rcases h1an with h1and | h1not
          · rw [h1and] at hsh1
            obtain ⟨a1, b1, _, _, _, _, heff1, _, _, heval1⟩ := hsh1
            rw [heff1] at hm1
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
            apply hnoelim j2.val j2.isLt
            right
            refine ⟨p.val, by have := p.isLt; omega, fun u _ => ?_⟩
            rw [hpair u, heval1 u, wireVal_input C 7 u p]
            rcases hm1 with rfl | rfl
            · rw [wireVal_input C 7 u p]; cases u p <;> simp
            · rw [wireVal_input C 7 u p]; cases u p <;> simp
          · rw [h1not] at hsh1
            obtain ⟨a1, _, _, heff1, _, heval1⟩ := hsh1
            rw [heff1] at hm1
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
            subst hm1
            apply hnoelim j2.val j2.isLt
            left
            intro y z _ _
            rw [hpair y, hpair z, heval1 y, heval1 z, wireVal_input C 7 y p, wireVal_input C 7 z p]
            cases y p <;> cases z p <;> rfl
        refine ⟨p, false, ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        have hsub : ({j1, j2, k1} : Finset (Fin C.size)) ⊆ elimSet C 7 (fun x => x p = false) := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with hi | hi | hi
          · rw [hi]; exact hp_in_elim p false j1 hm1
          · rw [hi]; exact hp_in_elim p false j2 hm2
          · rw [hi]; exact hk1el
        have hne12 : j1 ≠ j2 := ne_of_lt h12
        have hne1k : j1 ≠ k1 := ne_of_lt h1k1
        have hcard : ({j1, j2, k1} : Finset (Fin C.size)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hne12, hne1k]), Finset.card_pair hk1_ne_j2.symm]
        rw [← hcard]
        exact Finset.card_le_card hsub
      · -- Subcase 1c: both j1 and j2 are OR
        have h1or : (C.gates[j1.val]'j1.isLt).op = GateOp.or := by
          rcases hop1 with h | h | h
          · exact absurd (Or.inl h) h1an
          · exact h
          · exact absurd (Or.inr h) h1an
        have hc1 : IsConstOn C 7 (fun x => x p = true) (7 + j1.val) := fun y z hy hz => by
          rw [hval_or_true j1 hm1 h1or y hy, hval_or_true j1 hm1 h1or z hz]
        have hc2 : IsConstOn C 7 (fun x => x p = true) (7 + j2.val) := fun y z hy hz => by
          rw [hval_or_true j2 hm2 h2or y hy, hval_or_true j2 hm2 h2or z hz]
        obtain ⟨k1, h1k1, hk1mem, hk1el⟩ := hconst_next p true j1 hc1
        obtain ⟨k2, h2k2, hk2mem, hk2el⟩ := hconst_next p true j2 hc2
        have hk1_ne_j2 : k1 ≠ j2 := by
          intro heq
          rw [heq] at hk1mem
          rw [h2or] at hsh2
          obtain ⟨a2, b2, _, _, _, _, heff2, _, _, heval2⟩ := hsh2
          rw [heff2] at hm2 hk1mem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2 hk1mem
          have hpair : ∀ u : Fin 7 → Bool,
              wireVal C 7 u (7 + j2.val) = (u p || wireVal C 7 u (7 + j1.val)) := by
            intro u
            rw [heval2 u]
            have hne_p_j1 : p.val ≠ 7 + j1.val := by have := p.isLt; omega
            rcases hm2 with rfl | rfl <;> rcases hk1mem with h | h
            · exact absurd h.symm hne_p_j1
            · subst h; rw [wireVal_input C 7 u p]
            · subst h; rw [wireVal_input C 7 u p, Bool.or_comm]
            · exact absurd h.symm hne_p_j1
          rw [h1or] at hsh1
          obtain ⟨a1, b1, _, _, _, _, heff1, _, _, heval1⟩ := hsh1
          rw [heff1] at hm1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
          apply hnoelim j2.val j2.isLt
          right
          refine ⟨7 + j1.val, by omega, fun u _ => ?_⟩
          rw [hpair u, heval1 u]
          rcases hm1 with rfl | rfl
          · rw [wireVal_input C 7 u p]; cases u p <;> simp
          · rw [wireVal_input C 7 u p]; cases u p <;> simp
        refine ⟨p, true, ?_⟩
        simp only [ite_true]
        by_cases hk12 : k1 = k2
        · subst hk12
          have hshk := (not_elim_gate_shape C 7 (fun _ => True) hC k1.val k1.isLt (hnoelim k1.val k1.isLt)).2
          have hopk := (hC _ (List.getElem_mem k1.isLt)).1
          have hck : IsConstOn C 7 (fun x => x p = true) (7 + k1.val) := by
            have hne_j12 : 7 + j1.val ≠ 7 + j2.val := by
              have : j1.val < j2.val := h12; omega
            rcases hopk with h_op | h_op | h_op
            · rw [h_op] at hshk
              obtain ⟨ak, bk, _, _, _, _, heffk, _, _, hevalk⟩ := hshk
              rw [heffk] at hk1mem hk2mem
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hk1mem hk2mem
              intro y z hy hz
              rw [hevalk y, hevalk z]
              rcases hk1mem with rfl | rfl <;> rcases hk2mem with h | h
              · exact absurd h.symm hne_j12
              · subst h; rw [hc1 y z hy hz, hc2 y z hy hz]
              · subst h; rw [hc1 y z hy hz, hc2 y z hy hz]
              · exact absurd h.symm hne_j12
            · rw [h_op] at hshk
              obtain ⟨ak, bk, _, _, _, _, heffk, _, _, hevalk⟩ := hshk
              rw [heffk] at hk1mem hk2mem
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hk1mem hk2mem
              intro y z hy hz
              rw [hevalk y, hevalk z]
              rcases hk1mem with rfl | rfl <;> rcases hk2mem with h | h
              · exact absurd h.symm hne_j12
              · subst h; rw [hc1 y z hy hz, hc2 y z hy hz]
              · subst h; rw [hc1 y z hy hz, hc2 y z hy hz]
              · exact absurd h.symm hne_j12
            · rw [h_op] at hshk
              obtain ⟨ak, _, _, heffk, _, _⟩ := hshk
              rw [heffk] at hk1mem hk2mem
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hk1mem hk2mem
              exact absurd (hk1mem.trans hk2mem.symm) hne_j12
          obtain ⟨k3, hk13, _, hk3el⟩ := hconst_next p true k1 hck
          have hsub : ({j1, j2, k1, k3} : Finset (Fin C.size)) ⊆ elimSet C 7 (fun x => x p = true) := by
            intro i hi
            simp only [Finset.mem_insert, Finset.mem_singleton] at hi
            rcases hi with hi | hi | hi | hi
            · rw [hi]; exact hp_in_elim p true j1 hm1
            · rw [hi]; exact hp_in_elim p true j2 hm2
            · rw [hi]; exact hk1el
            · rw [hi]; exact hk3el
          have hcard : ({j1, j2, k1, k3} : Finset (Fin C.size)).card = 4 := by
            have h1k : j1 < k1 := h1k1
            have h2k : j2 < k1 := h2k2
            rw [Finset.card_insert_of_notMem (by simp [ne_of_lt h12, ne_of_lt h1k, ne_of_lt (lt_trans h1k hk13)]),
                Finset.card_insert_of_notMem (by simp [ne_of_lt h2k, ne_of_lt (lt_trans h2k hk13)]),
                Finset.card_pair (ne_of_lt hk13)]
          rw [← hcard]
          exact Finset.card_le_card hsub
        · have hsub : ({j1, j2, k1, k2} : Finset (Fin C.size)) ⊆ elimSet C 7 (fun x => x p = true) := by
            intro i hi
            simp only [Finset.mem_insert, Finset.mem_singleton] at hi
            rcases hi with hi | hi | hi | hi
            · rw [hi]; exact hp_in_elim p true j1 hm1
            · rw [hi]; exact hp_in_elim p true j2 hm2
            · rw [hi]; exact hk1el
            · rw [hi]; exact hk2el
          have hcard : ({j1, j2, k1, k2} : Finset (Fin C.size)).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp [ne_of_lt h12, ne_of_lt h1k1, ne_of_lt (lt_trans h12 h2k2)]),
                Finset.card_insert_of_notMem (by simp [hk1_ne_j2.symm, ne_of_lt h2k2]),
                Finset.card_pair hk12]
          rw [← hcard]
          exact Finset.card_le_card hsub
  · -- Case 2: Some NOT(p) feeds two distinct gates k1 < k2
    by_cases hCase2 : ∃ (p : Fin 7) (j1 k1 k2 : Fin C.size),
        (C.gates[j1.val]'j1.isLt).op = GateOp.not ∧
        p.val ∈ effInputs (C.gates[j1.val]'j1.isLt) (7 + j1.val) ∧
        k1 < k2 ∧
        7 + j1.val ∈ effInputs (C.gates[k1.val]'k1.isLt) (7 + k1.val) ∧
        7 + j1.val ∈ effInputs (C.gates[k2.val]'k2.isLt) (7 + k2.val)
    · obtain ⟨p, j1, k1, k2, hnot1, hm1, hk12, hmk1, hmk2⟩ := hCase2
      have hsh1 := (not_elim_gate_shape C 7 (fun _ => True) hC j1.val j1.isLt (hnoelim j1.val j1.isLt)).2
      rw [hnot1] at hsh1
      obtain ⟨a, _, _, heff1, _, heval1⟩ := hsh1
      rw [heff1] at hm1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
      subst hm1
      have hc1 : IsConstOn C 7 (fun x => x p = false) (7 + j1.val) := by
        intro y z hy hz
        rw [heval1 y, heval1 z, wireVal_input C 7 y p, wireVal_input C 7 z p, hy, hz]
      have hj1_lt_k1 : j1 < k1 := by
        unfold effInputs at hmk1
        have hlt := of_decide_eq_true (List.mem_filter.mp hmk1).2
        exact Fin.mk_lt_mk.mpr (by omega)
      refine ⟨p, false, ?_⟩
      simp only [Bool.false_eq_true, ite_false]
      have hsub : ({j1, k1, k2} : Finset (Fin C.size)) ⊆ elimSet C 7 (fun x => x p = false) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hi with hi | hi | hi
        · rw [hi]; exact Or.inl hc1
        · rw [hi]; exact elim_of_const_effInput C 7 (fun x => x p = false) hC k1.val k1.isLt (7 + j1.val) hmk1 hc1
        · rw [hi]; exact elim_of_const_effInput C 7 (fun x => x p = false) hC k2.val k2.isLt (7 + j1.val) hmk2 hc1
      have hcard : ({j1, k1, k2} : Finset (Fin C.size)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_of_lt hj1_lt_k1, ne_of_lt (lt_trans hj1_lt_k1 hk12)]),
            Finset.card_pair (ne_of_lt hk12)]
      rw [← hcard]
      exact Finset.card_le_card hsub
    · -- Case 3: Contradiction!
      exfalso
      have hfan1 : ∀ (p : Fin 7) (j1 j2 : Fin C.size),
          p.val ∈ effInputs (C.gates[j1.val]'j1.isLt) (7 + j1.val) →
          p.val ∈ effInputs (C.gates[j2.val]'j2.isLt) (7 + j2.val) → j1 = j2 := by
        intro p j1 j2 h1 h2
        rcases lt_trichotomy j1 j2 with hlt | heq | hgt
        · exact absurd ⟨p, j1, j2, hlt, h1, h2⟩ hCase1
        · exact heq
        · exact absurd ⟨p, j2, j1, hgt, h2, h1⟩ hCase1
      have hfanNot : ∀ (p : Fin 7) (j1 k1 k2 : Fin C.size),
          (C.gates[j1.val]'j1.isLt).op = GateOp.not →
          p.val ∈ effInputs (C.gates[j1.val]'j1.isLt) (7 + j1.val) →
          7 + j1.val ∈ effInputs (C.gates[k1.val]'k1.isLt) (7 + k1.val) →
          7 + j1.val ∈ effInputs (C.gates[k2.val]'k2.isLt) (7 + k2.val) → k1 = k2 := by
        intro p j1 k1 k2 hnot1 hm1 h1 h2
        rcases lt_trichotomy k1 k2 with hlt | heq | hgt
        · exact absurd ⟨p, j1, k1, k2, hnot1, hm1, hlt, h1, h2⟩ hCase2
        · exact heq
        · exact absurd ⟨p, j1, k2, k1, hnot1, hm1, hgt, h2, h1⟩ hCase2
      -- Helper: any prefix of NOT gates only negates input wires
      have hnot_prefix : ∀ (M : ℕ), (∀ j : ℕ, (hj : j < C.size) → j < M → (C.gates[j]'hj).op = GateOp.not) →
          ∀ j : ℕ, (hj : j < C.size) → j < M →
            ∃ p : Fin 7, effInputs (C.gates[j]'hj) (7 + j) = [p.val] ∧
              ∀ x, wireVal C 7 x (7 + j) = !(x p) := by
        intro M hM j
        induction j using Nat.strong_induction_on with
        | _ j ih =>
          intro hj hjM
          have hnotj := hM j hj hjM
          have hshj := (not_elim_gate_shape C 7 (fun _ => True) hC j hj (hnoelim j hj)).2
          rw [hnotj] at hshj
          obtain ⟨a, ha, _, heff, _, heval⟩ := hshj
          by_cases ha7 : a < 7
          · refine ⟨⟨a, ha7⟩, heff, fun x => ?_⟩
            rw [heval x, wireVal_input C 7 x ⟨a, ha7⟩]
          · set j' := a - 7
            have hj' : j' < j := by omega
            obtain ⟨q, _, hqeval⟩ := ih j' hj' (by omega) (by omega)
            exfalso
            apply hnoelim j hj
            right
            refine ⟨q.val, by have := q.isLt; omega, fun u _ => ?_⟩
            rw [heval u, show a = 7 + j' by omega, hqeval u, Bool.not_not, wireVal_input C 7 u q]
      -- Step 3.1: There must exist a non-NOT gate
      have hex_nonnot : ∃ m : ℕ, ∃ hm : m < C.size, (C.gates[m]'hm).op ≠ GateOp.not := by
        by_contra hall
        push Not at hall
        have hpref := hnot_prefix C.size (fun j hj _ => hall j hj)
        by_cases ho1 : C.output < 7
        · apply fC7_not_unary_on_fix ⟨0, by omega⟩ ⟨C.output, ho1⟩ false id
          intro x _
          rw [← hcomp x]
          exact wireVal_input C 7 x ⟨C.output, ho1⟩
        · by_cases ho2 : C.output < 7 + C.size
          · set j := C.output - 7
            obtain ⟨q, _, hqeval⟩ := hpref j (by omega) (by omega)
            apply fC7_not_unary_on_fix ⟨0, by omega⟩ q false Bool.not
            intro x _
            rw [← hcomp x]
            change wireVal C 7 x C.output = !(x q)
            rw [show C.output = 7 + j by omega, hqeval x]
          · obtain ⟨y, z, _, _, hne⟩ := fC7_nc ⟨0, by omega⟩ false
            apply hne
            rw [← hcomp y, ← hcomp z]
            change wireVal C 7 y C.output = wireVal C 7 z C.output
            rw [wireVal_oob C 7 y C.output (by omega), wireVal_oob C 7 z C.output (by omega)]
      let m := Nat.find hex_nonnot
      obtain ⟨hm, hm_nonnot⟩ := Nat.find_spec hex_nonnot
      have hbefore : ∀ j : ℕ, (hj : j < C.size) → j < m → (C.gates[j]'hj).op = GateOp.not := by
        intro j hj hjm
        by_contra hne
        exact Nat.find_min hex_nonnot hjm ⟨hj, hne⟩
      have hpref_m := hnot_prefix m hbefore
      have hm_or_and : (C.gates[m]'hm).op = GateOp.and ∨ (C.gates[m]'hm).op = GateOp.or := by
        rcases (hC _ (List.getElem_mem hm)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hm_nonnot
      -- Extract the two inputs w1, w2 of gate m
      have hshm := (not_elim_gate_shape C 7 (fun _ => True) hC m hm (hnoelim m hm)).2
      have hm_inputs : ∃ w1 w2 : ℕ, w1 < 7 + m ∧ w2 < 7 + m ∧ w1 ≠ w2 ∧
          effInputs (C.gates[m]'hm) (7 + m) = [w1, w2] ∧
          ((C.gates[m]'hm).op = GateOp.and ∧
            (∀ x, wireVal C 7 x (7 + m) = (wireVal C 7 x w1 && wireVal C 7 x w2)) ∨
           (C.gates[m]'hm).op = GateOp.or ∧
            (∀ x, wireVal C 7 x (7 + m) = (wireVal C 7 x w1 || wireVal C 7 x w2))) := by
        rcases hm_or_and with h_op | h_op
        · rw [h_op] at hshm
          obtain ⟨w1, w2, h1, h2, hne, _, heff, _, _, heval⟩ := hshm
          exact ⟨w1, w2, h1, h2, hne, heff, Or.inl ⟨h_op, heval⟩⟩
        · rw [h_op] at hshm
          obtain ⟨w1, w2, h1, h2, hne, _, heff, _, _, heval⟩ := hshm
          exact ⟨w1, w2, h1, h2, hne, heff, Or.inr ⟨h_op, heval⟩⟩
      obtain ⟨w1, w2, hw1, hw2, hw12, hmeff, hm_op_eval⟩ := hm_inputs
      -- Classify any wire w < 7 + m as either x p or !(x p)
      have hclassify : ∀ w : ℕ, w < 7 + m →
          ∃ (p : Fin 7) (pol : Bool),
            (pol = false ∧ w = p.val ∧ ∀ x, wireVal C 7 x w = x p) ∨
            (pol = true ∧ ∃ j : Fin C.size, j.val < m ∧ w = 7 + j.val ∧
              (C.gates[j.val]'j.isLt).op = GateOp.not ∧
              effInputs (C.gates[j.val]'j.isLt) (7 + j.val) = [p.val] ∧
              ∀ x, wireVal C 7 x w = !(x p)) := by
        intro w hw
        by_cases hw7 : w < 7
        · exact ⟨⟨w, hw7⟩, false, Or.inl ⟨rfl, rfl, fun x => wireVal_input C 7 x ⟨w, hw7⟩⟩⟩
        · set j : Fin C.size := ⟨w - 7, by omega⟩
          have hjm : j.val < m := by simp [j]; omega
          obtain ⟨p, hpeff, hpeval⟩ := hpref_m j.val j.isLt hjm
          refine ⟨p, true, Or.inr ⟨rfl, j, hjm, by simp [j]; omega, hbefore j.val j.isLt hjm, hpeff, ?_⟩⟩
          intro x
          rw [show w = 7 + j.val by simp [j]; omega]
          exact hpeval x
      obtain ⟨p1, pol1, hcl1⟩ := hclassify w1 hw1
      obtain ⟨p2, pol2, hcl2⟩ := hclassify w2 hw2
      have hval1 : ∀ x, wireVal C 7 x w1 = if pol1 then !(x p1) else x p1 := by
        intro x
        rcases hcl1 with ⟨rfl, _, hv⟩ | ⟨rfl, _, _, _, _, _, hv⟩
        · simp [hv x]
        · simp [hv x]
      have hval2 : ∀ x, wireVal C 7 x w2 = if pol2 then !(x p2) else x p2 := by
        intro x
        rcases hcl2 with ⟨rfl, _, hv⟩ | ⟨rfl, _, _, _, _, _, hv⟩
        · simp [hv x]
        · simp [hv x]
      -- Step 3.3: p1 ≠ p2
      have hp12 : p1 ≠ p2 := by
        intro heq
        subst heq
        rcases hcl1 with ⟨rfl, rfl, _⟩ | ⟨rfl, j1, _, rfl, _, _, hv1⟩ <;>
        rcases hcl2 with ⟨rfl, rfl, _⟩ | ⟨rfl, j2, _, rfl, _, _, hv2⟩
        · exact hw12 rfl
        · apply hnoelim m hm
          left
          intro y z _ _
          rcases hm_op_eval with ⟨_, hev⟩ | ⟨_, hev⟩
          · rw [hev y, hev z, wireVal_input C 7 y p1, wireVal_input C 7 z p1, hv2 y, hv2 z]
            cases y p1 <;> cases z p1 <;> rfl
          · rw [hev y, hev z, wireVal_input C 7 y p1, wireVal_input C 7 z p1, hv2 y, hv2 z]
            cases y p1 <;> cases z p1 <;> rfl
        · apply hnoelim m hm
          left
          intro y z _ _
          rcases hm_op_eval with ⟨_, hev⟩ | ⟨_, hev⟩
          · rw [hev y, hev z, hv1 y, hv1 z, wireVal_input C 7 y p1, wireVal_input C 7 z p1]
            cases y p1 <;> cases z p1 <;> rfl
          · rw [hev y, hev z, hv1 y, hv1 z, wireVal_input C 7 y p1, wireVal_input C 7 z p1]
            cases y p1 <;> cases z p1 <;> rfl
        · rcases lt_trichotomy j1 j2 with hlt | rfl | hgt
          · apply hnoelim j2.val j2.isLt
            right
            refine ⟨7 + j1.val, by omega, fun u _ => ?_⟩
            rw [hv2 u, hv1 u]
          · exact hw12 rfl
          · apply hnoelim j1.val j1.isLt
            right
            refine ⟨7 + j2.val, by omega, fun u _ => ?_⟩
            rw [hv1 u, hv2 u]
      -- Step 3.4: Choose b1 so gate m is constant on x p1 = b1
      have hchoose_b1 : ∃ b1 : Bool, IsConstOn C 7 (fun x => x p1 = b1) (7 + m) := by
        rcases hm_op_eval with ⟨_, hev⟩ | ⟨_, hev⟩
        · refine ⟨pol1, fun y z hy hz => ?_⟩
          rw [hev y, hev z, hval1 y, hval1 z, hy, hz]
          cases pol1 <;> simp
        · refine ⟨!pol1, fun y z hy hz => ?_⟩
          rw [hev y, hev z, hval1 y, hval1 z, hy, hz]
          cases pol1 <;> simp
      obtain ⟨b1, hconst_m⟩ := hchoose_b1
      -- Step 3.5: On x p1 = b1, flipping p2 leaves every wire other than p2 and w2 unchanged
      have hflip_inv : ∀ (x : Fin 7 → Bool), x p1 = b1 →
          ∀ w : ℕ, w ≠ p2.val → w ≠ w2 →
            wireVal C 7 (Function.update x p2 (!x p2)) w = wireVal C 7 x w := by
        intro x hxp1 w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro hnep2 hnew2
          set x' := Function.update x p2 (!x p2)
          have hx'p1 : x' p1 = b1 := by
            simp only [x', Function.update_of_ne hp12, hxp1]
          by_cases hw7 : w < 7
          · have h1 := wireVal_input C 7 x' ⟨w, hw7⟩
            have h2 := wireVal_input C 7 x ⟨w, hw7⟩
            dsimp at h1 h2
            rw [h1, h2]
            exact Function.update_of_ne (fun heq => hnep2 (congrArg Fin.val heq)) _ _
          · by_cases hwlt : w < 7 + C.size
            · set j := w - 7
              have hj : j < C.size := by omega
              have hwj : w = 7 + j := by omega
              rw [hwj]
              by_cases hjm : j = m
              · rw [hjm]
                exact hconst_m x' x hx'p1 hxp1
              · apply wireVal_gate_congr C 7 x' x j hj (hC _ (List.getElem_mem hj)).1
                intro u hu
                have hult : u < 7 + j := of_decide_eq_true (List.mem_filter.mp hu).2
                have hunep2 : u ≠ p2.val := by
                  intro heq
                  subst heq
                  rcases hcl2 with ⟨_, rfl, _⟩ | ⟨_, j2, _, hw2eq, _, hj2eff, _⟩
                  · have hm_has_p2 : p2.val ∈ effInputs (C.gates[m]'hm) (7 + m) := by
                      rw [hmeff]; simp
                    have heq_jm := hfan1 p2 ⟨j, hj⟩ ⟨m, hm⟩ hu hm_has_p2
                    exact hjm (congrArg Fin.val heq_jm)
                  · have hj2_has_p2 : p2.val ∈ effInputs (C.gates[j2.val]'j2.isLt) (7 + j2.val) := by
                      rw [hj2eff]; simp
                    have heq_jj2 := hfan1 p2 ⟨j, hj⟩ j2 hu hj2_has_p2
                    have heq_val : j = j2.val := congrArg Fin.val heq_jj2
                    apply hnew2
                    rw [hwj, hw2eq, heq_val]
                have hunew2 : u ≠ w2 := by
                  intro heq
                  subst heq
                  rcases hcl2 with ⟨_, hw2eq, _⟩ | ⟨_, j2, _, hw2eq, hj2not, hj2eff, _⟩
                  · exact hunep2 hw2eq
                  · have hj2_has_p2 : p2.val ∈ effInputs (C.gates[j2.val]'j2.isLt) (7 + j2.val) := by
                      rw [hj2eff]; simp
                    have hm_has_w2 : 7 + j2.val ∈ effInputs (C.gates[m]'hm) (7 + m) := by
                      rw [hmeff, hw2eq]; simp
                    rw [hw2eq] at hu
                    have heq_jm := hfanNot p2 j2 ⟨j, hj⟩ ⟨m, hm⟩ hj2not hj2_has_p2 hu hm_has_w2
                    exact hjm (congrArg Fin.val heq_jm)
                exact ih u (by omega) hunep2 hunew2
            · rw [wireVal_oob C 7 x' w (by omega), wireVal_oob C 7 x w (by omega)]
      -- Step 3.6: C.output cannot be p2.val or w2, giving final contradiction
      have hout_nep2 : C.output ≠ p2.val := by
        intro heq
        apply fC7_not_unary_on_fix p1 p2 b1 id
        intro x _
        rw [← hcomp x]
        change wireVal C 7 x C.output = x p2
        rw [heq, wireVal_input C 7 x p2]
      have hout_new2 : C.output ≠ w2 := by
        intro heq
        apply fC7_not_unary_on_fix p1 p2 b1 (fun t => if pol2 then !t else t)
        intro x _
        rw [← hcomp x]
        change wireVal C 7 x C.output = _
        rw [heq, hval2 x]
      obtain ⟨x, hxp1, hxne⟩ := fC7_dep_after_fix p1 p2 b1 hp12
      apply hxne
      rw [← hcomp, ← hcomp]
      exact hflip_inv x hxp1 C.output hout_nep2 hout_new2

theorem no_size_le_9 : ∀ s : ℕ, s ≤ 9 → ¬ HasCircuitSize 7 fC7 s := by
  intro s hs h
  obtain ⟨C, hC, hsz, hcomp, hmin⟩ := exists_minimal_circuit 7 fC7 s h
  have hnc_global : ∃ y z : Fin 7 → Bool, fC7 y ≠ fC7 z := by
    obtain ⟨y, z, _, _, hne⟩ := fC7_nc ⟨0, by omega⟩ false
    exact ⟨y, z, hne⟩
  have hnodead : ∀ j : ℕ, (hj : j < C.size) → ¬ IsDead C 7 j :=
    minimal_no_dead 7 fC7 C hC hcomp hmin
  have hnoelim : ∀ j : ℕ, (hj : j < C.size) → ¬ IsElim C 7 (fun _ => True) j :=
    minimal_no_elim 7 fC7 C hC hcomp hmin hnc_global
  obtain ⟨p, b, hcard⟩ := fanout_tight C hC hcomp hnodead hnoelim
  have hnc_P : ∃ y z : Fin 7 → Bool,
      y p = b ∧ z p = b ∧ C.eval (List.ofFn y) ≠ C.eval (List.ofFn z) := by
    obtain ⟨y, z, hy, hz, hne⟩ := fC7_nc p b
    exact ⟨y, z, hy, hz, by rw [hcomp y, hcomp z]; exact hne⟩
  obtain ⟨C', hC', hsz', hev', hunused'⟩ := elim_circuit C 7 (fun x => x p = b) hC hnc_P
  have hpconst : IsConstOn C 7 (fun x => x p = b) p.val := by
    intro y z hy hz
    rw [wireVal_input C 7 y p, wireVal_input C 7 z p, hy, hz]
  obtain ⟨hout', hpu'⟩ := hunused' p hpconst
  have hcomp_upd : HasCircuitSize 7 (fun x => fC7 (Function.update x p b)) C'.size := by
    refine ⟨C', hC', le_rfl, fun x => ?_⟩
    have hupd_eq : C'.eval (List.ofFn x) = C'.eval (List.ofFn (Function.update x p b)) := by
      apply wireVal_indep_of_unused C' 7 hC' p hpu'
      · intro i hi; simp [Function.update_of_ne hi]
      · exact hout'
    rw [hupd_eq, hev' (Function.update x p b) (by simp), hcomp]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hcard
    have h6 := rename_size (piFalse p) _ C'.size hcomp_upd
    have heq : (fun y : Fin 6 → Bool =>
        (fun x => fC7 (Function.update x p false)) (y ∘ piFalse p)) = G 6 0 := by
      funext y; exact fC7_del_false p y
    rw [heq] at h6
    have hlb := G_lower 6 (by omega) 0 6 C'.size rfl h6
    omega
  | true =>
    simp only [ite_true] at hcard
    have h6 := rename_size (piTrue p) _ C'.size hcomp_upd
    have heq : (fun y : Fin 6 → Bool =>
        (fun x => fC7 (Function.update x p true)) (y ∘ piTrue p)) = G 6 2 := by
      funext y; exact fC7_del_true p y
    rw [heq] at h6
    have hlb := G_lower 4 (by omega) 2 6 C'.size rfl h6
    omega

end PEqualNP.Outside.L_meta_1413

theorem PEqualNP.Outside.L_meta_1413 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → C.size = 10 → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = true ↔ ∃ i : Fin 7, x i = true ∧ x (i + 1) = true) → ∃ (p : Fin 7) (b : Bool) (S : Finset (Fin 10)), (if b = true then 4 else 3) ≤ S.card ∧ ∀ j ∈ S, (∀ y z : Fin 7 → Bool, y p = b → z p = b → (C.wires (List.ofFn y)).getD (7 + ((j : Fin 10) : ℕ)) false = (C.wires (List.ofFn z)).getD (7 + ((j : Fin 10) : ℕ)) false) ∨ ∃ w < 7 + ((j : Fin 10) : ℕ), ∀ u : Fin 7 → Bool, u p = b → (C.wires (List.ofFn u)).getD (7 + ((j : Fin 10) : ℕ)) false = (C.wires (List.ofFn u)).getD w false := by
  intro C hC hsz hspec
  have hcomp : PEqualNP.Outside.L_meta_1413.Computes 7 C PEqualNP.Outside.L_meta_1413.fC7 := by
    intro x
    rw [Bool.eq_iff_iff, hspec x]
    simp [PEqualNP.Outside.L_meta_1413.fC7]
  have hnodead : ∀ j : ℕ, (hj : j < C.size) → ¬ PEqualNP.Outside.L_meta_1413.IsDead C 7 j := by
    intro j hj hdead
    obtain ⟨C', hC', hsz', hev'⟩ := PEqualNP.Outside.L_meta_1413.elim_dead_gate C 7 hC j hj hdead
    exact PEqualNP.Outside.L_meta_1413.no_size_le_9 9 le_rfl
      ⟨C', hC', by omega, fun x => by rw [hev' x, hcomp x]⟩
  have hnoelim : ∀ j : ℕ, (hj : j < C.size) →
      ¬ PEqualNP.Outside.L_meta_1413.IsElim C 7 (fun _ => True) j := by
    intro j hj hel
    have hnc_out : ∃ y z : Fin 7 → Bool,
        True ∧ True ∧ C.eval (List.ofFn y) ≠ C.eval (List.ofFn z) := by
      obtain ⟨y, z, _, _, hne⟩ := PEqualNP.Outside.L_meta_1413.fC7_nc ⟨0, by omega⟩ false
      exact ⟨y, z, trivial, trivial, by rw [hcomp y, hcomp z]; exact hne⟩
    obtain ⟨C', hC', hsz', hev', _⟩ :=
      PEqualNP.Outside.L_meta_1413.elim_circuit C 7 (fun _ => True) hC hnc_out
    have hcard : 1 ≤ (PEqualNP.Outside.L_meta_1413.elimSet C 7 (fun _ => True)).card := by
      classical
      apply Finset.card_pos.mpr
      refine ⟨⟨j, hj⟩, ?_⟩
      simp [PEqualNP.Outside.L_meta_1413.elimSet, hel]
    exact PEqualNP.Outside.L_meta_1413.no_size_le_9 9 le_rfl
      ⟨C', hC', by omega, fun x => by rw [hev' x trivial, hcomp x]⟩
  obtain ⟨p, b, hcard⟩ := PEqualNP.Outside.L_meta_1413.fanout_tight C hC hcomp hnodead hnoelim
  let emb : Fin C.size ↪ Fin 10 := ⟨Fin.cast hsz, Fin.cast_injective hsz⟩
  refine ⟨p, b, (PEqualNP.Outside.L_meta_1413.elimSet C 7 (fun x => x p = b)).map emb, ?_, ?_⟩
  · rw [Finset.card_map]
    exact hcard
  · intro j hj
    obtain ⟨j0, hj0, rfl⟩ := Finset.mem_map.mp hj
    classical
    simp only [PEqualNP.Outside.L_meta_1413.elimSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hj0
    exact hj0

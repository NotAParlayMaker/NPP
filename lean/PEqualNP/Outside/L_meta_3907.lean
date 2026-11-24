import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3907_aux

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem drun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

theorem drun_single (g : Gate) (x : List Bool) :
    drun [g] x = x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)] :=
  rfl

theorem drun_append (A B : List Gate) (x : List Bool) : drun (A ++ B) x = drun B (drun A x) := by
  simp [drun, List.foldl_append]

theorem drun_length (gs : List Gate) (x : List Bool) :
    (drun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [drun]
  | cons g gs ih => rw [drun_cons, ih]; simp; omega

theorem drun_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (drun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [drun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

theorem drun_gate (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate) (hg : gs[j]? = some g) :
    (drun gs x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun i => (drun (gs.take j) x).getD i false) := by
  have hj : j < gs.length := by
    rcases Nat.lt_or_ge j gs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hg
      exact absurd hg (by simp)
  have hgj : gs[j] = g := by
    rw [List.getElem?_eq_getElem hj] at hg
    exact Option.some.inj hg
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
  have htl : (drun (gs.take j) x).length = x.length + j := by
    rw [drun_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have e1 : drun gs x = drun (gs.drop (j + 1)) (drun [g] (drun (gs.take j) x)) := by
    conv_lhs => rw [hsplit]
    rw [show gs.take j ++ gs[j] :: gs.drop (j + 1) = gs.take j ++ ([gs[j]] ++ gs.drop (j + 1)) from rfl,
      drun_append, drun_append, hgj]
  have hlen1 : x.length + j < (drun [g] (drun (gs.take j) x)).length := by
    rw [drun_single, List.length_append, htl, List.length_singleton]
    omega
  rw [e1, drun_getD _ _ _ hlen1, drun_single, List.getD_append_right _ _ _ _ (le_of_eq htl),
    htl, Nat.sub_self, List.getD_cons_zero]

theorem drun_prefix (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j ≤ gs.length) (i : ℕ) :
    (drun (gs.take j) x).getD i false = if i < x.length + j then (drun gs x).getD i false else false := by
  have htl : (drun (gs.take j) x).length = x.length + j := by
    rw [drun_length, List.length_take, Nat.min_eq_left hj]
  split_ifs with h
  · have e : drun gs x = drun (gs.drop j) (drun (gs.take j) x) := by
      rw [← drun_append, List.take_append_drop]
    rw [e, drun_getD (gs.drop j) (drun (gs.take j) x) i (by rw [htl]; exact h)]
  · exact List.getD_eq_default _ _ (by rw [htl]; omega)

def W (C : Circuit) (y : Fin 9 → Bool) (i : ℕ) : Bool := (C.wires (List.ofFn y)).getD i false

def enc (v : Fin 17) (i : ℕ) : Bool ⊕ Fin 17 :=
  if h : i < (v : ℕ) then Sum.inr ⟨i, lt_trans h v.isLt⟩ else Sum.inl false

theorem enc_val (C : Circuit) (v : Fin 17) (i : ℕ) (y : Fin 9 → Bool) :
    Sum.elim id (fun u : Fin 17 => W C y u) (enc v i) = if i < (v : ℕ) then W C y i else false := by
  unfold enc
  split_ifs <;> rfl

theorem enc_lt (v : Fin 17) (i : ℕ) (u : Fin 17) (h : enc v i = Sum.inr u) : u < v := by
  unfold enc at h
  by_cases hi : i < (v : ℕ)
  · rw [dif_pos hi] at h
    cases h
    exact hi
  · rw [dif_neg hi] at h
    cases h

theorem gate_shape (C : Circuit) (hmono : Monotone2 C) (hsize : C.size = 8) (v : Fin 17)
    (hv : 9 < (v : ℕ)) :
    ∃ (a b : Bool ⊕ Fin 17), (∀ u : Fin 17, a = Sum.inr u ∨ b = Sum.inr u → u < v) ∧
      ((∀ y : Fin 9 → Bool, W C y v =
          (Sum.elim id (fun u : Fin 17 => W C y u) a && Sum.elim id (fun u : Fin 17 => W C y u) b)) ∨
       (∀ y : Fin 9 → Bool, W C y v =
          (Sum.elim id (fun u : Fin 17 => W C y u) a || Sum.elim id (fun u : Fin 17 => W C y u) b))) := by
  have hlen : C.gates.length = 8 := hsize
  have hj : (v : ℕ) - 9 < C.gates.length := by
    have := v.isLt
    omega
  obtain ⟨g, hg⟩ : ∃ g, C.gates[(v : ℕ) - 9]? = some g := ⟨_, List.getElem?_eq_getElem hj⟩
  have hmem : g ∈ C.gates := List.mem_iff_getElem?.mpr ⟨_, hg⟩
  obtain ⟨hop, hle⟩ := hmono g hmem
  have key : ∀ y : Fin 9 → Bool, W C y v =
      g.op.eval (g.inputs.map fun i => Sum.elim id (fun u : Fin 17 => W C y u) (enc v i)) := by
    intro y
    have h1 := drun_gate C.gates (List.ofFn y) ((v : ℕ) - 9) g hg
    rw [List.length_ofFn, show 9 + ((v : ℕ) - 9) = (v : ℕ) by omega] at h1
    show (drun C.gates (List.ofFn y)).getD (v : ℕ) false = _
    rw [h1]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [enc_val, drun_prefix C.gates (List.ofFn y) ((v : ℕ) - 9) (le_of_lt hj) i, List.length_ofFn,
      show 9 + ((v : ℕ) - 9) = (v : ℕ) by omega]
    rfl
  have hbd : ∀ i k : ℕ, ∀ u : Fin 17, enc v i = Sum.inr u ∨ enc v k = Sum.inr u → u < v := by
    intro i k u hu
    rcases hu with hu | hu
    · exact enc_lt v i u hu
    · exact enc_lt v k u hu
  rcases hop with hop | hop
  · rcases hlist : g.inputs with _ | ⟨i, _ | ⟨k, _ | ⟨m, rest⟩⟩⟩
    · refine ⟨Sum.inl true, Sum.inl true, fun u hu => (by rcases hu with hu | hu <;> cases hu), Or.inl fun y => ?_⟩
      rw [key y, hop, hlist]
      rfl
    · refine ⟨enc v i, enc v i, hbd i i, Or.inl fun y => ?_⟩
      rw [key y, hop, hlist]
      simp [GateOp.eval]
    · refine ⟨enc v i, enc v k, hbd i k, Or.inl fun y => ?_⟩
      rw [key y, hop, hlist]
      simp [GateOp.eval]
    · rw [hlist] at hle
      simp at hle
  · rcases hlist : g.inputs with _ | ⟨i, _ | ⟨k, _ | ⟨m, rest⟩⟩⟩
    · refine ⟨Sum.inl false, Sum.inl false, fun u hu => (by rcases hu with hu | hu <;> cases hu), Or.inr fun y => ?_⟩
      rw [key y, hop, hlist]
      rfl
    · refine ⟨enc v i, enc v i, hbd i i, Or.inr fun y => ?_⟩
      rw [key y, hop, hlist]
      simp [GateOp.eval]
    · refine ⟨enc v i, enc v k, hbd i k, Or.inr fun y => ?_⟩
      rw [key y, hop, hlist]
      simp [GateOp.eval]
    · rw [hlist] at hle
      simp at hle

end PEqualNP.Outside.L_meta_3907_aux

theorem PEqualNP.Outside.L_meta_3907 : have x1 : (Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) → Bool ⊕ Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) (x2 : Bool ⊕ Fin (17 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => Sum.elim id (fun (x4 : Fin (17 : ℕ)) => x1 x4 x3) x2; have x2 : (Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) → Fin (17 : ℕ) → Prop := fun (x2 : Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) (x3 : Fin (17 : ℕ)) => ∃ (x4 : Bool ⊕ Fin (17 : ℕ)) (x5 : Bool ⊕ Fin (17 : ℕ)), (∀ (x6 : Fin (17 : ℕ)), x4 = Sum.inr x6 ∨ x5 = Sum.inr x6 → x6 < x3) ∧ ((∀ (x6 : Fin (9 : ℕ) → Bool), x2 x3 x6 = (x1 x2 x4 x6 && x1 x2 x5 x6)) ∨ ∀ (x6 : Fin (9 : ℕ) → Bool), x2 x3 x6 = (x1 x2 x4 x6 || x1 x2 x5 x6)); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size = (8 : ℕ) → ∀ (x6 : Fin (17 : ℕ)), (9 : ℕ) < ↑x6 → x2 (fun (x8 : Fin (17 : ℕ)) (x9 : Fin (9 : ℕ) → Bool) => (x3.wires (List.ofFn x9)).getD (↑x8) Bool.false) x6 := by
  dsimp only
  intro C hmono hsize v hv
  exact PEqualNP.Outside.L_meta_3907_aux.gate_shape C hmono hsize v hv

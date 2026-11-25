import PEqualNP.Defs

-- The wire evaluation lemmas and gate compilation induction adapt L_meta_17201.
-- Here a representative wire need only agree on the prescribed set of inputs.
namespace PEqualNP.Outside.L_meta_17573_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false
theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem compile {n : ℕ} (C : Circuit) (T : Set (Fin n → Bool)) (S : Finset ℕ)
    (fan : FanInTwo C) (bounds : ∀ j∈S, j < C.size)
    (dup : ∀ j∈S, ∃ i < n+j, ∀ x : T, val C.gates (n+j) x.val = val C.gates i x.val) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + S.card ≤ C.size ∧
      ∀ x : T, D.eval (List.ofFn x.val) = C.eval (List.ofFn x.val) := by
  classical
  let z := n + C.size
  let Rep := fun (gs : List Gate) (i : ℕ) => ∃ a : ℕ,
    (a < n + gs.length ∨ a = z) ∧ ∀ x : T, val gs a x.val = val C.gates i x.val
  have go (k : ℕ) (hk : k ≤ C.size) : ∃ gs : List Gate,
      FanInTwo ⟨gs,0⟩ ∧ gs.length + (S.filter (· < k)).card = k ∧
      ∀ i < n+k, Rep gs i := by
    induction k with
    | zero =>
      refine ⟨[], by simp [FanInTwo], by simp, ?_⟩
      intro i hi
      have il : i < n := by omega
      refine ⟨i, Or.inl (by simpa), fun x => ?_⟩
      rw [val_input _ _ _ il, val_input _ _ _ il]
    | succ k ih =>
      obtain ⟨gs,hg,cnt,rep⟩ := ih (by omega)
      have small : gs.length ≤ k := by omega
      have newCount : S.filter (· < k+1) = if k∈S then insert k (S.filter (· < k)) else S.filter (· < k) := by
        ext j
        by_cases eq : j=k
        · subst j; by_cases h : k∈S <;> simp [h]
        · have lt : j ≤ k ↔ j < k := by omega
          by_cases h : k∈S <;> simp [h,eq,lt]
      have outsideFilter : k ∉ S.filter (· < k) := by simp
      by_cases h : k∈S
      · refine ⟨gs,hg,by rw [newCount,if_pos h,Finset.card_insert_of_notMem outsideFilter]; omega,?_⟩
        intro i hi
        by_cases old : i < n+k
        · exact rep i old
        have eq : i=n+k := by omega
        subst i
        obtain ⟨j,jl,same⟩ := dup k h
        obtain ⟨a,ha,r⟩ := rep j jl
        exact ⟨a,ha,fun x => (r x).trans (same x).symm⟩
      · have kl : k < C.gates.length := by change k < C.size; omega
        let g := C.gates[k]
        have source (i : ℕ) : ∃ a : ℕ, (a < n+gs.length ∨ a=z) ∧ ∀ x : T,
            val gs a x.val = (wf (C.gates.take k) (List.ofFn x.val)).getD i false := by
          by_cases hi : i<n+k
          · obtain ⟨a,ha,ra⟩ := rep i hi
            exact ⟨a,ha,fun x => (ra x).trans (wire_take _ _ k i (by simpa using hi) (by omega))⟩
          · exact ⟨z,Or.inr rfl,fun x => (val_big _ _ _ (by dsimp [z];omega)).trans
              (List.getD_eq_default _ _ (by rw [wf_len,List.length_ofFn,List.length_take,Nat.min_eq_left (by omega : k ≤ C.gates.length)]; omega)).symm⟩
        let idx := fun i => (source i).choose
        let newGate : Gate := ⟨g.op,g.inputs.map idx⟩
        let ns := gs ++ [newGate]
        have outputEq (x : T) : val ns (n+gs.length) x.val = val C.gates (n+k) x.val := by
          have old := gate_val C.gates (List.ofFn x.val) k kl
          rw [List.length_ofFn] at old
          unfold val
          rw [old]
          change (wf (gs ++ [newGate]) (List.ofFn x.val)).getD _ false = _
          rw [wf_snoc]
          have leq : (wf gs (List.ofFn x.val)).length = n+gs.length := by simp [wf_len]
          rw [←leq,getD_snoc_eq]
          apply congrArg g.op.eval
          simp only [newGate,List.map_map]
          exact List.map_congr_left (fun i _ => (source i).choose_spec.2 x)
        refine ⟨ns,?_,by rw [newCount,if_neg h]; simp only [ns,List.length_append,List.length_singleton]; omega,?_⟩
        · intro q hq
          change q ∈ gs ++ [newGate] at hq
          rcases List.mem_append.mp hq with hq|hq
          · exact hg q hq
          · have heq : q=newGate := by simpa using hq
            subst q
            have ok := fan g (List.getElem_mem kl)
            simpa [newGate] using ok
        · intro i hi
          by_cases prior : i < n+k
          · obtain ⟨a,ha,ra⟩ := rep i prior
            refine ⟨a,ha.imp_left (fun lt => by simp [ns];omega),fun x => ?_⟩
            rcases ha with al|rfl
            · exact (wf_prefix gs [newGate] (List.ofFn x.val) a (by simpa using al)).trans (ra x)
            · exact (val_big ns x.val _ (by simp [z,ns];omega)).trans ((val_big gs x.val _ (by simp [z];omega)).symm.trans (ra x))
          · have same : i=n+k := by omega
            exact ⟨n+gs.length,Or.inl (by simp [ns]),same ▸ outputEq⟩
  obtain ⟨gs,fanGs,count,reps⟩ := go C.size le_rfl
  have full : S.filter (· < C.size) = S := Finset.filter_true_of_mem bounds
  rw [full] at count
  by_cases out : C.output < n+C.size
  · obtain ⟨a,_,resultEq⟩ := reps _ out
    exact ⟨⟨gs,a⟩,fanGs,count.le,resultEq⟩
  · exact ⟨⟨[],n⟩,by simp [FanInTwo],by change 0 + S.card ≤ C.size; omega,
      fun x => (val_big [] x.val n (by simp)).trans
        (val_big C.gates x.val C.output (by change n+C.size ≤ C.output;omega)).symm⟩
end PEqualNP.Outside.L_meta_17573_aux

open PEqualNP.Outside.L_meta_17573_aux in
theorem PEqualNP.Outside.L_meta_17573 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Set (List Bool)) (x4 : Finset (Fin x1.size)), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x6 ∈ x3, x6.length = x2) → (∀ x7 ∈ x4, ∃ x9 < x2 + ↑x7, ∀ x10 ∈ x3, (x1.wires x10).getD (x2 + ↑x7) Bool.false = (x1.wires x10).getD x9 Bool.false) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + x4.card ≤ x1.size ∧ ∀ x9 ∈ x3, x8.eval x9 = x1.eval x9 := by
  classical
  intro C n X S fan lengths copies
  let T : Set (Fin n → Bool) := {f | List.ofFn f ∈ X}
  let I := S.image Fin.val
  have bound : ∀ j ∈ I, j < C.size := by
    intro j hj
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hj
    exact v.isLt
  have dup : ∀ j ∈ I, ∃ i < n+j, ∀ x : T, val C.gates (n+j) x.val = val C.gates i x.val := by
    intro j hj
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨i,hi,eq⟩ := copies v hv
    exact ⟨i,hi,fun x => eq _ x.property⟩
  obtain ⟨D,hd,hs,he⟩ := compile C T I fan bound dup
  have card : I.card = S.card := Finset.card_image_of_injective _ Fin.val_injective
  refine ⟨D,hd,by simpa only [card] using hs,?_⟩
  intro y hy
  have repr : ∃ f : Fin n → Bool, List.ofFn f = y := by
    have hlen := lengths y hy
    subst n
    exact ⟨y.get, List.ofFn_get y⟩
  obtain ⟨f,rfl⟩ := repr
  exact he ⟨f,hy⟩

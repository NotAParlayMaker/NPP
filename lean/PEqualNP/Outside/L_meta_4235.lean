import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4235

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def supp {n : ℕ} (E : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ e ∈ E, v ∈ e)

theorem peel_edges (n k : ℕ) :
    ∀ (m : ℕ) (V : Finset (Fin n)) (E : Finset (Sym2 (Fin n))),
      V.card = m → supp E ⊆ V →
      ∃ E' ⊆ E, E.card ≤ k * V.card + E'.card ∧
        ∀ v : Fin n, (E'.filter (fun e => v ∈ e)).card = 0 ∨ k < (E'.filter (fun e => v ∈ e)).card := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro V E hm hsub
    by_cases hdone : ∀ v : Fin n, (E.filter (fun e => v ∈ e)).card = 0 ∨ k < (E.filter (fun e => v ∈ e)).card
    · exact ⟨E, Finset.Subset.rfl, Nat.le_add_left _ _, hdone⟩
    · push Not at hdone
      rcases hdone with ⟨v, hv0, hvk⟩
      have hv_pos : 0 < (E.filter (fun e => v ∈ e)).card := Nat.pos_of_ne_zero hv0
      obtain ⟨e0, he0⟩ := Finset.card_pos.mp hv_pos
      rw [Finset.mem_filter] at he0
      have hv_supp : v ∈ supp E := by
        rw [supp, Finset.mem_filter]
        exact ⟨Finset.mem_univ v, e0, he0.1, he0.2⟩
      have hvV : v ∈ V := hsub hv_supp
      let Ev := E.filter (fun e => v ∈ e)
      let Er := E.filter (fun e => v ∉ e)
      have hEvk : Ev.card ≤ k := hvk
      have hdisj : Disjoint Ev Er := by
        rw [Finset.disjoint_left]
        intro e hev her
        rw [Finset.mem_filter] at hev her
        exact her.2 hev.2
      have hunion : Ev ∪ Er = E := by
        ext e
        simp only [Ev, Er, Finset.mem_union, Finset.mem_filter]
        tauto
      have hcard_split : E.card = Ev.card + Er.card := by
        rw [← hunion, Finset.card_union_of_disjoint hdisj]
      have hsub_erase : supp Er ⊆ V.erase v := by
        intro u hu
        rw [supp, Finset.mem_filter] at hu
        rcases hu with ⟨_, e, he, hue⟩
        rw [Finset.mem_filter] at he
        have huv : u ≠ v := fun h => he.2 (h ▸ hue)
        have hu_supp : u ∈ supp E := by
          rw [supp, Finset.mem_filter]
          exact ⟨Finset.mem_univ u, e, he.1, hue⟩
        exact Finset.mem_erase.mpr ⟨huv, hsub hu_supp⟩
      have hlt : (V.erase v).card < m := by
        rw [← hm]
        exact Finset.card_erase_lt_of_mem hvV
      obtain ⟨E', hE'sub, hE'card, hE'deg⟩ := ih (V.erase v).card hlt (V.erase v) Er rfl hsub_erase
      refine ⟨E', Finset.Subset.trans hE'sub (Finset.filter_subset _ _), ?_, hE'deg⟩
      have hVcard : V.card = (V.erase v).card + 1 := (Finset.card_erase_add_one hvV).symm
      rw [hcard_split, hVcard, Nat.mul_add, Nat.mul_one]
      omega

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def backReachAux (start : ℕ) (init : Finset ℕ) : List Gate → Finset ℕ
  | [] => init
  | g :: gs =>
    let S := backReachAux (start + 1) init gs
    if start ∈ S then S ∪ (g.inputs.toFinset.filter (fun i => i < start)) else S

theorem init_subset_backReachAux (start : ℕ) (init : Finset ℕ) (gs : List Gate) :
    init ⊆ backReachAux start init gs := by
  induction gs generalizing start with
  | nil => exact Finset.Subset.rfl
  | cons g gs ih =>
    dsimp [backReachAux]
    split_ifs
    · exact Finset.Subset.trans (ih (start + 1)) Finset.subset_union_left
    · exact ih (start + 1)

theorem backReachAux_small_init (start : ℕ) (init : Finset ℕ) (gs : List Gate)
    (hinit : ∀ w ∈ init, w < start) :
    backReachAux start init gs = init := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    dsimp [backReachAux]
    have h1 : ∀ w ∈ init, w < start + 1 := fun w hw => Nat.lt_succ_of_lt (hinit w hw)
    rw [ih (start + 1) h1]
    have hnotin : start ∉ init := fun hs => Nat.lt_irrefl start (hinit start hs)
    simp [hnotin]

theorem backReachAux_closed (start : ℕ) (init : Finset ℕ) (gs : List Gate) :
    ∀ j (hj : j < gs.length), start + j ∈ backReachAux start init gs →
      ∀ i ∈ gs[j].inputs, i < start + j → i ∈ backReachAux start init gs := by
  induction gs generalizing start with
  | nil => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | cons g gs ih =>
    intro j hj hmem i hi hilt
    cases j with
    | zero =>
      simp only [Nat.add_zero] at hmem hilt
      dsimp [backReachAux] at hmem ⊢
      split_ifs at hmem ⊢ with hs
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hi, hilt⟩)
      · exact absurd hmem hs
    | succ k =>
      have hk : k < gs.length := Nat.lt_of_succ_lt_succ hj
      dsimp [backReachAux] at hmem ⊢
      have hmemS : (start + 1) + k ∈ backReachAux (start + 1) init gs := by
        split_ifs at hmem with hs
        · rcases Finset.mem_union.mp hmem with hS | hG
          · exact (by omega : (start + 1) + k = start + (k + 1)) ▸ hS
          · rw [Finset.mem_filter] at hG
            omega
        · exact (by omega : (start + 1) + k = start + (k + 1)) ▸ hmem
      have hi_in : i ∈ backReachAux (start + 1) init gs := by
        have hilt' : i < (start + 1) + k := by omega
        exact ih (start + 1) k hk hmemS i hi hilt'
      split_ifs
      · exact Finset.mem_union_left _ hi_in
      · exact hi_in

theorem backReachAux_origin (start : ℕ) (init : Finset ℕ) (gs : List Gate) :
    ∀ w ∈ backReachAux start init gs, w ∉ init →
      ∃ j, ∃ (_ : j < gs.length), start + j ∈ backReachAux start init gs ∧ w ∈ gs[j].inputs := by
  induction gs generalizing start with
  | nil =>
    intro w hw hnotin
    exact absurd hw hnotin
  | cons g gs ih =>
    intro w hw hnotin
    dsimp [backReachAux] at hw ⊢
    by_cases hwS : w ∈ backReachAux (start + 1) init gs
    · obtain ⟨k, hk, hSk, hwk⟩ := ih (start + 1) w hwS hnotin
      refine ⟨k + 1, Nat.succ_lt_succ hk, ?_, hwk⟩
      have hSk' : start + (k + 1) ∈ backReachAux (start + 1) init gs := by
        rwa [show start + (k + 1) = (start + 1) + k by omega]
      split_ifs
      · exact Finset.mem_union_left _ hSk'
      · exact hSk'
    · split_ifs at hw with hs
      · rcases Finset.mem_union.mp hw with hS | hG
        · exact absurd hS hwS
        · rw [Finset.mem_filter] at hG
          refine ⟨0, Nat.zero_lt_succ gs.length, ?_, List.mem_toFinset.mp hG.1⟩
          rw [Nat.add_zero]
          split_ifs
          exact Finset.mem_union_left _ hs
      · exact absurd hw hwS

theorem foldl_stepWire_agree (S : Finset ℕ) (gs : List Gate) :
    ∀ (start : ℕ) (wx wy : List Bool),
      wx.length = start → wy.length = start →
      (∀ j (hj : j < gs.length), start + j ∈ S → ∀ i ∈ gs[j].inputs, i < start + j → i ∈ S) →
      (∀ i < start, i ∈ S → wx.getD i false = wy.getD i false) →
      (gs.foldl stepWire wx).length = start + gs.length ∧
      (gs.foldl stepWire wy).length = start + gs.length ∧
      ∀ i < start + gs.length, i ∈ S →
        (gs.foldl stepWire wx).getD i false = (gs.foldl stepWire wy).getD i false := by
  induction gs with
  | nil =>
    intro start wx wy hwx hwy _ hag
    exact ⟨hwx, hwy, hag⟩
  | cons g gs ih =>
    intro start wx wy hwx hwy hclosed hag
    simp only [List.foldl_cons]
    have hlenx : (stepWire wx g).length = start + 1 := by
      simp [stepWire, hwx]
    have hleny : (stepWire wy g).length = start + 1 := by
      simp [stepWire, hwy]
    have hclosed' : ∀ j (hj : j < gs.length), (start + 1) + j ∈ S → ∀ i ∈ gs[j].inputs, i < (start + 1) + j → i ∈ S := by
      intro j hj hmem i hi hilt
      have hmem' : start + (j + 1) ∈ S := by rwa [show start + (j + 1) = (start + 1) + j by omega]
      exact hclosed (j + 1) (Nat.succ_lt_succ hj) hmem' i hi (by omega)
    have hag' : ∀ i < start + 1, i ∈ S → (stepWire wx g).getD i false = (stepWire wy g).getD i false := by
      intro i hilt hiS
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hilt) with hilt0 | heq
      · have hx : (stepWire wx g).getD i false = wx.getD i false := by
          dsimp [stepWire]
          exact List.getD_append _ _ _ _ (by omega)
        have hy : (stepWire wy g).getD i false = wy.getD i false := by
          dsimp [stepWire]
          exact List.getD_append _ _ _ _ (by omega)
        rw [hx, hy]
        exact hag i hilt0 hiS
      · rw [heq] at hiS ⊢
        have hx : (stepWire wx g).getD start false = g.op.eval (g.inputs.map fun idx => wx.getD idx false) := by
          dsimp [stepWire]
          rw [List.getD_append_right _ _ _ _ (by omega : wx.length ≤ start), hwx, Nat.sub_self]
          rfl
        have hy : (stepWire wy g).getD start false = g.op.eval (g.inputs.map fun idx => wy.getD idx false) := by
          dsimp [stepWire]
          rw [List.getD_append_right _ _ _ _ (by omega : wy.length ≤ start), hwy, Nat.sub_self]
          rfl
        rw [hx, hy]
        congr 1
        apply List.map_congr_left
        intro idx hidx
        by_cases hlt : idx < start
        · have hidxS : idx ∈ S := hclosed 0 (Nat.zero_lt_succ gs.length) (by simpa using hiS) idx hidx (by simpa using hlt)
          exact hag idx hlt hidxS
        · have hge : start ≤ idx := Nat.le_of_not_lt hlt
          have hx_f : wx.getD idx false = false := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : wx.length ≤ idx)]
          have hy_f : wy.getD idx false = false := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : wy.length ≤ idx)]
          rw [hx_f, hy_f]
    obtain ⟨hl1, hl2, hag_out⟩ := ih (start + 1) (stepWire wx g) (stepWire wy g) hlenx hleny hclosed' hag'
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega
    · intro i hi hiS
      exact hag_out i (by simp only [List.length_cons] at hi; omega) hiS

def reachSet (n : ℕ) (C : Circuit) : Finset ℕ :=
  backReachAux n (if C.output < n + C.gates.length then {C.output} else ∅) C.gates

def reachInputs (n : ℕ) (C : Circuit) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val ∈ reachSet n C)

theorem eval_eq_of_agree_on_reachInputs (n : ℕ) (C : Circuit) (a b : Fin n → Bool)
    (hag : ∀ v ∈ reachInputs n C, a v = b v) :
    C.eval (List.ofFn a) = C.eval (List.ofFn b) := by
  let init : Finset ℕ := if C.output < n + C.gates.length then {C.output} else ∅
  have hclosed := backReachAux_closed n init C.gates
  have hag_init : ∀ i < n, i ∈ reachSet n C → (List.ofFn a).getD i false = (List.ofFn b).getD i false := by
    intro i hi hiS
    have hmem : (⟨i, hi⟩ : Fin n) ∈ reachInputs n C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS⟩
    have heq := hag ⟨i, hi⟩ hmem
    simp [List.getD_eq_getElem?_getD, hi, heq]
  obtain ⟨hla, hlb, hwire⟩ := foldl_stepWire_agree (reachSet n C) C.gates n (List.ofFn a) (List.ofFn b)
    (List.length_ofFn) (List.length_ofFn) hclosed hag_init
  change (C.wires (List.ofFn a)).getD C.output false = (C.wires (List.ofFn b)).getD C.output false
  have hla' : (C.wires (List.ofFn a)).length = n + C.gates.length := hla
  have hlb' : (C.wires (List.ofFn b)).length = n + C.gates.length := hlb
  by_cases ho : C.output < n + C.gates.length
  · have hoS : C.output ∈ reachSet n C := by
      apply init_subset_backReachAux
      split_ifs
      exact Finset.mem_singleton_self _
    exact hwire C.output ho hoS
  · have ha_f : (C.wires (List.ofFn a)).getD C.output false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (C.wires (List.ofFn a)).length ≤ C.output)]
    have hb_f : (C.wires (List.ofFn b)).getD C.output false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (C.wires (List.ofFn b)).length ≤ C.output)]
    rw [ha_f, hb_f]

theorem reachInputs_card_le (n : ℕ) (C : Circuit) (hm : Monotone2 C) :
    (reachInputs n C).card ≤ C.size + 1 := by
  by_cases ho1 : C.output < n + C.gates.length
  · by_cases ho2 : C.output < n
    · have hS : reachSet n C = {C.output} := by
        dsimp [reachSet]
        split_ifs
        apply backReachAux_small_init
        intro w hw
        rw [Finset.mem_singleton] at hw
        omega
      have hI : reachInputs n C ⊆ {⟨C.output, ho2⟩} := by
        intro v hv
        rw [reachInputs, Finset.mem_filter, hS, Finset.mem_singleton] at hv
        rw [Finset.mem_singleton]
        exact Fin.ext hv.2
      calc (reachInputs n C).card
          ≤ ({⟨C.output, ho2⟩} : Finset (Fin n)).card := Finset.card_le_card hI
        _ = 1 := Finset.card_singleton _
        _ ≤ C.size + 1 := Nat.le_add_left 1 C.size
    · have hge : n ≤ C.output := Nat.le_of_not_lt ho2
      let o : Fin C.gates.length := ⟨C.output - n, by omega⟩
      let S := reachSet n C
      let G : Finset (Fin C.gates.length) := Finset.univ.filter (fun j => n + j.val ∈ S)
      let I := reachInputs n C
      have hoS : n + o.val ∈ S := by
        have : n + o.val = C.output := by dsimp [o]; omega
        rw [this]
        apply init_subset_backReachAux
        split_ifs
        exact Finset.mem_singleton_self _
      have hoG : o ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hoS⟩
      let WI : Finset ℕ := I.image Fin.val
      let WG : Finset ℕ := (G.erase o).image (fun j : Fin C.gates.length => n + j.val)
      have hdisj : Disjoint WI WG := by
        rw [Finset.disjoint_left]
        intro w hwI hwG
        rw [Finset.mem_image] at hwI hwG
        rcases hwI with ⟨v, _, rfl⟩
        rcases hwG with ⟨j, _, hj⟩
        omega
      have hsub : WI ∪ WG ⊆ G.biUnion (fun k => C.gates[k.val].inputs.toFinset) := by
        intro w hw
        have hwS : w ∈ S ∧ w ∉ ({C.output} : Finset ℕ) := by
          rcases Finset.mem_union.mp hw with hwI | hwG
          · rw [Finset.mem_image] at hwI
            rcases hwI with ⟨v, hvI, rfl⟩
            dsimp [I, reachInputs] at hvI
            rw [Finset.mem_filter] at hvI
            refine ⟨hvI.2, ?_⟩
            rw [Finset.mem_singleton]
            omega
          · rw [Finset.mem_image] at hwG
            rcases hwG with ⟨j, hjG, rfl⟩
            rw [Finset.mem_erase, Finset.mem_filter] at hjG
            refine ⟨hjG.2.2, ?_⟩
            rw [Finset.mem_singleton]
            intro heq
            apply hjG.1
            apply Fin.ext
            dsimp [o]
            omega
        have hS_def : S = backReachAux n {C.output} C.gates := by
          dsimp [S, reachSet]
          split_ifs
          rfl
        rw [hS_def] at hwS
        obtain ⟨k, hk, hSk, hwk⟩ := backReachAux_origin n {C.output} C.gates w hwS.1 hwS.2
        rw [Finset.mem_biUnion]
        refine ⟨⟨k, hk⟩, ?_, List.mem_toFinset.mpr hwk⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hS_def]
        exact hSk
      have hcard_union : (WI ∪ WG).card = I.card + (G.card - 1) := by
        rw [Finset.card_union_of_disjoint hdisj]
        have hWI : WI.card = I.card := Finset.card_image_of_injective I Fin.val_injective
        have hinj : Function.Injective (fun j : Fin C.gates.length => n + j.val) := by
          intro a b hab
          dsimp at hab
          exact Fin.ext (by omega)
        have hWG : WG.card = (G.erase o).card := Finset.card_image_of_injective _ hinj
        rw [hWI, hWG, Finset.card_erase_of_mem hoG]
      have hcard_rhs : (G.biUnion (fun k => C.gates[k.val].inputs.toFinset)).card ≤ 2 * G.card := by
        calc (G.biUnion (fun k => C.gates[k.val].inputs.toFinset)).card
            ≤ ∑ k ∈ G, (C.gates[k.val].inputs.toFinset).card := Finset.card_biUnion_le
          _ ≤ ∑ k ∈ G, 2 := by
            apply Finset.sum_le_sum
            intro k _
            have hmem : C.gates[k.val] ∈ C.gates := List.getElem_mem k.isLt
            have hlen : C.gates[k.val].inputs.length ≤ 2 := (hm _ hmem).2
            exact Nat.le_trans (List.toFinset_card_le _) hlen
          _ = 2 * G.card := by simp [Nat.mul_comm]
      have hcard_le := Finset.card_le_card hsub
      have hG_pos : 1 ≤ G.card := Finset.card_pos.mpr ⟨o, hoG⟩
      have hG_le : G.card ≤ C.size := by
        calc G.card ≤ (Finset.univ : Finset (Fin C.gates.length)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = C.gates.length := Fintype.card_fin _
          _ = C.size := rfl
      change I.card ≤ C.size + 1
      omega
  · have hS : reachSet n C = ∅ := by
      dsimp [reachSet]
      split_ifs
      apply backReachAux_small_init
      intro w hw
      simp at hw
    have hI : reachInputs n C = ∅ := by
      ext v
      simp [reachInputs, hS]
    rw [hI, Finset.card_empty]
    exact Nat.zero_le _

theorem supp_subset_reachInputs (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (C : Circuit) (heq : circuitFun n C = graphFun K ∅) (E : Finset (Sym2 (Fin n)))
    (hE : E ⊆ K.edgeFinset) :
    supp E ⊆ reachInputs n C := by
  intro v hv
  rw [supp, Finset.mem_filter] at hv
  rcases hv with ⟨_, e, heE, hve⟩
  have heK : e ∈ K.edgeSet := SimpleGraph.mem_edgeFinset.mp (hE heE)
  have hadj : ∃ w : Fin n, K.Adj v w := by
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at heK
      rcases Sym2.mem_iff.mp hve with rfl | rfl
      · exact ⟨y, heK⟩
      · exact ⟨x, heK.symm⟩
  rcases hadj with ⟨w, hvw⟩
  let a : Fin n → Bool := fun i => decide (i = w)
  let b : Fin n → Bool := fun i => decide (i = v ∨ i = w)
  have ha_graph : graphFun K ∅ a = false := by
    dsimp [graphFun, a]
    rw [Bool.or_eq_false_iff]
    constructor
    · simp
    · rw [decide_eq_false_iff_not]
      rintro ⟨u1, u2, hu, h1, h2⟩
      simp only [decide_eq_true_eq] at h1 h2
      subst h1; subst h2
      exact K.ne_of_adj hu rfl
  have hb_graph : graphFun K ∅ b = true := by
    dsimp [graphFun, b]
    rw [Bool.or_eq_true]
    right
    rw [decide_eq_true_eq]
    exact ⟨v, w, hvw, by simp, by simp⟩
  have hca : C.eval (List.ofFn a) = false := by
    change circuitFun n C a = false
    rw [heq]
    exact ha_graph
  have hcb : C.eval (List.ofFn b) = true := by
    change circuitFun n C b = true
    rw [heq]
    exact hb_graph
  by_contra hv_not
  have hag : ∀ i ∈ reachInputs n C, a i = b i := by
    intro i hi
    have hiv : i ≠ v := fun h => hv_not (h ▸ hi)
    dsimp [a, b]
    simp [hiv]
  have hev := eval_eq_of_agree_on_reachInputs n C a b hag
  rw [hca, hcb] at hev
  exact Bool.noConfusion hev

end PEqualNP.Outside.L_meta_4235

theorem PEqualNP.Outside.L_meta_4235 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x7 ⊆ x2.edgeFinset, ∀ (x9 : ℕ), ∃ x10 ⊆ x7, x7.card ≤ x9 * (x4.size + (1 : ℕ)) + x10.card ∧ ∀ (x11 : Fin x1), {x12 ∈ x10 | x11 ∈ x12}.card = (0 : ℕ) ∨ x9 < {x12 ∈ x10 | x11 ∈ x12}.card := by
  intro x1 x2 _ x4 hm heq x7 hx7 x9
  have hsub := PEqualNP.Outside.L_meta_4235.supp_subset_reachInputs x1 x2 x4 heq x7 hx7
  have hcard := PEqualNP.Outside.L_meta_4235.reachInputs_card_le x1 x4 hm
  obtain ⟨x10, hx10, hle, hdeg⟩ := PEqualNP.Outside.L_meta_4235.peel_edges x1 x9
    (PEqualNP.Outside.L_meta_4235.reachInputs x1 x4).card
    (PEqualNP.Outside.L_meta_4235.reachInputs x1 x4) x7 rfl hsub
  refine ⟨x10, hx10, ?_, hdeg⟩
  calc x7.card
      ≤ x9 * (PEqualNP.Outside.L_meta_4235.reachInputs x1 x4).card + x10.card := hle
    _ ≤ x9 * (x4.size + 1) + x10.card := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left x9 hcard) _

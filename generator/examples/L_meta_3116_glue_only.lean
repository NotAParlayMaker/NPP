import Cert

-- GLUE-BEGIN
-- New for L-meta-3116: the two given wires are put back as the first two gates of a
-- circuit on the nine inputs. A derivation that reads either wire and input 0 or
-- input 3 loses two gates when that input is pinned to false, against the checked
-- bound for the graph without that vertex. A derivation that reads neither input
-- leaves a positive and a negative row undistinguished. A derivation that reads
-- neither wire is excluded by the checked frontier certificate.
namespace PEqualNP.Outside.L_meta_3116
namespace Glue
open PEqualNP.CircuitLowerBounds Main1672

def gA : Gate := ⟨.and, [0, 3]⟩
def gN : Gate := ⟨.not, [9]⟩
def sA : Sig := bin false raw0 raw3
def sN : Sig := neg sA
def wiresW : List Sig := raw ++ [sA] ++ [sN]
def restW : List Sig := [raw1, raw2, raw4, raw5, raw6, raw7, raw8, sA, sN]

lemma gvA : gv raw gA = sA := by decide +kernel
lemma gvN : gv (raw ++ [sA]) gN = sN := by decide +kernel
lemma raw0_ne_sA : raw0 ≠ sA := by decide +kernel
lemma raw0_ne_sN : raw0 ≠ sN := by decide +kernel
lemma raw3_ne_sA : raw3 ≠ sA := by decide +kernel
lemma raw3_ne_sN : raw3 ≠ sN := by decide +kernel
lemma rest_fail : unionSep true restW != top := by decide +kernel
lemma rest_sub : ∀ a ∈ restW, a ∈ wiresW := by decide +kernel

lemma valid_raw0 : Valid raw0 := raw_valid raw0 (by simp [raw])
lemma valid_raw3 : Valid raw3 := raw_valid raw3 (by simp [raw])
lemma valid_sA : Valid sA := valid_bin valid_raw0 valid_raw3
lemma valid_sN : Valid sN := valid_neg valid_sA

lemma valid_W : ∀ a ∈ wiresW, Valid a := by
  intro a ha
  simp only [wiresW, List.mem_append, List.mem_singleton] at ha
  rcases ha with (ha | rfl) | rfl
  · exact raw_valid a ha
  · exact valid_sA
  · exact valid_sN

def extend (C : Circuit) : Circuit := ⟨gA :: gN :: C.gates, C.output⟩

lemma extend_fan (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (extend C) := by
  intro g hg
  simp only [extend, List.mem_cons] at hg
  rcases hg with rfl | rfl | hg
  · exact ⟨by simp [gA], by simp [gA]⟩
  · exact ⟨by simp [gN], by simp [gN]⟩
  · exact h g hg

lemma extend_eval (C : Circuit) (x : Fin 9 → Bool) :
    (extend C).eval (List.ofFn x) =
      C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!(x 0 && x 3)]) := by
  have h1 : gA.op.eval (gA.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 && x 3) := by
    simp [gA, GateOp.eval, List.getD_eq_getElem?_getD]
  have h2 : gN.op.eval (gN.inputs.map fun i => (List.ofFn x ++ [x 0 && x 3]).getD i false)
      = !(x 0 && x 3) := by
    simp [gN, GateOp.eval, List.getD_eq_getElem?_getD]
  change ((C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    ((List.ofFn x ++ [gA.op.eval (gA.inputs.map fun i => (List.ofFn x).getD i false)]) ++
      [gN.op.eval (gN.inputs.map fun i =>
        (List.ofFn x ++ [gA.op.eval (gA.inputs.map fun i => (List.ofFn x).getD i false)]).getD
          i false)])).getD C.output false) = _
  rw [h1, h2]
  rfl

lemma target_mem (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!(x 0 && x 3)]) = edgeF x) :
    target ∈ execute C.gates wiresW := by
  have h := circuit_target (extend C) (extend_fan C hf)
    (fun x => (extend_eval C x).trans (he x))
  change target ∈ execute C.gates ((raw ++ [gv raw gA]) ++ [gv (raw ++ [gv raw gA]) gN]) at h
  rw [gvA, gvN] at h
  exact h

lemma proj_raw0 : (homProject 0).fn raw0 = zero := project_raw_zero 0
lemma proj_raw3 : (homProject 3).fn raw3 = zero := project_raw_zero 3

lemma projA0 : (homProject 0).fn sA = zero := by
  change (homProject 0).fn (bin false raw0 raw3) = zero
  rw [(homProject 0).hbin, proj_raw0, bin_comm]
  exact (bin_laws ((homProject 0).valid raw3)).2.2.1

lemma projA3 : (homProject 3).fn sA = zero := by
  change (homProject 3).fn (bin false raw0 raw3) = zero
  rw [(homProject 3).hbin, proj_raw3]
  exact (bin_laws ((homProject 3).valid raw0)).2.2.1

lemma projN (i : Fin 9) (h : (homProject i).fn sA = zero) : (homProject i).fn sN = one := by
  change (homProject i).fn (neg sA) = one
  rw [(homProject i).hneg valid_sA, h]
  exact neg_laws.1

lemma image_sub (i : Fin 9) (hA : (homProject i).fn sA = zero)
    {S : Finset Sig} (hsub : ∀ a ∈ S, a ∈ wiresW) {q : Nat}
    (h : Feasible (homProject i) q S) : Feasible (homProject i) q raw.toFinset := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro x hx
  obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp (hs hx)
  have hp := live_proper hl _ hx
  have ha := hsub a haS
  simp only [wiresW, List.mem_append, List.mem_singleton] at ha
  rcases ha with (ha | rfl) | rfl
  · exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr ha)
  · exact (hp.2.1 hA).elim
  · exact (hp.2.2 (projN i hA)).elim

lemma two_lost (i : Fin 9) (hi : ¬ (i.val = 4 ∨ i.val = 6 ∨ i.val = 7))
    (hA : (homProject i).fn sA = zero)
    {k t : Nat} {S : Finset Sig} (hlive : Live k t S) (hk : k ≤ 13)
    (hsub : ∀ a ∈ S, a ∈ wiresW)
    (a b : Sig) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hca : ¬ proper ((homProject i).fn a)) (hcb : ¬ proper ((homProject i).fn b)) : False := by
  obtain ⟨q, hq, hfe⟩ := feasible_two_consts hlive (homProject i) a b ha hb hab hca hcb
  exact root_project_deg3 i hi (feasible_mono (image_sub i hA hsub hfe) (by omega))

theorem main (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!(x 0 && x 3)]) = edgeF x) :
    14 ≤ C.size := by
  by_contra hlt
  have hle : C.gates.length ≤ 13 := by
    change ¬ 14 ≤ C.gates.length at hlt
    omega
  obtain ⟨k, t, S, hk, hlive, hsub⟩ :=
    extract C.gates wiresW valid_W (fun g hg => hf g hg) (target_mem C hf he)
  have hk13 : k ≤ 13 := hk.trans hle
  by_cases hsp : sA ∈ S ∨ sN ∈ S
  · by_cases h0 : raw0 ∈ S
    · rcases hsp with h | h
      · exact two_lost 0 (by decide) projA0 hlive hk13 hsub raw0 sA h0 h raw0_ne_sA
          (fun hp => hp.2.1 proj_raw0) (fun hp => hp.2.1 projA0)
      · exact two_lost 0 (by decide) projA0 hlive hk13 hsub raw0 sN h0 h raw0_ne_sN
          (fun hp => hp.2.1 proj_raw0) (fun hp => hp.2.2 (projN 0 projA0))
    · by_cases h3 : raw3 ∈ S
      · rcases hsp with h | h
        · exact two_lost 3 (by decide) projA3 hlive hk13 hsub raw3 sA h3 h raw3_ne_sA
            (fun hp => hp.2.1 proj_raw3) (fun hp => hp.2.1 projA3)
        · exact two_lost 3 (by decide) projA3 hlive hk13 hsub raw3 sN h3 h raw3_ne_sN
            (fun hp => hp.2.1 proj_raw3) (fun hp => hp.2.2 (projN 3 projA3))
      · have hcov : unionSep true restW = top := by
          apply Nat.eq_of_testBit_eq
          intro i
          rw [testBit_top]
          by_cases hi : i < 414
          · simp only [hi, decide_true]
            obtain ⟨b, hbS, hsep⟩ := live_sep hlive i hi
            have hbm : b ∈ restW := by
              have hb := hsub b hbS
              simp only [wiresW, raw, List.mem_append, List.mem_cons, List.mem_singleton,
                List.not_mem_nil, or_false] at hb
              rcases hb with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl
              · exact (h0 hbS).elim
              · simp [restW]
              · simp [restW]
              · exact (h3 hbS).elim
              · simp [restW]
              · simp [restW]
              · simp [restW]
              · simp [restW]
              · simp [restW]
              · simp [restW]
              · simp [restW]
            exact (mem_unionSep true _ _).2
              ⟨b, hbm, sep_weaken _ (live_proper hlive b hbS).1 i hi hsep⟩
          · simp only [hi, decide_false]
            exact valid_unionSep (fun x hx => valid_W x (rest_sub x hx)) i (by omega)
        have hf1 := rest_fail
        simp [hcov] at hf1
  · have hsubRaw : ∀ a ∈ S, a ∈ raw := by
      intro a ha
      have h := hsub a ha
      simp only [wiresW, List.mem_append, List.mem_singleton] at h
      rcases h with (h | rfl) | rfl
      · exact h
      · exact (hsp (Or.inl ha)).elim
      · exact (hsp (Or.inr ha)).elim
    have heq := necessary hlive hsubRaw
    subst S
    have sz := live_size hlive
    rw [List.toFinset_card_of_nodup raw_nd] at sz
    have hlenRaw : raw.length = 9 := rfl
    have hk14 : k ≤ 14 := by omega
    exact rootImpossible t (by omega) k hk14 raw.toFinset rootTag rootWires_rep
      (restrict_live hlive (rootTag_ok hk14))

end Glue
end PEqualNP.Outside.L_meta_3116

theorem PEqualNP.Outside.L_meta_3116 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))] ++ [!(x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size :=
  fun C hf he => PEqualNP.Outside.L_meta_3116.Glue.main C hf he

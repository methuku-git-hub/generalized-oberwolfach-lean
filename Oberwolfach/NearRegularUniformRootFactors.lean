module

public import Oberwolfach.RootPackingDivisibility
public import Oberwolfach.ExtendRootedCyclePacking
public import Oberwolfach.InducedBoundedFactorInputs
public import Oberwolfach.CycleSubgraphFactorLift
public import Oberwolfach.AlmostRegularCycleFactor
public import Oberwolfach.NearRegularAugmentationBounds

@[expose] public section
/-! First cover each root by a cycle containing no other root; complete its
packing and then find an edge-disjoint factor on the fresh set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem near_regular_root_separated_factors_uniform_roots (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1):
    ∃ η:ℝ,0<η ∧ ∀ q:ℕ,∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) (S:Finset V) (D:ℝ),
      N≤S.card → (m+1)∣S.card → (m+1)∣Fintype.card V → Fintype.card V-S.card≤q →
      (cycleThreshold (m+1)+α)*(S.card:ℝ)≤D → D≤S.card →
      (∀ v,|((G.neighborFinset v∩S).card:ℝ)-D|≤η*S.card) →
      ∃ M₁ M₂:Finset (OrdinaryCycle G (m+1)),
        (∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices G (m+1) C) (ordinaryCycleVertices G (m+1) E)) ∧
        M₁.biUnion (ordinaryCycleVertices G (m+1))=Finset.univ ∧
        (∀ C∈M₂,∀ E∈M₂,C≠E→Disjoint (ordinaryCycleVertices G (m+1) C) (ordinaryCycleVertices G (m+1) E)) ∧
        M₂.biUnion (ordinaryCycleVertices G (m+1))=S ∧
        (∀ C∈M₁,∀ E∈M₂,Disjoint C.val.val.edgeFinset E.val.val.edgeFinset) ∧
        (∀ C∈M₁,(ordinaryCycleVertices G (m+1) C∩(Finset.univ\S)).card≤1):=by
  obtain ⟨ε,hε,Nf,hfactor⟩:=almost_regular_cycle_factor m hm (α/8) (by positivity)
  let c:=min α ε
  have hc:0<c:=lt_min hα hε
  refine ⟨c/32,by positivity,?_⟩
  intro q
  obtain ⟨Nr,hroots⟩:=root_separated_cycle_packing (α/4) (by positivity) (m+1) q (by omega)
  obtain ⟨K,hK⟩:=exists_nat_gt (32*(((m+1)*q:ℕ)+q+2)/c)
  let N:=max (Nf+(m+1)*q) (max Nr (max K 1))
  refine ⟨N,?_⟩
  intro V _ _ G S D hs hSdiv hdiv hq hDlo hDhi hnear
  have hspos:0<S.card:=by dsimp [N] at hs;omega
  have hsR:(0:ℝ)<S.card:=by exact_mod_cast hspos
  have hSv:S.card≤Fintype.card V:=Finset.card_le_univ S
  have hSV:(S.card:ℝ)≤Fintype.card V:=by exact_mod_cast hSv
  have hK':32*(((m+1)*q:ℕ)+q+2)/c<(S.card:ℝ):=
    lt_of_lt_of_le hK (by exact_mod_cast (show K≤S.card by dsimp [N] at hs;omega))
  have hlarge:(((m+1)*q:ℕ):ℝ)+(q:ℝ)+2≤c*S.card/32:=by
    have hh:= (div_lt_iff₀ hc).mp hK'
    push_cast at hh ⊢
    nlinarith
  have hηα:c/32≤α/8:=by dsimp [c];have hh:=min_le_left α ε;linarith
  have hηε:c/32≤ε/8:=by dsimp [c];have hh:=min_le_right α ε;linarith
  have hδ0:(1/2:ℝ)≤cycleThreshold (m+1):=cycleThreshold_half_le (by omega)
  have hδ1:cycleThreshold (m+1)≤1:=cycleThreshold_le_one _
  have hsmall:((q:ℝ)+2)≤min α ε*(S.card:ℝ)/8:=by dsimp [c] at hlarge; nlinarith [show (0:ℝ)≤(m+1)*q by positivity]
  have hbound:=near_regular_augmentation_bounds G ⊥ S D (cycleThreshold (m+1)) α (c/32) ε q
    hδ0 hδ1 hα hα1 (by positivity) hηα hηε hε hspos hq hsmall hDlo hDhi hnear (by intro v;simp)
  let T:Finset V:=Finset.univ\S
  have hTcard:T.card≤q:=by dsimp [T];simpa [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ] using hq
  have hTdiv:(m+1)∣T.card:=by
    dsimp [T]
    simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ]
    exact Nat.dvd_sub hdiv hSdiv
  have hpart:S∪T=Finset.univ:=by dsimp [T];ext v;simp
  have hdis:Disjoint S T:=by
    apply Finset.disjoint_left.mpr
    intro v hvS hvT
    exact (Finset.mem_sdiff.mp hvT).2 hvS
  have hGmin:∀ v,(1/2+α/4)*(Fintype.card V:ℝ)≤(G.degree v:ℝ):=by
    intro v
    have hh:=hbound.2.2.1 v
    have hle:triangleAugmentationGraph G ⊥ S≤G:=fun _ _ h=>h.1
    have hd:((triangleAugmentationGraph G ⊥ S).degree v:ℝ)≤G.degree v:=by exact_mod_cast SimpleGraph.degree_le_of_le hle (v:=v)
    have hn0:(0:ℝ)≤Fintype.card V:=by positivity
    nlinarith
  have hNr:Nr≤Fintype.card V:=by dsimp [N] at hs;omega
  obtain ⟨M₀,hpack₀,hcover₀,hroot,hM₀⟩:=hroots V hNr G hGmin T hTcard
  let U:=M₀.biUnion (ordinaryCycleVertices G (m+1))
  have hU:U.card≤(m+1)*q:=by
    have hh:=Finset.card_biUnion_le_card_mul M₀ (ordinaryCycleVertices G (m+1)) (m+1)
      (by intro C hC;exact (ordinaryCycleVertices_card G (m+1) C).le)
    exact hh.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right (m+1) (hM₀.trans hTcard))
  let A:=S\U
  have hAS:A⊆S:=Finset.sdiff_subset
  have hremoved:(S\A).card≤(m+1)*q:=by
    have hh:S\A⊆U:=by intro v hv;have :=Finset.mem_sdiff.mp hv;by_contra h;exact this.2 (Finset.mem_sdiff.mpr ⟨this.1,h⟩)
    exact (Finset.card_le_card hh).trans hU
  have hAcard:S.card≤A.card+(m+1)*q:=by
    have hh:=Finset.card_sdiff_add_card A S
    have hjoin:S⊆(S\A)∪A:=by
      intro v hv
      by_cases ha:v∈A
      · exact Finset.mem_union_right _ ha
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv,ha⟩)
    have hh':S.card≤(S\A).card+A.card:=(Finset.card_le_card hjoin).trans (Finset.card_union_le _ _)
    omega
  have hSsize:S.card≤2*A.card:=by
    have hSr:(S.card:ℝ)≤A.card+(m+1)*q:=by exact_mod_cast hAcard
    have hc1:c≤1:=by dsimp [c];exact (min_le_left _ _).trans hα1
    have hs0:(0:ℝ)≤S.card:=by positivity
    have hbig:(((m+1)*q:ℕ):ℝ)≤(S.card:ℝ)/2:=by nlinarith [mul_le_mul_of_nonneg_right hc1 hs0]
    push_cast at hbig
    exact_mod_cast (show (S.card:ℝ)≤2*A.card by linarith)
  have hNA:Nf≤A.card:=by dsimp [N] at hs;omega
  have hAdiv:(m+1)∣A.card:=root_packing_remaining_divisible G (m+1) S T M₀ hpart hdis hSdiv hTdiv hpack₀ hcover₀
  have herrα:(c/32)*(S.card:ℝ)+((m+1)*q:ℕ)+2≤(α/2)*S.card:=by
    have hh:=mul_le_mul_of_nonneg_right (min_le_left α ε) hsR.le
    nlinarith
  have herrε:(c/32)*(S.card:ℝ)+((m+1)*q:ℕ)+2≤ε*A.card:=by
    have hh:=mul_le_mul_of_nonneg_right (min_le_right α ε) hsR.le
    have hsize:(S.card:ℝ)≤2*A.card:=by exact_mod_cast hSsize
    nlinarith
  let Q₀:=triangleAugmentationGraph G ⊥ A
  have hQ₀:Q₀≤G:=fun _ _ h=>h.1
  have hi₀:=induced_bounded_factor_inputs G ⊥ S A D (cycleThreshold (m+1)) α (c/32) ε ((m+1)*q)
    hδ0 hα hε hAS hremoved hSsize hDlo hDhi hnear (by intro v;simp) herrα herrε
  have hFA:HasResourceDecomposition (ordinaryCycleVertices (Q₀.induce (A:Set V)) (m+1)) Finset.univ:=
    hfactor (A:Set V) (by simpa using hNA) (Q₀.induce (A:Set V)) D hi₀.1 hi₀.2.1 hi₀.2.2.1 hi₀.2.2.2 (by simpa using hAdiv)
  obtain ⟨MresQ,hpackQ,hcoverQ⟩:=ordinary_factor_induced_lift A hFA
  let lift₀:=ordinaryCycleSubgraphLift (r:=m+1) hQ₀
  let Mres:=MresQ.image lift₀
  have hres:=ordinary_subgraph_factor_lift hQ₀ A MresQ hpackQ hcoverQ
  let M₁:=M₀∪Mres
  have hfull:=extend_rooted_cycle_packing G (m+1) S T M₀ Mres hpart hdis hpack₀ hcover₀ hroot hres.1 hres.2
  let Dgraph:=ordinaryFactorGraph M₁
  have hDgraph:∀v,Dgraph.degree v≤2:=ordinaryFactorGraph_degree_le_two M₁ hfull.1
  have herrα':(c/32)*(S.card:ℝ)+0+2≤(α/2)*S.card:=by
    have hh:(0:ℝ)≤((m+1)*q:ℕ):=by positivity
    linarith
  have herrε':(c/32)*(S.card:ℝ)+0+2≤ε*S.card:=by
    have hASR:(A.card:ℝ)≤S.card:=by exact_mod_cast Finset.card_le_card hAS
    nlinarith [mul_le_mul_of_nonneg_left hASR hε.le]
  let Q₂:=triangleAugmentationGraph G Dgraph S
  have hQ₂:Q₂≤G:=fun _ _ h=>h.1
  have hi₂:=induced_bounded_factor_inputs G Dgraph S S D (cycleThreshold (m+1)) α (c/32) ε 0
    hδ0 hα hε (Finset.Subset.rfl) (by simp) (by omega) hDlo hDhi hnear hDgraph (by simpa using herrα') (by simpa using herrε')
  have hFS:HasResourceDecomposition (ordinaryCycleVertices (Q₂.induce (S:Set V)) (m+1)) Finset.univ:=
    hfactor (S:Set V) (by simpa using (show Nf≤S.card by dsimp [N] at hs;omega))
      (Q₂.induce (S:Set V)) D hi₂.1 hi₂.2.1 hi₂.2.2.1 hi₂.2.2.2 (by simpa using hSdiv)
  obtain ⟨M₂Q,hpack₂,hcover₂⟩:=ordinary_factor_induced_lift S hFS
  let lift₂:=ordinaryCycleSubgraphLift (r:=m+1) hQ₂
  let M₂:=M₂Q.image lift₂
  have hsecond:=ordinary_subgraph_factor_lift hQ₂ S M₂Q hpack₂ hcover₂
  refine ⟨M₁,M₂,hfull.1,hfull.2.1,hsecond.1,hsecond.2,?_,hfull.2.2⟩
  intro C hC E hE
  obtain ⟨E',hE',rfl⟩:=Finset.mem_image.mp hE
  apply Finset.disjoint_left.mpr
  intro e heC heE
  induction e using Sym2.ind with
  | _ v w =>
    have hc:C.val.val.Adj v w:=by simpa using heC
    have he:E'.val.val.Adj v w:=by
      have hh:(lift₂ E').val.val.Adj v w:=by simpa using heE
      exact hh
    have hQedge:=E'.property he
    have hDedge:Dgraph.Adj v w:=by
      change (⨆ C∈M₁,C.val.val).Adj v w
      simp only [SimpleGraph.iSup_adj]
      exact ⟨C,hC,hc⟩
    exact hQedge.2.2 hDedge
end Oberwolfach

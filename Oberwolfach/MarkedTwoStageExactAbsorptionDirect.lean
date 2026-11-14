module

public import Oberwolfach.MarkedTwoStageTerminalAbsorber
public import Oberwolfach.MarkedPackingAndDeletedDecomposition
public import Oberwolfach.MarkedReservedGraphsPackingIdentity
public import Oberwolfach.MarkedPhysicalDeletionComposition
public import Oberwolfach.MarkedEqualSampleWheelRebase

@[expose] public section
/-! Complete a pair of physically disjoint cover-down packings by absorbing
a divisible terminal remainder and lifting all wheels to the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
def MarkedTwoStageCompletionForGraphs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (Xterm:Finset V) (Zterm:Finset U)
    (Mres Nres:Finset (Finset V⊕(V×U))) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)):Prop:=
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    let σf:=rawMarkedDeleteRims σ DR.edgeFinset
    let Hf:=markedDeletePhysicalSpokes H DS
    let Ef:=MarkedSampleArc P π (3*d) (fun e=>σf (Sum.inl e)) false
    let Kf:=MarkedSampleArc P π (3*d) (fun e=>σf (Sum.inl e)) true
    let tf:=fun e:Ef=>e.val.1
    let hf:=fun e:Ef=>e.val.2
    let ktf:=fun e:Kf=>e.val.1
    let khf:=fun e:Kf=>e.val.2;
    ∀ (A:Finset (Ef⊕Kf)) (S:Finset (V×U)),
    (∀ a∈A,Sum.elim tf ktf a∈Xterm∧Sum.elim hf khf a∈Xterm)→
    (∀ z∈S,z.1∈Xterm∧z.2∈Zterm∧(Hf false z.1 z.2∨Hf true z.1 z.2))→
    MarkedRemainderDivisible tf hf ktf khf (Hf true) A S m→
    HasResourceDecomposition
      (fun Q:MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)=>markedWheelPhysicalResources Q)
      (Mres∪(Nres∪
        (C∪markedFiniteResources tf hf ktf khf π A S)))
theorem marked_two_stage_exact_decomposition_direct
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m) (hd:1≤3*d)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (Xterm:Finset V) (Zterm:Finset U)
    (habs:MarkedUniversalTerminalDeletionAbsorber P π d m σ H C Xterm Zterm)
    (I T:Finset V) (J W:Finset U) (hI:∀ x,π x∈I↔x∈I)
    (hX:Xterm⊆I\T) (hZ:Zterm⊆J\W) (hC:∀ e∈C,¬markedInnerResource I J e):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ (A₀:Finset (E⊕K)) (S₀:Finset (V×U))
      (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)))
      (R:Finset (Finset V⊕(V×U))),
    (∀ a∈A₀,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ z∈S₀,z.1∈I∧z.2∈J)→
    (∀ X∈M,∀ Y∈M,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))→
    Disjoint C (M.biUnion markedWheelPhysicalResources)→
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=R.filter (markedStarResource T W)→
    let Astar:=A₀.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let Sstar:=S₀.filter (fun z=>z.1∈T∨z.2∈W)
    let DR₁:=markedSampleArcSetGraph P π d σ (Astar∪M.biUnion markedWheelArcs)
    let DS₁:=markedFiniteSpokeGraph (Sstar∪M.biUnion markedWheelSpokePairs)
    let σ₁:=rawMarkedDeleteRims σ DR₁.edgeFinset
    let H₁:=markedDeletePhysicalSpokes H DS₁
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ₁ (Sum.inl e)) false
    let K₁:=MarkedSampleArc P π (3*d) (fun e=>σ₁ (Sum.inl e)) true;
    ∀ N:Finset (MarkedWheel (fun e:E₁=>e.val.1) (fun e=>e.val.2)
      (fun e:K₁=>e.val.1) (fun e=>e.val.2) m π (3*d) (H₁ false) (H₁ true)),
    (∀ X∈N,∀ Y∈N,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))→
    Disjoint C (N.biUnion markedWheelPhysicalResources)→
    (N.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅→
    let DR₂:=markedPackingRimGraph N
    let DS₂:=markedFiniteSpokeGraph (N.biUnion markedWheelSpokePairs)
    let DR:=DR₁⊔DR₂
    let DS:=DS₁⊔DS₂
    MarkedTwoStageCompletionForGraphs P π d m σ H C Xterm Zterm
      (M.biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources) DR DS:=by
  intro E K tail head ktail khead A₀ S₀ M R hA₀ hS₀ hM hMC hMinner Astar Sstar DR₁ DS₁ σ₁ H₁ E₁ K₁ N hN hNC hNinner DR₂ DS₂ DR DS
  unfold MarkedTwoStageCompletionForGraphs
  intro Ebase Kbase tailbase headbase ktailbase kheadbase σf Hf Ef Kf tf hf ktf khf A S hA hS hdiv
  have hAstar:∀ a∈Astar,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I:=fun a ha=>hA₀ a (Finset.mem_filter.mp ha).1
  have hSstar:∀ z∈Sstar,z.1∈I∧z.2∈J:=fun z hz=>hS₀ z (Finset.mem_filter.mp hz).1
  have hfirst:=marked_first_deletion_preserves_reserved_resources P π d m σ H C I J hI hC Astar Sstar M hAstar hSstar hMC
  have hsecondR:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬DR₂.Adj x y:=by
    intro x y hc hxy
    have hr:({x,y}:Finset V)∈markedPackingRims N:=hxy.2
    exact Finset.disjoint_left.mp hNC hc ((markedPackingResources_rim N _).mpr hr)
  have hsecondS:∀ v u,Sum.inr (v,u)∈C→¬DS₂.Adj (Sum.inl v) (Sum.inr u):=by
    intro v u hc huv
    have hz:(v,u)∈N.biUnion markedWheelSpokePairs:=(markedFiniteSpokeGraph_adj _ v u).mp huv
    have hr:Sum.inr (v,u)∈N.biUnion markedWheelPhysicalResources:=by
      rw [←markedPackingResources_eq_finite _ _ _ _ π N]
      exact (markedFiniteResources_spoke _ _ _ _ π _ _ (v,u)).mpr hz
    exact Finset.disjoint_left.mp hNC hc hr
  have hactive:=marked_two_stage_deletion_spoke_graphs_avoid_active_pair I T J W S₀ M R hMinner N hNinner
  have hR:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬DR.Adj x y:=by
    intro x y hc
    simpa only [DR,SimpleGraph.sup_adj,not_or] using ⟨hfirst.1 x y hc,hsecondR x y hc⟩
  have hSgraph:∀ v u,Sum.inr (v,u)∈C→¬DS.Adj (Sum.inl v) (Sum.inr u):=by
    intro v u hc
    simpa only [DS,SimpleGraph.sup_adj,not_or] using ⟨hfirst.2.1 v u hc,hsecondS v u hc⟩
  have hTerm:∀ v∈Xterm,∀ u∈Zterm,¬DS.Adj (Sum.inl v) (Sum.inr u):=by
    intro v hv u hu
    have hh:=hactive v (hX hv) u (hZ hu)
    simpa only [DS,SimpleGraph.sup_adj,not_or] using hh
  have habs':=habs DR DS hR hSgraph hTerm A S hA hS hdiv
  have hdec:=habs'.2.2
  have hσ:=rawMarkedDeleteRims_sup σ DR₁ DR₂
  have hH:=markedDeletePhysicalSpokes_sup H DS₁ DS₂
  have hdec₁:HasResourceDecomposition
      (fun Q:MarkedPhysicalDeletedSampleWheel P π d m σ₁ DR₂ DS₂ H₁=>markedWheelPhysicalResources Q)
      (C∪markedFiniteResources tf hf ktf khf π A S):=by
    obtain ⟨Q,hQ,hQres⟩ := hdec
    have heqσ:σf=rawMarkedDeleteRims σ₁ DR₂.edgeFinset:=by
      dsimp only [σf,σ₁]
      rw [rawMarkedDeleteRims_union]
      congr 1
      ext e
      simp only [Finset.mem_union,SimpleGraph.mem_edgeFinset,DR,
        SimpleGraph.edgeSet_sup,Set.mem_union]
    have heqH:Hf=markedDeletePhysicalSpokes H₁ DS₂:=by
      simpa only [Hf,H₁,DS] using hH.symm
    obtain ⟨Q',hQ'pair,hQ'res⟩ := marked_equal_sample_wheels_rebase P π d m σf
      (rawMarkedDeleteRims σ₁ DR₂.edgeFinset) Hf (markedDeletePhysicalSpokes H₁ DS₂)
      heqσ heqH Q hQ
    exact ⟨Q',hQ'pair,hQ'res.trans hQres⟩
  have hgraphsN:=marked_reserved_graphs_of_packing (N.biUnion markedWheelPhysicalResources) N rfl
  have hRN:physicalEdgeGraph (markedReservedRimPairs (N.biUnion markedWheelPhysicalResources))≤DR₂:=by
    rw [←hgraphsN.1]
  have hSN:markedFiniteSpokeGraph (markedReservedSpokePairs (N.biUnion markedWheelPhysicalResources))≤DS₂:=by
    rw [←hgraphsN.2]
  have hdecN:=marked_packing_union_with_deleted_host_decomposition P π d m hm hd σ₁ H₁ DR₂ DS₂ N hN hRN hSN _ hdec₁
  have hgraphsM:=marked_reserved_graphs_of_packing (M.biUnion markedWheelPhysicalResources) M rfl
  have hRM:physicalEdgeGraph (markedReservedRimPairs (M.biUnion markedWheelPhysicalResources))≤DR₁:=by
    rw [←hgraphsM.1,←markedSampleArcSetGraph_packing P π d m σ H M]
    dsimp only [DR₁]
    rw [markedSampleArcSetGraph_union]
    exact le_sup_right
  have hSM:markedFiniteSpokeGraph (markedReservedSpokePairs (M.biUnion markedWheelPhysicalResources))≤DS₁:=by
    rw [←hgraphsM.2]
    dsimp only [DS₁]
    rw [markedFiniteSpokeGraph_union]
    exact le_sup_right
  exact marked_packing_union_with_deleted_host_decomposition P π d m hm hd σ H DR₁ DS₁ M hM hRM hSM _ hdecN
end Oberwolfach

module

public import Oberwolfach.MarkedProtectedResourceRestoration
public import Oberwolfach.MarkedFixedTerminalCompletion

@[expose] public section

/-! Combine the prescribed-edge, deep-vertex and active packings. The
remainder is obtained by deleting only their whole wheels, so temporarily
reserved resources are not inadvertently removed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_three_stage_restoration
    (hm:1≤m) (hb:1≤b)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (A:Finset (E⊕K)) (S:Finset (V×U))
    (hdiv:MarkedRemainderDivisible tail head ktail khead HK A S m)
    (ME MD MU:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hME:∀ W∈ME,∀ Z∈ME,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hMD:∀ W∈MD,∀ Z∈MD,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hMU:∀ W∈MU,∀ Z∈MU,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hED:Disjoint (ME.biUnion markedWheelPhysicalResources) (MD.biUnion markedWheelPhysicalResources))
    (hEU:Disjoint (ME.biUnion markedWheelPhysicalResources) (MU.biUnion markedWheelPhysicalResources))
    (hDU:Disjoint (MD.biUnion markedWheelPhysicalResources) (MU.biUnion markedWheelPhysicalResources))
    (I T:Finset V) (J W:Finset U) (E₀:Finset (Finset V⊕(V×U)))
    (hE:(ME.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=E₀)
    (hD:(MD.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅)
    (hU:(MU.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      (MU.biUnion markedWheelPhysicalResources).filter (markedInnerResource (I\T) (J\W)))
    (hstar:∀ e∈E₀,markedStarResource T W e)
    (hdeep:E₀.filter (markedInnerResource T W)=∅)
    (hsub:ME.biUnion markedWheelPhysicalResources∪MD.biUnion markedWheelPhysicalResources∪MU.biUnion markedWheelPhysicalResources⊆
      A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr)
    (hArcs:∀ a∈A,Sum.elim tail ktail a∉I∨Sum.elim head khead a∉I→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈
        ME.biUnion markedWheelPhysicalResources∪MD.biUnion markedWheelPhysicalResources∪MU.biUnion markedWheelPhysicalResources)
    (hSpokes:∀ z∈S,z.1∉I∨z.2∉J→Sum.inr z∈
      ME.biUnion markedWheelPhysicalResources∪MD.biUnion markedWheelPhysicalResources∪MU.biUnion markedWheelPhysicalResources):
    ∃ N:Finset (MarkedWheel tail head ktail khead m π b H₀ HK),
      (∀ W∈N,∀ Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      N.biUnion markedWheelPhysicalResources=
        ME.biUnion markedWheelPhysicalResources∪MD.biUnion markedWheelPhysicalResources∪MU.biUnion markedWheelPhysicalResources∧
      let A':=A\N.biUnion markedWheelArcs
      let S':=S\N.biUnion markedWheelSpokePairs
      let B:=A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr
      let L:=A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr
      let removed:=B.filter (markedInnerResource I J)\L
      MarkedRemainderDivisible tail head ktail khead HK A' S' m∧
      (∀ a∈A',Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)∧
      (∀ z∈S',z.1∈I∧z.2∈J)∧L=B\N.biUnion markedWheelPhysicalResources∧
      removed=E₀∪(MU.biUnion markedWheelPhysicalResources).filter (markedInnerResource (I\T) (J\W))∧
      removed.filter (markedStarResource T W)=E₀∧removed.filter (markedInnerResource T W)=∅∧
      ∀ p:Finset V⊕(V×U)→Prop,
        (removed.filter p).card≤(E₀.filter p).card+
          (((MU.biUnion markedWheelPhysicalResources).filter (markedInnerResource (I\T) (J\W))).filter p).card:=by
  let R:=fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W
  let FE:=ME.biUnion R
  let FD:=MD.biUnion R
  let FU:=MU.biUnion R
  have hdecE:HasResourceDecomposition R FE:=⟨ME,hME,rfl⟩
  have hdecD:HasResourceDecomposition R FD:=⟨MD,hMD,rfl⟩
  have hdecU:HasResourceDecomposition R FU:=⟨MU,hMU,rfl⟩
  obtain ⟨N,hN,hcov⟩:=resource_decomposition_union R (FE∪FD) FU
    (resource_decomposition_union R FE FD hdecE hdecD hED) hdecU
    (Finset.disjoint_union_left.mpr ⟨hEU,hDU⟩)
  have hNsub:N.biUnion markedWheelPhysicalResources⊆
      A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr:=by
    rw [hcov]
    exact hsub
  obtain ⟨hNA,hNS⟩:=marked_packing_resources_contained hp N A S hNsub
  have hCA:∀ a∈A,Sum.elim tail ktail a∉I∨Sum.elim head khead a∉I→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈N.biUnion markedWheelPhysicalResources:=by
    intro a ha hx
    rw [hcov]
    exact hArcs a ha hx
  have hCS:∀ z∈S,z.1∉I∨z.2∉J→Sum.inr z∈N.biUnion markedWheelPhysicalResources:=by
    intro z hz hx
    rw [hcov]
    exact hSpokes z hz hx
  obtain ⟨hd,ha,hs,heq⟩:=marked_boundary_remainder hp hH I J A S hdiv N hN hNA hNS hCA hCS
  have hpair:∀ e:Finset V,Sum.inl e∈FU→e.Nonempty:=by
    intro e he
    obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp ((markedWheelPhysicalResources_rim W e).mp he)
    have hc:=markedCycle_physical_edge_card tail head ktail khead m π b hm hb W.1 i
    have hc':e.card=2:=by simpa only [←hi,Function.comp_apply] using hc
    exact Finset.card_pos.mp (by omega)
  obtain ⟨hrestore,_,hstars,hdeeps,hcounts⟩:=marked_protected_resource_restoration FE FD FU E₀ I T J W hE hD hU hEU hstar hdeep hpair
  refine ⟨N,hN,hcov,hd,ha,hs,heq,?_⟩
  have hrem:
      (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr).filter (markedInnerResource I J)\
      ((A\N.biUnion markedWheelArcs).image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
        (S\N.biUnion markedWheelSpokePairs).image Sum.inr)=
      (FE∪FD∪FU).filter (markedInnerResource I J):=by
    rw [heq,hcov]
    ext e
    have hh:=fun h:e∈FE∪FD∪FU=>hsub h
    simp only [Finset.mem_filter,Finset.mem_sdiff] at hh ⊢
    tauto
  rw [hrem]
  exact ⟨hrestore,hstars,hdeeps,hcounts⟩

end Oberwolfach

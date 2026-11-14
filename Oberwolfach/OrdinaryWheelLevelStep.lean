module

public import Oberwolfach.OrdinaryWheelHostLift
public import Oberwolfach.OrdinaryRootTerminalGeometry
public import Oberwolfach.RowCoverUnion
public import Oberwolfach.TriangleFactorHubTrade

@[expose] public section
/-! A physically disjoint wheel packing that covers selected rows and hubs
produces one exact, balanced-resource level step in a wider ambient host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_wheel_packing_level_step
    (G P F:SimpleGraph V) (H K:V→U→Prop) (r:ℕ)
    (hGP:G≤P) (hHK:∀v u,H v u→K v u)
    (I:Finset V) (J:Finset U) (T:Finset V) (W:Finset U)
    (hroot:ordinaryHostResources G H⊆ordinaryRootResources I J)
    (M:Finset (OrdinaryWheel G F H r))
    (hM:∀a∈M,∀b∈M,a≠b→Disjoint (ordinaryWheelResources a) (ordinaryWheelResources b))
    (hrim:∀v∈T,∀w,(ordinaryWheelRimGraph M).Adj v w↔G.Adj v w)
    (hrow:∀v∈T,∀u,ordinaryPackingSpokes M v u↔H v u)
    (hcol:∀u∈W,∀v,ordinaryPackingSpokes M v u↔H v u):
    let S:=ordinaryHostResources G H
    let D:=M.biUnion ordinaryWheelResources
    let Next:=S\D;
    Next⊆S ∧ Next⊆ordinaryRootResources (I\T) (J\W) ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=K) (r:=r)) (S\Next):=by
  intro S D Next
  have hMsub:D⊆S:=by
    change M.biUnion ordinaryWheelResources⊆ordinaryHostResources G H
    rw [ordinaryPacking_resources]
    apply ordinary_host_resources_monotone (ordinaryWheelRimGraph M) G (ordinaryPackingSpokes M) H
    · exact ordinaryWheelRimGraph_subhost M
    · rintro v u ⟨a,ha,hh,hv⟩
      rw [←hh]
      exact a.property.1 v hv
  have hdec:HasResourceDecomposition (ordinaryWheelResources (P:=G) (F:=F) (Hbase:=H) (r:=r)) D:=
    ⟨M,hM,rfl⟩
  have heq:S\Next=D:=by
    ext e
    have hh:=fun he=>hMsub (x:=e) he
    simp only [Next,Finset.mem_sdiff]
    tauto
  refine ⟨Finset.sdiff_subset,?_,?_⟩
  · intro e he
    obtain ⟨heS,heD⟩:=Finset.mem_sdiff.mp he
    cases e with
    | inl e=>
      induction e using Sym2.ind with
      | _ v w=>
        have hG:G.Adj v w:=(ordinaryHostResources_rim G H s(v,w)).mp heS
        have hI: v∈I∧w∈I:=(ordinaryRootResources_rim_iff I J v w).mp (hroot heS)
        have hv:v∉T:=by
          intro hv
          apply heD
          change Sum.inl s(v,w)∈M.biUnion ordinaryWheelResources
          rw [ordinaryPacking_resources,ordinaryHostResources_rim]
          exact (hrim v hv w).mpr hG
        have hw:w∉T:=by
          intro hw
          apply heD
          change Sum.inl s(v,w)∈M.biUnion ordinaryWheelResources
          rw [ordinaryPacking_resources,ordinaryHostResources_rim]
          exact ((hrim w hw v).mpr hG.symm).symm
        exact ordinaryRootResources_rim _ _ v w (Finset.mem_sdiff.mpr ⟨hI.1,hv⟩) (Finset.mem_sdiff.mpr ⟨hI.2,hw⟩)
    | inr vu=>
      rcases vu with ⟨v,u⟩
      have hH:H v u:=(ordinaryHostResources_spoke G H v u).mp heS
      have hI:v∈I∧u∈J:=(ordinaryRootResources_spoke_iff I J v u).mp (hroot heS)
      have hv:v∉T:=by
        intro hv
        apply heD
        change Sum.inr (v,u)∈M.biUnion ordinaryWheelResources
        rw [ordinaryPacking_resources,ordinaryHostResources_spoke]
        exact (hrow v hv u).mpr hH
      have hu:u∉W:=by
        intro hu
        apply heD
        change Sum.inr (v,u)∈M.biUnion ordinaryWheelResources
        rw [ordinaryPacking_resources,ordinaryHostResources_spoke]
        exact (hcol u hu v).mpr hH
      exact ordinaryRootResources_spoke _ _ v u (Finset.mem_sdiff.mpr ⟨hI.1,hv⟩) (Finset.mem_sdiff.mpr ⟨hI.2,hu⟩)
  · rw [heq]
    exact ordinary_wheel_host_decomposition_lift hGP hHK D hdec
end Oberwolfach

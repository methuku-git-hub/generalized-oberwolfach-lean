module

public import Oberwolfach.OrdinaryRootFirstFinishData
public import Oberwolfach.OrdinaryRootFirstCleanupRemainder
public import Oberwolfach.OrdinaryRootFirstPackingAmbientFacts
public import Oberwolfach.OrdinaryRootFirstFourPieceLevel

@[expose] public section
/-! Assemble the actual root cover, packing, cleanup and a certified
boundary finish into one protected level decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_level_from_finish
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ) (limit:ℝ)
    (E:OrdinaryRootFirstFinishData Q F H X T Z W r η ell t ν D σ O limit)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    let K:=O.context;
    let B:=ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K;
    let SB:=ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K;
    let C:=wheelFamilyRim O.cleanup.wheels;let SC:=wheelFamilySpokes O.cleanup.wheels;
    let R:=(((K.cover.rim⊔B)⊔C)⊔E.rim);
    let S:=fun v u=>((K.cover.spokes v u∨SB v u)∨SC v u)∨E.spokes v u;
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R S) ∧
    HasOrdinaryWheelDecomposition R S r ∧
    (Q\R).support⊆(X:Set V) ∧ (∀v u,H v u∧¬S v u→v∈X∧u∈Z) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η+limit) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η) ∧
    Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W):=by
  intro K B SB C SC R S
  let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W r η ell t ν D σ O
  let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W r η ell t ν D σ O
  have hb:=ordinary_root_first_packing_ambient_facts Q F H X T Z W r η ell t K
  have hc:=ordinary_root_first_cleanup_remainder Q F H X T Z W r η ell t ν D σ O hbal hdiv
  have hC:=wheelFamily_subhost O.cleanup.wheels
  have hfinishhost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources E.rim E.spokes):=
    ordinary_wheel_host_decomposition_lift (show Q₂≤Q from sdiff_le.trans (sdiff_le.trans sdiff_le))
      (fun _ _ h=>h.1.1.1) _ E.host_decomposition
  have hseq:=ordinary_root_first_four_piece_level Q K.cover.rim B C E.rim F H K.cover.spokes SB SC E.spokes
    X T Z W r ν η limit K.root_sub K.hub_sub K.cover.host_decomposition hb.1 hc.1 hfinishhost
    K.cover.decomposition hb.2.1 O.cleanup.decomposition E.decomposition hb.2.2.1 hb.2.2.2.1
    hC.1 hC.2 E.rim_sub E.spoke_sub hb.2.2.2.2 O.cleanup.degree K.cover.inner_degree E.inner_degree
    K.cover.avoids_deep O.avoids_deep E.avoids_star
  refine ⟨hseq.1,hseq.2.1,?_,?_,hseq.2.2.2.2.1,hseq.2.2.2.2.2.1,hseq.2.2.2.2.2.2⟩
  · rw [hseq.2.2.1]
    exact E.rim_inside
  · intro v u hvu
    have heq:=hseq.2.2.2.1
    have hh:(fun v u=>H v u∧¬S v u) v u:=hvu
    rw [heq] at hh
    exact E.spoke_inside v u hh
end Oberwolfach

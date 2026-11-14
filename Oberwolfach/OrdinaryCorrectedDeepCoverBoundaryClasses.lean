module

public import Oberwolfach.OrdinaryDeepCoverClearsBoundaryClasses
public import Oberwolfach.OrdinaryCorrectedInnerStarBalance
public import Oberwolfach.OrdinaryUnreservedPackingCertificate

@[expose] public section
/-! The corrected deep-root cover gives a globally balanced remainder and
clears the actual outer boundary classes on that very same wheel packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_corrected_deep_cover_boundary_classes
    (Q D F:SimpleGraph V) (H J:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    let R:=ordinaryRimRootStar ((spanningRestriction Q X)\D) T;
    let S:=ordinarySpokeRootStar (fun v u=>(H v u∧v∈X∧u∈Z)∧¬J v u) T W;
    let Qout:=Q\R;let Hout:=fun v u=>H v u∧¬S v u;
    ∀M:Finset (OrdinaryWheel Qout F Hout r),
      (∀A∈M,∀B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B))→
      (∀v∈T,∀w,(ordinaryWheelRimGraph M).Adj v w↔Qout.Adj v w)→
      (∀v∈T,∀u,ordinaryPackingSpokes M v u↔Hout v u)→
      (∀u∈W,∀v,ordinaryPackingSpokes M v u↔Hout v u)→
    let Q':=Q\ordinaryWheelRimGraph M;let H':=fun v u=>H v u∧¬ordinaryPackingSpokes M v u;
    (∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) ∧
    (∀i,ordinaryBoundaryRimSet Q' X i⊆X\T) ∧
    (∀i,ordinaryBoundaryRowSet H' X Z i⊆Z\W) ∧
    (∀j,ordinaryBoundaryHubSet H' Z X j⊆X\T):=by
  intro R S Qout Hout M hdis hRcover hSrow hScol Q' H'
  have hRreserved:R≤spanningRestriction Q X:=by
    intro v w hvw
    exact hvw.1.1
  have hSreserved:∀v u,S v u→v∈X∧u∈Z:=by
    intro v u hvu
    exact ⟨hvu.1.1.2.1,hvu.1.1.2.2⟩
  have hclasses:=ordinary_deep_cover_clears_boundary_classes Q R (ordinaryWheelRimGraph M) H S
    (ordinaryPackingSpokes M) X T Z W hRreserved hSreserved
    (fun v hv w hw=>(hRcover v hv w).mpr hw)
    (fun v hv u hu=>(hSrow v hv u).mpr hu)
    (fun u hu v hv=>(hScol u hu v).mpr hv)
  have hRsub:ordinaryWheelRimGraph M≤Q:=(ordinaryWheelRimGraph_subhost M).trans sdiff_le
  have hSsub:∀v u,ordinaryPackingSpokes M v u→H v u:=by
    intro v u hvu
    obtain ⟨A,hA,ha,hv⟩:=hvu
    have hh:Hout v (ordinaryWheelHub A):=A.property.1 v hv
    exact (ha ▸ hh).1
  have hdec:=ordinaryPacking_decomposition M hdis
  have hb:=ordinary_decomposition_remainder_balance Q (ordinaryWheelRimGraph M) H (ordinaryPackingSpokes M) r
    hRsub hSsub hbal hdiv hdec
  exact ⟨hb.1,hb.2,hclasses.1,hclasses.2.1,hclasses.2.2⟩
end Oberwolfach

module

public import Oberwolfach.OrdinaryRootCoverDataFromCorrectedPacking

@[expose] public section
/-! Instantiate the root-cover package with the actual correction and
outer-degree bounds supplied by the deep-cover construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_data_from_deep_bounds
    (m K:ℕ) (a ξ:ℝ) (Q D F:SimpleGraph V) (H J:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (hTX:T⊆X) (hWZ:W⊆Z)
    (hDdeep:∀v∈T,∀w∈T,¬D.Adj v w)
    (hJdeep:∀v u,J v u→¬(v∈T∧u∈W))
    (hDdegree:∀w:V⊕U,((ordinaryPhysicalGraph D J).degree w:ℝ)≤10*ξ*X.card):
    let ReservedRim:=ordinaryRimRootStar ((spanningRestriction Q X)\D) T;
    let ReservedSpokes:=ordinarySpokeRootStar (fun v u=>(H v u∧v∈X∧u∈Z)∧¬J v u) T W;
    let Qout:=Q\ReservedRim;let Hout:=fun v u=>H v u∧¬ReservedSpokes v u;
    let E:=(ordinaryHostResources D J).filter (ordinaryResourceTouchesRoots T W);
    ∀M:Finset (OrdinaryWheel Qout F Hout (m+1)),
      (∀A∈M,∀B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B))→
      M.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Qout X)
        (fun v u=>Hout v u∧v∈X∧u∈Z)=E→
      (∀v∈T,∀w,(ordinaryWheelRimGraph M).Adj v w↔Qout.Adj v w)→
      (∀v∈T,∀u,ordinaryPackingSpokes M v u↔Hout v u)→
      (∀u∈W,∀v,ordinaryPackingSpokes M v u↔Hout v u)→
      (∀v∉X,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inl v):ℝ)≤
        18*a*Fintype.card V+3*((W.card:ℝ)+(K+1)*T.card))→
      (∀u∉Z,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inr u):ℝ)≤
        3*a*Fintype.card V*(m+1)+(T.card:ℝ)*(m+1))→
      Nonempty (OrdinaryRootCoverData Q F H X T Z W (m+1) (10*ξ*X.card)
        (max (18*a*Fintype.card V+3*((W.card:ℝ)+(K+1)*T.card))
          (3*a*Fintype.card V*(m+1)+(T.card:ℝ)*(m+1)))):=by
  intro ReservedRim ReservedSpokes Qout Hout E M hdis hE hRcover hSrow hScol hleft hright
  apply ordinary_root_cover_data_from_corrected_packing Q D F H J X T Z W (m+1) (10*ξ*X.card)
    (max (18*a*Fintype.card V+3*((W.card:ℝ)+(K+1)*T.card))
      (3*a*Fintype.card V*(m+1)+(T.card:ℝ)*(m+1))) hTX hWZ hDdeep hJdeep hDdegree
    M hdis hE hRcover hSrow hScol
  · intro v hv;exact (hleft v hv).trans (le_max_left _ _)
  · intro u hu;exact (hright u hu).trans (le_max_right _ _)
end Oberwolfach

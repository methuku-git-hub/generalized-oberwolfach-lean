module

public import Oberwolfach.OrdinaryRootCoverData
public import Oberwolfach.OrdinaryDeepCoverInnerDegree
public import Oberwolfach.OrdinaryCorrectedInnerStarBalance
public import Oberwolfach.OrdinaryCorrectedInnerStarResources
public import Oberwolfach.OrdinarySequentialHostDecompositions

@[expose] public section
/-! Package the corrected deep-root cover as local resource data on its
original host, preserving the actual wheel decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_data_from_corrected_packing
    (Q D F:SimpleGraph V) (H J:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z)
    (hDdeep:∀v∈T,∀w∈T,¬D.Adj v w)
    (hJdeep:∀v u,J v u→¬(v∈T∧u∈W))
    (hDdegree:∀w:V⊕U,((ordinaryPhysicalGraph D J).degree w:ℝ)≤η):
    let ReservedRim:=ordinaryRimRootStar ((spanningRestriction Q X)\D) T;
    let ReservedSpokes:=ordinarySpokeRootStar (fun v u=>(H v u∧v∈X∧u∈Z)∧¬J v u) T W;
    let Qout:=Q\ReservedRim;let Hout:=fun v u=>H v u∧¬ReservedSpokes v u;
    let E:=(ordinaryHostResources D J).filter (ordinaryResourceTouchesRoots T W);
    ∀M:Finset (OrdinaryWheel Qout F Hout r),
      (∀A∈M,∀B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B))→
      M.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Qout X)
        (fun v u=>Hout v u∧v∈X∧u∈Z)=E→
      (∀v∈T,∀w,(ordinaryWheelRimGraph M).Adj v w↔Qout.Adj v w)→
      (∀v∈T,∀u,ordinaryPackingSpokes M v u↔Hout v u)→
      (∀u∈W,∀v,ordinaryPackingSpokes M v u↔Hout v u)→
      (∀v∉X,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inl v):ℝ)≤ell)→
      (∀u∉Z,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inr u):ℝ)≤ell)→
      Nonempty (OrdinaryRootCoverData Q F H X T Z W r η ell):=by
  intro ReservedRim ReservedSpokes Qout Hout E M hdis hE hRcover hSrow hScol hleft hright
  let R:=ordinaryWheelRimGraph M
  let S:=ordinaryPackingSpokes M
  have hRout:R≤Qout:=ordinaryWheelRimGraph_subhost M
  have hSout:∀v u,S v u→Hout v u:=by
    intro v u hvu
    obtain ⟨A,hA,ha,hv⟩:=hvu
    exact ha ▸ A.property.1 v hv
  have hQout:Qout≤Q:=sdiff_le
  have hHout:∀v u,Hout v u→H v u:=by intro v u h;exact h.1
  have hR:R≤Q:=hRout.trans hQout
  have hS:∀v u,S v u→H v u:=fun v u h=>hHout v u (hSout v u h)
  have hdec:=ordinaryPacking_decomposition M hdis
  have hraw:HasResourceDecomposition (ordinaryWheelResources (P:=Qout) (F:=F) (Hbase:=Hout) (r:=r))
      (ordinaryHostResources R S):=⟨M,hdis,ordinaryPacking_resources M⟩
  have hhost:=resource_decomposition_map ordinaryWheelResources ordinaryWheelResources
    (ordinaryWheelToLarger (F:=F) (r:=r) hQout hHout) (ordinaryWheelToLarger_resources hQout hHout)
    (ordinaryHostResources R S) hraw
  have hEsub:E⊆ordinaryHostResources D J:=Finset.filter_subset _ _
  have hinner:=ordinary_deep_cover_inner_degree Qout D F Hout J X Z r M E hE hEsub η hDdegree
  have hinnerRes:ordinaryHostResources R S ∩ ordinaryHostResources (spanningRestriction Qout X)
      (fun v u=>Hout v u∧v∈X∧u∈Z)⊆ordinaryHostResources D J:=by
    rw [←ordinaryPacking_resources M,hE]
    exact hEsub
  have hinnerSub:=ordinary_inner_packing_controlled_by_correction Qout R D Hout S J X Z hRout hSout hinnerRes
  have hDavoid:Disjoint (ordinaryPhysicalGraph D J) (ordinaryDeepBlocker T W):=by
    apply (ordinaryPhysicalGraph_disjoint _ _ _ _).mpr
    constructor
    · apply disjoint_iff_inf_le.mpr
      intro v w hvw
      have hh:=(ordinary_deep_rim_blocker_adj T v w).mp hvw.2
      exact hDdeep v hh.2.1 w hh.2.2 hvw.1
    · intro v u hvu
      exact hJdeep v u hvu.1 hvu.2
  have hav:Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W):=by
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    obtain ⟨ha,hb⟩:=ordinary_deep_blocker_support_nested X T Z W hTX hWZ a b hab.2
    have hi:(spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).Adj a b:=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hab.1,ha,hb⟩
    exact (disjoint_iff_inf_le.mp hDavoid) ⟨hinnerSub hi,hab.2⟩
  have hout:∀w∉ordinaryInnerVertices X Z,((ordinaryPhysicalGraph R S).degree w:ℝ)≤ell:=by
    intro w hw
    cases w with
    | inl v=>exact hleft v (fun hv=>hw ((ordinaryInnerVertices_left X Z v).mpr hv))
    | inr u=>exact hright u (fun hu=>hw ((ordinaryInnerVertices_right X Z u).mpr hu))
  have hcoverR:∀v∈T,∀w∉X,Q.Adj v w→R.Adj v w:=by
    intro v hv w hw hq
    have hn:¬ReservedRim.Adj v w:=by
      intro h
      exact hw ((spanningRestriction_adj Q X v w).mp h.1.1).2.2
    exact (hRcover v hv w).mpr ⟨hq,hn⟩
  have hcoverS:∀v∈T,∀u∉Z,H v u→S v u:=by
    intro v hv u hu hh
    have hn:¬ReservedSpokes v u:=by intro h;exact hu h.1.1.2.2
    exact (hSrow v hv u).mpr ⟨hh,hn⟩
  have hcoverH:∀u∈W,∀v∉X,H v u→S v u:=by
    intro u hu v hv hh
    have hn:¬ReservedSpokes v u:=by intro h;exact hv h.1.1.2.1
    exact (hScol u hu v).mpr ⟨hh,hn⟩
  exact ⟨⟨R,S,hR,hS,hhost,hdec,hinner,hout,hav,hcoverR,hcoverS,hcoverH⟩⟩
end Oberwolfach

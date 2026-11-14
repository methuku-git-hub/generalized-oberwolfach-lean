module

public import Oberwolfach.OrdinaryNonrootWheelCoverResult

@[expose] public section
/-! Name the protected root-cover output so it can be transported along the
vortex and combined with the later pairing step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]

def OrdinaryNonrootTriangleCoverRateResult
    (ξ δ:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (I T:Finset V) (B W:Finset U):Prop:=
    ∃(D:SimpleGraph V) (J:V→U→Prop),
      D≤spanningRestriction Q I ∧ (∀v∈T,∀w∈T,¬D.Adj v w) ∧
      (∀v u,J v u→(H v u∧v∈I∧u∈B)∧¬(v∈T∧u∈W)) ∧
      (∀v,((spanningRestriction Q I)\D).degree v=
        2*(Finset.univ.filter (fun u=>(H v u∧v∈I∧u∈B)∧¬J v u)).card) ∧
      (∀u,3∣(Finset.univ.filter (fun v=>(H v u∧v∈I∧u∈B)∧¬J v u)).card) ∧
      (∀x:V⊕U,((ordinaryPhysicalGraph D J).degree x:ℝ)≤10*ξ*I.card) ∧
      let ReservedRim:=ordinaryRimRootStar ((spanningRestriction Q I)\D) T;
      let ReservedSpokes:=ordinarySpokeRootStar (fun v u=>(H v u∧v∈I∧u∈B)∧¬J v u) T W;
      let Qout:=Q\ReservedRim;
      let Hout:=fun v u=>H v u∧¬ReservedSpokes v u;
      let E:=(ordinaryHostResources D J).filter (ordinaryResourceTouchesRoots T W);
      ∃M:Finset (OrdinaryWheel Qout F Hout 3),
        (∀A∈M,∀B'∈M,A≠B'→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B')) ∧
        M.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Qout I)
          (fun v u=>Hout v u∧v∈I∧u∈B)=E ∧
        (∀v∈T,∀w,(ordinaryWheelRimGraph M).Adj v w↔Qout.Adj v w) ∧
        (∀v∈T,∀u,ordinaryPackingSpokes M v u↔Hout v u) ∧
        (∀u∈W,∀v,ordinaryPackingSpokes M v u↔Hout v u) ∧
      (∀v∉T,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inl v):ℝ)≤
        δ*I.card) ∧
      (∀u∉W,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inr u):ℝ)≤
        δ*I.card) ∧
      Disjoint (M.biUnion ordinaryWheelResources)
        (ordinaryHostResources (spanningRestriction Q T) (fun v u=>H v u∧v∈T∧u∈W))
theorem ordinary_nonroot_triangle_cover_rate_improvement
    (ξ a δ:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop) (I T:Finset V) (B W:Finset U)
    (hcover:OrdinaryNonrootWheelCoverResult 2 0 ξ a Q F H I T B W)
    (hrow:18*a*Fintype.card V+3*((W.card:ℝ)+T.card)≤δ*I.card)
    (hcol:9*a*Fintype.card V+3*(T.card:ℝ)≤δ*I.card):
    OrdinaryNonrootTriangleCoverRateResult ξ δ Q F H I T B W :=by
  rcases hcover with ⟨D,J,hDI,hDA,hJ,hCb,hKd,hdeg,M,hpair,hinner,hr,hs,hc,hR,hH,havoid⟩
  refine ⟨D,J,hDI,hDA,hJ,hCb,hKd,hdeg,M,hpair,hinner,hr,hs,hc,?_,?_,havoid⟩
  · intro v hv
    have hh:=hR v hv
    norm_num at hh
    exact hh.trans hrow
  · intro u hu
    have hh:=hH u hu
    norm_num at hh
    nlinarith only [hh,hcol]
end Oberwolfach

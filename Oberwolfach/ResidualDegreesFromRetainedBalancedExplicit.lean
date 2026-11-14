module

public import Oberwolfach.ResidualDegreesFromBalancedComplement
public import Oberwolfach.RetainedMarkedIntervalGeometry

@[expose] public section
/-! The exact retained-interval geometry supplies the uniformity required
for the balanced complement degree calculation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_degrees_from_retained_balanced_complement_explicit
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    {X:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (π:Equiv.Perm V) (c d:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t)
    (F:∀w,SimpleGraph (X w)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (e:∀w,∀C:(F w).ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (Dsrc:∀w,X w→X w→Prop) (horient:∀w x,Dsrc w x (factorCycleOrientation (F w) (e w) x))
    (ext:∀w,retainedMarkedIndex π d σ g t J w→Fin (c*d+5)↪X w)
    (inner:∀w,retainedMarkedIndex π d σ g t J w→Fin (c*d+1)↪X w)
    (hinner:∀w i p,inner w i p=ext w i ⟨p.val+2,by omega⟩)
    (hdis:∀w i j,i≠j→Disjoint (Finset.univ.image (ext w i)) (Finset.univ.image (ext w j)))
    (hσ:∀w,(complementTailDomain (bufferedPathFullDomain (fun _=>c*d) (inner w)) (bufferedFinalEndpoints (fun _=>c*d) (inner w))).image
      (factorCycleOrientation (F w) (e w))=complementTailDomain (bufferedPathFullDomain (fun _=>c*d) (inner w)) (bufferedInitialEndpoints (fun _=>c*d) (inner w)))
    (fC:∀w,{x // x∉bufferedPathStrictInterior (fun _=>c*d) (inner w)}↪V)
    (hstart:∀w i,fC w (bufferedInitialEndpointInComplement (fun _=>c*d) (ext w) (inner w) (hinner w) (hdis w) i)=i.val)
    (hfinish:∀w i,fC w (bufferedEndpointInComplement (fun _=>c*d) (ext w) (inner w) (hinner w) (hdis w) i)=(π^d) i.val)
    (G:SimpleGraph V) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if G.Adj x y then 1 else 0)
    (hbalance:∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U)
    (hDir:∀w x y,(F w).Adj x.1 y.1→Dsrc w x.1 y.1→M (fC w x) (fC w y)=1)
    (hpack:∀w z,w≠z→Disjoint
      (((F w).induce {x | x∉bufferedPathStrictInterior (fun _=>c*d) (inner w)}).edgeFinset.image (Sym2.map (fC w)))
      (((F z).induce {x | x∉bufferedPathStrictInterior (fun _=>c*d) (inner z)}).edgeFinset.image (Sym2.map (fC z)))):
    let H:=orientationMatrixArcs M
    let tail:=fun w=>bufferedOrientedTailEmbedding (fun _=>c*d) (ext w) (inner w) (hinner w) (hdis w) (fC w)
    let head:=fun w=>bufferedOrientedHeadEmbedding (fun _=>c*d) (ext w) (inner w) (hinner w) (hdis w)
      (factorCycleOrientation (F w) (e w)) (hσ w) (fC w)
    ∀v,(((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun x=>(tail w x,head w x)))).filter (fun e=>e.1=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (fun _=>c*d) (inner w) (fC w) ∪
        Finset.univ.image (fun j:retainedMarkedIndex π d σ g t J w=>(π^d) j.val))).card) ∧
      (((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun x=>(tail w x,head w x)))).filter (fun e=>e.2=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (fun _=>c*d) (inner w) (fC w) ∪
        Finset.univ.image (fun j:retainedMarkedIndex π d σ g t J w=>(π^d) j.val))).card):=by
  intro H tail head
  obtain ⟨hinj,hdisIntervals,huniform⟩:=retained_marked_interval_geometry π d hd hnoshort σ g t J
  exact residual_degrees_from_balanced_complement (V:=V) (U:=U)
    (I:=fun w=>retainedMarkedIndex π d σ g t J w) (X:=X) π (fun _ _=>d) (fun _ i=>i.val)
    (fun _ _=>hd) hinj hdisIntervals huniform (fun _ _=>c*d) ext inner hinner hdis
    F hF e Dsrc horient hσ fC hstart hfinish G M hphysical hbalance hDir hpack
end Oberwolfach

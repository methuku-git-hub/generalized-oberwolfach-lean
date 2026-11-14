module

public import Oberwolfach.ActualPrescribedMultiplicityDependent
public import Oberwolfach.OrdinaryUnreservedFactorPaths

@[expose] public section
/-! The prescribed vertices of the unreserved factors use only sampled
extended intervals, so the same sample's occupancy bounds their load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_prescribed_image_load
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] {J:U→Type} [∀w,DecidableEq (J w)]
    (π:Equiv.Perm (Fin n)) (d c:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r)
    (F:U→SimpleGraph (Fin n)) (Cres:∀w,Finset (F w).ConnectedComponent):
    let X:=fun w=>{x:Fin n // (F w).connectedComponentMk x∉Cres w}
    let G:=fun w=>(F w).induce {x | (F w).connectedComponentMk x∉Cres w};
    ∀(data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false r Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}) (J:=J w) (G w))
    (ext:∀w,(retainedMarkedIndex π d σ false r Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin (c*d+5)↪X w)
    (ψ:∀w,X w→Fin n)
    (hc:∀w,(data w).c=c) (hd:∀w,(data w).d=d)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hmarker:∀w i (j:Fin (d+1)),bufferedMarker c d (ext w i) j∈(data w).prescribed→
      ψ w (bufferedMarker c d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σ false true r Jret w i))
    (bound:ℝ) (hOcc:∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤bound),
    ∀v,((Finset.univ.filter (fun w=>v∈
      (residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)≤bound:=by
  intro X G data ext ψ hc hd hsupp hmarker bound hOcc v
  have hh:=actual_prescribed_multiplicity_dependent_le_extended_hubs π d c σ r Jret G data ext ψ hc hd hsupp hmarker v
  exact hh.trans (hOcc v)
end Oberwolfach

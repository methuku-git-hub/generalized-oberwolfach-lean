module

public import Oberwolfach.OrdinaryPackagedPrescribedBoundaryLoadShape

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_packaged_prescribed_boundary_load_named
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t):
    OrdinaryPackagedPrescribedBoundaryLoadShape (K:=K) (X:=X) π d m hd Rim raw t Jret :=by
  unfold OrdinaryPackagedPrescribedBoundaryLoadShape
  intro σ H RM state RR φ L AM AU len Qwheel E S MW W Good Pack A B root Pos F Arc Avail Reserve p Bbound Rbound Q Row hrows hboundary
  have hh:=ordinary_prescribed_boundary_spoke_matching_named (K:=K) (X:=X) (J:=AU) π d m (m+1) hd Rim raw t Jret
  apply hh L (fun u=>(p u).marker) (fun u=>(p u).hGood) F (fun u=>(p u).data) (fun u=>(p u).ext) (fun u=>(p u).ψ)
    (fun u=>(p u).hc) (fun u=>(p u).hd) (fun u=>(p u).hs₂) (fun u=>(p u).hSupp) (fun u=>(p u).hMarker)
    (by intro u a; simpa only [Pos,root,retainedAndRawIntervalRoot] using (p u).hPos a) Bbound Rbound hrows hboundary
end Oberwolfach

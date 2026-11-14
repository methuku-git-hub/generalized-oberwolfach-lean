module

public import Oberwolfach.OrdinaryPackagedLoadTargetColumnsShape
public import Oberwolfach.OrdinaryPackagedPrescribedBoundaryLoadNamed

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_packaged_load_target_columns
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t):
    OrdinaryPackagedLoadTargetColumnsShape (K:=K) (X:=X) π d m hd Rim raw t Jret :=by
  unfold OrdinaryPackagedLoadTargetColumnsShape
  intro σ H RM state RR φ L AM AU len Qwheel E S MW W Good Pack A B root Pos F Arc Avail Reserve p δ a γ Q Row Prescribed
    hδ hU hD hN hMatching hrows hboundary T Old Gbad hbad hTarget
  have hnamed:=ordinary_packaged_prescribed_boundary_load_named (K:=K) (X:=X) π d m hd Rim raw t Jret
  unfold OrdinaryPackagedPrescribedBoundaryLoadShape at hnamed
  have hpres:=hnamed L F Arc Avail Reserve p
    (4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)) ((max a γ)*n) hrows hboundary
  have hbudget:=ordinary_boundary_prescribed_load_budget n (Fintype.card U) d δ a γ (by omega) hδ hU hD hN hMatching
    (fun v=>((Finset.univ.filter (fun u=>v∈Prescribed u)).card:ℝ)) (fun v=>(Gbad.degree v:ℝ)) hpres hbad
  intro v
  linarith [hbudget v,hTarget v]
end Oberwolfach

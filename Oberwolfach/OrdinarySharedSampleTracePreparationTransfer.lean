module

public import Oberwolfach.OrdinaryNaturalTraceCertificate
public import Oberwolfach.OrdinarySharedSamplePreparationTransfer

@[expose] public section
/-! Transfer a completion proved on the expanded experiment to the original
Bernoulli preparation event, without selecting a different outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) sharedTraceTransferFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_shared_sample_trace_preparation_transfer
    {n q r:ℕ} {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (a:U→Γ→ℝ) (ha:∀w j,0≤a w j) (hA:∀w,∑j,a w j≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑j,a w j))
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop)
    (b:ℝ)
    (hE:b≤((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd a ha hA s hs hS)).sigma ν).probability E)
    (hcomplete:∀z,E z→OrdinaryNaturalTraceCertificate (r:=r) P (longPhysicalStateGraph P z.1 {0,1,2,3,4}) I ξ B F C):
    b≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (2*p+2*k+2*p₂+2*k₂+u)
      (by positivity) hsum)).probability (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F) :=by
  apply ordinary_shared_sample_preparation_transfer P I ξ B F hF C hr hsize p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd a ha hA s hs hS ν E b hE
  intro z hz
  exact ordinary_natural_trace_certificate_to_preparation P (longPhysicalStateGraph P z.1 {0,1,2,3,4}) I ξ B F hF C hr hsize (hcomplete z hz)
end Oberwolfach

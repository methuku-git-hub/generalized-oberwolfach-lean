module

public import Oberwolfach.OrdinaryProductCoinTracePreparationTransfer
public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData

@[expose] public section
/-! The original assigned experiment, including the same reference coins,
transfers a deterministic trace certificate to its exact retention marginal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) assignedCoinTraceTransferFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_coin_trace_preparation_transfer
    {n q r D K:ℕ} (P:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (i₀:Fin K) (rsv θ cSample ρ₀ smin:ℝ) (d:ℕ) (hd:2≤d)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ cSample ρ₀ smin d)
    (hρ0:0≤ initialIndexDensity (Fin q) D) (hρ1:initialIndexDensity (Fin q) D≤1)
    {R:(∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κcoins:FiniteLaw (Sym2 (Fin n)→Bool))
    (E:((Σσ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool))→Prop)
    (b:ℝ):
    let p:=initialIndexDensity (Fin q) D*rsv/2;
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ cSample D;
    let qprob:=ordinaryAssignedMarkedProbability F hF K θ cSample;
    let sprob:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ cSample;
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd
      qprob sampling.hq sampling.hQ sprob sampling.hs sampling.hS);
    b≤((μ.sigma ν).prod κcoins).probability E→
    (∀z,E z→OrdinaryNaturalTraceCertificate (r:=r) P (longPhysicalStateGraph P z.1.1 {0,1,2,3,4}) I ξ B F C)→
    b≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (initialIndexDensity (Fin q) D) hρ0 hρ1)).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F) :=by
  intro p p₂ qprob sprob μ hE hcomplete
  have hphysical:initialIndexDensity (Fin q) D=2*p+2*0+2*p₂+2*0+sampling.u:=by
    simpa only [p,p₂] using sampling.hphysical.symm
  exact ordinary_product_coin_trace_preparation_transfer P I ξ B F hF C hr hsize
    p 0 p₂ 0 sampling.u sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum
    d hd qprob sampling.hq sampling.hQ sprob sampling.hs sampling.hS ν κcoins E b hE hcomplete
    (initialIndexDensity (Fin q) D) hphysical hρ0 hρ1
end Oberwolfach

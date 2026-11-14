module

public import Oberwolfach.OrdinaryAssignedCoinNaturalPreparationTransfer
public import Oberwolfach.OrdinaryCommonSampleTargetFailureBudget

@[expose] public section
/-! Once the deterministic preparation certificate is established on the common event, the
original assigned retention law attains the requested failure probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) assignedCoinNaturalTargetFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_coin_natural_target
    (χ:ℝ) (hχ:0<χ):
    ∃cap:ℝ,0<cap ∧ ∃N:ℕ,1≤N ∧
    ∀{n q r D K:ℕ},N≤n→
    ∀(P:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (i₀:Fin K) (rsv θ cSample ρ₀ smin:ℝ) (d:ℕ) (hd:2≤d)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ cSample ρ₀ smin d)
    (hρ0:0≤ initialIndexDensity (Fin q) D) (hρ1:initialIndexDensity (Fin q) D≤1)
    {R:(∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κcoins:FiniteLaw (Sym2 (Fin n)→Bool))
    (E:((Σσ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool))→Prop)
    (lossE ζMatch χtwo χrows χdeep χcut χHub χEndpoint χhost χref χinner χfine:ℝ),
    lossE≤cap→ζMatch≤cap→χtwo≤cap→χrows≤cap→χdeep≤cap→χcut≤cap→
    χHub≤cap→χEndpoint≤cap→χhost≤cap→χref≤cap→χinner≤cap→χfine≤cap→
    let p:=initialIndexDensity (Fin q) D*rsv/2;
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ cSample D;
    let qprob:=ordinaryAssignedMarkedProbability F hF K θ cSample;
    let sprob:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ cSample;
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd
      qprob sampling.hq sampling.hQ sprob sampling.hs sampling.hS);
    let loss:=lossE+ζMatch+χtwo+χrows+χdeep+χcut+χHub+χEndpoint+χhost+χref+χinner+χfine;
    1-loss-2/(n:ℝ)^10-(1/(n:ℝ)+2/(n:ℝ)^2)≤((μ.sigma ν).prod κcoins).probability E→
    (∀z,E z→OrdinaryNaturalPreparationCertificate (r:=r) P (longPhysicalStateGraph P z.1.1 {0,1,2,3,4}) I ξ B F C)→
    1-χ-1/(n:ℝ)^10≤
      (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (initialIndexDensity (Fin q) D) hρ0 hρ1)).probability
        (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F) :=by
  obtain ⟨cap,hcap,N,hN,hbudget⟩:=ordinary_common_sample_target_failure_budget χ hχ
  refine ⟨cap,hcap,N,hN,?_⟩
  intro n q r D K hn P I ξ B F hF C hr hsize i₀ rsv θ cSample ρ₀ smin d hd sampling hρ0 hρ1
    R _ ν κcoins E lossE ζMatch χtwo χrows χdeep χcut χHub χEndpoint χhost χref χinner χfine
    hEcap hMatch htwo hrows hdeep hcut hHub hEndpoint hhost href hinner hfine p p₂ qprob sprob μ loss hE hcomplete
  have hb:=hbudget n hn lossE ζMatch χtwo χrows χdeep χcut χHub χEndpoint χhost χref χinner χfine
    hEcap hMatch htwo hrows hdeep hcut hHub hEndpoint hhost href hinner hfine
  have htarget:1-χ-1/(n:ℝ)^10≤1-loss-2/(n:ℝ)^10-(1/(n:ℝ)+2/(n:ℝ)^2):=by
    dsimp [loss]
    linarith only [hb]
  have hprep:=ordinary_assigned_coin_natural_preparation_transfer P I ξ B F hF C hr hsize
    i₀ rsv θ cSample ρ₀ smin d hd sampling hρ0 hρ1 ν κcoins E
    (1-loss-2/(n:ℝ)^10-(1/(n:ℝ)+2/(n:ℝ)^2)) hE hcomplete
  exact htarget.trans hprep
end Oberwolfach

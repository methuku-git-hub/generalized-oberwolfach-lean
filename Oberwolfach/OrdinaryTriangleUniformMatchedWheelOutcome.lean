module

public import Oberwolfach.OrdinaryTriangleUniformSplitBeforeSample
public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
/-! Name the uniform same-sample wheel callback and retain it inside an
existing common event without any additional probability loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleUniformMatchedWheelOutcome
    {n q mAbs tAbs aAbs bAbs:ℕ} (d:ℕ) (P:SimpleGraph (Fin n)) (D mv:ℕ) (β ε rate ξroot:ℝ)
    (Vor:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (Fs:Fin q→SimpleGraph (Fin n)) (Comps:∀u,Finset (Fs u).ConnectedComponent)
    (Ares Wterm:Finset (Fin n)) (Bterm:Finset (Fin q)) (ξabs:ℝ)
    (Cost:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))→ℝ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e):Prop :=
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e)
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P raw\Bad
    let Href:=rawWheelSpokes π d raw false
    ∀Kres JQ JH,OrdinaryCorrectedProtectedReservoirWitness 3 mAbs tAbs aAbs bAbs ξabs Reference Bad Href Ares
      (Vor.extendedVertices 1) Wterm Bterm (Vor.extendedIndices 1) Kres JQ JH→
    ∀Target:SimpleGraph (Fin n),Target≤P→Target.IsRegularOfDegree (2*q)→
    ∀embed:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉Comps u}↪Fin n,
      OrdinaryTrackedComplementFor P Target π d σ Fs Comps (Vor.extendedVertices 1) (Vor.extendedIndices 1) Kres (Cost Kres) embed→
      OrdinaryTrackedSplitWheelCertificatesAt P Target Bad Fs Comps 3 Kres D mv β ε Vor Vor.length
        (ordinaryVortexSelectedCost Vor rate) (ordinaryFineDeepCost Vor ξroot) embed

theorem ordinary_triangle_probability_attach_uniform_wheels
    {Ω:Type} [Fintype Ω] {n q mAbs tAbs aAbs bAbs:ℕ} (μ:FiniteLaw Ω) (Prior Tests:Ω→Prop)
    (d:ℕ) (P:SimpleGraph (Fin n)) (D mv:ℕ) (β ε rate ξroot:ℝ) (Vor:Vortex (Fin q) P D β ε mv)
    (π:Equiv.Perm (Fin n)) (Fs:Fin q→SimpleGraph (Fin n)) (Comps:∀u,Finset (Fs u).ConnectedComponent)
    (Ares Wterm:Finset (Fin n)) (Bterm:Finset (Fin q)) (ξabs:ℝ)
    (Cost:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))→ℝ)
    (sample:Ω→∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (hWheel:∀z,Prior z→Tests z→OrdinaryTriangleUniformMatchedWheelOutcome (mAbs:=mAbs) (tAbs:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
      d P D mv β ε rate ξroot Vor π Fs Comps Ares Wterm Bterm ξabs Cost (sample z)) (bprob:ℝ)
    (hprob:bprob≤μ.probability (fun z=>Prior z∧Tests z)):
    bprob≤μ.probability (fun z=>Prior z ∧
      OrdinaryTriangleUniformMatchedWheelOutcome (mAbs:=mAbs) (tAbs:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
        d P D mv β ε rate ξroot Vor π Fs Comps Ares Wterm Bterm ξabs Cost (sample z)) :=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1,hWheel z hz.1 hz.2⟩
end Oberwolfach

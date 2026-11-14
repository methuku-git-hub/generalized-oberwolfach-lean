module

public import Oberwolfach.OrdinaryAssignedProductPhysicalMarginal
public import Oberwolfach.OrdinaryNaturalPreparationCertificate

@[expose] public section
/-! Once a same-sample natural certificate is proved, transfer its probability
under the exact assigned sampler to the original retention marginal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_natural_preparation_transfer
    {n q r D:ℕ} (P:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (K:ℕ) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (π:Equiv.Perm (Fin n)) (d:ℕ) (hd:2≤d)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d)
    {R:(∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 (Fin n)→Bool))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
    (bprob:ℝ):
    let p:=initialIndexDensity (Fin q) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let marks:=ordinaryAssignedMarkedProbability F hF K θ c
    let spokes:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd marks sampling.hq sampling.hQ spokes sampling.hs sampling.hS);
    bprob≤((μ.sigma ν).prod κ).probability E→
    (∀z,E z→OrdinaryNaturalPreparationCertificate (r:=r) P (longPhysicalStateGraph P z.1.1 {0,1,2,3,4}) I ξ B F C)→
    bprob≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (initialIndexDensity (Fin q) D)
      (by unfold initialIndexDensity;positivity)
      (by rw [←sampling.hphysical];exact sampling.hsum))).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F) :=by
  intro p p₂ marks spokes μ hE hcompletion
  let Good:=fun S₀:SimpleGraph (Fin n)=>ProtectedFactorPreparation P S₀ I ξ B F
  have hgood:bprob≤((μ.sigma ν).prod κ).probability (fun z=>Good (longPhysicalStateGraph P z.1.1 {0,1,2,3,4})):=by
    apply hE.trans
    apply finiteLaw_probability_mono
    intro z hz
    exact ordinary_natural_certificate_prepares P (longPhysicalStateGraph P z.1.1 {0,1,2,3,4}) I ξ B F hF C hr hsize (hcompletion z hz)
  have hmarg:=ordinary_assigned_product_physical_marginal F hF K i₀ rsv θ c ρ₀ smin d hd sampling P ν κ Good
  rw [hmarg] at hgood
  exact hgood
end Oberwolfach

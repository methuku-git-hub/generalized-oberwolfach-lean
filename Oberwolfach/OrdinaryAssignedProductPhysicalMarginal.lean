module

public import Oberwolfach.OrdinaryAssignedVortexPhysicalMarginal
public import Oberwolfach.FiniteProductRegrouping

@[expose] public section
/-! Additional reference coins, even when a good event uses them, do not
change the original physical retention marginal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency true in
theorem ordinary_assigned_product_physical_marginal
    {n D:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ) (hd:2≤d)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d)
    (P:SimpleGraph (Fin n))
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 (Fin n)→Bool))
    (Good:SimpleGraph (Fin n)→Prop):
    let p:=initialIndexDensity U D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS);
    ((μ.sigma ν).prod κ).probability (fun z=>Good (longPhysicalStateGraph P z.1.1 {0,1,2,3,4}))=
    (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (initialIndexDensity U D)
      (by unfold initialIndexDensity; positivity)
      (by rw [←sampling.hphysical];exact sampling.hsum))).probability (fun σ=>Good (retainedGraph P σ)) :=by
  intro p p₂ q s μ
  have hp:=finiteLaw_prod_first_probability (μ.sigma ν) κ
    (fun z=>Good (longPhysicalStateGraph P z.1 {0,1,2,3,4}))
  calc
    _ = (μ.sigma ν).probability (fun z=>Good (longPhysicalStateGraph P z.1 {0,1,2,3,4})) :=by
      convert hp using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    _ = _ :=by
      convert ordinary_assigned_vortex_physical_marginal F hF K i₀ rsv θ c ρ₀ smin d hd sampling P ν Good using 1 <;>
        congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach

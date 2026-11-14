module

public import Oberwolfach.OrdinaryActiveVortexDensityBalance

@[expose] public section
/-! The trimmed active level satisfies a fixed retained density margin and
    the actual parent balance, under the original vortex error hierarchy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_active_vortex_profiles
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (P:SimpleGraph V) (D m r:ℕ) (β ε θ α ρ pH:ℝ)
    (Q:Vortex U P D β ε m) (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:ρ=initialIndexDensity U D) (hρpos:0<ρ) (hβ:0≤β) (hε:0≤ε) (hεsmall:ε≤1/4) (hpH:0≤pH)
    (hdegree:(θ+α)*Fintype.card V≤D) (hthreshold:cycleThreshold r≤θ) (hα:0<α)
    (hβsmall:(10/3:ℝ)*β≤α/2) (i:ℕ):
    let C:=Q.extendedVertices i\Q.extendedVertices (i+2);
    let W:=Q.extendedIndices i\Q.extendedIndices (i+2);
    let A:=Q.extendedVertices (i+1)\Q.extendedVertices (i+2);
    let B:=Q.extendedIndices (i+1)\Q.extendedIndices (i+2);
    let Ain:=A.subtype (fun v=>v∈C);
    let Bin:=B.subtype (fun u=>u∈W);
    let Pactive:=P.induce (C:Set V);
    cycleThreshold r+α/2≤θ+α/2 ∧
    (∀x:{v:V // v∈C},(θ+α/2)*Ain.card≤((Ain∩Pactive.neighborFinset x).card:ℝ)) ∧
    (∀x:{v:V // v∈C},|(ρ*pH)*(Pactive.neighborFinset x∩Ain).card-2*pH*Bin.card|≤
      (ρ*pH)*(5/3:ℝ)*β*Ain.card):=by
  intro C W A B Ain Bin Pactive
  have hh:=ordinary_active_vortex_density_balance P D m β ε θ α ρ pH Q hn hreg hρ hρpos hβ hε hεsmall hpH hdegree i
  refine ⟨by linarith,?_,?_⟩
  · intro x
    have hscale:=mul_le_mul_of_nonneg_right (show θ+α/2≤θ+α-(10/3:ℝ)*β by linarith)
      (show (0:ℝ)≤Ain.card by positivity)
    exact hscale.trans (hh.1 x)
  · intro x
    rw [Finset.inter_comm (Pactive.neighborFinset x) Ain]
    convert hh.2 x using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach

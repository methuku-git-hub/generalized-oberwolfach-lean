module

public import Oberwolfach.MixedMarkedAssignedLawIdentity
public import Oberwolfach.MixedClassActualRetention

@[expose] public section
/-! Transfer any marked retained event to the mixed exposure using the exact
same interval law, all five physical probabilities, and conditional retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) mixedMarkedExtraTransferFinEquality (n:ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

theorem mixed_marked_assigned_retained_extra_transfer {I:Type} {U:I→Type} [∀i,Fintype (U i)]
    {n:ℕ} [Nonempty (Fin n)] (K m d:ℕ) (hd:2≤d) (θ sOrd:ℝ)
    (label:I→Option (Fin K)) (F:∀i,U i→SimpleGraph (Fin n))
    (hF:∀i w,(F i w).IsRegularOfDegree 2) (a:I) (hj:label a=none)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (π:Equiv.Perm (Fin n)) (tag:Bool) (χ extraErr:ℝ):
    letI : DecidableEq (U a) := Classical.decEq (U a)
    let qm:=mixedAssignedIntervalProbability K m θ label F hF a
    let sm:=mixedAssignedSpokeProbability K m sOrd θ label F hF a
    let ql:=longAssignedIntervalProbability (F a) (hF a) K m θ
    let sl:=longAssignedSpokeProbability (F a) (hF a) K m θ;
    ∀ (hqm:∀w g,0≤qm w g) (hQm:∀w,∑g,qm w g≤1/8)
      (hsm:∀w g,0≤sm w g) (hSm:∀w,∑g,sm w g≤ intervalUncoveredProbability d (∑g,qm w g))
      (hql:∀w g,0≤ql w g) (hQl:∀w,∑g,ql w g≤1/8)
      (hsl:∀w g,0≤sl w g) (hSl:∀w,∑g,sl w g≤ intervalUncoveredProbability d (∑g,ql w g)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd qm hqm hQm sm hsm hSm)
    let ν:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd ql hql hQl sl hsl hSl)
    letI : ∀ ω:(∀e:RawWheelCoordinate (Fin n) (U a),RawExpandedMarkedCoordinateState Bool Bool e),
      Fintype (mixedClassRetentionSpace true π d tag ω):=fun ω=>mixedClassRetentionFintype true π d tag ω
    letI : Fintype (Σ ω:(∀e:RawWheelCoordinate (Fin n) (U a),RawExpandedMarkedCoordinateState Bool Bool e),mixedClassRetentionSpace true π d tag ω):=
      @Sigma.instFintype _ _ (fun ω=>mixedClassRetentionFintype true π d tag ω) inferInstance;
    ∀E:(Σ ω:(∀e:RawWheelCoordinate (Fin n) (U a),RawExpandedMarkedCoordinateState Bool Bool e),mixedClassRetentionSpace true π d tag ω)→Prop,
      1-100*χ-107/(n:ℝ)-extraErr≤(ν.sigma (mixedClassActualRetention true π d tag)).probability E→
      1-100*χ-107/(n:ℝ)-extraErr≤(μ.sigma (mixedClassActualRetention true π d tag)).probability E :=by
  intro qm sm ql sl hqm hQm hsm hSm hql hQl hsl hSl μ ν E hE
  have heq:μ=ν:=mixed_marked_assigned_law_identity K m d hd θ sOrd label F hF a hj p k p₂ k₂ u
    hp hk hp₂ hk₂ hu hsum hqm hQm hsm hSm hql hQl hsl hSl
  rw [heq]
  exact hE
end Oberwolfach

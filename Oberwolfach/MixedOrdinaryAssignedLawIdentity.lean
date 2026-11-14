module

public import Oberwolfach.MixedAssignedSamplingRecipes
public import Oberwolfach.OrdinaryRawLawCongruence

@[expose] public section
/-! For an ordinary class the selected marginal of the mixed experiment is
exactly the original ordinary product law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) mixedOrdinaryLawFinEquality (n:ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

theorem mixed_ordinary_assigned_law_identity {I:Type} {U:I→Type} [∀i,Fintype (U i)]
    {n:ℕ} (K m d:ℕ) (hd:2≤d) (θ sOrd:ℝ)
    (label:I→Option (Fin K)) (F:∀i,U i→SimpleGraph (Fin n))
    (hF:∀i w,(F i w).IsRegularOfDegree 2) (a:I) (j:Fin K) (hj:label a=some j)
    (p ρ:ℝ) (hprob:2*p=ρ*sOrd)
    (hp0:∀_:Sym2 (Fin n),0≤2*p) (hp1:∀_:Sym2 (Fin n),2*p≤1)
    (hr0:∀_:Sym2 (Fin n),0≤ρ*sOrd) (hr1:∀_:Sym2 (Fin n),ρ*sOrd≤1):
    let qm:=mixedAssignedIntervalProbability K m θ label F hF a
    let sm:=mixedAssignedSpokeProbability K m sOrd θ label F hF a
    let qo:=ordinaryAssignedMarkedProbability (F a) (hF a) K θ ((m:ℝ)+1)
    let so:=ordinaryAssignedSpokeProbability (F a) (hF a) K j sOrd θ ((m:ℝ)+1);
    ∀ (hqm:∀w g,0≤qm w g) (hQm:∀w,∑g,qm w g≤1/8)
      (hsm:∀w g,0≤sm w g) (hSm:∀w,∑g,sm w g≤ intervalUncoveredProbability d (∑g,qm w g))
      (hqo:∀w g,0≤qo w g) (hQo:∀w,∑g,qo w g≤1/8)
      (hso:∀w g,0≤so w g) (hSo:∀w,∑g,so w g≤ intervalUncoveredProbability d (∑g,qo w g)),
    FiniteLaw.pi (rawWheelLaw (fun _=>2*p) hp0 hp1 d hd qm hqm hQm sm hsm hSm)=
    FiniteLaw.pi (rawWheelLaw (fun _=>ρ*sOrd) hr0 hr1 d hd qo hqo hQo so hso hSo) :=by
  intro qm sm qo so hqm hQm hsm hSm hqo hQo hso hSo
  congr 1
  apply raw_wheel_law_congr d hd
  · funext e; exact hprob
  · dsimp only [qm,qo,mixedAssignedIntervalProbability]; rw [hj]
  · dsimp only [sm,so,mixedAssignedSpokeProbability]; rw [hj]
end Oberwolfach

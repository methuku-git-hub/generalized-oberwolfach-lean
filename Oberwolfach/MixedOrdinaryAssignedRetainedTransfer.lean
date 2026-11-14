module

public import Oberwolfach.MixedOrdinaryAssignedLawIdentity
public import Oberwolfach.OrdinaryRetainedClassBudget

@[expose] public section
/-! Transfer an ordinary class event to the mixed experiment on its original
categorical exposure and singleton retention variable. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) mixedOrdinaryTransferFinEquality (n:ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

theorem mixed_ordinary_assigned_retained_transfer {I:Type} {U:I→Type} [∀i,Fintype (U i)]
    {n:ℕ} [Nonempty (Fin n)] (K m d:ℕ) (hd:2≤d) (θ sOrd:ℝ)
    (label:I→Option (Fin K)) (F:∀i,U i→SimpleGraph (Fin n))
    (hF:∀i w,(F i w).IsRegularOfDegree 2) (a:I) (j:Fin K) (hj:label a=some j)
    (p ρ:ℝ) (hprob:2*p=ρ*sOrd)
    (hp0:∀_:Sym2 (Fin n),0≤2*p) (hp1:∀_:Sym2 (Fin n),2*p≤1)
    (hr0:∀_:Sym2 (Fin n),0≤ρ*sOrd) (hr1:∀_:Sym2 (Fin n),ρ*sOrd≤1)
    (π:Equiv.Perm (Fin n)) (tag:Bool) (χ:ℝ) (hχ:0≤χ):
    letI : DecidableEq (U a) := Classical.decEq (U a)
    let qm:=mixedAssignedIntervalProbability K m θ label F hF a
    let sm:=mixedAssignedSpokeProbability K m sOrd θ label F hF a
    let qo:=ordinaryAssignedMarkedProbability (F a) (hF a) K θ ((m:ℝ)+1)
    let so:=ordinaryAssignedSpokeProbability (F a) (hF a) K j sOrd θ ((m:ℝ)+1);
    ∀ (hqm:∀w g,0≤qm w g) (hQm:∀w,∑g,qm w g≤1/8)
      (hsm:∀w g,0≤sm w g) (hSm:∀w,∑g,sm w g≤ intervalUncoveredProbability d (∑g,qm w g))
      (hqo:∀w g,0≤qo w g) (hQo:∀w,∑g,qo w g≤1/8)
      (hso:∀w g,0≤so w g) (hSo:∀w,∑g,so w g≤ intervalUncoveredProbability d (∑g,qo w g)),
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _=>2*p) hp0 hp1 d hd qm hqm hQm sm hsm hSm)
    let ν:=FiniteLaw.pi (rawWheelLaw (fun _=>ρ*sOrd) hr0 hr1 d hd qo hqo hQo so hso hSo)
    letI : ∀ ω:RawWheelOutcome (Fin n) (U a) Bool Bool,Fintype (mixedClassRetentionSpace false π d tag ω):=
      fun ω=>mixedClassRetentionFintype false π d tag ω
    letI : Fintype (Σ ω:RawWheelOutcome (Fin n) (U a) Bool Bool,mixedClassRetentionSpace false π d tag ω):=
      @Sigma.instFintype _ _ (fun ω=>mixedClassRetentionFintype false π d tag ω) inferInstance;
    ∀E:RawWheelOutcome (Fin n) (U a) Bool Bool→Prop,
      1-(1/(n:ℝ)+3/(n:ℝ)^2)≤ν.probability E→
      1-(100*χ+200/(n:ℝ))≤(μ.sigma (mixedClassActualRetention false π d tag)).probability (fun z=>E z.1) :=by
  intro qm sm qo so hqm hQm hsm hSm hqo hQo hso hSo μ ν E hE
  have heq:μ=ν:=mixed_ordinary_assigned_law_identity K m d hd θ sOrd label F hF a j hj p ρ hprob
    hp0 hp1 hr0 hr1 hqm hQm hsm hSm hqo hQo hso hSo
  have hE':1-(1/(Fintype.card (Fin n):ℝ)+3/(Fintype.card (Fin n):ℝ)^2)≤μ.probability E:=by
    rw [heq]
    simpa only [Fintype.card_fin] using hE
  have h:=@ordinary_same_sample_retained_class_budget (Fin n) (U a)
    (inferInstance : Fintype (Fin n)) (inferInstance : LinearOrder (Fin n))
    (inferInstance : Nonempty (Fin n)) (inferInstance : Fintype (U a)) (Classical.decEq (U a))
    π d tag χ hχ μ E hE'
  simpa only [Fintype.card_fin] using h
end Oberwolfach

module

public import Oberwolfach.MixedOrdinaryAssignedRetainedTransfer
public import Oberwolfach.OrdinaryAssignedNamedClassEvent

@[expose] public section
/-! Use the proved ordinary event as the event for an ordinary class of the
shared mixed exposure, preserving the original law and retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) mixedOrdinaryNamedFinEquality (n:ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

theorem mixed_ordinary_named_event_transfer {I:Type} {U:I→Type} [∀i,Fintype (U i)]
    {n:ℕ} [Nonempty (Fin n)] (K m d r:ℕ) (hd:2≤d) (hr:3≤r) (θ sOrd:ℝ)
    (label:I→Option (Fin K)) (F:∀i,U i→SimpleGraph (Fin n))
    (hF:∀i w,(F i w).IsRegularOfDegree 2) (a:I) (j:Fin K) (hj:label a=some j)
    (p ρ:ℝ) (hprob:2*p=ρ*sOrd)
    (hp0:∀_:Sym2 (Fin n),0≤2*p) (hp1:∀_:Sym2 (Fin n),2*p≤1)
    (π:Equiv.Perm (Fin n)) (χ:ℝ) (hχ:0≤χ)
    (θhost α ρ₀ s₀ βP ηP row ηH βH c B:ℝ) (hρ₀:0<ρ₀) (hs₀:0<s₀)
    (kH:ℕ) (R Conflict:SimpleGraph (Fin n)) (weight:OrdinaryCycle R (r+1)→ℝ):
    letI : DecidableEq (U a) := Classical.decEq (U a)
    let qm:=mixedAssignedIntervalProbability K m θ label F hF a
    let sm:=mixedAssignedSpokeProbability K m sOrd θ label F hF a;
    ∀ (hqm:∀w g,0≤qm w g) (hQm:∀w,∑g,qm w g≤1/8)
      (hsm:∀w g,0≤sm w g) (hSm:∀w,∑g,sm w g≤ intervalUncoveredProbability d (∑g,qm w g)),
    ordinaryAssignedNamedClassEvent r d K hr hd j θhost α ρ₀ s₀ βP ηP row ηH βH c B hρ₀ hs₀ kH
      R Conflict π (F a) (hF a) sOrd θ ((m:ℝ)+1) ρ weight→
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _=>2*p) hp0 hp1 d hd qm hqm hQm sm hsm hSm)
    let so:=ordinaryAssignedSpokeProbability (F a) (hF a) K j sOrd θ ((m:ℝ)+1)
    let E:=ordinaryCombinedHostEvent (V:=Fin n) (U:=U a) (Γ:=Bool) (Color:=Bool)
      r d kH hr R Conflict π θhost α (ρ₀*s₀/2) βP ηP row ηH βH c B (ρ*sOrd) sOrd weight so false
    letI : ∀ ω:RawWheelOutcome (Fin n) (U a) Bool Bool,Fintype (mixedClassRetentionSpace false π d false ω):=
      fun ω=>mixedClassRetentionFintype false π d false ω
    letI : Fintype (Σ ω:RawWheelOutcome (Fin n) (U a) Bool Bool,mixedClassRetentionSpace false π d false ω):=
      @Sigma.instFintype _ _ (fun ω=>mixedClassRetentionFintype false π d false ω) inferInstance;
    1-(100*χ+200/(n:ℝ))≤(μ.sigma (mixedClassActualRetention false π d false)).probability (fun z=>E z.1) :=by
  intro qm sm hqm hQm hsm hSm hE μ so E
  unfold ordinaryAssignedNamedClassEvent at hE
  obtain ⟨hRlo,hRhi,hqo,hQo,hso,hSo,hbound⟩:=hE
  have hr0:∀_:Sym2 (Fin n),0≤ρ*sOrd:=fun _=>(lt_of_lt_of_le (div_pos (mul_pos hρ₀ hs₀) (by norm_num)) hRlo).le
  have hr1:∀_:Sym2 (Fin n),ρ*sOrd≤1:=fun _=>hRhi
  exact mixed_ordinary_assigned_retained_transfer K m d hd θ sOrd label F hF a j hj p ρ hprob hp0 hp1 hr0 hr1
    π false χ hχ hqm hQm hsm hSm hqo hQo hso hSo E hbound
end Oberwolfach

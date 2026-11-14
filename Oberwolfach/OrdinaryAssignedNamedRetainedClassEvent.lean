module

public import Oberwolfach.OrdinaryAssignedNamedClassEvent
public import Oberwolfach.OrdinaryRetainedClassBudget

@[expose] public section
/-! Name the original one-class probability assertion, keeping the same
product law, fixed weight and factor-dependent interval probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) namedRetainedFiniteEquality (n:ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

def ordinaryAssignedNamedRetainedClassEvent {n:ℕ} [Nonempty (Fin n)] {U:Type} [Fintype U] [DecidableEq U]
    (m d K:ℕ) (hm:3≤m) (hd:2≤d) (i₀:Fin K)
    (θhost α ρ₀ s₀ βP ηP row ηH βH c B:ℝ) (hρ₀:0<ρ₀) (hs₀:0<s₀)
    (kH:ℕ) (R Conflict:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (sOrd θfreq caux ρ χ:ℝ) (a:Bool) (weight:OrdinaryCycle R (m+1)→ℝ):Prop :=
  let q:=ordinaryAssignedMarkedProbability F hF K θfreq caux
  let sco:=ordinaryAssignedSpokeProbability F hF K i₀ sOrd θfreq caux
  let pR:=ρ*sOrd
  let pstar:ℝ:=ρ₀*s₀/2;
  ∃ (hRlo:ρ₀*s₀/2≤pR) (hRhi:pR≤1)
    (hq:∀w j,0≤q w j) (hQ:∀w,∑j,q w j≤1/8)
    (hs:∀w j,0≤sco w j) (hS':∀w,∑j,sco w j≤ intervalUncoveredProbability d (∑j,q w j)),
  let μ:=FiniteLaw.pi (rawWheelLaw (V:=Fin n) (fun _=>pR)
    (fun _=>(lt_of_lt_of_le (div_pos (mul_pos hρ₀ hs₀) (by norm_num)) hRlo).le)
    (fun _=>hRhi) d hd q hq hQ sco hs hS');
  letI : ∀ ω:RawWheelOutcome (Fin n) U Bool Bool,Fintype (mixedClassRetentionSpace false π d a ω):=
    fun ω=>mixedClassRetentionFintype false π d a ω
  letI : Fintype (Σ ω:RawWheelOutcome (Fin n) U Bool Bool,mixedClassRetentionSpace false π d a ω):=
    @Sigma.instFintype _ _ (fun ω=>mixedClassRetentionFintype false π d a ω) inferInstance;
  1-(100*χ+200/(n:ℝ))≤
    (μ.sigma (mixedClassActualRetention false π d a)).probability (fun z=>
      ordinaryCombinedHostEvent (V:=Fin n) (U:=U) (Γ:=Bool) (Color:=Bool)
        m d kH hm R Conflict π θhost α pstar βP ηP row ηH βH c B pR sOrd weight sco false z.1)
end Oberwolfach

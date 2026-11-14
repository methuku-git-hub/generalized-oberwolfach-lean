module

public import Oberwolfach.OrdinaryAssignedNamedRetainedClassEvent

@[expose] public section
/-! The unchanged ordinary event survives the singleton retention extension,
with the error estimate required for the mixed-class union bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) retainedBudgetFiniteEquality (n:ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

theorem ordinary_assigned_named_retained_budget {n:ℕ} [Nonempty (Fin n)] {U:Type} [Fintype U] [DecidableEq U]
    (m d K:ℕ) (hm:3≤m) (hd:2≤d) (i₀:Fin K)
    (θhost α ρ₀ s₀ βP ηP row ηH βH c B:ℝ) (hρ₀:0<ρ₀) (hs₀:0<s₀)
    (kH:ℕ) (R Conflict:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (sOrd θfreq caux ρ χ:ℝ) (a:Bool) (weight:OrdinaryCycle R (m+1)→ℝ)
    (hχ:0≤χ)
    (hE:ordinaryAssignedNamedClassEvent m d K hm hd i₀ θhost α ρ₀ s₀ βP ηP row ηH βH c B
       hρ₀ hs₀ kH R Conflict π F hF sOrd θfreq caux ρ weight):
    ordinaryAssignedNamedRetainedClassEvent m d K hm hd i₀ θhost α ρ₀ s₀ βP ηP row ηH βH c B
       hρ₀ hs₀ kH R Conflict π F hF sOrd θfreq caux ρ χ a weight := by
  unfold ordinaryAssignedNamedClassEvent at hE
  unfold ordinaryAssignedNamedRetainedClassEvent
  obtain ⟨hRlo,hRhi,hq,hQ,hs,hS,hprob⟩:=hE
  refine ⟨hRlo,hRhi,hq,hQ,hs,hS,?_⟩
  let μ:=FiniteLaw.pi (rawWheelLaw (V:=Fin n) (fun _=>ρ*sOrd)
    (fun _=>(lt_of_lt_of_le (div_pos (mul_pos hρ₀ hs₀) (by norm_num)) hRlo).le)
    (fun _=>hRhi) d hd (ordinaryAssignedMarkedProbability F hF K θfreq caux) hq hQ
    (ordinaryAssignedSpokeProbability F hF K i₀ sOrd θfreq caux) hs hS)
  let E:=ordinaryCombinedHostEvent (V:=Fin n) (U:=U) (Γ:=Bool) (Color:=Bool)
    m d kH hm R Conflict π θhost α (ρ₀*s₀/2) βP ηP row ηH βH c B (ρ*sOrd) sOrd weight
    (ordinaryAssignedSpokeProbability F hF K i₀ sOrd θfreq caux) false
  have hp:1-(1/(Fintype.card (Fin n):ℝ)+3/(Fintype.card (Fin n):ℝ)^2)≤μ.probability E:=by
    simpa only [Fintype.card_fin] using hprob
  have h:=ordinary_same_sample_retained_class_budget π d a χ hχ μ E hp
  simpa only [Fintype.card_fin] using h
end Oberwolfach

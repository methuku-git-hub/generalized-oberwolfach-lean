module

public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData
public import Oberwolfach.CandidateOrdinaryAssignedNamedSamplingWitness

@[expose] public section
/-! Keep the exact total physical-edge retention probability of the original
assigned recipe along with all categorical sampling witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_assigned_vortex_exact_sampling_data_candidate {n D:ℕ} (hn:0<n) (hD:0<D)
    {U:Type} [Fintype U] [DecidableEq U] (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ) (hd:2≤d)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hsmin:0<smin) (hslo:smin≤rsv) (hs1:rsv≤1/100)
    (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c) (hda:1/θ≤d)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,i₀∈factorShortCandidates (F w) K):
    Nonempty (OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d) :=by
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hDreal:0<(D:ℝ):=by exact_mod_cast hD
  have hsize:initialIndexDensity U D*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    simp [initialIndexDensity,ne_of_gt hDreal]
  have hrsv:0<rsv:=hsmin.trans_le hslo
  obtain ⟨u,hu,hp₂,hp₂lo,hsum,hud,hq,hQ,hs,hS,hfalse⟩:=
    ordinary_assigned_named_sampling_witness_candidate hn F hF Allowed hAllowed K hK i₀ rsv θ c
      (initialIndexDensity U D) D d hd hrsv.le hs1 hθ hθ1 hc hda hρ hρhi hDreal hsize hsclass hclass
  have hρ₀one:ρ₀≤1:=hρlo.trans hρhi
  have hprod:ρ₀*smin≤ initialIndexDensity U D*rsv:=mul_le_mul hρlo hslo hsmin.le hρ.le
  have hsb:ρ₀*smin≤rsv:=by nlinarith
  have heq:2*(initialIndexDensity U D*rsv/2)+2*0+
    2*ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D+2*0+u=initialIndexDensity U D:=by linarith
  have hsum1:2*(initialIndexDensity U D*rsv/2)+2*0+
    2*ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D+2*0+u≤1:=heq.le.trans hρhi
  refine ⟨⟨⟨u,by positivity,hp₂,hu,hsum1,?_,hsb,by linarith,hq,hQ,hs,hS,?_⟩,heq⟩⟩
  · linarith
  · intro w
    exact (hfalse w).2
end Oberwolfach

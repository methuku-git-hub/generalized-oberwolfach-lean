module

public import Oberwolfach.OrdinaryAssignedSamplingNamedWitness
public import Oberwolfach.Vortex

@[expose] public section
/-! The original assigned sample recipe has exactly the fixed spoke
marginal and parent density required by the vortex construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_vortex_sampling_witness {n D:ℕ} (hn:0<n) (hD:0<D)
    {U:Type} [Fintype U] [DecidableEq U] (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ) (hd:2≤d)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hsmin:0<smin) (hslo:smin≤rsv) (hs1:rsv≤1/100)
    (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c) (hda:1/θ≤d)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,factorPreparationClass (F w) K=some i₀) :
    ∃u:ℝ, let ρ:=initialIndexDensity U D;
      let p:=ρ*rsv/2;
      let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D;
      let q:=ordinaryAssignedMarkedProbability F hF K θ c;
      let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c;
      0≤p ∧ 0≤p₂ ∧ 0≤u ∧ 2*p+2*0+2*p₂+2*0+u≤1 ∧
      ρ₀*smin≤2*p ∧ ρ₀*smin≤rsv ∧ rsv≤1 ∧ 2*p=ρ*rsv ∧
      (∀w j,0≤q w j) ∧ (∀w,∑j,q w j≤1/8) ∧
      (∀w j,0≤s w j) ∧ (∀w,∑j,s w j≤ intervalUncoveredProbability d (∑j,q w j)) ∧
      (∀w,s w false=rsv) :=by
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hDreal:0<(D:ℝ):=by exact_mod_cast hD
  have hsize:initialIndexDensity U D*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    simp [initialIndexDensity,ne_of_gt hDreal]
  obtain ⟨u,hu,hp₂,hp₂lo,hsum,hud,hq,hQ,hs,hS,hfalse⟩:=
    ordinary_assigned_named_sampling_witness hn F hF Allowed hAllowed K hK i₀ rsv θ c
      (initialIndexDensity U D) D d hd (le_of_lt (hsmin.trans_le hslo)) hs1 hθ hθ1 hc hda hρ hρhi hDreal hsize hsclass hclass
  have hrsv:0<rsv:=hsmin.trans_le hslo
  have hρ₀one:ρ₀≤1:=hρlo.trans hρhi
  have hprod:ρ₀*smin≤ initialIndexDensity U D*rsv:=
    mul_le_mul hρlo hslo hsmin.le hρ.le
  have hrsvbound:ρ₀*smin≤rsv:=by nlinarith
  refine ⟨u,?_,hp₂,hu,?_,?_,hrsvbound,?_,?_,hq,hQ,hs,hS,?_⟩
  · positivity
  · linarith
  · linarith
  · linarith
  · ring
  · intro w
    exact (hfalse w).2
end Oberwolfach

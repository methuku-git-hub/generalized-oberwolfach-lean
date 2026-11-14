module

public import Oberwolfach.OrdinaryFirstVortexParentDensityBalance
public import Oberwolfach.OrdinaryAbundanceThresholdFromOriginal

@[expose] public section
/-! The original regular-host and abundance hypotheses give the first
    vortex rim density, reserved-cycle threshold and parent balance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_first_vortex_rim_from_original
    (θ α ρstar βfreq β ε ρ pH:ℝ) (hθ:(1/2:ℝ)≤θ) (hα:0<α)
    (hρstar:0<ρstar) (hβfreq:0<βfreq) (hβsmall:β≤α) (hpH:0≤pH)
    (n D q rstar m:ℕ) (hn:0<n) (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D)
    (hdegree:(θ+α)*(n:ℝ)≤D) (hρlo:ρstar≤2*(q:ℝ)/(D:ℝ))
    (F:Fin q→SimpleGraph (Fin n))
    (hthreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ)
    (habundance:∀w,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ))
    (Q:Vortex (Fin q) P D β ε m) (hρ:ρ=initialIndexDensity (Fin q) D):
    0<α/2 ∧ α/2≤1/2 ∧ cycleThreshold rstar≤θ+α/2 ∧
    (1/2:ℝ)+α/2≤θ+α/2 ∧
    (∀v,(θ+α/2)*(Q.vertices 1).card≤(((Q.vertices 1)∩P.neighborFinset v).card:ℝ)) ∧
    (∀v,|(ρ*pH)*((Q.vertices 1)∩P.neighborFinset v).card-
      2*pH*(Q.indices 1).card|≤(ρ*pH)*β*(Q.vertices 1).card) := by
  have hρpos:0<ρ:=by
    rw [hρ]
    exact hρstar.trans_le (by simpa [initialIndexDensity] using hρlo)
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn
  let v:Fin n:=⟨0,hn⟩
  have hDle:(D:ℝ)≤n:=by
    have hh:=P.degree_lt_card_verts v
    rw [hreg v] at hh
    have hh':D≤n:=by simpa using hh.le
    exact_mod_cast hh'
  have hcoef:θ+α≤1:=by
    have hh:θ+α≤(n:ℝ)/n:=(le_div_iff₀ hnR).2 (hdegree.trans hDle)
    simpa [hnR.ne'] using hh
  have hα1:α≤1:=by linarith
  have hres:=ordinary_first_vortex_parent_density_balance P D m β ε θ α ρ pH Q
    (by simpa using hn) hρ hρpos hpH (by simpa using hdegree)
  have hthreshold':=ordinary_abundance_threshold_from_original θ ρstar βfreq hρstar hβfreq n D q rstar hn hρlo F hthreshold habundance
  refine ⟨by positivity,by linarith,by linarith,by linarith,?_,?_⟩
  · intro v
    have hI:(0:ℝ)≤(Q.vertices 1).card:=by positivity
    have hh:=mul_le_mul_of_nonneg_right (show θ+α/2≤θ+α-β/2 by linarith) hI
    convert hh.trans (hres.1 v) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v
    convert hres.2 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach

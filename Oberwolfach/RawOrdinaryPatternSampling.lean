module

public import Oberwolfach.OrdinaryRawIntervalSampling
public import Oberwolfach.SupportedPatternSums
public import Oberwolfach.FinitePatternIncidence

@[expose] public section

/-! Fixed ordinary rim/spoke patterns under the original product law.
Physical rims and locally dependent interval spokes keep their supplied law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
variable (P : SimpleGraph V) (π : Equiv.Perm V)
    (ρ : Sym2 V→ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
    (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μord" => rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS

def rawOrdinaryPatternSum {I:Type} [Fintype I]
    (R:I→Finset (Sym2 V⊕(V×U))) (w:I→ℝ) (j:Color)
    (σ:RawWheelOutcome V U Γ Color) : ℝ:=
  supportedPatternSum R w (fun _ _=>true)
    (fun σ=>ordinaryResourceState (rawWheelGraph P σ) (rawWheelSpokes π d σ j)) σ

theorem rawOrdinaryPatternSum_expectation
    (hnoshort:∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    {I:Type} [Fintype I] (R:I→Finset (Sym2 V⊕(V×U))) (w:I→ℝ)
    (hdisj:∀ i,∀ a∈R i,∀ b∈R i,a≠b →
      Disjoint (rawWheelResourceCoordinates π d a) (rawWheelResourceCoordinates π d b)) (j:Color) :
    (FiniteLaw.pi μord).expectation (rawOrdinaryPatternSum P π d R w j)=
      ∑ i,w i*∏ a∈R i,rawWheelMarginal P ρ s j a := by
  unfold rawOrdinaryPatternSum
  have hh:=supportedPatternSum_expectation μord R w (fun _ _=>true)
    (rawWheelResourceCoordinates π d)
    (fun σ=>ordinaryResourceState (rawWheelGraph P σ) (rawWheelSpokes π d σ j))
    (rawWheelResourceState_supported P π d j) hdisj
  simpa only [rawWheelResource_probability P π ρ hρ hρ1 d hd q hq hQ s hs hS hnoshort j] using hh

theorem rawOrdinaryPatternSum_tail
    (hnoshort:∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    {I:Type} [Fintype I] (R:I→Finset (Sym2 V⊕(V×U))) (w:I→ℝ) (hw:∀ i,0≤w i)
    (hdisj:∀ i,∀ a∈R i,∀ b∈R i,a≠b →
      Disjoint (rawWheelResourceCoordinates π d a) (rawWheelResourceCoordinates π d b))
    (j:Color) (a r L:ℝ) (ha:0<a) (hr:0<r) (hL:0<L)
    (hsize:∀ i,((R i).card:ℝ)≤r) (htotal:(∑ i,w i)≤L)
    (hload:∀ e,(∑ i,if e∈R i then w i else 0)≤a) (t:ℝ) (ht:0<t) :
    (FiniteLaw.pi μord).probability (fun σ=>t≤
      |rawOrdinaryPatternSum P π d R w j σ-
        ∑ i,w i*∏ e∈R i,rawWheelMarginal P ρ s j e|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(a*r*L))) := by
  rw [←rawOrdinaryPatternSum_expectation P π ρ hρ hρ1 d hd q hq hQ s hs hS hnoshort R w hdisj j]
  apply supportedPatternSum_tail μord R w hw (fun _ _=>true)
    (rawWheelResourceCoordinates π d)
    (fun σ=>ordinaryResourceState (rawWheelGraph P σ) (rawWheelSpokes π d σ j))
    (rawWheelResourceState_supported P π d j)
    (4*(d:ℝ)+3) (a*r*L) (by positivity) (by positivity)
    (by intro e;exact_mod_cast rawWheelResourceCoordinates_card π d e)
    (by intro e;exact_mod_cast rawWheelResourceCoordinates_reverse_card π d e)
  · exact finite_pattern_incidence_square_sum R w hw a r L ha.le hr.le hsize htotal hload
  · exact ht

end Oberwolfach

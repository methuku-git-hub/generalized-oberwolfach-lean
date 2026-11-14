module

public import Oberwolfach.MarkedExpandedRetainedProjection
public import Oberwolfach.MarkedRetainedRobustChangeEvent
public import Oberwolfach.FiniteLawUniformEventReorder

@[expose] public section
/-! Join a protected-class event in the expanded experiment to the robust
change event from the collapsed retained experiment, on one outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem expanded_stable_external_event_join
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (hd:2≤d)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j)
    (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (ε ζ cap:ℝ) (size a₀ b₀ e₀ f₀:ℕ):
    let Ret:=fun raw:RawMarkedOutcome V U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome V U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (ω e)
    let Base:=rawMarkedRetentionLaw π d hd false p k hp hk (by linarith) q hq hQ s hs hS;
    ∀(Good:(Σω,Ret (f ω))→Prop) (δgood δstable:ℝ),
      1-δgood≤(μ.sigma (fun ω=>ν (f ω))).probability Good→
      1-δstable≤Base.probability (MarkedRetainedRobustChangeEvent P π d r false false ε ζ cap size a₀ b₀ e₀ f₀)→
      1-(δgood+δstable)≤(μ.sigma (fun ω=>ν (f ω))).probability
        (fun z=>Good z ∧ MarkedRetainedRobustChangeEvent P π d r false false ε ζ cap size a₀ b₀ e₀ f₀ ⟨f z.1,z.2⟩):=by
  intro Ret ν μ f Base Good δgood δstable hgood hstable
  let E:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false→Prop:=MarkedRetainedRobustChangeEvent P π d r false false ε ζ cap size a₀ b₀ e₀ f₀
  have hproj:=raw_expanded_marked_retained_projection_probability p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS Ret ν E
  have hstable':1-δstable≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E ⟨f z.1,z.2⟩):=by
    rw [hproj]
    simpa only [Base,rawMarkedRetentionLaw] using hstable
  have hh:=finiteLaw_intersection_lower (μ.sigma (fun ω=>ν (f ω))) Good (fun z=>E ⟨f z.1,z.2⟩) δgood δstable hgood hstable'
  linarith
end Oberwolfach

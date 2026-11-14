module

public import Oberwolfach.ExpandedStableJointExplicitDensities
public import Oberwolfach.ExpandedStableExternalEventJoin
public import Oberwolfach.MarkedSampledRobustAbsorberSharedChanges

@[expose] public section
/-! Choose the stable-absorber parameters before the later expanded event,
and join the two events using the exact retained projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_stable_alone_sample_explicit_densities
    (k₀ r Q:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α ρstar sstar ω:ℝ) (hα:0<α) (hρstar:0<ρstar) (hsstar:0<sstar) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+α/2≤1/2+α):
    ∃ ε ζ δ cap:ℝ,0<ε∧0<ζ∧0<δ∧0<cap∧∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f d:ℕ,∀ hd:2≤d,∃ N:ℕ,1≤N∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V→ω*Fintype.card V≤(Fintype.card U:ℝ)→Fintype.card U≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),(∀ x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀ D:ℝ,(Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
      (∀ v,|(P.degree v:ℝ)-D|≤δ*Fintype.card V)→
      (∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ))→
    ∀ (ρ s₀:ℝ) (hρlo:ρstar≤ρ) (hρhi:ρ≤1) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    ∀ (p k:ℝ),p=ρ*s₀/2→k=p/((r+4:ℕ):ℝ)→
    ∀ (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Bool→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)),
    (∀w,q w false=s₀/((r+4:ℕ):ℝ))→(∀w,s w false=s₀)→
    ∀ (p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),
    let Ret:=fun raw:RawMarkedOutcome V U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome V U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let collapse:=fun (z:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (z e);
    1-2/(Fintype.card V:ℝ)^Q≤(μ.sigma (fun z=>ν (collapse z))).probability
      (fun z=>MarkedRetainedRobustChangeEvent P π d r false false ε ζ cap size a₀ b₀ e₀ f ⟨collapse z.1,z.2⟩) :=by
  obtain ⟨ε,ζ,δ,cap,hε,hζ,hδ,hcap,hstable⟩:=
    expanded_stable_joint_sample_explicit_densities k₀ r Q hr hlen α ρstar sstar ω hα hρstar hsstar hω hmargin
  refine ⟨ε,ζ,δ,cap,hε,hζ,hδ,hcap,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hstable⟩:=hstable size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f d hd
  obtain ⟨N,hN,hstable⟩:=hstable f d hd
  refine ⟨N,hN,?_⟩
  intro V U _ _ _ _ _ hn hulo huhi P π hnoshort D hDlo hDhi hnear hmindeg ρ s₀ hρlo hρhi hslo hshi p k hpEq hkEq q hq hQ s hs hS hq0 hs0 p₂ k₂ u hp hk hp₂ hk₂ hu hsum Ret ν μ collapse
  have htrue:1-(0:ℝ)≤(μ.sigma (fun z=>ν (collapse z))).probability (fun _=>True):=by simp [finiteLaw_probability_true]
  have h:=hstable V U hn hulo huhi P π hnoshort D hDlo hDhi hnear hmindeg ρ s₀ hρlo hρhi hslo hshi p k hpEq hkEq q hq hQ s hs hS hq0 hs0 p₂ k₂ u hp hk hp₂ hk₂ hu hsum (fun _=>True) 0 htrue
  simpa only [zero_add,true_and] using h
end Oberwolfach

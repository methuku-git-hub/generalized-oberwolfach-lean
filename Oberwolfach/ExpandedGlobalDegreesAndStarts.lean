module

public import Oberwolfach.ExpandedGlobalBoundaryRetentionDegrees
public import Oberwolfach.MarkedExpandedStartsArbitraryFailure
public import Oberwolfach.ExpandedGlobalBoundaryRetentionProbability
public import Oberwolfach.MarkedExpandedDegreeArbitraryFailure
public import Oberwolfach.FiniteLawIntersectionLower
public import Oberwolfach.ExpandedGlobalRetentionProbability
public import Oberwolfach.ExpandedBoundaryHubsLocalSmallFailure
public import Oberwolfach.MarkedExpandedRetainedProjection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- Global row and hub retention can be requested on the same expanded
sample, with arbitrarily small failure probability. -/
theorem expanded_global_boundary_retention_degrees_starts
    (d:ℕ) (hd:2≤d) (pRet ζ c failure:ℝ)
    (hp:0<pRet) (hζ:0<ζ) (hc:0<c) (hfailure:0<failure):
    ∃m₀ N:ℕ,1≤m₀ ∧ 1≤N ∧ ∀(V U:Type) [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U],
    N≤Fintype.card V → m₀≤Fintype.card V → Fintype.card U≤Fintype.card V →
    c*(Fintype.card V:ℝ)≤Fintype.card U →
    ∀(G:SimpleGraph V) (π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp₁:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (t₀:ℝ) (hq0:∀w,q w false=t₀) (hmass:pRet*Fintype.card V≤t₀*Fintype.card U),
    let Ret:=fun raw:RawMarkedOutcome V U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome V U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp₁ hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (ω e)
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z:Σω,Ret (f ω)=>
      ((RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2 ∧
      ∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) Finset.univ v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/d+4*(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
      (∀a x,
        |((∑y,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) a x y:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u a/2*G.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ) ∧
        |((∑y,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) a y x:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u a/2*G.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ) ∧
        |(sampledColourDegree G (fun e=>(z.1 (Sum.inl e)).1) a x:ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u a*G.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ))) ∧
      (∀g a,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g a).card:ℝ)-(∑w,q w g/(d:ℝ))|<(Fintype.card V:ℝ)^(3/5:ℝ))) :=by
  obtain ⟨m₀,N,hm₀,hN,hBase⟩:=expanded_global_boundary_retention_degrees_high_probability d hd pRet ζ c (failure/2) hp hζ hc (by positivity)
  obtain ⟨NStart,hStart⟩:=raw_expanded_starts_arbitrary_failure (failure/2) (by positivity)
  refine ⟨m₀,max N NStart,hm₀,by omega,?_⟩
  intro V U _ _ _ _ _ hn hm hu hsize G π p k p₂ k₂ u hp₁ hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort t₀ hq0 hmass Ret ν μ f
  have hfirst:=hBase V U (by omega) hm hu hsize G π p k p₂ k₂ u hp₁ hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort t₀ hq0 hmass
  have hU:0<Fintype.card U:=by
    have hV:0<(Fintype.card V:ℝ):=by exact_mod_cast (Fintype.card_pos : 0<Fintype.card V)
    have :0<(Fintype.card U:ℝ):=lt_of_lt_of_le (mul_pos hc hV) hsize
    exact_mod_cast this
  have hsecond:=hStart V (by omega) U Bool Bool hU hu (by simp) π d hd p k p₂ k₂ u hp₁ hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort Ret ν
  have hh:=finiteLaw_intersection_lower (μ.sigma (fun ω=>ν (f ω))) _ _ (failure/2) (failure/2) hfirst hsecond
  linarith only [hh]
end Oberwolfach

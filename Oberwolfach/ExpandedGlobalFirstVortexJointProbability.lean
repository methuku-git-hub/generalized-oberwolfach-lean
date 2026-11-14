module

public import Oberwolfach.FirstVortexExpandedSixTestsProbability
public import Oberwolfach.ExpandedGlobalDegreesAndStarts

@[expose] public section
/-! Global and first-vortex retention tests hold on one expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_global_and_first_vortex_tests_high_probability
    (d:ℕ) (hd:2≤d) (ε ρ₀ pRet ζ c failure:ℝ)
    (hε:0<ε) (hεq:ε≤1/4) (hρ₀:0<ρ₀) (hpRet:0<pRet) (hζ:0<ζ) (hc:0<c) (hfailure:0<failure):
    ∃m₀ N:ℕ,1≤m₀ ∧ 1≤N ∧ ∀(V U:Type) [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    c*(Fintype.card V:ℝ)≤Fintype.card U →
    ∀(G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D → 0<Fintype.card V → (Fintype.card V:ℝ)/2≤D → 0<D →
    ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D≤1 →
    0≤β → β≤1/4 → 0<m → m₀≤m →
    ∀(π:Equiv.Perm V), (∀x,π x∈Q.extendedVertices 1↔x∈Q.extendedVertices 1) →
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (t₀:ℝ) (hq0:∀u,q u false=t₀) (hmass:pRet*Fintype.card V≤t₀*Fintype.card U)
    (hspoke:∀u,(1/100:ℝ)≤s u false),
    let Ret:=fun raw:RawMarkedOutcome V U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome V U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (ω e)
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z:Σω,Ret (f ω)=>
      (((RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2 ∧
      ∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) Finset.univ v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/d+4*(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
      (∀a x,
        |((∑y,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) a x y:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u a/2*G.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ) ∧
        |((∑y,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) a y x:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u a/2*G.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ) ∧
        |(sampledColourDegree G (fun e=>(z.1 (Sum.inl e)).1) a x:ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u a*G.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ))) ∧
      (∀g a,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g a).card:ℝ)-(∑w,q w g/(d:ℝ))|<(Fintype.card V:ℝ)^(3/5:ℝ))) ∧
      ((∀v,|(((G.neighborFinset v∩Q.extendedVertices 1).filter (fun x=>(z.1 (Sum.inl s(v,x))).1=4)).card:ℝ)-
        u*(G.neighborFinset v∩Q.extendedVertices 1).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
      (∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (Q.extendedVertices 1)-
        ((Q.extendedVertices 1).card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
      (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v (Q.extendedIndices 1)-
        ∑w∈Q.extendedIndices 1,(1-(∑g,q w g)-(∑j,s w j))|<((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
      (∀v∈Q.extendedVertices 1,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Q.extendedIndices 1) v).card:ℝ)≤
        4*((Q.extendedIndices 1).card:ℝ)/d+4*((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
      RetainedRestrictionLocalGood π d (fun e=>z.1 (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
        (Q.extendedVertices 1) (Q.extendedIndices 1) ζ z.2 ∧
      (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(Fintype.card V:ℝ)^(3/4:ℝ)≤
        (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
          rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ)))) := by
  obtain ⟨mLocal,NLocal,hmLocal,hNLocal,hLocal⟩:=
    raw_expanded_first_vortex_six_tests_high_probability d hd ε ρ₀ pRet ζ (failure/2) hε hεq hρ₀ hpRet hζ (by positivity)
  obtain ⟨mGlobal,NGlobal,hmGlobal,hNGlobal,hGlobal⟩:=
    expanded_global_boundary_retention_degrees_starts d hd pRet ζ c (failure/2) hpRet hζ hc (by positivity)
  refine ⟨mLocal,max (max NLocal NGlobal) mGlobal,hmLocal,by omega,?_⟩
  intro V U _ _ _ _ _ hn hu hcU G D m β Q hreg hV hD hDpos hρ hρhi hβ hβ1 hm hsize π hpres
    p k p₂ k₂ u hp hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort t₀ hq0 hmass hspoke Ret ν μ f
  have hFirst:=hLocal V U (by omega) hu G D m β Q hreg hV hD hDpos hρ hρhi hβ hβ1 hm hsize π hpres
    p k p₂ k₂ u hp hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort t₀ hq0 hmass hspoke
  have hSecond:=hGlobal V U (by omega) (by omega) hu hcU G π
    p k p₂ k₂ u hp hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort t₀ hq0 hmass
  have hh:=finiteLaw_intersection_lower (μ.sigma (fun ω=>ν (f ω))) _ _ (failure/2) (failure/2) hSecond hFirst
  linarith only [hh]
end Oberwolfach

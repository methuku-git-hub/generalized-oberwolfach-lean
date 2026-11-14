module

public import Oberwolfach.RawExpandedReservedPairsProbability
public import Oberwolfach.FirstVortexExpandedFiveTestsProbability
public import Oberwolfach.FirstVortexExpandedUnassignedRimProbability
public import Oberwolfach.FirstVortexExpandedLocalTestsProbability
public import Oberwolfach.FirstVortexExpandedUnassignedBoundaryProbability
public import Oberwolfach.FirstVortexExpandedRetentionProbability
public import Oberwolfach.FirstVortexIndicesNonempty
public import Oberwolfach.RawMarkedRetentionLocalEvent
public import Oberwolfach.MarkedExpandedRetainedProjection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_first_vortex_six_tests_high_probability
    (d:ℕ) (hd:2≤d) (ε ρ₀ pRet ζ failure:ℝ)
    (hε:0<ε) (hεq:ε≤1/4) (hρ₀:0<ρ₀) (hpRet:0<pRet) (hζ:0<ζ) (hfailure:0<failure):
    ∃m₀ N:ℕ,1≤m₀ ∧ 1≤N ∧ ∀(V U:Type) [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
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
      (∀v,|(((G.neighborFinset v∩Q.extendedVertices 1).filter (fun x=>(z.1 (Sum.inl s(v,x))).1=4)).card:ℝ)-
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
          rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ))) :=by
  obtain ⟨m₀,N,hM,hN,hFive⟩:=raw_expanded_first_vortex_five_tests_high_probability d hd ε ρ₀ pRet ζ (failure/2) hε hεq hρ₀ hpRet hζ (by positivity)
  obtain ⟨Npair,hPair⟩:=raw_expanded_reserved_pairs_high_probability d hd (1/100) (failure/2) (by norm_num) (by positivity)
  refine ⟨m₀,max N Npair,hM,by omega,?_⟩
  intro V U _ _ _ _ _ hn hu G D m β Q hreg hV hD hDpos hρ hρhi hβ hβ1 hm hsize π hpres p k p₂ k₂ u hp hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort t₀ hq0 hmass hspoke Ret ν μ f
  have hU:0<Fintype.card U:=by
    by_contra hh
    have hz:Fintype.card U=0:=by omega
    simp only [initialIndexDensity,hz,Nat.cast_zero,mul_zero,zero_div] at hρ
    linarith
  have hFirst:=hFive V U (by omega) hu G D m β Q hreg hV hD hDpos hρ hρhi hβ hβ1 hm hsize π hpres
    p k p₂ k₂ u hp hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort t₀ hq0 hmass
  have hSecond:=hPair V (by omega) U Bool Bool hU hu π p k p₂ k₂ u hp hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort false hspoke Ret ν
  have hh:=finiteLaw_intersection_lower (μ.sigma (fun ω=>ν (f ω))) _ _ (failure/2) (failure/2) hFirst hSecond
  simp only [and_assoc] at hh
  linarith only [hh]
end Oberwolfach

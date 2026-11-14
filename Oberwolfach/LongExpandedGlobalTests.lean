module

public import Oberwolfach.ExpandedGlobalDegreesAndStarts
public import Oberwolfach.MarkedExpandedActualSample

@[expose] public section
/-! Name the global retention, degree and starting-hub tests without an
unneeded existential regular-class completion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 10000) globalTestsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

def LongExpandedGlobalTests {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (ζ p k p₂ k₂ u:ℝ) (q:U→Bool→ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d):Prop :=
    ((RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2 ∧
      (∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) Finset.univ v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))) ∧
    (∀j x,
      |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j x y:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree x|<(n:ℝ)^(3/5:ℝ) ∧
      |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j y x:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree x|<(n:ℝ)^(3/5:ℝ) ∧
      |(sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) j x:ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j*P.degree x|<(n:ℝ)^(3/5:ℝ))) ∧
    (∀g x,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g x).card:ℝ)-(∑w,q w g/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))

theorem long_expanded_global_tests_high_probability
    (d:ℕ) (hd:2≤d) (pRet ζ c failure:ℝ)
    (hpRet:0<pRet) (hζ:0<ζ) (hc:0<c) (hfailure:0<failure):
    ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U],
    Fintype.card U≤n→c*n≤(Fintype.card U:ℝ)→
    ∀(P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (p k p₂ k₂ u:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u) (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (t₀:ℝ) (hq0:∀w,q w false=t₀) (hmass:pRet*n≤t₀*Fintype.card U),
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (ω e);
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z:Σω,Ret (f ω)=>LongExpandedGlobalTests P π d ζ p k p₂ k₂ u q z) :=by
  obtain ⟨m,N,hm,hN,hGlobal⟩:=expanded_global_boundary_retention_degrees_starts d hd pRet ζ c failure hpRet hζ hc hfailure
  refine ⟨max m N,by omega,?_⟩
  intro n hn _ U _ _ hU hUlo P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort t₀ hq0 hmass Ret ν μ f
  have h:=hGlobal (Fin n) U (by simp;omega) (by simp;omega) (by simpa using hU) (by simpa using hUlo)
    P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort t₀ hq0 (by simpa using hmass)
  simpa only [LongExpandedGlobalTests,Fintype.card_fin] using h
end Oberwolfach

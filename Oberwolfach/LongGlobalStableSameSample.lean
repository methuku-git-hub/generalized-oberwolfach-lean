module

public import Oberwolfach.LongExpandedGlobalTests
public import Oberwolfach.ExpandedStableAloneExplicitDensities

@[expose] public section
/-! Combine global retention and stable-absorber tests in a small context,
with all classes and the absorber using the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 10000) longGlobalStableFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_global_stable_same_sample
    (k₀ r Q:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α ρstar sstar ω:ℝ) (hα:0<α) (hρstar:0<ρstar) (hsstar:0<sstar) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+α/2≤1/2+α):
    ∃ ε ζ δ cap:ℝ,0<ε∧0<ζ∧0<δ∧0<cap∧∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f d:ℕ,∀ hd:2≤d,
    ∀(pRet ζret c χ:ℝ),0<pRet→0<ζret→0<c→0<χ→∃N:ℕ,1≤N ∧
    ∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U],
      ω*n≤(Fintype.card U:ℝ)→c*n≤(Fintype.card U:ℝ)→Fintype.card U≤n→
    ∀(P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)),(∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀D:ℝ,(n:ℝ)/2≤D→D≤2*n→(∀v,|(P.degree v:ℝ)-D|≤δ*n)→
      (∀v,(1/2+α)*n≤(P.degree v:ℝ))→
    ∀(ρ s₀:ℝ),ρstar≤ρ→ρ≤1→sstar≤s₀→s₀≤1/100→
    ∀(p k:ℝ),p=ρ*s₀/2→k=p/((r+4:ℕ):ℝ)→
    ∀(q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Bool→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)),
    (∀w,q w false=s₀/((r+4:ℕ):ℝ))→(∀w,s w false=s₀)→
    pRet*n≤(s₀/((r+4:ℕ):ℝ))*Fintype.card U→
    ∀(p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let collapse:=fun (z:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (z e);
    1-(χ+2/(n:ℝ)^Q)≤(μ.sigma (fun z=>ν (collapse z))).probability (fun z:Σω,Ret (collapse ω)=>
      LongExpandedGlobalTests P π d ζret p k p₂ k₂ u q z ∧
      MarkedRetainedRobustChangeEvent P π d r false false ε ζ cap size a₀ b₀ e₀ f ⟨collapse z.1,z.2⟩) :=by
  obtain ⟨ε,ζ,δ,cap,hε,hζ,hδ,hcap,hstable⟩:=
    expanded_stable_alone_sample_explicit_densities k₀ r Q hr hlen α ρstar sstar ω hα hρstar hsstar hω hmargin
  refine ⟨ε,ζ,δ,cap,hε,hζ,hδ,hcap,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hstable⟩:=hstable size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f d hd pRet ζret c χ hpRet hζret hc hχ
  obtain ⟨Ns,hNs,hstable⟩:=hstable f d hd
  obtain ⟨Ng,hNg,hglobal⟩:=long_expanded_global_tests_high_probability d hd pRet ζret c χ hpRet hζret hc hχ
  refine ⟨max Ns Ng,by omega,?_⟩
  intro n hn _ U _ _ hUlo hUglobal hUhi P π hshort D hDlo hDhi hnear hmin ρ s₀ hρlo hρhi hslo hshi
    p k hpEq hkEq q hq hQ s hs hS hq0 hs0 hmass p₂ k₂ u hp hk hp₂ hk₂ hu hsum Ret ν μ collapse
  have hg:=hglobal n (by omega) U hUhi hUglobal P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum
    q hq hQ s hs hS hshort (s₀/((r+4:ℕ):ℝ)) hq0 hmass
  have hsamp:=hstable (Fin n) U (by simpa using (show Ns≤n by omega)) (by simpa using hUlo) (by simpa using hUhi)
    P π hshort D (by simpa using hDlo) (by simpa using hDhi) (by simpa using hnear) (by simpa using hmin)
    ρ s₀ hρlo hρhi hslo hshi p k hpEq hkEq q hq hQ s hs hS hq0 hs0 p₂ k₂ u hp hk hp₂ hk₂ hu hsum
  rw [sub_add_eq_sub_sub]
  apply finiteLaw_intersection_lower (μ.sigma (fun z=>ν (collapse z)))
    (fun z=>LongExpandedGlobalTests P π d ζret p k p₂ k₂ u q z)
    (fun z=>MarkedRetainedRobustChangeEvent P π d r false false ε ζ cap size a₀ b₀ e₀ f ⟨collapse z.1,z.2⟩) χ (2/(n:ℝ)^Q)
  · exact hg
  · simpa only [Fintype.card_fin] using hsamp
end Oberwolfach

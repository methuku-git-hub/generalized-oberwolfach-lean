module

public import Oberwolfach.LongGlobalStableSameSample
public import Oberwolfach.FirstVortexExpandedLocalAllTestsProbability

@[expose] public section
/-! Global, stable-absorber, six local and all-hub tests hold simultaneously
on the very same expanded sample and retained outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 10000) longGlobalStableLocalOrderedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_global_stable_local_all_ordered
    (k₀ r Qpow:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α ρstar sstar ω:ℝ) (hα:0<α) (hρstar:0<ρstar) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+α/2≤1/2+α):
    ∃ εAbs ζAbs δAbs cap:ℝ,0<εAbs∧0<ζAbs∧0<δAbs∧0<cap∧
    ∀(d:ℕ) (hd:2≤d) (pRet εQ ζlocal failure:ℝ),0<pRet→0<εQ→εQ≤1/4→0<ζlocal→0<failure→
    ∃m₀ Nlocal:ℕ,1≤m₀ ∧ 1≤Nlocal ∧ ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f₀:ℕ,
    ∀(ζret c χ:ℝ),0<ζret→0<c→0<χ→∃N:ℕ,1≤N ∧
    ∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U],
      ω*n≤(Fintype.card U:ℝ)→c*n≤(Fintype.card U:ℝ)→Fintype.card U≤n→
    ∀(P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)),(∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀D:ℝ,(n:ℝ)/2≤D→D≤2*n→(∀v,|(P.degree v:ℝ)-D|≤δAbs*n)→
      (∀v,(1/2+α)*n≤(P.degree v:ℝ))→
    ∀(ρ:ℝ),ρstar≤ρ→ρ≤1→
    ∀(p k:ℝ),p=ρ*(1/100)/2→k=p/((r+4:ℕ):ℝ)→
    ∀(q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Bool→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)),
    (∀w,q w false=(1/100:ℝ)/((r+4:ℕ):ℝ))→(∀w,s w false=1/100)→
    pRet*n≤((1/100:ℝ)/((r+4:ℕ):ℝ))*Fintype.card U→
    ∀(p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),
    ∀(Dnat m:ℕ) (βQ:ℝ) (Q:Vortex U P Dnat βQ εQ m),
      D=(Dnat:ℝ)→initialIndexDensity U Dnat=ρ→P.IsRegularOfDegree Dnat→
      0≤βQ→βQ≤1/4→0<m→m₀≤m→
      (∀x,π x∈Q.extendedVertices 1↔x∈Q.extendedVertices 1)→
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let collapse:=fun (z:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (z e);
    1-(χ+2/(n:ℝ)^Qpow+failure)≤(μ.sigma (fun z=>ν (collapse z))).probability (fun z:Σω,Ret (collapse ω)=>
      (LongExpandedGlobalTests P π d ζret p k p₂ k₂ u q z ∧
       MarkedRetainedRobustChangeEvent P π d r false false εAbs ζAbs cap size a₀ b₀ e₀ f₀ ⟨collapse z.1,z.2⟩) ∧
      (FirstVortexExpandedSixLocalTests P π d Dnat m βQ εQ Q q s u ζlocal z ∧
       FirstVortexExpandedAllHubTests P π d Dnat m βQ εQ Q q s z)) :=by
  obtain ⟨εAbs,ζAbs,δAbs,cap,hεAbs,hζAbs,hδAbs,hcap,hstable⟩:=
    long_global_stable_same_sample k₀ r Qpow hr hlen α ρstar sstar ω hα hρstar hsstar hω hmargin
  refine ⟨εAbs,ζAbs,δAbs,cap,hεAbs,hζAbs,hδAbs,hcap,?_⟩
  intro d hd pRet εQ ζlocal failure hpRet hεQ hεQ1 hζlocal hfailure
  obtain ⟨m₀,Nl,hm₀,hNl,hlocal⟩:=first_vortex_expanded_local_all_tests_high_probability d hd εQ ρstar pRet ζlocal failure
    hεQ hεQ1 hρstar hpRet hζlocal hfailure
  refine ⟨m₀,Nl,hm₀,hNl,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hstable⟩:=hstable size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f₀ ζret c χ hζret hc hχ
  obtain ⟨Ns,hNs,hstable⟩:=hstable f₀ d hd pRet ζret c χ hpRet hζret hc hχ
  refine ⟨max Ns Nl,by omega,?_⟩
  intro n hn _ U _ _ hUlo hUc hUhi P π hshort D hDlo hDhi hnear hmin ρ hρlo hρhi
    p k hpEq hkEq q hq hQ s hs hS hq0 hs0 hmass p₂ k₂ u hp hk hp₂ hk₂ hu hsum
    Dnat m βQ Q hDnat hρnat hreg hβ hβ1 hm hm₀' hpres Ret ν μ collapse
  have hst:=hstable n (by omega) U hUlo hUc hUhi P π hshort D hDlo hDhi hnear hmin
    ρ (1/100) hρlo hρhi hsstar1 (by norm_num) p k hpEq hkEq q hq hQ s hs hS hq0 hs0 hmass
    p₂ k₂ u hp hk hp₂ hk₂ hu hsum
  have hnpos:0<Fintype.card (Fin n):=by simp;omega
  have hDv:(Fintype.card (Fin n):ℝ)/2≤Dnat:=by simpa only [Fintype.card_fin,hDnat] using hDlo
  have hDpos:0<Dnat:=by
    have hnpos':(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
    have hD':(0:ℝ)<Dnat:=by rw [←hDnat];linarith
    exact_mod_cast hD'
  have hρlo':ρstar≤ initialIndexDensity U Dnat:=by simpa [hρnat] using hρlo
  have hρhi':initialIndexDensity U Dnat≤1:=by simpa [hρnat] using hρhi
  have hloc:=hlocal (Fin n) U (by simpa using (show Nl≤n by omega)) (by simpa using hUhi)
    P Dnat m βQ Q hreg hnpos hDv hDpos hρlo' hρhi' hβ hβ1 hm hm₀' π hpres
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hshort
    ((1/100:ℝ)/((r+4:ℕ):ℝ)) hq0 (by simpa using hmass) (by intro w;rw [hs0 w])
  have hh:=finiteLaw_intersection_lower (μ.sigma (fun z=>ν (collapse z)))
    (fun z=>LongExpandedGlobalTests P π d ζret p k p₂ k₂ u q z ∧
      MarkedRetainedRobustChangeEvent P π d r false false εAbs ζAbs cap size a₀ b₀ e₀ f₀ ⟨collapse z.1,z.2⟩)
    (fun z=>FirstVortexExpandedSixLocalTests P π d Dnat m βQ εQ Q q s u ζlocal z ∧
      FirstVortexExpandedAllHubTests P π d Dnat m βQ εQ Q q s z)
    (χ+2/(n:ℝ)^Qpow) failure hst hloc
  linarith only [hh]
end Oberwolfach

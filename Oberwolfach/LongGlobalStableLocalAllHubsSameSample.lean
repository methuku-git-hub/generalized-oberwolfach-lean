module

public import Oberwolfach.LongGlobalStableSameSample
public import Oberwolfach.FirstVortexExpandedSixTestsProbability
public import Oberwolfach.FirstVortexExpandedUnassignedAllHubsProbability

@[expose] public section
/-! Global, stable and local tests on one expanded sample, without any
lower bound on complementary partition densities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxRecDepth 32768
set_option maxHeartbeats 90000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 10000) globalStableLocalFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

def LongVortexLocalSixTests {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (q s:U→Bool→ℝ) (u ζ:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d):Prop :=
    (∀v,|(((P.neighborFinset v∩Q.extendedVertices 1).filter (fun x=>(z.1 (Sum.inl s(v,x))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩Q.extendedVertices 1).card|<(n:ℝ)^(3/4:ℝ)) ∧
    (∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (Q.extendedVertices 1)-
      ((Q.extendedVertices 1).card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v (Q.extendedIndices 1)-
      ∑w∈Q.extendedIndices 1,(1-(∑g,q w g)-(∑j,s w j))|<((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    (∀v∈Q.extendedVertices 1,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Q.extendedIndices 1) v).card:ℝ)≤
      4*((Q.extendedIndices 1).card:ℝ)/d+4*((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    RetainedRestrictionLocalGood π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) (Q.extendedVertices 1) (Q.extendedIndices 1) ζ z.2 ∧
    (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ))

def LongVortexAllHubTests {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (q s:U→Bool→ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d):Prop :=
    (∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (Q.extendedVertices 1)-
      ((Q.extendedVertices 1).card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(n:ℝ)^(3/4:ℝ)) ∧
    (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v Finset.univ-
      ∑w:U,(1-(∑g,q w g)-(∑j,s w j))|<(n:ℝ)^(3/4:ℝ))

theorem long_global_stable_local_all_hubs_same_sample
    (k₀ r Qpow:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α ρstar sstar ω:ℝ) (hα:0<α) (hρstar:0<ρstar) (hsstar:0<sstar) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+α/2≤1/2+α):
    ∃ εStable ζStable δStable capStable:ℝ,0<εStable ∧ 0<ζStable ∧ 0<δStable ∧ 0<capStable ∧
    ∀d:ℕ,∀hd:2≤d,
    ∀(εQ pRet ζret ζLocal c χ:ℝ),0<εQ→εQ≤1/4→0<pRet→0<ζret→0<ζLocal→0<c→0<χ→
    ∃m₀:ℕ,1≤m₀ ∧ ∀size:ℕ,∃a₀ b₀ e₀:ℕ,∀f:ℕ,
    ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→∀[Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U],
    ω*n≤(Fintype.card U:ℝ)→c*n≤(Fintype.card U:ℝ)→Fintype.card U≤n→
    ∀(P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)),(∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(Dnat m:ℕ) (β:ℝ) (Vort:Vortex U P Dnat β εQ m),
    P.IsRegularOfDegree Dnat→0<Dnat→(n:ℝ)/2≤Dnat→(Dnat:ℝ)≤2*n→
    (∀v,|(P.degree v:ℝ)-Dnat|≤δStable*n)→(1/2+α)*n≤(Dnat:ℝ)→
    ρstar≤ initialIndexDensity U Dnat→initialIndexDensity U Dnat≤1→0≤β→β≤1/4→0<m→m₀≤m→
    (∀x,π x∈Vort.extendedVertices 1↔x∈Vort.extendedVertices 1)→
    ∀(s₀:ℝ),sstar≤s₀→s₀≤1/100→
    ∀(p k:ℝ),p=initialIndexDensity U Dnat*s₀/2→k=p/((r+4:ℕ):ℝ)→
    ∀(q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Bool→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)),
    (∀w,q w false=s₀/((r+4:ℕ):ℝ))→(∀w,s w false=s₀)→(1/100:ℝ)≤s₀→
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
    1-(χ+2/(n:ℝ)^Qpow)≤(μ.sigma (fun z=>ν (collapse z))).probability (fun z:Σω,Ret (collapse ω)=>
      (LongExpandedGlobalTests P π d ζret p k p₂ k₂ u q z ∧
       MarkedRetainedRobustChangeEvent P π d r false false εStable ζStable capStable size a₀ b₀ e₀ f ⟨collapse z.1,z.2⟩) ∧
      (LongVortexLocalSixTests P π d Dnat m β εQ Vort q s u ζLocal z ∧
       LongVortexAllHubTests P π d Dnat m β εQ Vort q s z)) :=by
  obtain ⟨εStable,ζStable,δStable,capStable,hεStable,hζStable,hδStable,hcapStable,hstable⟩:=
    long_global_stable_same_sample k₀ r Qpow hr hlen α ρstar sstar ω hα hρstar hsstar hω hmargin
  refine ⟨εStable,ζStable,δStable,capStable,hεStable,hζStable,hδStable,hcapStable,?_⟩
  intro d hd εQ pRet ζret ζLocal c χ hεQ hεQ1 hpRet hζret hζLocal hc hχ
  obtain ⟨m₀,Nlocal,hm₀,hNlocal,hlocal⟩:=raw_expanded_first_vortex_six_tests_high_probability d hd εQ ρstar pRet ζLocal (χ/4) hεQ hεQ1 hρstar hpRet hζLocal (by positivity)
  obtain ⟨Nall,hall⟩:=raw_expanded_first_vortex_unassigned_all_hubs_high_probability d hd εQ ρstar (χ/4) hεQ hρstar (by positivity)
  refine ⟨m₀,hm₀,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hstable⟩:=hstable size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f
  obtain ⟨Ng,hNg,hglobal⟩:=hstable f d hd pRet ζret c (χ/2) hpRet hζret hc (by positivity)
  refine ⟨max Ng (max Nlocal Nall),by omega,?_⟩
  intro n hn _ U _ _ hUlo hUc hU P π hnoshort Dnat m β Vort hreg hDpos hDlo hDhi hnear hmin hρlo hρhi hβ hβ1 hm hm₀ hpres
    s₀ hslo hshi p k hpEq hkEq q hq hQ s hs hS hq0 hs0 hs100 hmass p₂ k₂ u hp hk hp₂ hk₂ hu hsum Ret ν μ collapse
  have hnpos:0<n:=by omega
  have hmin':∀v,(1/2+α)*n≤(P.degree v:ℝ):=by
    intro v
    simpa only [hreg v] using hmin
  have hg:=hglobal n (by omega) U hUlo hUc hU P π hnoshort Dnat hDlo hDhi hnear hmin'
    (initialIndexDensity U Dnat) s₀ hρlo hρhi hslo hshi p k hpEq hkEq q hq hQ s hs hS hq0 hs0 hmass
    p₂ k₂ u hp hk hp₂ hk₂ hu hsum
  have hl:=hlocal (Fin n) U (by simp;omega) (by simpa using hU) P Dnat m β Vort hreg (by simpa using hnpos)
    (by simpa using hDlo) hDpos hρlo hρhi hβ hβ1 hm hm₀ π hpres p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort
    (s₀/((r+4:ℕ):ℝ)) hq0 (by simpa using hmass) (by intro w;rw [hs0];exact hs100)
  have ha:=hall (Fin n) (by simp;omega) U Bool Bool (by simpa using hU) P Dnat m β Vort hreg (by simpa using hnpos)
    (by simpa using hDlo) hρlo hβ hβ1 hm π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort Ret ν
  have hl':1-χ/4≤(μ.sigma (fun z=>ν (collapse z))).probability (fun z=>LongVortexLocalSixTests P π d Dnat m β εQ Vort q s u ζLocal z):=by
    simpa only [LongVortexLocalSixTests,Fintype.card_fin] using hl
  have ha':1-χ/4≤(μ.sigma (fun z=>ν (collapse z))).probability (fun z=>LongVortexAllHubTests P π d Dnat m β εQ Vort q s z):=by
    simpa only [LongVortexAllHubTests,Fintype.card_fin] using ha
  have hlocalboth:=finiteLaw_intersection_lower (μ.sigma (fun z=>ν (collapse z))) _ _ (χ/4) (χ/4) hl' ha'
  have hlocalboth':1-χ/2≤(μ.sigma (fun z=>ν (collapse z))).probability
      (fun z=>LongVortexLocalSixTests P π d Dnat m β εQ Vort q s u ζLocal z ∧
        LongVortexAllHubTests P π d Dnat m β εQ Vort q s z):=by linarith only [hlocalboth]
  have hglobalboth:=finiteLaw_intersection_lower (μ.sigma (fun z=>ν (collapse z)))
    (fun z=>LongExpandedGlobalTests P π d ζret p k p₂ k₂ u q z ∧
      MarkedRetainedRobustChangeEvent P π d r false false εStable ζStable capStable size a₀ b₀ e₀ f ⟨collapse z.1,z.2⟩)
    (fun z=>LongVortexLocalSixTests P π d Dnat m β εQ Vort q s u ζLocal z ∧
      LongVortexAllHubTests P π d Dnat m β εQ Vort q s z)
    (χ/2+2/(n:ℝ)^Qpow) (χ/2) hg hlocalboth'
  linarith only [hglobalboth]
end Oberwolfach

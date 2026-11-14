module

public import Oberwolfach.LongBinaryFirstVortexProtectedProbability
public import Oberwolfach.ExpandedGlobalDegreesAndStarts
public import Oberwolfach.FiniteLawIntersectionLower
public import Oberwolfach.LongBinaryFirstVortexPartitionInputs
public import Oberwolfach.ExpandedDensityOneProtectedClass
public import Oberwolfach.FiniteLawSupportAlmostSure
public import Oberwolfach.GroupedRegularClassTransfer
public import Oberwolfach.ExpandedBinaryColourProjection
public import Oberwolfach.JointEventPolynomialMargins

@[expose] public section
/-! The actual binary class is regular and protects the first vortex pair
and every bounded later reserve, with probability arbitrarily close to one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_binary_first_vortex_external_probability
    (αHost rPart ξPart failure:ℝ) (Bpart d:ℕ) (hd:2≤d)
    (pRet ζret c:ℝ) (hα:0<αHost) (hr:0<rPart) (hξ:0<ξPart) (hfailure:0<failure)
    (hpRet:0<pRet) (hζret:0<ζret) (hc:0<c):
    ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U I:Type) [Fintype U] [DecidableEq U] [Fintype I]
    (P:SimpleGraph (Fin n)) (Dnat vsize:ℕ) (β εQ:ℝ) (Q:Vortex U P Dnat β εQ vsize)
    (hreg:P.IsRegularOfDegree Dnat) (hD:0<Dnat) (heven:Even Dnat)
    (hmin:(1/2+αHost)*(n:ℝ)≤(Dnat:ℝ)) (hε:0≤εQ) (hεsmall:εQ≤αHost/100000)
    (density:I→ℝ) (i:I) (hρ:∀j,0≤density j) (hsum:∑j,density j=1)
    (hsmall:∀j,density j=0∨rPart≤density j) (hcurrent:rPart≤density i)
    (hsize:density i*Dnat=2*Fintype.card U) (s₀:ℝ) (a b:U→ℝ)
    (π:Equiv.Perm (Fin n)),
    let ρ:=density i
    let p:=ρ*(1/100)/2
    let k:=ρ*s₀/2
    let p₂:=(∑w,b w)/(Dnat:ℝ)
    let k₂:=(∑w,a w)/(Dnat:ℝ)
    let udens:=2*(∑w,(1-1/100-s₀-a w-b w))/(Dnat:ℝ)
    let Zpart:=spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)
    let mpart:=binaryClassMultiplicity Dnat (Fintype.card U);
    ∀ (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤udens)
      (hphys:2*p+2*k+2*p₂+2*k₂+udens≤1)
      (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (sp:U→Bool→ℝ) (hsp:∀u j,0≤sp u j)
      (hSp:∀u,∑j,sp u j≤ intervalUncoveredProbability d (∑g,q u g))
      (hUhi:Fintype.card U≤n) (hUlo:c*n≤(Fintype.card U:ℝ))
      (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
      (t₀:ℝ) (hq0:∀u,q u false=t₀) (hmass:pRet*n≤t₀*Fintype.card U),
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ udens hp hk hp₂ hk₂ hu hphys d hd q hq hQ sp hsp hSp)
    let f:=fun (z:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (z e);
    1-failure≤(μ.sigma (fun z=>ν (f z))).probability (fun z:Σz,Ret (f z)=>
      (∀A:SimpleGraph (Fin n),(∀v,A.degree v≤Bpart)→
        ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
          (∀x y,(Zpart⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n)) ∧
      (((RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret z.2 ∧
        (∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) Finset.univ v).card:ℝ)≤
          4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))) ∧
       (∀j x,
        |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j x y:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ udens j/2*P.degree x|<(n:ℝ)^(3/5:ℝ) ∧
        |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j y x:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ udens j/2*P.degree x|<(n:ℝ)^(3/5:ℝ) ∧
        |(sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) j x:ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ udens j*P.degree x|<(n:ℝ)^(3/5:ℝ))) ∧
       (∀g x,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g x).card:ℝ)-(∑w,q w g/(d:ℝ))|<(n:ℝ)^(3/5:ℝ)))) :=by
  obtain ⟨Npart,hNpart,hPart⟩:=long_binary_first_vortex_protected_probability αHost rPart ξPart (failure/2) Bpart hα hr hξ (by positivity)
  obtain ⟨mGlobal,NGlobal,hmGlobal,hNGlobal,hGlobal⟩:=expanded_global_boundary_retention_degrees_starts d hd pRet ζret c (failure/2) hpRet hζret hc (by positivity)
  refine ⟨max Npart (max mGlobal NGlobal),by omega,?_⟩
  intro n hn _ U I _ _ _ P Dnat vsize β εQ Q hreg hD heven hmin hε hεsmall density i hρ hsum hsmall hcurrent hsize s₀ a b π ρ p k p₂ k₂ udens Zpart mpart hp hk hp₂ hk₂ hu hphys q hq hQ sp hsp hSp hUhi hUlo hnoshort t₀ hq0 hmass Ret ν μ f
  have hP:=hPart n (by omega) U I P Dnat vsize β εQ Q hreg hD heven hmin hε hεsmall density i hρ hsum hsmall hcurrent hsize s₀ a b π d hd
    hp hk hp₂ hk₂ hu hphys q hq hQ sp hsp hSp
  have hG:=hGlobal (Fin n) U (by simpa using (show NGlobal≤n by omega)) (by simpa using (show mGlobal≤n by omega))
    (by simpa using hUhi) (by simpa using hUlo) P π p k p₂ k₂ udens hp hk hp₂ hk₂ hu hphys q hq hQ sp hsp hSp hnoshort t₀ hq0 (by simpa using hmass)
  have hh:=finiteLaw_intersection_lower (μ.sigma (fun z=>ν (f z))) _ _ (failure/2) (failure/2) hP (by simpa only [Fintype.card_fin] using hG)
  linarith
end Oberwolfach

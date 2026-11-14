module

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

theorem long_binary_first_vortex_protected_probability
    (αHost rPart ξPart failure:ℝ) (Bpart:ℕ)
    (hα:0<αHost) (hr:0<rPart) (hξ:0<ξPart) (hfailure:0<failure):
    ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U I:Type) [Fintype U] [DecidableEq U] [Fintype I]
    (P:SimpleGraph (Fin n)) (Dnat vsize:ℕ) (β εQ:ℝ) (Q:Vortex U P Dnat β εQ vsize)
    (hreg:P.IsRegularOfDegree Dnat) (hD:0<Dnat) (heven:Even Dnat)
    (hmin:(1/2+αHost)*(n:ℝ)≤(Dnat:ℝ)) (hε:0≤εQ) (hεsmall:εQ≤αHost/100000)
    (density:I→ℝ) (i:I) (hρ:∀j,0≤density j) (hsum:∑j,density j=1)
    (hsmall:∀j,density j=0∨rPart≤density j) (hcurrent:rPart≤density i)
    (hsize:density i*Dnat=2*Fintype.card U) (s₀:ℝ) (a b:U→ℝ)
    (π:Equiv.Perm (Fin n)) (d:ℕ) (hd:2≤d),
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
      (hSp:∀u,∑j,sp u j≤ intervalUncoveredProbability d (∑g,q u g)),
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ udens hp hk hp₂ hk₂ hu hphys d hd q hq hQ sp hsp hSp)
    let f:=fun (z:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (z e);
    1-failure≤(μ.sigma (fun z=>ν (f z))).probability (fun z:Σz,Ret (f z)=>
      ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤Bpart)→
        ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
          (∀x y,(Zpart⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n)):=by
  obtain ⟨Npart,hPart⟩:=grouped_regular_class_transfer αHost rPart ξPart hα hr hξ Bpart
  obtain ⟨Nsmall,_,hsmallPow⟩:=joint_event_polynomial_margin (1-failure) 1 0 10 1 (by linarith) (by norm_num) (by norm_num)
  refine ⟨max 1 (max Npart Nsmall),by omega,?_⟩
  intro n hn _ U I _ _ _ P Dnat vsize β εQ Q hreg hD heven hmin hε hεsmall density i hρ hsum hsmall hcurrent hsize s₀ a b π d hd ρ p k p₂ k₂ udens Zpart mpart hp hk hp₂ hk₂ hu hphys q hq hQ sp hsp hSp Ret ν μ f
  have hin:=long_binary_first_vortex_partition_inputs P β εQ αHost Q density i rPart s₀ a b hD heven hρ hsum hsmall hcurrent hsize hε hεsmall
  obtain ⟨hPartSum,hPartMass,hPartLower,hPartProtect,hClique,hZero⟩:=hin
  let PartGood:=fun z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω))=>
      ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤Bpart)→
        ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*mpart 0) ∧
          (∀x y,(Zpart⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n)
  have hPartGood:1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability PartGood:=by
    rcases hPartLower with hone|hboth
    · have htwo:Dnat=2*mpart 0:=by
        have hh:=hPartMass 0
        simp only [expandedBinaryProbability,Matrix.cons_val_zero,hone] at hh
        have hr':(Dnat:ℝ)=2*(mpart 0:ℝ):=by linarith
        exact_mod_cast hr'
      have hreg':P.IsRegularOfDegree (2*mpart 0):=by simpa only [htwo] using hreg
      have hpone:(μ.sigma (fun ω=>ν (f ω))).probability PartGood=1:=by
        apply finiteLaw_probability_one_of_positive_mass
        intro z hz A hA
        have hh:=expanded_density_one_protected_regular_class p k p₂ k₂ udens hp hk hp₂ hk₂ hu hphys hone
          d hd q hq hQ sp hsp hSp (fun ω=>ν (f ω)) P Zpart (mpart 0) hreg' ξPart hξ.le z hz A
        have hdec6:instDecidableEqFin 6=referenceWitnessFinDecidable 6:=Subsingleton.elim _ _
        try rw [hdec6] at hh
        simpa only [Fintype.card_fin] using hh
      rw [hpone];linarith
    · let ρbin:=expandedBinaryProbability p k p₂ k₂ udens
      let hρbin:=expanded_binary_probability_nonneg p k p₂ k₂ udens hp hk hp₂ hk₂ hu hphys
      let hρtotal:=expanded_binary_probability_sum p k p₂ k₂ udens
      have hGroup:=hPart n (by omega) U Bool Bool P Zpart Dnat mpart ρbin hρbin hρtotal
        hreg heven hmin hPartSum hPartMass hboth hPartProtect
        (Ω := Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω))
      have hdec:instDecidableEqFin n=referenceWitnessFinDecidable n:=Subsingleton.elim _ _
      have hdec2:instDecidableEqFin 2=referenceWitnessFinDecidable 2:=Subsingleton.elim _ _
      have hdec6:instDecidableEqFin 6=referenceWitnessFinDecidable 6:=Subsingleton.elim _ _
      try rw [hdec] at hGroup
      try rw [hdec2] at hGroup
      try rw [hdec6] at hGroup
      have hProjection:∀E:(Sym2 (Fin n)→Fin 2)→Prop,
          (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>(expandedBinaryClass (z.1 (Sum.inl e))).1))=
            (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.categorical ρbin hρbin hρtotal)).probability E:=by
        intro E
        exact expanded_binary_colour_probability_after_retention p k p₂ k₂ udens hp hk hp₂ hk₂ hu hphys
          d hd q hq hQ sp hsp hSp (fun ω=>ν (f ω)) E
      have hprob:=hGroup (μ.sigma (fun ω=>ν (f ω))) (fun z=>z.1) hProjection
      have hsmallPart:=hsmallPow n (by omega)
      have hpow:(n:ℝ)^(-(10:ℝ))=1/(n:ℝ)^10:=by rw [Real.rpow_neg (Nat.cast_nonneg n),one_div];congr 1 <;> norm_num
      rw [hpow] at hsmallPart
      simp only [one_mul,zero_mul,add_zero] at hsmallPart
      have hcompare:1-failure≤1-1/(n:ℝ)^10:=by linarith only [hsmallPart]
      exact hcompare.trans (by simpa only [PartGood] using hprob)
  apply hPartGood.trans
  apply finiteLaw_probability_mono
  intro z hz A hA
  obtain ⟨S,hS,hregS,hprotect,hedit⟩:=hz A hA
  have hz:mpart 0=Fintype.card U:=by simp [mpart,binaryClassMultiplicity]
  exact ⟨S,hS,by rw [←hz];exact hregS,hprotect,hedit⟩
end Oberwolfach

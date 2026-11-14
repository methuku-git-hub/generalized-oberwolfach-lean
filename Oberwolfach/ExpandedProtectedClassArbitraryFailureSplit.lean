module

public import Oberwolfach.ExpandedDensityOneProtectedClassBoundedProbability
public import Oberwolfach.GroupedRegularClassArbitraryFailure
public import Oberwolfach.ExpandedDensityOneProtectedClass
public import Oberwolfach.FiniteLawSupportAlmostSure
public import Oberwolfach.GroupedRegularClassTransfer
public import Oberwolfach.ExpandedBinaryColourProjection
public import Oberwolfach.JointEventPolynomialMargins

@[expose] public section
/-! An arbitrarily likely protected regular class event on the original
expanded sample, including the density-one boundary case. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 120000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance splitProtectedFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem expanded_protected_regular_class_arbitrary_failure_split
    (α r ξ δ:ℝ) (B:ℕ) (hα:0<α) (hr:0<r) (hξ:0<ξ) (hδ:0<δ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (P Z:SimpleGraph (Fin n)) (D:ℕ) (m:Fin 2→ℕ)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑g,q u g))
    (F:RawMarkedOutcome (Fin n) U Bool Bool→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)),
    P.IsRegularOfDegree D→Even D→(1/2+α)*n≤(D:ℝ)→(∑i,m i)=D/2→
    (∀i,expandedBinaryProbability p k p₂ k₂ u i/2*D=(m i:ℝ))→
    ((2*p+2*k+2*p₂+2*k₂+u=1) ∨ ∀i,r≤expandedBinaryProbability p k p₂ k₂ u i)→
    (∀v,(Z.degree v:ℝ)≤α/100000*n)→
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (ω e);
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
        ∃T:SimpleGraph (Fin n),T≤P ∧ T.IsRegularOfDegree (2*m 0) ∧
          (∀x y,(Z⊔A).Adj x y→(T.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (T.neighborFinset v)).card:ℝ)≤ξ*n)) := by
  obtain ⟨Npart,hPart⟩:=grouped_regular_class_arbitrary_failure α r ξ δ hα hr hξ hδ B
  refine ⟨max Npart 1,?_⟩
  intro n hn U _ _ P Z D m p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F _ ν hreg heven hmin hsumM hmass hLower hProtect μ f
  have hnpos:0<n:=by omega
  letI : Nonempty (Fin n):=⟨⟨0,hnpos⟩⟩
  let PartGood:=fun z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,F (f ω))=>
    ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
      ∃T:SimpleGraph (Fin n),T≤P ∧ T.IsRegularOfDegree (2*m 0) ∧
        (∀x y,(Z⊔A).Adj x y→(T.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (T.neighborFinset v)).card:ℝ)≤ξ*n)
  change 1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability PartGood
  rcases hLower with hone | hboth
  · have htwo:D=2*m 0:=by
      have hh:=hmass 0
      simp only [expandedBinaryProbability, Matrix.cons_val_zero, hone] at hh
      have hh':(D:ℝ)=2*(m 0:ℝ):=by linarith
      exact_mod_cast hh'
    have hreg':P.IsRegularOfDegree (2*m 0):=by simpa only [htwo] using hreg
    have hpone:((μ.sigma (fun ω=>ν (f ω))).probability PartGood)=1:=by
      have hh:=expanded_density_one_protected_class_bounded_probability p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hone
        d hd q hq hQ s hs hS (fun ω=>ν (f ω)) P Z (m 0) hreg' ξ hξ.le B
      have hdec6:instDecidableEqFin 6=splitProtectedFinDecidable 6:=Subsingleton.elim _ _
      try rw [hdec6] at hh
      simpa only [PartGood,Fintype.card_fin] using hh
    rw [hpone]
    linarith
  · let ρbin:=expandedBinaryProbability p k p₂ k₂ u
    let hρbin:=expanded_binary_probability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum
    let hρtotal:=expanded_binary_probability_sum p k p₂ k₂ u
    have hGroup:=hPart n (by omega) U Bool Bool P Z D m ρbin hρbin hρtotal
      hreg heven hmin hsumM hmass hboth hProtect
      (Ω := Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,F (f ω))
    have hdec:instDecidableEqFin n=splitProtectedFinDecidable n:=Subsingleton.elim _ _
    have hdec2:instDecidableEqFin 2=splitProtectedFinDecidable 2:=Subsingleton.elim _ _
    have hdec6:instDecidableEqFin 6=splitProtectedFinDecidable 6:=Subsingleton.elim _ _
    try rw [hdec] at hGroup
    try rw [hdec2] at hGroup
    try rw [hdec6] at hGroup
    have hProjection:∀E:(Sym2 (Fin n)→Fin 2)→Prop,
        (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>(expandedBinaryClass (z.1 (Sum.inl e))).1))=
          (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.categorical ρbin hρbin hρtotal)).probability E:=by
      intro E
      exact expanded_binary_colour_probability_after_retention p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS (fun ω=>ν (f ω)) E
    have hprob:=hGroup (μ.sigma (fun ω=>ν (f ω))) (fun z=>z.1) hProjection
    simpa only [PartGood] using hprob
end Oberwolfach

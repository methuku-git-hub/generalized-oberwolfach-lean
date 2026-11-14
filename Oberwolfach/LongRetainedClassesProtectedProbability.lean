module

public import Oberwolfach.ExpandedProtectedClassArbitraryFailureSplit
public import Oberwolfach.LongBinaryPartitionRetainedClasses

@[expose] public section
/-! The original retained-class density alternatives supply the protected
regular class event on the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance retainedProtectedFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_retained_classes_protected_probability
    (α r ξ δ:ℝ) (B:ℕ) (hα:0<α) (hr:0<r) (hξ:0<ξ) (hδ:0<δ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U I:Type) [Fintype U] [DecidableEq U] [Fintype I]
    (density:I→ℝ) (i:I) (D:ℕ) (hD:0<D) (heven:Even D)
    (hdensity:∀j,0≤density j) (hdensitySum:∑j,density j=1)
    (hsmall:∀j,density j=0 ∨ r≤density j) (hcurrent:r≤density i)
    (hsize:density i*D=2*Fintype.card U) (a b:U→ℝ) (sc:ℝ)
    (P Z:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D)
    (hmin:(1/2+α)*n≤(D:ℝ)) (hProtect:∀v,(Z.degree v:ℝ)≤α/100000*n),
    let p:=density i*(1/100)/2
    let k:=density i*sc/2
    let p₂:=(∑u,b u)/(D:ℝ)
    let k₂:=(∑u,a u)/(D:ℝ)
    let u:=2*(∑w,(1-1/100-sc-a w-b w))/(D:ℝ);
    ∀(hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑g,q u g))
    (F:RawMarkedOutcome (Fin n) U Bool Bool→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (ω e);
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
        ∃T:SimpleGraph (Fin n),T≤P ∧ T.IsRegularOfDegree (2*Fintype.card U) ∧
          (∀x y,(Z⊔A).Adj x y→(T.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (T.neighborFinset v)).card:ℝ)≤ξ*n)) := by
  obtain ⟨N,hPart⟩:=expanded_protected_regular_class_arbitrary_failure_split α r ξ δ B hα hr hξ hδ
  refine ⟨N,?_⟩
  intro n hn U I _ _ _ density i D hD heven hdensity hdensitySum hsmall hcurrent hsize a b sc P Z hreg hmin hProtect p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F _ ν μ f
  obtain ⟨hmSum,hmMass,hAlternative⟩:=long_binary_partition_from_retained_classes density i r sc D a b hD heven hdensity hdensitySum hsmall hcurrent hsize
  have hh:=hPart n hn U P Z D (binaryClassMultiplicity D (Fintype.card U)) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν hreg heven hmin hmSum hmMass hAlternative hProtect
  simpa only [binaryClassMultiplicity,Matrix.cons_val_zero] using hh
end Oberwolfach

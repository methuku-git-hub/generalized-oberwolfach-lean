module

public import Oberwolfach.LongResidualBalancedDivisibility
public import Oberwolfach.LongResidualOrientationArcIdentity

@[expose] public section
/-! The correction's physical residual and the balanced complement residual
are the same finite arcs; their common marked correction yields divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
attribute [local instance] partitionedDivisibleDecEq partitionedDivisibleArc partitionedDivisibleArcFinite
  partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_same_sample_residual_divisibility
    (S Small:SimpleGraph V) (Mhost:V→V→ℕ) (A:Finset (V×V))
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hA:∀a∈A,Mhost a.1 a.2=1)
    (hSmall:Small.edgeFinset=A.image (fun a=>s(a.1,a.2)))
    (π:Equiv.Perm V) (d m:ℕ) (hd:1≤d) (hnoshort:∀x l,0<l→l<d→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (j:Color) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t) (R:U→Finset V)
    (hsubset:∀u,markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ g t J u=>d) Subtype.val⊆R u)
    (hsize:∀u,(R u).card=(m+1)*(markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ g t J u=>d) Subtype.val).card)
    (hdegree:∀v,((orientationMatrixArcs Mhost\A).filter (fun a=>a.1=v)).card=(Finset.univ.filter (fun u=>v∈R u)).card ∧
      ((orientationMatrixArcs Mhost\A).filter (fun a=>a.2=v)).card=(Finset.univ.filter (fun u=>v∈R u)).card):
    let P:=longEligibleResidualArc Mhost Small ⊥
    ∀K:Finset {e:V×V // P e},
    (∀v,directedInCount P K v=d*t)→
    let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ g t J u=>d) Subtype.val
    let H₀:=fun v u=>v∈R u\Y u
    MarkedRemainderDivisible
      (fun e:residualOrdinaryArc P K=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc P K=>e.val.val.1) (fun e=>π.symm e.val.val.2)
      (retainedRawMarkedSpokes π d σ g t J g j true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨retainedRawMarkedSpokes π d σ g t J g j true z.1 z.2)) m:=by
  intro P K hmarked Y H₀
  have hP:∀a,P a↔a∈orientationMatrixArcs Mhost\A:=by
    rintro ⟨x,y⟩
    exact long_residual_orientation_arc_identity S Small Mhost A hphysical hA hSmall x y
  have h:=long_residual_balanced_divisibility P (orientationMatrixArcs Mhost\A) hP K π d m hd hnoshort σ g j t J R hsubset hsize hdegree hmarked
  convert h using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
end Oberwolfach

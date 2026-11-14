module

public import Oberwolfach.LongEncodedResidualSampleReconstructionGeometry
public import Oberwolfach.MarkedRemainderDivisibleEquiv

@[expose] public section
/-! The balanced oriented residual and the corrected sampled arcs have the
same typed occurrences, so divisibility transfers to the actual sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_encoded_residual_sample_divisibility
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [Nonempty V] [DecidableEq U]
    (G S Small:SimpleGraph V) (M:V→V→ℕ)
    (π:Equiv.Perm V) (d m:ℕ) (σ:Sym2 V→Option (Bool×Bool))
    (T:Finset {a:V×V // longEligibleResidualArc M Small ⊥ a})
    (HK:V→U→Prop) (Sp:Finset (V×U))
    (hcode:∀mark x y,markedPhysicalRim G π (3*d) σ mark x y=1 ↔
      if mark then ∃e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
      else ∃e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧e.val.val.2=y)
    (hdiv:MarkedRemainderDivisible
      (fun e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T=>e.val.val.1) (fun e=>π.symm e.val.val.2)
      HK Finset.univ Sp m):
    MarkedRemainderDivisible
      (fun e:MarkedSampleArc G π (3*d) σ false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc G π (3*d) σ true=>e.val.1) (fun e=>e.val.2)
      HK Finset.univ Sp m:=by
  let O:=residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T
  let K:=residualMarkedArc (longEligibleResidualArc M Small ⊥) T
  let E':=MarkedSampleArc G π (3*d) σ false
  let K':=MarkedSampleArc G π (3*d) σ true
  let fo:O→E':=fun a=>⟨a.val.val,(hcode false _ _).mpr ⟨a,rfl,rfl⟩⟩
  let fk:K→K':=fun a=>⟨(a.val.val.1,π.symm a.val.val.2),(hcode true _ _).mpr ⟨a,rfl,rfl⟩⟩
  have hfo:Function.Bijective fo:=by
    constructor
    · intro a b h
      have hv: a.val.val=b.val.val:=congrArg (fun x:E' => x.val) h
      exact Subtype.ext (Subtype.ext hv)
    · intro a
      obtain ⟨b,hx,hy⟩:=(hcode false a.val.1 a.val.2).mp a.property
      refine ⟨b,Subtype.ext ?_⟩
      exact Prod.ext hx hy
  have hfk:Function.Bijective fk:=by
    constructor
    · intro a b h
      have hv:(a.val.val.1,π.symm a.val.val.2)=(b.val.val.1,π.symm b.val.val.2):=congrArg (fun x:K' => x.val) h
      have hxy:=Prod.mk.inj hv
      have hx:a.val.val.1=b.val.val.1:=hxy.1
      have hy:a.val.val.2=b.val.val.2:=π.symm.injective hxy.2
      exact Subtype.ext (Subtype.ext (Prod.ext hx hy))
    · intro a
      obtain ⟨b,hx,hy⟩:=(hcode true a.val.1 a.val.2).mp a.property
      refine ⟨b,Subtype.ext ?_⟩
      exact Prod.ext hx hy
  let eo:=Equiv.ofBijective fo hfo
  let ek:=Equiv.ofBijective fk hfk
  exact marked_remainder_divisible_equiv _ _ _ _ _ _ _ _ eo ek
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) HK Sp m hdiv
end Oberwolfach

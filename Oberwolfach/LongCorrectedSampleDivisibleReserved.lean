module

public import Oberwolfach.LongEncodedResidualSampleDivisibility
public import Oberwolfach.MarkedRobustChangedSampleReserved

@[expose] public section
/-! The encoded balanced residual and the robust event refer to the same
corrected sample; its exact divisibility and reserved-absorber property follow
together from the matching/correction witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_corrected_sample_divisible_reserved
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [Nonempty V] [DecidableEq U]
    (P S Small:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false)
    (ε ζ cap:ℝ) (size a₀ b₀ e₀ f:ℕ) (hζ:0≤ζ)
    (hstable:MarkedRetainedRobustChangeEvent P π d r false false ε ζ cap size a₀ b₀ e₀ f z)
    (τ:RawMarkedOutcome V U Bool Bool) (Hnew:Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hR:∀a,¬(rawMarkedPairRims P π d z.1 a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀b v u,¬(retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false b v u↔Hnew b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤cap*Fintype.card V) (hFS:∀x,(FS.degree x:ℝ)≤cap*Fintype.card V)
    (htypes:∀v u,¬(Hnew false v u∧Hnew true v u))
    (M:V→V→ℕ) (T:Finset {a:V×V // longEligibleResidualArc M Small ⊥ a})
    (hcode:∀mark x y,markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
      if mark then ∃e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
      else ∃e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧e.val.val.2=y):
    let Sp:=Finset.univ.filter (fun p:V×U=>Hnew false p.1 p.2∨Hnew true p.1 p.2)
    let E:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true;
    MarkedRemainderDivisible
      (fun e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T=>e.val.val.1) (fun e=>π.symm e.val.val.2)
      (Hnew true) Finset.univ Sp (r+4)→
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (Hnew true) Finset.univ Sp (r+4) ∧
    MarkedReservedTerminalAbsorberProperty (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (Hnew false) (Hnew true) π (3*d) r size a₀ b₀ e₀ f ε:=by
  intro Sp E K hdiv
  constructor
  · exact long_encoded_residual_sample_divisibility P S Small M π d (r+4) (fun e=>τ (Sum.inl e)) T (Hnew true) Sp hcode hdiv
  · exact marked_robust_changed_sample_reserved P π d r false false ε ζ cap size a₀ b₀ e₀ f hζ z hstable τ Hnew FR FS hR hS hFR hFS htypes
end Oberwolfach

module

public import Oberwolfach.RawMarkedResourceCoordinates
public import Oberwolfach.MarkedSampleArcs

@[expose] public section
/-! Ordinary and marked sampled successor arcs both give their actual
physical directed arcs in the original sampled graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def rawMixedPhysicalArc {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color) (x y:V):Prop:=
  rawMarkedPairRims P π d raw (Sum.inl (x,y)) ∨ rawMarkedPairRims P π d raw (Sum.inr (x,π.symm y))

theorem raw_mixed_sampled_arcs_in_physical_host
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color):
    let E:=MarkedSampleArc P π (3*d) (fun x=>raw (Sum.inl x)) false
    let K:=MarkedSampleArc P π (3*d) (fun x=>raw (Sum.inl x)) true
    (∀e:E,P.Adj e.val.1 e.val.2) ∧ (∀e:K,P.Adj e.val.1 (π e.val.2)) ∧
    (∀e:E,rawMixedPhysicalArc P π d raw e.val.1 e.val.2) ∧
    (∀e:K,rawMixedPhysicalArc P π d raw e.val.1 (π e.val.2)) ∧
    (∀x y,rawMarkedPairRims P π d raw (Sum.inl (x,y))→ rawMixedPhysicalArc P π d raw x y):=by
  intro E K
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro e
    have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) (fun x=>raw (Sum.inl x)) false e.val.1 e.val.2).mp e.property
    simpa only [Bool.false_eq_true,ite_false] using hh.2.1
  · intro e
    have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) (fun x=>raw (Sum.inl x)) true e.val.1 e.val.2).mp e.property
    simpa only [ite_true] using hh.2.1
  · intro e
    left
    exact e.property
  · intro e
    right
    change markedPhysicalRim P π (3*d) (fun x=>raw (Sum.inl x)) true e.val.1 (π.symm (π e.val.2))=1
    simpa only [Equiv.symm_apply_apply] using e.property
  · exact fun x y h=>Or.inl h
end Oberwolfach

module

public import Oberwolfach.LongApproximateSampleGraphEmbedding
public import Oberwolfach.LongPreparationPhysicalContainment
public import Oberwolfach.RawSelectedPhysicalNeighbourTests

@[expose] public section
/-! Both physical layers used by the residual completion lie in the host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_approximate_physical_graph_le_host
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    longApproximatePhysicalGraph P π d σ≤P:=by
  intro x y h
  let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
  change x≠y ∧ ({x,y}:Finset V)∈
    (Finset.univ.image (markedPhysicalEdge
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false=>e.val.1)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true=>e.val.1)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true=>e.val.2) π)) at h
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp h.2
  have hpair {a b c e:V} (hh:({a,b}:Finset V)={c,e}):a=c ∧ b=e ∨ a=e ∧ b=c:=by
    apply Set.pair_eq_pair_iff.mp
    simpa only [Finset.coe_pair] using congrArg (fun S:Finset V=>(S:Set V)) hh
  cases a with
  | inl e=>
    have hadj:P.Adj e.val.1 e.val.2:=((markedPhysicalRim_eq_one_iff P π (3*d) _ false _ _).mp e.property).2.1
    rcases hpair (by simpa [markedPhysicalEdge] using ha) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hadj
    · exact hadj.symm
  | inr e=>
    have hadj:P.Adj e.val.1 (π e.val.2):=((markedPhysicalRim_eq_one_iff P π (3*d) _ true _ _).mp e.property).2.1
    rcases hpair (by simpa [markedPhysicalEdge] using ha) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hadj
    · exact hadj.symm

theorem long_required_physical_graph_le_host
    (P P₀ Sel:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (D M:V→V→Prop)
    (hP₀:P₀≤P):longRequiredPhysicalGraph P P₀ Sel π d I D M≤P:=by
  intro x y h
  rcases (show (spanningRestriction (P₀\Sel) I).Adj x y ∨ (longCloseRequiredGraph P π d D M).Adj x y from h) with hh|hh
  · exact hP₀ ((spanningRestriction_adj _ _ _ _).mp hh).1.1
  · exact hh.1

theorem raw_selected_physical_relation_in_host
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool) (x y:V):
    rawSelectedPhysicalRelation P π d ω x y→P.Adj x y:=by
  intro h
  exact ((markedPhysicalRim_eq_one_iff P π (3*d) _ false _ _).mp h).2.1
end Oberwolfach

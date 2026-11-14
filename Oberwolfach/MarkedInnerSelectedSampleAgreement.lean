module

public import Oberwolfach.MarkedFinitePhysicalDeletion

@[expose] public section
/-! Equality of the typed physical state on each edge of the fixed inner
set transfers the full selected sample there, with its original direction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem marked_inner_full_selected_sample_agreement
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (σ τ:RawMarkedOutcome V U Γ Color)
    (hAgree:∀x∈I,∀y∈I,σ (Sum.inl s(x,y))=τ (Sum.inl s(x,y))):
    ∀x∈I,∀y∈I,(markedSampleArcSetGraph P π d σ Finset.univ).Adj x y→
      (markedSampleArcSetGraph P π d τ Finset.univ).Adj x y:=by
  intro x hx y hy h
  have hxy:({x,y}:Finset V)⊆I:=by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl <;> assumption
  change x≠y ∧ ({x,y}:Finset V)∈
    Finset.univ.image (markedPhysicalEdge (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1)
      (fun e=>e.val.2) (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2) π) at h
  obtain ⟨z,_,hz⟩:=Finset.mem_image.mp h.2
  cases z with
  | inl z =>
    let u:=z.val.1
    let v:=z.val.2
    have hp:({u,v}:Finset V)={x,y}:=hz
    have hu:u∈I:=hxy (hp ▸ (by simp: u∈({u,v}:Finset V)))
    have hv:v∈I:=hxy (hp ▸ (by simp: v∈({u,v}:Finset V)))
    have hr:markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) false u v=1:=by
      have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) _ false u v).mp z.property
      apply (markedPhysicalRim_eq_one_iff P π (3*d) _ false u v).mpr
      refine ⟨hh.1,hh.2.1,?_⟩
      change τ (Sum.inl s(u,v))=some (false,orientationBit u v)
      rw [←hAgree u hu v hv]
      exact hh.2.2
    let z':MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false:=⟨(u,v),hr⟩
    have hm:s(u,v)∈(markedSampleArcSetGraph P π d τ Finset.univ).edgeFinset:=by
      simpa only [Sum.elim_inl] using
        (markedSampleArcSetGraph_coordinate P π d τ Finset.univ (Sum.inl z')).mpr (Finset.mem_univ _)
    have heq:s(u,v)=s(x,y):=by
      apply Sym2.eq_iff.mpr
      apply Set.pair_eq_pair_iff.mp
      simpa only [Finset.coe_pair] using congrArg (fun S:Finset V=>(S:Set V)) hp
    rw [heq] at hm
    exact SimpleGraph.mem_edgeFinset.mp hm
  | inr z =>
    let u:=z.val.1
    let v:=z.val.2
    have hp:({u,π v}:Finset V)={x,y}:=hz
    have hu:u∈I:=hxy (hp ▸ (by simp: u∈({u,π v}:Finset V)))
    have hv:π v∈I:=hxy (hp ▸ (by simp: π v∈({u,π v}:Finset V)))
    have hr:markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) true u v=1:=by
      have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) _ true u v).mp z.property
      apply (markedPhysicalRim_eq_one_iff P π (3*d) _ true u v).mpr
      refine ⟨hh.1,hh.2.1,?_⟩
      change τ (Sum.inl s(u,π v))=some (true,orientationBit u (π v))
      rw [←hAgree u hu (π v) hv]
      exact hh.2.2
    let z':MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true:=⟨(u,v),hr⟩
    have hm:s(u,π v)∈(markedSampleArcSetGraph P π d τ Finset.univ).edgeFinset:=by
      simpa only [Sum.elim_inr,z'] using
        (markedSampleArcSetGraph_coordinate P π d τ Finset.univ (Sum.inr z')).mpr (Finset.mem_univ _)
    have heq:s(u,π v)=s(x,y):=by
      apply Sym2.eq_iff.mpr
      apply Set.pair_eq_pair_iff.mp
      simpa only [Finset.coe_pair] using congrArg (fun S:Finset V=>(S:Set V)) hp
    rw [heq] at hm
    exact SimpleGraph.mem_edgeFinset.mp hm
end Oberwolfach

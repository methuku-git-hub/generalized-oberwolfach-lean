module

public import Oberwolfach.MarkedRawStateChangeOnHost
public import Oberwolfach.RawMarkedRimDeletion

@[expose] public section
/-! Delete precisely the underlying physical edges on which two raw rim
states differ. The result is a typed subhost of each, including direction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_rim_common_subhost_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (I:Finset V)
    (hinner:∀ x y,x∈I→y∈I→σ (Sum.inl s(x,y))=τ (Sum.inl s(x,y))):
    ∃ D:SimpleGraph V,D≤P ∧
      (∀ x y,D.Adj x y↔P.Adj x y∧σ (Sum.inl s(x,y))≠τ (Sum.inl s(x,y))) ∧
      (∀ x∈I,∀ y∈I,¬D.Adj x y) ∧
      (∀ x,D.degree x=(Finset.univ.filter (fun y=>P.Adj x y∧
        σ (Sum.inl s(x,y))≠τ (Sum.inl s(x,y)))).card) ∧
      (∀ mark x y,markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) mark x y=1 →
        markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ∧
        markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1) :=by
  let D:SimpleGraph V := {
    Adj := fun x y => P.Adj x y∧σ (Sum.inl s(x,y))≠τ (Sum.inl s(x,y))
    symm := ⟨by
      intro x y h
      refine ⟨h.1.symm,?_⟩
      have he:s(y,x)=s(x,y):=Sym2.eq_swap
      rw [he]
      exact h.2⟩
    loopless := ⟨by
      intro x h
      exact P.loopless.irrefl x h.1⟩
  }
  letI : DecidableRel D.Adj := fun x y=>Classical.propDecidable (D.Adj x y)
  refine ⟨D,(fun _ _ h=>h.1),(fun _ _=>Iff.rfl),?_,?_,?_⟩
  · intro x hx y hy h
    exact h.2 (hinner x y hx hy)
  · intro x
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext y
    simp [D,SimpleGraph.mem_neighborFinset]
  · intro mark x y h
    let e:Sym2 V:=s(x,if mark then π y else y)
    have hh:=h
    rw [markedPhysicalRim_eq_one_iff] at hh
    have hp:=hh.2.1
    have hraw:=hh.2.2
    change rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)=_ at hraw
    have hnot:e∉D.edgeFinset:=by
      intro he
      simp only [rawMarkedDeleteRims,he,ite_true] at hraw
      cases hraw
    have heq:σ (Sum.inl e)=τ (Sum.inl e):=by
      by_contra hne
      have hd:D.Adj x (if mark then π y else y):=⟨hp,hne⟩
      exact hnot (by dsimp [e];exact SimpleGraph.mem_edgeFinset.mpr hd)
    have hσ:σ (Sum.inl e)=some (mark,orientationBit x (if mark then π y else y)):=by
      simpa only [rawMarkedDeleteRims,hnot,ite_false] using hraw
    constructor
    · rw [markedPhysicalRim_eq_one_iff]
      exact ⟨hh.1,hp,hσ⟩
    · rw [markedPhysicalRim_eq_one_iff]
      exact ⟨hh.1,hp,heq.symm.trans hσ⟩
end Oberwolfach

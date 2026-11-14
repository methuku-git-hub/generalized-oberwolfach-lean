module

public import Oberwolfach.OrdinaryPhysicalGraphDeletion

@[expose] public section
/-! Pulling the physical root cover into the nonroot domains gives exactly
the induced post-cover rim and spoke relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_cover_deletion_pair (Q D:SimpleGraph V) (H S:V→U→Prop)
    (T:Finset V) (W:Finset U):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let C:=(ordinaryPhysicalGraph D S).comap (φ.sumMap ψ);
    (Q.induce (A:Set V))\C.comap Sum.inl=(Q\D).induce (A:Set V) ∧
    (fun (v:A) (u:B)=>H v.val u.val∧¬C.Adj (Sum.inl v) (Sum.inr u))=
      (fun (v:A) (u:B)=>H v.val u.val∧¬S v.val u.val):=by
  intro A B φ ψ C
  constructor
  · ext v w
    rfl
  · rfl
end Oberwolfach

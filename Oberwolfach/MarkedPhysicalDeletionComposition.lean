module

public import Oberwolfach.MarkedFiniteDeletionDegrees

@[expose] public section

/-! Successive physical deletions have exactly the same outcome and
spoke relation as deleting their union. Retained directions, types and
all other coordinates are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem rawMarkedDeleteRims_union (σ:RawMarkedOutcome V U Γ Color) (A B:Finset (Sym2 V)):
    rawMarkedDeleteRims (rawMarkedDeleteRims σ A) B=rawMarkedDeleteRims σ (A∪B):=by
  funext e
  cases e with
  | inl e=>by_cases ha:e∈A <;> by_cases hb:e∈B <;> simp [rawMarkedDeleteRims,ha,hb]
  | inr e=>rfl

theorem rawMarkedDeleteRims_sup (σ:RawMarkedOutcome V U Γ Color) (A B:SimpleGraph V):
    rawMarkedDeleteRims (rawMarkedDeleteRims σ A.edgeFinset) B.edgeFinset=
      rawMarkedDeleteRims σ (A⊔B).edgeFinset:=by
  rw [rawMarkedDeleteRims_union]
  congr 1
  ext e
  simp only [Finset.mem_union,SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_sup,Set.mem_union]

theorem markedDeletePhysicalSpokes_sup (H:Bool→V→U→Prop) (A B:SimpleGraph (V⊕U)):
    markedDeletePhysicalSpokes (markedDeletePhysicalSpokes H A) B=markedDeletePhysicalSpokes H (A⊔B):=by
  funext j v u
  apply propext
  simp only [markedDeletePhysicalSpokes,SimpleGraph.sup_adj]
  tauto

end Oberwolfach

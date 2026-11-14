module

public import Oberwolfach.ResidualActualFullPhysicalAssembly
public import Oberwolfach.MarkedReservedSpokeFromLabels

@[expose] public section
/-! Preserve the actual reserved spoke resources when the old images,
assigned images and free-image lists avoid their physical vertex labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I K J V:Type} [Fintype I] [DecidableEq I] [DecidableEq K] [DecidableEq J]
  [Fintype V] [DecidableEq V] {X:I → Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_residual_reserved_spokes_from_image_exclusions
    (F:∀i,SimpleGraph (X i)) (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
    (ψ f:∀i,X i → V) (Φ g:∀i,{x // x∈(a i).remaining} → V)
    (Anchors:∀i,Finset {x // x∈(a i).remaining}) (Lists A:I → Finset V)
    (hOldAgree:∀i x,x∈(a i).oldDomain → f i x=ψ i x)
    (hRemAgree:∀i (x:{x // x∈(a i).remaining}),f i x.1=Φ i x)
    (hAnchorAgree:∀i x,x∈Anchors i → Φ i x=g i x)
    (hFree:∀i x,x∉Anchors i → Φ i x∈Lists i)
    (hOldAvoid:∀i x,x∈(a i).oldDomain → ψ i x∉A i)
    (hAnchorAvoid:∀i x,x∈Anchors i → g i x∉A i)
    (hListAvoid:∀i,Disjoint (Lists i) (A i))
    (C:Finset (Finset V⊕(V×I))) (Hold Hnew:Bool → V → I → Prop)
    (Y B:I → Finset V)
    (hMarked:∀v i,Hnew true v i ↔ v∈Y i)
    (hOrdinary:∀v i,Hnew false v i ↔ v∉(Finset.univ.image (f i))∧v∉B i∧v∉Y i)
    (hFixed:∀v i,Sum.inr (v,i)∈C → Hold true v i → v∈Y i)
    (hDisjoint:∀v i,Hold false v i → v∉Y i)
    (hLabel:∀v i,Sum.inr (v,i)∈C → Hold false v i → v∈A i)
    (hBAvoid:∀v i,Sum.inr (v,i)∈C → Hold false v i → v∉B i):
    (∀i,Disjoint (Finset.univ.image (f i)) (A i)) ∧
    (∀b v i,Sum.inr (v,i)∈C → Hold b v i → Hnew b v i) :=by
  have hAvoid:∀i,Disjoint (Finset.univ.image (f i)) (A i):=by
    intro i
    apply Finset.disjoint_left.mpr
    intro v hv hvA
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv
    have hx:x∈(a i).oldDomain ∨ x∈(a i).remaining:=by
      have hu:x∈(a i).oldDomain∪(a i).remaining:=by
        rw [(a i).old_domain_union_remaining (hCycle i)]
        exact Finset.mem_univ _
      exact Finset.mem_union.mp hu
    rcases hx with hx|hx
    · rw [hOldAgree i x hx] at hvA
      exact hOldAvoid i x hx hvA
    · let z:{x // x∈(a i).remaining}:=⟨x,hx⟩
      have heq:f i x=Φ i z:=hRemAgree i z
      by_cases hz:z∈Anchors i
      · rw [heq,hAnchorAgree i z hz] at hvA
        exact hAnchorAvoid i z hz hvA
      · have hmem:Φ i z∈Lists i:=hFree i z hz
        rw [heq] at hvA
        exact (Finset.disjoint_left.mp (hListAvoid i)) hmem hvA
  refine ⟨hAvoid,?_⟩
  apply marked_reserved_spokes_from_label_exclusions C Hold Y (fun i=>Finset.univ.image (f i)) B Hnew
    hMarked hOrdinary hFixed hDisjoint
  intro v i hC hHold
  refine ⟨?_,hBAvoid v i hC hHold⟩
  intro hv
  exact (Finset.disjoint_left.mp (hAvoid i)) hv (hLabel v i hC hHold)
end Oberwolfach

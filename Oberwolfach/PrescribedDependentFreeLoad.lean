module

public import Oberwolfach.PrescribedDependentMaps
public import Oberwolfach.PrescribedFamilyFinish

@[expose] public section
/-! Transfer the actual free-vertex occurrence bound back from the common
source universe to the original family of source vertex types. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

def prescribedDependentFreeVertices (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (A:∀ i,Finset (X i)):Finset (Σ i,X i):=
  Finset.univ.filter (fun z=>z.2∈prescribedDependentVertices pieces z.1 ∧ z.2∉A z.1)

theorem prescribed_dependent_free_load_transfer
    (pieces:∀ i,List (PrescribedSourcePiece (X i))) (A:∀ i,Finset (X i))
    (f:I→(Σ i,X i)→V) (t:ℝ)
    (hload:∀ v,(((prescribedFreeSourceOccurrences
      (prescribedSourceVertices (prescribedLiftDependentPieces Finset.univ.toList pieces))
      (prescribedLiftedSet A)).filter (fun p=>familyVertexImage f p=v)).card:ℝ)≤t):
    ∀ v,(((prescribedDependentFreeVertices pieces A).filter (fun z=>f z.1 z=v)).card:ℝ)≤t := by
  intro v
  let P:Finset (Σ i,X i):=(prescribedDependentFreeVertices pieces A).filter (fun z=>f z.1 z=v)
  let S:Finset (I×(Σ i,X i)):=(prescribedFreeSourceOccurrences
      (prescribedSourceVertices (prescribedLiftDependentPieces Finset.univ.toList pieces))
      (prescribedLiftedSet A)).filter (fun p=>familyVertexImage f p=v)
  let g:(Σ i,X i)→I×(Σ i,X i):=fun z=>(z.1,z)
  have hinj:Function.Injective g:=by intro z w h;exact congrArg Prod.snd h
  have hsub:P.image g⊆S:=by
    intro p hp
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hp
    have hz':z.2∈prescribedDependentVertices pieces z.1 ∧ z.2∉A z.1 ∧ f z.1 z=v:=by
      have hh:=Finset.mem_filter.mp hz
      have hfree:=Finset.mem_filter.mp hh.1
      exact ⟨hfree.2.1,hfree.2.2,hh.2⟩
    apply Finset.mem_filter.mpr
    constructor
    · change (z.1,z)∈Finset.univ.biUnion (fun i=>({i}:Finset I).product
        (prescribedSourceVertices (prescribedLiftDependentPieces Finset.univ.toList pieces) i\prescribedLiftedSet A i))
      apply Finset.mem_biUnion.mpr
      refine ⟨z.1,Finset.mem_univ _,Finset.mem_product.mpr ⟨by simp,?_⟩⟩
      apply Finset.mem_sdiff.mpr
      constructor
      · exact (prescribed_lifted_source_vertex_membership pieces z.1 z.2).mpr hz'.1
      · intro h
        exact hz'.2.1 ((prescribed_lifted_set_membership A z.1 z.2).mp h)
    · exact hz'.2.2
  have hc:(P.card:ℝ)≤(S.card:ℝ):=by
    have hn:P.card≤S.card:=by rw [←Finset.card_image_of_injective P hinj];exact Finset.card_le_card hsub
    exact_mod_cast hn
  exact hc.trans (hload v)
end Oberwolfach

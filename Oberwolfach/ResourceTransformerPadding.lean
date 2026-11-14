module

public import Oberwolfach.ResourceTransformers

@[expose] public section

/-! Remove two decomposable padding graphs from the endpoints of a
transformer, keeping both padding graphs as part of the new transformer. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W:Type*} [DecidableEq E] [DecidableEq W]

theorem resource_transformer_remove_padding (R:W→Finset E) (L L' P P' T:Finset E)
    (hT:IsResourceTransformer R (L∪P) (L'∪P') T)
    (hP:HasResourceDecomposition R P) (hP':HasResourceDecomposition R P')
    (hLP:Disjoint L P) (hLP':Disjoint L P')
    (hL'P:Disjoint L' P) (hL'P':Disjoint L' P') (hPP:Disjoint P P'):
    IsResourceTransformer R L L' (T∪P∪P'):=by
  have hTL:=Finset.disjoint_union_right.mp hT.1
  have hTL':=Finset.disjoint_union_right.mp hT.2.1
  refine ⟨?_,?_,?_,?_⟩
  · exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hTL.1,hLP.symm⟩,hLP'.symm⟩
  · exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hTL'.1,hL'P.symm⟩,hL'P'.symm⟩
  · have hd:Disjoint (T∪(L∪P)) P':=Finset.disjoint_union_left.mpr
      ⟨hTL'.2,Finset.disjoint_union_left.mpr ⟨hLP',hPP⟩⟩
    have hh:=resource_decomposition_union R _ _ hT.2.2.1 hP' hd
    convert hh using 1 <;> ext e <;> simp only [Finset.mem_union] <;> tauto
  · have hd:Disjoint (T∪(L'∪P')) P:=Finset.disjoint_union_left.mpr
      ⟨hTL.2,Finset.disjoint_union_left.mpr ⟨hL'P,hPP.symm⟩⟩
    have hh:=resource_decomposition_union R _ _ hT.2.2.2 hP hd
    convert hh using 1 <;> ext e <;> simp only [Finset.mem_union] <;> tauto

end Oberwolfach

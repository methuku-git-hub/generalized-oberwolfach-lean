module

public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.MarkedDecompositionPackingBridge
public import Oberwolfach.MarkedPhysicalHostGraph

@[expose] public section
/-! The full finite residual resource set used by the level chain is the
same target used by the fixed-factor reconstruction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem marked_finite_resources_univ_eq_decomposition_target
    {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U]
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (H₀ HK:V→U→Prop):
    markedFiniteResources tail head ktail khead π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2))=
    markedDecompositionTarget (markedPhysicalRimSet tail head ktail khead π) H₀ HK :=by
  simp only [markedFiniteResources,markedDecompositionTarget,markedPhysicalRimSet,Finset.image_image,Function.comp_def]
end Oberwolfach

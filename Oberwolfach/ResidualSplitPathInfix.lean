module

public import Oberwolfach.ResidualSplitPathStructure

@[expose] public section
/-! Every retained path block is a contiguous part of the original
ordered path and inherits its direction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem split_path_block_infix (H:SimpleGraph V) (xs block:List V)
    (hblock:block∈splitPathByGraph H xs):block <:+: xs := by
  have hh:=List.infix_of_mem_flatten hblock
  simpa [splitPathByGraph,split_ordered_path_flatten] using hh

theorem split_path_preserves_chain (H:SimpleGraph V) (D:V→V→Prop)
    (xs:List V) (hchain:List.IsChain D xs):
    ∀ block∈splitPathByGraph H xs,List.IsChain D block := by
  intro block hblock
  exact hchain.infix (split_path_block_infix H xs block hblock)
end Oberwolfach

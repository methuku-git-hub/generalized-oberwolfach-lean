module

public import Oberwolfach.OrdinaryTransferConfigurations

@[expose] public section
/-! The fixed transfer cycles commute with injective changes of vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem transfer_cycle_graph_embedding {A V:Type} {r:ℕ} (hr:0<r)
    (f:(Fin r×Fin r)↪A) (v:A) (hv:v∉Set.range f) (φ:A↪V)
    (hφ:φ v∉Set.range (f.trans φ)) (j:TransferCycleIndex r):
    (transferCycleGraph hr f v hv j).map φ=
      transferCycleGraph hr (f.trans φ) (φ v) hφ j:=by
  rcases j with ⟨⟩|⟨i,b⟩
  · simp only [transferCycleGraph,SimpleGraph.map_map]
    congr 1
  · cases b
    · simp only [transferCycleGraph,SimpleGraph.map_map]
      congr 1
    · simp only [transferCycleGraph,SimpleGraph.map_map]
      congr 1
      ext j
      change φ (if j=⟨0,hr⟩ then v else f (i,j))=(if j=⟨0,hr⟩ then φ v else φ (f (i,j)))
      split_ifs <;> rfl
end Oberwolfach

module

public import Oberwolfach.SelectedBufferedPathRestriction
public import Oberwolfach.MarkedPhysicalHostContainment

@[expose] public section
/-! The selected final-path map takes its source edges to the original host. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_marked_path_map_lifts_to_host
    {V E K X I:Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype K]
    [Fintype I] [DecidableEq I] [DecidableEq X]
    (H:SimpleGraph V) (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hE:∀e,H.Adj (tail e) (head e)) (hK:∀e,H.Adj (ktail e) (π (khead e)))
    (F:SimpleGraph X) (S:Finset I) (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (f:{x // x∈bufferedPathFullDomain n inner}↪V)
    (hmap:∀x y,F.Adj x.val y.val→
      (physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)).Adj (f x) (f y)) :
    ∀x y,F.Adj x.val y.val→H.Adj (restrictBufferedPathMap S n inner f x) (restrictBufferedPathMap S n inner f y) := by
  intro x y hxy
  apply marked_physical_host_graph_le H tail head ktail khead π hE hK
  exact (selected_buffered_path_map_graph_and_edges F
    (physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)) S n inner f hmap).1 x y hxy
end Oberwolfach

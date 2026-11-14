module

public import Oberwolfach.OrdinaryLocalFactorHostTransfer
public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! A hub factor whose physical rim avoids the deletion survives in the
actual remaining rim host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem local_ordinary_factor_graph_subhost
    (Q F:SimpleGraph V) (T:Finset V) (r:ℕ) (M:Finset (LocalOrdinaryCycle Q F T r)):
    localOrdinaryFactorGraph M≤Q:=by
  intro v w h
  obtain ⟨C,hC,hCvw⟩:=(localOrdinaryFactorGraph_adj M v w).mp h
  exact C.val.property hCvw

theorem local_ordinary_factor_graph_survives_physical_deletion
    (Q Q' F:SimpleGraph V) (K:SimpleGraph (V⊕U)) (T:Finset V) (r:ℕ)
    (M:Finset (LocalOrdinaryCycle Q F T r))
    (havoid:Disjoint ((localOrdinaryFactorGraph M).map (Function.Embedding.inl:V↪V⊕U)) K)
    (hkeep:Q\K.comap Sum.inl≤Q'):
    localOrdinaryFactorGraph M≤Q':=by
  have havoid':Disjoint (localOrdinaryFactorGraph M) (K.comap Sum.inl):=by
    rw [graph_map_inl_physical] at havoid
    apply disjoint_iff_inf_le.mpr
    intro v w h
    exact (disjoint_iff_inf_le.mp havoid) (v:=Sum.inl v) (w:=Sum.inl w) ⟨h.1,h.2⟩
  apply le_trans _ hkeep
  intro v w h
  refine ⟨local_ordinary_factor_graph_subhost Q F T r M h,?_⟩
  intro hk
  exact (disjoint_iff_inf_le.mp havoid') (v:=v) (w:=w) ⟨h,hk⟩
end Oberwolfach

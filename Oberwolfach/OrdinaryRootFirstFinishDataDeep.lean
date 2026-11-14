module

public import Oberwolfach.OrdinaryRootFirstDeepFinishData
public import Oberwolfach.OrdinaryDeepBlockerLeStar

@[expose] public section
/-! A finish avoiding the deeper root star also avoids the deeper block. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinary_root_first_finish_data_deep
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ) (limit:ℝ)
    (E:OrdinaryRootFirstFinishData Q F H X T Z W r η ell t ν D σ O limit):
    OrdinaryRootFirstDeepFinishData Q F H X T Z W r η ell t ν D σ O limit :=
  ⟨E.rim,E.spokes,E.rim_sub,E.spoke_sub,E.host_decomposition,E.decomposition,E.rim_inside,E.spoke_inside,
    E.inner_degree,E.avoids_star.mono_right (ordinary_deep_blocker_le_root_star T W)⟩
end Oberwolfach

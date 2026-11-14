module

public import Oberwolfach.OrdinaryRootCoverNonrootData
public import Oberwolfach.OrdinaryProtectedDeepMonotonicity

@[expose] public section
/-! Restrict the protected roots without changing the chosen cover.  The
nonroot degree assertion needs an additional bound on the newly exposed roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinary_root_cover_restrict_roots
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T Tplus:Finset V) (Z W Wplus:Finset U)
    (r:ℕ) (η ell:ℝ) (hT:T⊆Tplus) (hW:W⊆Wplus)
    (D:OrdinaryRootCoverData Q F H X Tplus Z Wplus r η ell):
    OrdinaryRootCoverData Q F H X T Z W r η ell where
  rim:=D.rim
  spokes:=D.spokes
  rim_sub:=D.rim_sub
  spoke_sub:=D.spoke_sub
  host_decomposition:=D.host_decomposition
  decomposition:=D.decomposition
  inner_degree:=D.inner_degree
  outside_degree:=D.outside_degree
  avoids_deep:=D.avoids_deep.mono_right (ordinary_deep_blocker_mono T Tplus W Wplus hT hW)
  covers_rim:=fun v hv w hw h=>D.covers_rim v (hT hv) w hw h
  covers_row:=fun v hv u hu h=>D.covers_row v (hT hv) u hu h
  covers_column:=fun u hu v hv h=>D.covers_column u (hW hu) v hv h

def ordinary_nonroot_cover_restrict_roots
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T Tplus:Finset V) (Z W Wplus:Finset U)
    (r:ℕ) (η ell:ℝ) (hT:T⊆Tplus) (hW:W⊆Wplus)
    (D:OrdinaryRootCoverNonrootData Q F H X Tplus Z Wplus r η ell)
    (hnew:∀w∈ordinaryInnerVertices Tplus Wplus,w∉ordinaryInnerVertices T W→
      ((ordinaryPhysicalGraph D.rim D.spokes).degree w:ℝ)≤ell):
    OrdinaryRootCoverNonrootData Q F H X T Z W r η ell where
  toOrdinaryRootCoverData:=ordinary_root_cover_restrict_roots Q F H X T Tplus Z W Wplus r η ell hT hW D.toOrdinaryRootCoverData
  nonroot_degree:=by
    intro w hw
    by_cases h:w∈ordinaryInnerVertices Tplus Wplus
    · exact hnew w h hw
    · exact D.nonroot_degree w h
end Oberwolfach

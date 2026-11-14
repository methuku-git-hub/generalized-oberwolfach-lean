module

public import Oberwolfach.PrescribedEdgeWheels
public import Oberwolfach.SparsePathDeletion
public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section

/-! Completion of one prescribed rim edge after realised rim deletions.
Old spoke endpoints are explicitly forbidden in the free part. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_rim_edge_wheel_after_deletion (Q D F:SimpleGraph V) (H:V→U→Prop)
    (A W:Finset V) (x y:V) (u:U) (hxy:Q.Adj x y) (hDxy:¬D.Adj x y) (hFxy:¬F.Adj x y)
    (hHx:H x u) (hHy:H y u) (hHA:∀ a∈A,H a u)
    (r:ℕ) (hr:3≤r) (L d b:ℝ) (hL:0≤L)
    (hF:∀ a,(F.degree a:ℝ)≤L) (hD:∀ a,(D.degree a:ℝ)≤d)
    (hcount:∀ a c,b≤((A∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hbudget:W.card+((r:ℝ)+2)*(L+1)+2*d<b) :
    ∃ C:OrdinaryWheel Q F H r,ordinaryWheelHub C=u ∧
      (ordinaryWheelRim C).Adj x y ∧ Disjoint (ordinaryWheelRim C) D ∧
      (∀ a∈(ordinaryWheelRim C).support,a=x ∨ a=y ∨ a∈A∧a∉W) :=by
  have hc (a c:V):b-2*d≤((A∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c).card:ℝ):=by
    have h:((A∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)≤
      (A∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c).card+D.degree a+D.degree c:=by
      exact_mod_cast two_common_neighbours_after_deletion Q D A a c
    linarith only [h,hD a,hD c,hcount a c]
  obtain ⟨C,hCu,hCxy,hCs⟩:=ordinary_rim_edge_wheel_from_common_counts (Q\D) F H A W x y u
    ⟨hxy,hDxy⟩ hFxy hHx hHy hHA r hr L (b-2*d) hL hF (by intro a c; convert hc a c using 1 <;> congr!) (by linarith only [hbudget])
  refine ⟨ordinaryWheelInclude sdiff_le C,hCu,hCxy,?_,hCs⟩
  apply disjoint_iff_inf_le.mpr
  intro a c hac
  exact ((C.val.1.property hac.1).2 hac.2).elim

end Oberwolfach

module

public import Oberwolfach.OrdinaryLocalDeletion
public import Oberwolfach.EndpointRelativeCounts

@[expose] public section

/-! Deletion costs for mixed rim/spoke common neighbourhoods, measured
against the original fixed row domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem common_graphs_comm (Q H:SimpleGraph V) (A X J:Finset V) :
    common (common A X (fun v=>Q.neighborFinset v)) J (fun v=>H.neighborFinset v)=
      common (common A J (fun v=>H.neighborFinset v)) X (fun v=>Q.neighborFinset v) := by
  ext v
  simp only [mem_common_iff]
  tauto

theorem mixed_common_sdiff_bound (Q H D E:SimpleGraph V) (A X J:Finset V) (L:ℝ)
    (hD:∀ v,(D.degree v:ℝ)≤L) (hE:∀ v,(E.degree v:ℝ)≤L) :
    |((common (common A X (fun v=>(Q\D).neighborFinset v)) J
      (fun v=>(H\E).neighborFinset v)).card:ℝ)-
      ((common (common A X (fun v=>Q.neighborFinset v)) J (fun v=>H.neighborFinset v)).card:ℝ)|≤
        (X.card+J.card:ℕ)*L := by
  have h₁:=ordinary_common_sdiff_bound H E (common A X (fun v=>(Q\D).neighborFinset v)) J L hE
  have h₂:=ordinary_common_sdiff_bound Q D (common A J (fun v=>H.neighborFinset v)) X L hD
  have h₂' : |((common (common A X (fun v=>(Q\D).neighborFinset v)) J
      (fun v=>H.neighborFinset v)).card:ℝ)-
      ((common (common A X (fun v=>Q.neighborFinset v)) J (fun v=>H.neighborFinset v)).card:ℝ)|≤X.card*L:=by
    convert h₂ using 2 <;> simp [common,Finset.filter_filter,and_comm,and_left_comm,and_assoc]
  have hh:=abs_sub_le
    (((common (common A X (fun v=>(Q\D).neighborFinset v)) J (fun v=>(H\E).neighborFinset v)).card):ℝ)
    (((common (common A X (fun v=>(Q\D).neighborFinset v)) J (fun v=>H.neighborFinset v)).card):ℝ)
    (((common (common A X (fun v=>Q.neighborFinset v)) J (fun v=>H.neighborFinset v)).card):ℝ)
  push_cast
  nlinarith only [h₁,h₂',hh]

end Oberwolfach

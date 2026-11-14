module

public import Oberwolfach.EndpointDeepCountInputs
public import Oberwolfach.FixedHubDomainCounts

@[expose] public section
/-! Three-root row counts survive the original bounded symmetric edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_row_counts_stability (P R Q F:SimpleGraph V) (H J:V→U→Prop)
    (A:Finset V) (B:Finset U) (pR pH t L ε:ℝ) (hpR:0≤pR) (hpH:0≤pH) (hL:0≤L)
    (hbudget:t+4*L≤ε*A.card)
    (hQ:∀v,((changed (A∩R.neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤L)
    (hJ:∀u∈B,((changed (A∩Finset.univ.filter (fun v=>H v u))
      (A∩Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L)
    (hbase:∀S:Finset V,∀T:Finset U,T⊆B→S.card≤3→T.card≤2→S.card+T.card≤4→
      |((common (common A S (fun v=>R.neighborFinset v)) T
        (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
        pR^S.card*pH^T.card*(common A S (fun v=>P.neighborFinset v)).card|≤t):
    ∀S:Finset V,∀T:Finset U,T⊆B→S.card≤3→T.card≤2→S.card+T.card≤4→
      pR^S.card*pH^T.card*(common A S (fun v=>(P\F).neighborFinset v)).card-ε*A.card≤
        ((common (common A S (fun v=>Q.neighborFinset v)) T
          (fun u=>Finset.univ.filter (fun v=>J v u))).card:ℝ):=by
  intro S T hTB hS hT hST
  have hnew:=fixed_domain_mixed_target_stability A S T
    (fun v=>R.neighborFinset v) (fun v=>Q.neighborFinset v)
    (fun u=>Finset.univ.filter (fun v=>H v u)) (fun u=>Finset.univ.filter (fun v=>J v u)) L L
    (pR^S.card*pH^T.card*(common A S (fun v=>P.neighborFinset v)).card) t
    (fun v _=>hQ v) (fun u hu=>hJ u (hTB hu)) (hbase S T hTB hS hT hST)
  have hsum:(S.card:ℝ)*L+T.card*L≤4*L:=by
    have hc:((S.card:ℝ)+(T.card:ℝ))≤4:=by exact_mod_cast hST
    nlinarith [mul_le_mul_of_nonneg_right hc hL]
  have hsub:common A S (fun v=>(P\F).neighborFinset v)⊆common A S (fun v=>P.neighborFinset v):=by
    intro z hz
    have hh:=(mem_common_iff _ _ _ _).mp hz
    exact (mem_common_iff _ _ _ _).mpr ⟨hh.1,fun v hv=>
      (P.mem_neighborFinset v z).mpr (((P\F).mem_neighborFinset v z).mp (hh.2 v hv)).1⟩
  have hscale:=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub))
    (show 0≤pR^S.card*pH^T.card by positivity)
  linarith only [(abs_le.mp hnew).1,hsum,hscale,hbudget]
end Oberwolfach

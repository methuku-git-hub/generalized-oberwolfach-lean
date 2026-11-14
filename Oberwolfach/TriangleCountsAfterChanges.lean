module

public import Oberwolfach.TriangleCountsAfterDeletion
public import Oberwolfach.FixedHubDomainCounts

@[expose] public section
/-! Triangle common-neighbour estimates remain valid under bounded symmetric
edits, including new rim edges and new spoke edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem triangle_relative_counts_after_changes (P R H F Q J:SimpleGraph V) (A B Y:Finset V)
    (hAY:A⊆Y) (pR pH ε ε' L:ℝ) (hpR:0≤pR) (hpH:0≤pH) (hL:0≤L)
    (hrowbudget:ε*A.card+7*L≤ε'*A.card) (hindexbudget:ε*B.card+3*L≤ε'*B.card)
    (hF:∀v,(F.degree v:ℝ)≤L)
    (hQ:∀v,((changed (A∩(R\F).neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤L)
    (hHr:∀v,((changed (B∩H.neighborFinset v) (B∩J.neighborFinset v)).card:ℝ)≤L)
    (hHc:∀u∈B,((changed (A∩H.neighborFinset u) (A∩J.neighborFinset u)).card:ℝ)≤L)
    (hrow:∀ S T:Finset V,S⊆Y→T⊆B→S.card≤3→T.card≤2→S.card+T.card≤4→
      |((common (common A S (fun v=>R.neighborFinset v)) T (fun u=>H.neighborFinset u)).card:ℝ)-
        pR^S.card*pH^T.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card)
    (hindex:∀ S:Finset V,S⊆Y→S.card≤3→(∀v∈S,∀w∈S,¬F.Adj v w)→
      |((common B S (fun v=>H.neighborFinset v)).card:ℝ)-pH^S.card*B.card|≤ε*B.card):
    (∀ S T:Finset V,S⊆Y→T⊆B→S.card≤3→T.card≤2→S.card+T.card≤4→
      pR^S.card*pH^T.card*(common A S (fun v=>(P\spanningRestriction F Y).neighborFinset v)).card-ε'*A.card≤
        ((common (common A S (fun v=>Q.neighborFinset v)) T (fun u=>J.neighborFinset u)).card:ℝ)) ∧
    (∀ S:Finset V,S⊆Y→S.card≤3→(∀v∈S,∀w∈S,¬(spanningRestriction F Y).Adj v w)→
      (pH^S.card-ε')*B.card≤((common B S (fun v=>J.neighborFinset v)).card:ℝ)):=by
  constructor
  · intro S T hSY hTB hSc hTc hST
    have hfirst:|((common (common A S (fun v=>(R\F).neighborFinset v)) T (fun u=>H.neighborFinset u)).card:ℝ)-
        ((common (common A S (fun v=>R.neighborFinset v)) T (fun u=>H.neighborFinset u)).card:ℝ)|≤3*L:=by
      have hh:=ordinary_common_sdiff_bound R F (common A T (fun u=>H.neighborFinset u)) S L hF
      have hh':|((common (common A S (fun v=>(R\F).neighborFinset v)) T (fun u=>H.neighborFinset u)).card:ℝ)-
          ((common (common A S (fun v=>R.neighborFinset v)) T (fun u=>H.neighborFinset u)).card:ℝ)|≤S.card*L:=by
        convert hh using 2 <;> simp [common,Finset.filter_filter,and_comm,and_left_comm,and_assoc]
      exact hh'.trans (mul_le_mul_of_nonneg_right (show (S.card:ℝ)≤3 by exact_mod_cast hSc) hL)
    have hbase:|((common (common A S (fun v=>(R\F).neighborFinset v)) T (fun u=>H.neighborFinset u)).card:ℝ)-
        pR^S.card*pH^T.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card+3*L:=by
      have hh:=abs_sub_le
        ((common (common A S (fun v=>(R\F).neighborFinset v)) T (fun u=>H.neighborFinset u)).card:ℝ)
        ((common (common A S (fun v=>R.neighborFinset v)) T (fun u=>H.neighborFinset u)).card:ℝ)
        (pR^S.card*pH^T.card*(common A S (fun v=>P.neighborFinset v)).card)
      linarith [hrow S T hSY hTB hSc hTc hST]
    have hnew:=fixed_domain_mixed_target_stability A S T
      (fun v=>(R\F).neighborFinset v) (fun v=>Q.neighborFinset v)
      (fun u=>H.neighborFinset u) (fun u=>J.neighborFinset u)
      L L (pR^S.card*pH^T.card*(common A S (fun v=>P.neighborFinset v)).card) (ε*A.card+3*L)
      (fun v _=>hQ v) (fun u hu=>hHc u (hTB hu)) hbase
    have hmul:(S.card:ℝ)*L+(T.card:ℝ)*L≤4*L:=by
      have hh:((S.card:ℝ)+(T.card:ℝ))≤4:=by exact_mod_cast hST
      nlinarith [mul_le_mul_of_nonneg_right hh hL]
    have hsub:common A S (fun v=>(P\spanningRestriction F Y).neighborFinset v)⊆common A S (fun v=>P.neighborFinset v):=by
      intro z hz
      have hh:=(mem_common_iff _ _ _ _).mp hz
      exact (mem_common_iff _ _ _ _).mpr ⟨hh.1,fun v hv=>(P.mem_neighborFinset v z).mpr (((P\spanningRestriction F Y).mem_neighborFinset v z).mp (hh.2 v hv)).1⟩
    have ht:=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub))
      (show 0≤pR^S.card*pH^T.card by positivity)
    linarith only [(abs_le.mp hnew).1,hmul,ht,hrowbudget]
  · intro S hSY hSc hI
    have hI':∀v∈S,∀w∈S,¬F.Adj v w:=by
      intro v hv w hw hf
      exact hI v hv w hw ((spanningRestriction_adj F Y v w).mpr ⟨hf,hSY hv,hSY hw⟩)
    have hnew:=target_stability (fixed_domain_neighbourhood_stability B S
      (fun v=>H.neighborFinset v) (fun v=>J.neighborFinset v) L (fun v _=>hHr v))
      (hindex S hSY hSc hI')
    have hm:(S.card:ℝ)*L≤3*L:=mul_le_mul_of_nonneg_right (by exact_mod_cast hSc) hL
    nlinarith only [(abs_le.mp hnew).1,hm,hindexbudget]
end Oberwolfach

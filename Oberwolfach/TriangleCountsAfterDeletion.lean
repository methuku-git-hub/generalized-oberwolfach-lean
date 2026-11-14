module

public import Oberwolfach.MixedGraphDeletionCounts
public import Oberwolfach.EndpointConflictRestriction

@[expose] public section

/-! The actual three-rim/two-spoke triangle tests after conflict deletion
and a later bounded deletion. Losses are charged at the original domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem triangle_relative_counts_after_deletion (P R H F D E:SimpleGraph V) (A B Y:Finset V)
    (hAY:A⊆Y) (pR pH ε ε' L:ℝ) (hpR:0≤pR) (hpH:0≤pH) (hL:0≤L)
    (hrowbudget:ε*A.card+7*L≤ε'*A.card) (hindexbudget:ε*B.card+3*L≤ε'*B.card)
    (hF:∀ v,(F.degree v:ℝ)≤L) (hD:∀ v,(D.degree v:ℝ)≤L) (hE:∀ v,(E.degree v:ℝ)≤L)
    (hrow:∀ S J:Finset V,S⊆Y → J⊆B → S.card≤3 → J.card≤2 → S.card+J.card≤4 →
      |((common (common A S (fun v=>R.neighborFinset v)) J (fun u=>H.neighborFinset u)).card:ℝ)-
        pR^S.card*pH^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card)
    (hindex:∀ S:Finset V,S⊆Y → S.card≤3 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
      |((common B S (fun v=>H.neighborFinset v)).card:ℝ)-pH^S.card*B.card|≤ε*B.card):
    (∀ S J:Finset V,S⊆Y → J⊆B → S.card≤3 → J.card≤2 → S.card+J.card≤4 →
      pR^S.card*pH^J.card*(common A S (fun v=>(P\spanningRestriction F Y).neighborFinset v)).card-ε'*A.card≤
        ((common (common A S (fun v=>((R\F)\D).neighborFinset v)) J (fun u=>(H\E).neighborFinset u)).card:ℝ)) ∧
    (∀ S:Finset V,S⊆Y → S.card≤3 → (∀ v∈S,∀ w∈S,¬(spanningRestriction F Y).Adj v w) →
      (pH^S.card-ε')*B.card≤((common B S (fun v=>(H\E).neighborFinset v)).card:ℝ)):=by
  constructor
  · intro S J hSY hJB hS hJ hSJ
    have h₂:=mixed_common_sdiff_bound (R\F) H D E A S J L hD hE
    have h₀:=hrow S J hSY hJB hS hJ hSJ
    have hfirst:|((common (common A S (fun v=>(R\F).neighborFinset v)) J (fun u=>H.neighborFinset u)).card:ℝ)-
        ((common (common A S (fun v=>R.neighborFinset v)) J (fun u=>H.neighborFinset u)).card:ℝ)|≤3*L:=by
      have hh:=ordinary_common_sdiff_bound R F (common A J (fun u=>H.neighborFinset u)) S L hF
      have hh':|((common (common A S (fun v=>(R\F).neighborFinset v)) J (fun u=>H.neighborFinset u)).card:ℝ)-
          ((common (common A S (fun v=>R.neighborFinset v)) J (fun u=>H.neighborFinset u)).card:ℝ)|≤S.card*L:=by
        convert hh using 2 <;> simp [common,Finset.filter_filter,and_comm,and_left_comm,and_assoc]
      exact hh'.trans (mul_le_mul_of_nonneg_right (show (S.card:ℝ)≤3 by exact_mod_cast hS) hL)
    have hsecond:=h₂.trans (mul_le_mul_of_nonneg_right (show ((S.card+J.card:ℕ):ℝ)≤4 by exact_mod_cast hSJ) hL)
    have hsub:common A S (fun v=>(P\spanningRestriction F Y).neighborFinset v)⊆
        common A S (fun v=>P.neighborFinset v):=by
      intro z hz
      have hh:=(mem_common_iff _ _ _ _).mp hz
      exact (mem_common_iff _ _ _ _).mpr ⟨hh.1,fun v hv=>(P.mem_neighborFinset v z).mpr (((P\spanningRestriction F Y).mem_neighborFinset v z).mp (hh.2 v hv)).1⟩
    have ht:=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub))
      (show 0≤pR^S.card*pH^J.card by positivity)
    have hsecond':|((common (common A S (fun v=>((R\F)\D).neighborFinset v)) J (fun u=>(H\E).neighborFinset u)).card:ℝ)-
        ((common (common A S (fun v=>(R\F).neighborFinset v)) J (fun u=>H.neighborFinset u)).card:ℝ)|≤4*L:=by
      convert hsecond using 1 <;> congr!
    have hlast:pR^S.card*pH^J.card*(common A S (fun v=>(P\spanningRestriction F Y).neighborFinset v)).card-ε'*A.card≤
        ((common (common A S (fun v=>((R\F)\D).neighborFinset v)) J (fun u=>(H\E).neighborFinset u)).card:ℝ):=by
      linarith only [(abs_le.mp hfirst).1,(abs_le.mp hsecond').1,(abs_le.mp h₀).1,ht,hrowbudget]
    convert hlast using 1 <;> congr!
  · intro S hSY hS hI
    have hI':∀ v∈S,∀ w∈S,¬F.Adj v w:=by
      intro v hv w hw hf
      exact hI v hv w hw ((spanningRestriction_adj F Y v w).mpr ⟨hf,hSY hv,hSY hw⟩)
    have h₀:=hindex S hSY hS hI'
    have hh:=(ordinary_common_sdiff_bound H E B S L hE).trans
      (mul_le_mul_of_nonneg_right (show (S.card:ℝ)≤3 by exact_mod_cast hS) hL)
    nlinarith only [(abs_le.mp h₀).1,(abs_le.mp hh).1,hindexbudget]

end Oberwolfach

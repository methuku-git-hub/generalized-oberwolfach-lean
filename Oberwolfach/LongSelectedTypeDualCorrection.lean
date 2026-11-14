module

public import Oberwolfach.LongEligibleForbiddenIncoming
public import Oberwolfach.MarkedCorrectionFromCandidateBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V]
local instance selectedTypeDualDecEq : DecidableEq V := Classical.decEq V
local instance selectedTypeDualArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=reservedCandidateArcDecEq P

theorem long_selected_types_dual_eligible_correction
    (P:V×V→Prop) (G Bad:SimpleGraph V) (Ord Mark Eligible:V×V→Prop) (hEquiv:∀e,Eligible e ↔ Ord e ∧ Mark e)
    (hhost:∀e,P e→G.Adj e.1 e.2) (hbad:∀x y,G.Adj x y→¬Eligible (x,y)→Bad.Adj x y)
    (S₀ S₁ T₁:Finset {e:V×V // P e}) (hMarked:∀e∈T₁,Mark e.val) (hForced:∀e,¬Ord e.val→e∈T₁) (I:Finset V)
    (C:Finset (Finset V⊕(V×U))) (b:ℕ) (rho eta:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (h₀:S₀⊆Finset.univ\T₁) (h₁:S₁⊆T₁)
    (hdev:∀v,|(directedInCount P T₁ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (base₀ base₁:V→ℝ) (Lbad:ℝ) (hBad:∀v,(Bad.degree v:ℝ)≤Lbad)
    (hbase₀:∀v,base₀ v≤(S₀.filter (fun e=>e.val.2=v)).card)
    (hbase₁:∀v,base₁ v≤(S₁.filter (fun e=>e.val.2=v)).card)
    (hmargin₀:∀v,rho*Fintype.card V≤base₀ v-I.card-C.card-Lbad)
    (hmargin₁:∀v,rho*Fintype.card V≤base₁ v-I.card-C.card-Lbad):
    ∃M:Finset {e:V×V // P e},
      (∀v,directedInCount P M v=b) ∧
      (∀e∈M,Mark e.val) ∧ (∀e,e∉M→Ord e.val) ∧
      (∀e,e.val.1∈I→(e∈M↔e∈T₁)) ∧
      (∀e,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→(e∈M↔e∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*Fintype.card V+(Fintype.card V:ℝ)^(3/5:ℝ)) :=by
  let T₀:Finset {e:V×V // P e}:=Finset.univ\T₁
  let F:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>e.val.1∈I ∨ Sum.inl ({e.val.1,e.val.2}:Finset V)∈C ∨ ¬Eligible e.val)
  have hdis:Disjoint T₀ T₁:=by
    apply Finset.disjoint_left.mpr
    intro e he he1
    exact (Finset.mem_sdiff.mp he).2 he1
  have hdiff₀:S₀\T₀⊆(∅:Finset {e:V×V // P e}):=by
    intro e he;exact False.elim ((Finset.mem_sdiff.mp he).2 (h₀ (Finset.mem_sdiff.mp he).1))
  have hdiff₁:S₁\T₁⊆(∅:Finset {e:V×V // P e}):=by
    intro e he;exact False.elim ((Finset.mem_sdiff.mp he).2 (h₁ (Finset.mem_sdiff.mp he).1))
  have hforbid:=long_eligible_forbidden_incoming P G Bad Eligible hhost hbad I C
  have hprot:∀e,({e.val.1,e.val.2}:Finset V)∈markedReservedRimPairs C→e∈F:=by
    intro e he;exact hforbid.2.1 e ((marked_reserved_rim_pairs_membership C _).mp he)
  have hh:=marked_correction_from_candidate_bounds (P:=P) S₀ S₁ T₀ T₁ ∅ ∅ F (markedReservedRimPairs C)
    b rho eta hrho heta hetaR hdis hdiff₀ hdiff₁ hprot hdev base₀ base₁ (fun _=>0) (fun _=>0)
    (fun _=>(I.card:ℝ)+C.card+Lbad) hbase₀ hbase₁ (by simp) (by simp)
    (by intro v;linarith only [hforbid.2.2.2 v,hBad v])
    (by intro v;linarith only [hmargin₀ v]) (by intro v;linarith only [hmargin₁ v])
  obtain ⟨M,hM,hA,hC,hbound⟩:=hh
  refine ⟨M,hM,?_,?_,?_,?_,hbound⟩
  · intro e he
    by_cases hf:Eligible e.val
    · exact ((hEquiv e.val).mp hf).2
    · have heF:=hforbid.2.2.1 e hf
      have hnot:e∉symmDiff M T₁:=by intro ht;exact (Finset.mem_sdiff.mp (hA ht)).2 heF
      have heT:e∈T₁:=by
        simp only [Finset.mem_symmDiff] at hnot
        tauto
      exact hMarked e heT
  · intro e he
    by_contra hn
    have heT:=hForced e hn
    have hf:¬Eligible e.val:=fun h=>hn ((hEquiv e.val).mp h).1
    have heF:=hforbid.2.2.1 e hf
    have hnot:e∉symmDiff M T₁:=by intro ht;exact (Finset.mem_sdiff.mp (hA ht)).2 heF
    simp only [Finset.mem_symmDiff] at hnot
    tauto
  · intro e he
    have hn:e∉symmDiff M T₁:=by
      intro he'
      exact (Finset.mem_sdiff.mp (hA he')).2 (hforbid.1 e he)
    simp only [Finset.mem_symmDiff] at hn
    tauto
  · intro e he
    exact hC e ((marked_reserved_rim_pairs_membership C _).mpr he)
end Oberwolfach

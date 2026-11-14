module

public import Oberwolfach.LongSelectedMarkedSampleBalance
public import Oberwolfach.MarkedCandidateIncomingPerturbation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance sampleProtectedCorrectionFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance sampleProtectedCorrectionArc (n:ℕ) (P:(Fin n)×(Fin n)→Prop):DecidableEq {e:(Fin n)×(Fin n) // P e}:=reservedCandidateArcDecEq P

theorem long_sample_protected_marked_correction
    {n d D m:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (G:SimpleGraph (Fin n)) (hreg:G.IsRegularOfDegree D) (hD:0<D) (hd:0<d) (hm:0<m)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (ω:Sym2 (Fin n)→Fin 6×Bool) (q:U→Bool→ℝ) (s p p₂ k₂ u err:ℝ) (herr:0≤err)
    (hq:∀w,q w false=s/(m:ℝ))
    (hstarts:∀v,|((rawStartHubSet π d σ false v).card:ℝ)-(∑w,q w false/(d:ℝ))|≤err)
    (hheads:∀v,|((∑x,sampledColourOrientation G ω 1 x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability p (initialIndexDensity U D*(s/(m:ℝ))/2) p₂ k₂ u 1/2*G.degree v|≤err)
    (P:(Fin n)×(Fin n)→Prop) (S₀ S₁ T₀ T₁ B₀ B₁:Finset {e:(Fin n)×(Fin n) // P e})
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (rho eta loss:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hchange:∀v,((changed (markedRawIncomingTails G ω v) (markedCandidateIncomingTails P T₁ v)).card:ℝ)≤loss)
    (hbudget:err+(d:ℝ)*err+loss≤eta*n)
    (hdis:Disjoint T₀ T₁) (h₀:S₀\T₀⊆B₀) (h₁:S₁\T₁⊆B₁)
    (base₀ base₁ loss₀ loss₁:Fin n→ℝ)
    (hbase₀:∀v,base₀ v≤(S₀.filter (fun e=>e.val.2=v)).card)
    (hbase₁:∀v,base₁ v≤(S₁.filter (fun e=>e.val.2=v)).card)
    (hloss₀:∀v,((B₀.filter (fun e=>e.val.2=v)).card:ℝ)≤loss₀ v)
    (hloss₁:∀v,((B₁.filter (fun e=>e.val.2=v)).card:ℝ)≤loss₁ v)
    (hmargin₀:∀v,rho*n≤base₀ v-loss₀ v-C.card)
    (hmargin₁:∀v,rho*n≤base₁ v-loss₁ v-C.card):
    let F:=Finset.univ.filter (fun e:{a:(Fin n)×(Fin n) // P a}=>Sum.inl ({e.val.1,e.val.2}:Finset (Fin n))∈C)
    let A:=(T₀∪T₁)\F
    ∃M:Finset {e:(Fin n)×(Fin n) // P e},
      (∀v,directedInCount P M v=d*startRetentionMinimum (rawStartHubSet π d σ false)) ∧
      symmDiff M T₁⊆A ∧
      (∀e,Sum.inl ({e.val.1,e.val.2}:Finset (Fin n))∈C→(e∈M↔e∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)) :=by
  intro F A
  have hraw:=long_sample_marked_retained_indegree_balance G hreg hD hd hm π σ ω q s p p₂ k₂ u err herr hq hstarts hheads
  have hdev':=marked_candidate_indegree_deviation_from_raw G ω P T₁
    (d*startRetentionMinimum (rawStartHubSet π d σ false)) (err+(d:ℝ)*err) loss
    (by simpa only [Nat.cast_mul] using hraw) hchange
  have hdev:∀v,|(directedInCount P T₁ v:ℝ)-(d*startRetentionMinimum (rawStartHubSet π d σ false):ℕ)|≤eta*Fintype.card (Fin n):=by
    intro v
    simpa only [Fintype.card_fin] using (hdev' v).trans (by linarith only [hbudget])
  have hh:=marked_correction_protects_reserved_resources P S₀ S₁ T₀ T₁ B₀ B₁ C
    (d*startRetentionMinimum (rawStartHubSet π d σ false)) rho eta hrho heta hetaR hdis h₀ h₁ hdev
    base₀ base₁ loss₀ loss₁ hbase₀ hbase₁ hloss₀ hloss₁ (by simpa only [Fintype.card_fin] using hmargin₀) (by simpa only [Fintype.card_fin] using hmargin₁)
  obtain ⟨M,hM,hA,hC,hbound⟩:=hh
  refine ⟨M,hM,?_,hC,?_⟩
  · intro e he
    have he':e∈symmDiff M T₁:=by simpa only [Finset.mem_symmDiff] using he
    have hh':=hA he'
    simpa only [A,F,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union] using hh' 
  · simpa only [Fintype.card_fin] using hbound
end Oberwolfach

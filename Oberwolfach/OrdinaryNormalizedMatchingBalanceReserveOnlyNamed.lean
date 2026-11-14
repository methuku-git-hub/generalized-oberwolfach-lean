module

public import Oberwolfach.CandidateOrdinaryRecodedAbundanceMatchingEventNormalizedIndependentReserve
public import Oberwolfach.OrdinaryNormalizedMatchingBalanceReserveOnlyShape

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_normalized_matching_balance_reserve_only_named
    (L rstar:ℕ) (βfreq ρ₀ α:ℝ) (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1)
    (hρ₀:0<ρ₀) (hα:0<α):
    OrdinaryNormalizedMatchingBalanceReserveOnlyShape L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα :=by
  unfold OrdinaryNormalizedMatchingBalanceReserveOnlyShape
  obtain ⟨m,k,hL,hm,heven,hlen,hratio,hselect⟩:=
    ordinary_recoded_abundance_matching_event_independent_reserve_with_normalization L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα
  refine ⟨m,k,hL,hm,heven,hlen,hratio,?_⟩
  intro θ hθ hθ1
  obtain ⟨βList,lamList,ζDel,smin,hβList,hβList1,hlam,hζDel,hsmin,hsminEq,hselect⟩:=hselect θ hθ hθ1
  refine ⟨βList,lamList,ζDel,smin,hβList,hβList1,hlam,hζDel,hsmin,hsminEq,?_⟩
  intro dNeed
  obtain ⟨d,K,rank,hdNeed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,hselect⟩:=hselect dNeed
  refine ⟨d,K,rank,hdNeed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,?_⟩
  intro hd' θhost hθhost
  obtain ⟨BO,hBO,hselect⟩:=hselect hd' θhost hθhost
  refine ⟨BO,hBO,?_⟩
  intro τ hτ t ξ ζ χpair χlist ht hξ hζ hχpair hχlist σ χbal χbd χnbr χpairR χpath hσ hχbal hχbd hχnbr hχpairR hχpath
  obtain ⟨a,ha,Nmatch,hmatch⟩:=hselect τ hτ t ξ ζ χpair χlist ht hξ hζ hχpair hχlist
  obtain ⟨Nextra,hextra⟩:=ordinary_matching_balance_reserved_tests_same_sample d hd' smin σ χbal χbd χnbr χpairR χpath
    hsmin hσ hχbal hχbd hχnbr hχpairR hχpath
  refine ⟨a,ha,max Nmatch Nextra,?_⟩
  intro n hn hn2 U _ _ hUn F hF hfreq D hD hρlo hρhi Allowed hAllowed hthreshold P hreg π hdegree hnoshort
  obtain ⟨i₀,rsv,C,hi,hslo,hs1,hclass,hsize,hcard,hreserve,sampling,w,seed,hweight,hNorm,hzero,hseed,hmatch⟩:=
    hmatch n (by omega) hn2 U hUn F hF hfreq D hD hρlo hρhi Allowed hAllowed hthreshold P hreg π hdegree hnoshort
  refine ⟨i₀,rsv,C,hi,hslo,hs1,hclass,hsize,hcard,hreserve,sampling,w,seed,hweight,hNorm,hzero,hseed,?_⟩
  intro R _ ν E εE p q s p₂ μ wM wO Core Match hE
  have hM:1-((εE+3*ζ+χpair)+2*χlist)≤(μ.sigma ν).probability (fun z=>E z ∧ Match z.1):=by
    simpa only [Match,Core,OrdinaryRecodedMatchingExtra] using hmatch ν E εE hE
  let Prior:=fun z=>(((E z ∧ Match z.1) ∧
    OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σ (2*((3*d:ℕ):ℝ)) z.1) ∧
    OrdinaryBoundaryStartEvent π d z.1) ∧ OrdinaryReservedCompletionTests P π d p smin s z.1
  have hB:1-(((((((εE+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath)≤(μ.sigma ν).probability Prior:=
    hextra n (by omega) (by omega) hUn F hF P hreg hD i₀ rsv θ ((m:ℝ)+1) ρ₀ hρ₀ hslo hρlo sampling π hnoshort
      ν Core a ζDel lamList E ((εE+3*ζ+χpair)+2*χlist) hM
  simpa only [Prior] using hB
end Oberwolfach

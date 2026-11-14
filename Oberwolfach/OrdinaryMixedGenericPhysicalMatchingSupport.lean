module

public import Oberwolfach.OrdinaryMixedGenericCandidateBounds
public import Oberwolfach.OrdinaryMixedGenericPhysicalInjection
public import Oberwolfach.PhysicalMixedSampledMatchingSupport

@[expose] public section
/-! The physical matching theorem for the ordinary mixed candidate family,
with candidate sizes, nonnegativity, fibers and pair bounds discharged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_mixed_generic_physical_matching_support
    (r Bpow:ℕ) (hr:2≤r) (hBpow:1≤Bpow)
    (Kcd α γ:ℝ) (hKcd:0<Kcd) (hα:0<α) (hγ:0<γ):
    ∃ε:ℝ,0<ε ∧ ∃n₀:ℕ,∀(V U I Test Row:Type) [Fintype V] [Fintype U] [Fintype I] [DecidableEq I]
      [Fintype Test] [Fintype Row] [LinearOrder V] [DecidableEq U],
    n₀≤Fintype.card V→0<Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(π:Equiv.Perm V) (b m:ℕ) (hm:3≤m) (hb:1≤b) (f:I→ℕ) (hf:∀i,1≤f i)
      (hrM:2*(m+1)≤r) (hrO:∀i,2*(f i+2)≤r)
      (wM:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
      (wO:∀i,OrderedOrdinaryWheel (U:=U) π b (f i+2)→ℝ)
      (BM:ℝ) (BO:I→ℝ) (hBM:0≤BM) (hBO:∀i,0≤BO i)
      (hwM:∀W,0≤wM W ∧ wM W≤BM/(Fintype.card V:ℝ)^m)
      (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(Fintype.card V:ℝ)^(f i+1))
      (σ:(((V×V)⊕(V×V))⊕(Bool×V×U))→Bool)
      (target:Option I→(((V×V)⊕(V×V))⊕(Bool×V×U))→ℝ) (τ t:ℝ),
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π b (f i+2))=>orderedOrdinaryResources W)
    let w:=ordinaryMixedGenericWeight wM wO
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let C:Option I→ℝ:=fun i=>match i with
      | none=>((m:ℝ)+1)^4*BM
      | some i=>((f i:ℝ)+2)^3*BO i
    let W:=PhysicalSampledActive φ σ
    let Cand:=PhysicalSampledCandidate (mixedCandidateResources R) σ
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources R) σ;
    ∀(g:Test→Cand→ℝ) (S:Row→Finset W),
    Fintype.card W≤(Fintype.card V)^Bpow→Fintype.card Test≤(Fintype.card V)^Bpow→Fintype.card Row≤(Fintype.card V)^Bpow→
    0≤t→4*(Fintype.card (Option I):ℝ)*t+τ≤ε→
    (∀x:W,∑a∈Finset.univ.filter (fun a=>φ a=x.val ∧ σ a=true),∑i,target i a=1)→
    (∀i a,σ a=true→|resourcePatternLoad (R i) (w i) (fun _ _=>true) a σ-target i a|≤t+τ*target i a)→
    (∑i,(16:ℝ)*C i)≤Kcd→
    (∀j,α*Fintype.card V≤(S j).card)→(∀i c,0≤g i c ∧ g i c≤1)→
    (∀i,α*Fintype.card V≤∑c:Cand,g i c*mixedCandidateWeight w c.val)→
    ∃L:Finset Cand,(∀c∈L,0<mixedCandidateWeight w c.val) ∧ (∀c∈L,∀c'∈L,c≠c'→Disjoint (Q c) (Q c')) ∧
      (∀j,((S j\L.biUnion Q).card:ℝ)≤γ*(S j).card) ∧
      (∀i,(1-γ)*(∑c:Cand,g i c*mixedCandidateWeight w c.val)≤∑c∈L,g i c) ∧
      (∀i,(∑c∈L,g i c)≤(1+γ)*(∑c:Cand,g i c*mixedCandidateWeight w c.val)) :=by
  obtain ⟨ε,hε,n₀,hmatch⟩:=physical_mixed_sampled_matching_support r Bpow hr hBpow Kcd α γ hKcd hα hγ
  refine ⟨ε,hε,n₀,?_⟩
  intro V U I Test Row _ _ _ _ _ _ _ _ hn hnV hU π b m hm hb f hf hrM hrO wM wO BM BO hBM hBO hwM hwO σ target τ t R w φ C W Cand Q g S hW hTest hRow ht herr htarget hload hC hS hg hmass
  have hbds:=ordinary_mixed_generic_candidate_bounds π b m r hm hnV hU f hf hrM hrO wM wO BM BO hBM hBO hwM hwO
  have hinj:=ordinary_mixed_generic_physical_injective (U:=U) π b m (by omega) hb f hf
  have hpair:=hbds.2.2.2
  have hconst:(∑i,(4:ℝ)^2*C i)≤Kcd:=by norm_num at hC ⊢; exact hC
  have hresult:=hmatch (Fintype.card V) hn (Option I) (((V×V)⊕(V×V))⊕(Bool×V×U)) (Sym2 V⊕(V×U)) Test Row
    (OrdinaryMixedGenericFamily _ _) φ R w σ 4 target τ t C g S hW hTest hRow
    hinj hbds.1 hbds.2.1 (ordinary_mixed_physical_resource_fiber_card π) ht herr htarget hload hbds.2.2.1 hpair hconst hS hg (by
      intro i
      convert hmass i using 1 <;> congr! 5)
  obtain ⟨L,hsupport,hdis,hcover,hlo,hhi⟩:=hresult
  refine ⟨L,hsupport,hdis,hcover,?_,?_⟩
  · intro i
    convert hlo i using 1 <;> congr! 5
  · intro i
    convert hhi i using 1 <;> congr! 5
end Oberwolfach

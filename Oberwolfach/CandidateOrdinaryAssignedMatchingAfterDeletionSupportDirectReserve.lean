module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryAssignedMatchingAfterDeletionSupport
public import Oberwolfach.OrdinaryAssignedMatchingAfterDeletionSupport
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedApproximateDensityBoundsDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedEligibleFiberNormalizationDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedMassAfterBoundedDeletionDirectReserve
public import Oberwolfach.OrdinaryMixedGenericPhysicalMatchingSupport
public import Oberwolfach.OrdinaryAssignedMassAfterBoundedDeletion
public import Oberwolfach.OrdinaryAssignedEligibleFiberNormalization
public import Oberwolfach.OrdinaryPhysicalMatchingCardinality

@[expose] public section
/-! For every bounded physical rim deletion, match the actual retained
ordinary factor-frequency tests on the same sample and control every physical
rim and spoke row. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_assigned_matching_after_deletion_support_candidate_direct_reserve
    (r K m d:ℕ) (hr:2≤r) (hK3:3≤K) (hm:7≤m) (hd:2≤d)
    (hrM:2*(m+1)≤r) (hrO:∀i:Fin K,2*(longPaddedSeedExponent i+2)≤r)
    (θ α γ Kcd BM:ℝ) (hθ:0<θ) (hθ1:θ≤1/100) (hα:0<α) (hγ:0<γ) (hKcd:0<Kcd) (hBM:0≤BM)
    (hαbound:α≤θ/(1600*(K:ℝ)*(K:ℝ)))
    (BO:Fin K→ℝ) (hBO:∀i,0≤BO i)
    (hKpair:(∑i:Option (Fin K),(16:ℝ)*(match i with
      | none=>((m:ℝ)+1)^4*BM
      | some i=>((longPaddedSeedExponent i:ℝ)+2)^3*BO i))≤Kcd):
    ∃ε:ℝ,0<ε ∧ ∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (i₀:Fin K) (rsv ρ D:ℝ) (hs0:0≤rsv) (hs1:rsv≤1/100)
      (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
      (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
      (pstar:ℝ) (hpstar:0<pstar)
      (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (δ:ℝ) (hDel:∀x,(Del.degree x:ℝ)≤δ)
      (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
      (hwM:∀W,0≤wM W ∧ wM W≤BM/(n:ℝ)^m)
      (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
      (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(n:ℝ)^(longPaddedSeedExponent i+1))
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
      (τ t countErr:ℝ) (ht:0≤t) (hτ:τ≤1/2) (hcountErr:countErr≤pstar*n/2),
    let c:ℝ:=(m:ℝ)+1
    let a:=ordinaryAssignedLongWeight F hF K θ c
    let b:=ordinaryAssignedShortWeight F hF K i₀ rsv θ c
    let p:=(∑u,(a u+b u))/D
    let η:=fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let raw':=rawMarkedDeleteRims raw Del.edgeFinset
    let old:=typedMarkedResourceState (ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d raw) (rawMarkedPairSpokes π d raw true true)
    let state:=typedMarkedResourceState (ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d raw') (rawMarkedPairSpokes π d raw' true true)
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let w:=ordinaryMixedGenericWeight wM wO
    let target:=ordinaryMixedIdealTarget (m:ℝ) D p a b η
    let loss:Option (Fin K)→ℝ:=fun i=>match i with
      | none=>22*((m:ℝ)+1)^4*BM
      | some i=>10*((longPaddedSeedExponent i:ℝ)+2)^4*BO i
    let terr:=t+(∑i,loss i)*δ/(n:ℝ)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let W:=PhysicalSampledActive φ state
    let Cand:=PhysicalSampledCandidate (mixedCandidateResources R) state
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources R) state
    let rows:=fun j:OrdinaryPhysicalRowIndex (Fin n) U=>physicalSampledRow φ state (ordinaryPhysicalRow j)
    let tests:=OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ
    let g:=fun z:tests=>fun c:Cand=>ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z c.val;
    (∀u,pstar≤b u)→(terr≤θ/(800*(K:ℝ)))→
    (4*((K:ℝ)+1)*terr+τ≤ε)→
    (∀i v,old v=true→|resourcePatternLoad (R i) (w i) (fun _ _=>true) v old-target i v|≤t+τ*target i v)→
    (∀u,|rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) true true false u Finset.univ-b u*n|≤countErr)→
    ∃L:Finset Cand,
      (∀x∈L,0<mixedCandidateWeight w x.val) ∧
      (∀x∈L,∀y∈L,x≠y→Disjoint (Q x) (Q y)) ∧
      (∀j,(((rows j)\L.biUnion Q).card:ℝ)≤max α γ*n) ∧
      (∀z,(1-γ)*(∑x:Cand,g z x*mixedCandidateWeight w x.val)≤∑x∈L,g z x) ∧
      (∀z,(∑x∈L,g z x)≤(1+γ)*(∑x:Cand,g z x*mixedCandidateWeight w x.val)) :=by
  obtain ⟨ε,hε,N₀,hmatch⟩:=physical_mixed_sampled_matching_support r 3 hr (by omega) Kcd α γ hKcd hα hγ
  refine ⟨ε,hε,max (max N₀ K) 2,?_⟩
  intro n hn hn0 U _ _ hU F hF Allowed hAllowed i₀ rsv ρ D hs0 hs1 hda hρ hρ1 hD hsize hClassReserve pstar hpstar P Del π δ hDel wM hwM wO hwO σ τ t countErr ht hτ hcountErr
    c a b p η raw raw' old state R w target loss terr φ W Cand Q rows tests g hbstar hterr herr hload hcount
  have hK:0<K:=by omega
  have hc:8≤c:=by dsimp [c];exact_mod_cast (show 8≤m+1 by omega)
  have hdens:=ordinary_assigned_approximate_density_bounds_candidate_direct_reserve hn0 F hF K hK i₀ rsv θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize Allowed hAllowed hClassReserve
  have hb:∀u,0<b u ∧ b u≤1:=by
    intro u
    exact ⟨lt_of_lt_of_le hdens.1 (hdens.2.2.2.1 u).1,(hdens.2.2.2.1 u).2⟩
  have hnorm:=ordinary_assigned_eligible_fiber_normalization_candidate_direct_reserve hn0 F hF K hK i₀ rsv θ ρ D d m hd hm
    hs0 hs1 hθ hθ1 hda hρ hρ1 hD hsize Allowed hAllowed hClassReserve P π raw'
  have htarget:∀x:W,∑v∈Finset.univ.filter (fun v=>φ v=x.val ∧ state v=true),∑i,target i v=1:=by
    intro x
    dsimp only at hnorm
    have hh:=hnorm x
    convert hh using 1 <;> (try simp only [target,φ,state,p,a,b,η,c]) <;> congr! 5
  have hnew:=ordinary_mixed_root_targets_after_deletion (ordinaryEligibleHost P π d) Del π d m (by omega) hn0 hU longPaddedSeedExponent
    long_padded_seed_exponent_positive wM BM hBM hwM wO BO hBO hwO raw true true δ hDel target τ t hload
  have hδ:0≤δ:=(Nat.cast_nonneg (Del.degree ⟨0,hn0⟩)).trans (hDel ⟨0,hn0⟩)
  have hloss:∀i,0≤loss i:=by intro i;cases i with | none=>dsimp [loss];positivity | some i=>dsimp [loss];have hh:=hBO i;positivity
  have hsumloss:0≤∑i,loss i:=Finset.sum_nonneg (fun i _=>hloss i)
  have hterr0:0≤terr:=by dsimp [terr];positivity
  have hmass:=ordinary_assigned_retained_mass_after_bounded_deletion_candidate_direct_reserve hn0 F hF Allowed hAllowed hK3 i₀ rsv θ c
    hs0 hs1 hθ hθ1 hc hClassReserve b (fun _=>rfl) hb pstar hpstar hbstar π d m (by omega) wM wO BM hBM hwM BO hBO hwO hU (ordinaryEligibleHost P π d) σ Del δ hDel a D p τ t countErr hτ hcountErr hterr hload hcount
  let Large:=LargeMatchingRow rows n α
  let S:Large→Finset W:=fun j=>rows j.val
  have hcard:=ordinary_physical_matching_cardinality (by omega:2≤n) (by omega:K≤n) hU F hF i₀ rsv θ φ state rows α
  have hsize:∀j,(rows j).card≤n:=by intro j;simpa only [Fintype.card_fin] using physical_sampled_row_card_le φ state (by simpa using hU) j
  have hrow:∀j:Large,α*n≤(S j).card:=fun j=>j.property
  have hg:∀z x,0≤g z x ∧ g z x≤1:=by intro z x;exact ordinary_assigned_retained_hub_indicator_range F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val
  have hmass':∀z,α*n≤∑x:Cand,g z x*mixedCandidateWeight w x.val:=by
    intro z
    have hh:=hmass z
    have ha:=mul_le_mul_of_nonneg_right hαbound (Nat.cast_nonneg n)
    have ha':α*(n:ℝ)≤θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ)):=by convert ha using 1 <;> ring
    have hh':θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ))≤∑x:Cand,g z x*mixedCandidateWeight w x.val:=by
      convert hh using 1 <;> (try simp only [g,w,tests]) <;> congr! 5
    exact ha'.trans hh'
  have hbudget:4*(Fintype.card (Option (Fin K)):ℝ)*terr+τ≤ε:=by simpa only [Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using herr
  have hbds:=ordinary_mixed_generic_candidate_bounds π (3*d) m r (by omega) (by simpa using hn0)
    (by simpa using hU) longPaddedSeedExponent long_padded_seed_exponent_positive hrM hrO wM wO BM BO hBM hBO
    (by simpa using hwM) (by simpa using hwO)
  have hinj:=ordinary_mixed_generic_physical_injective (U:=U) (I:=Fin K) π (3*d) m (by omega) (by omega)
    longPaddedSeedExponent long_padded_seed_exponent_positive
  have hinj' : ∀i W,Set.InjOn φ (↑(R i W):Set _) := by
    intro i W
    have hh:=hinj i W
    convert hh using 1 <;> (try simp only [φ,R]) <;> congr! 5 <;>
      (try (ext t; cases t <;> simp [typedMarkedOccurrenceResources_rim,typedMarkedOccurrenceResources_spoke]))
  have hsize' : ∀i W,2≤(R i W).card ∧ (R i W).card≤r := by
    intro i W
    have hh:=hbds.1 i W
    convert hh using 1 <;> (try simp only [R]) <;> congr! 5 <;>
      (try (ext t; cases t <;> simp [typedMarkedOccurrenceResources_rim,typedMarkedOccurrenceResources_spoke]))
  have hnew' : ∀i v,state v=true→
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) v state-target i v|≤terr+τ*target i v := by
    intro i v hv
    have hh:=hnew i v hv
    convert hh using 1 <;> (try simp only [R,w,state,terr,loss]) <;> congr! 5 <;>
      (try (ext t; cases t <;> simp [typedMarkedOccurrenceResources_rim,typedMarkedOccurrenceResources_spoke]))
    all_goals (rename_i j hj; cases j <;> rfl)
  let C0:Option (Fin K)→ℝ:=fun i=>match i with
    | none=>((m:ℝ)+1)^4*BM
    | some i=>((longPaddedSeedExponent i:ℝ)+2)^3*BO i
  have hC00:∀i,0≤C0 i:=by
    intro i
    cases i with
    | none => dsimp [C0];positivity
    | some i => dsimp [C0];have hh:=hBO i;positivity
  have hpair' : ∀i e f,resourceOmittedPairWeight (R i) (w i) e f≤C0 i/(n:ℝ) := by
    intro i e f
    cases i with
    | none =>
      have hh:=hbds.2.2.2 none e f
      convert hh using 1 <;> (try simp only [R,w,C0,Fintype.card_fin]) <;> congr! 5 <;>
        (try (ext t; cases t <;> simp [typedMarkedOccurrenceResources_rim,typedMarkedOccurrenceResources_spoke]))
    | some i =>
      have hh:=hbds.2.2.2 (some i) e f
      convert hh using 1 <;> (try simp only [R,w,C0,Fintype.card_fin]) <;> congr! 5
  have hfiber : ∀x,(Finset.univ.filter (fun a=>φ a=x)).card≤4 := by
    intro x
    have hh:=ordinary_mixed_physical_resource_fiber_card (U:=U) π x
    convert hh using 1 <;> (try simp only [φ]) <;> congr! 5
  have hconst:(∑i,(4:ℝ)^2*C0 i)≤Kcd:=by norm_num at hKpair ⊢;exact hKpair
  have hres:=hmatch n (by omega) (Option (Fin K))
    (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)) (Sym2 (Fin n)⊕(Fin n×U)) tests Large
    (OrdinaryMixedGenericFamily _ _) φ R w state 4 target τ terr C0 g S
    (by simpa using hcard.1) (by simpa using hcard.2.1) (by simpa using hcard.2.2)
    hinj' hsize' hbds.2.1 hfiber hterr0 hbudget htarget hnew'
    hC00 hpair' hconst hrow hg (by intro z;convert hmass' z using 1 <;> congr! 5)
  obtain ⟨L,hsupp,hdis,hcover,hlo,hhi⟩:=hres
  refine ⟨L,hsupp,hdis,?_,?_,?_⟩
  · exact large_matching_rows_control_all rows n α γ hγ.le hsize (L.biUnion Q) hcover
  · intro z
    convert hlo z using 1 <;> congr! 5
  · intro z
    convert hhi z using 1 <;> congr! 5
end Oberwolfach

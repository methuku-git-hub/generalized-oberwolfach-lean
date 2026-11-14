module

public import Oberwolfach.LongSelectedRetainedClassDynamicSourceHostCompletionAllHubFull
public import Oberwolfach.LongSelectedRetainedSourceDynamicAllHubLoad
public import Oberwolfach.AllHubTargetsAvoidAssignedEndpoints
public import Oberwolfach.LongRetainedProtectedInnerTargets
public import Oberwolfach.ActualFixedSourceLateComplementDisjointTargetsTracked
public import Oberwolfach.LongSelectedRetainedClassDynamicSourceHostCompletionAllHubFull
public import Oberwolfach.LongSelectedRetainedSourceDynamicAllHubLoad
public import Oberwolfach.AllHubTargetsAvoidAssignedEndpoints
public import Oberwolfach.LongSelectedRetainedSourceDynamicGlobalLoad
public import Oberwolfach.LongSelectedClassDynamicSourceHostCompletion
public import Oberwolfach.LongSelectedClassOrientedSourceHostCompletion
public import Oberwolfach.LongSelectedOrientedSourceWithLoadAndMatching
public import Oberwolfach.LongSelectedOrientedSourceWithMatchingCapacity
public import Oberwolfach.LongSelectedOrientedSourceCapacityUpper
public import Oberwolfach.LongSelectedOrientedSourceGlobalLoad
public import Oberwolfach.LongSelectedOrientedSourceResidualCompletion
public import Oberwolfach.LongSelectedOrientedSourceGlobalLoad
public import Oberwolfach.LongSelectedOrientedSourceResidualCompletion
public import Oberwolfach.LongSelectedAlignedSourceResidualCompletion
public import Oberwolfach.FirstVortexClassPrescribedAssignmentNoMarkedBudget
public import Oberwolfach.ReservedSpokeAvoidsRetainedMarked

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexClassRetainedDynamicHostResidualAllHubFullFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

private theorem retained_dynamic_host_all_hub_full_protected_pair_reserved_endpoint {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (Lists:U→Finset V) (H:Finset U) (e:Sym2 V) (w:U) (v:V)
    (hw:w∈protectedPairEdgeHubs Lists H e) (hv:v∈e.toFinset) : v∈Lists w := by
  exact (Finset.mem_filter.mp hw).2.2 v hv

theorem first_vortex_class_retained_dynamic_host_residual_continuation_all_hub_full
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Sclass DelG:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2) (H:Finset U) (A:Finset (Fin n))
    (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (Dhost:Fin n→Fin n→Prop)
    (δlocal ρ₀ θ ε lam α b βfinal δglobal:ℝ)
    (hρ₀:0<ρ₀) (hb:0≤b) (hbsmall:b≤((ρ₀/4)/40000)/16) (hαb:α/16≤b)
    (hθδ:10*θ≤δglobal) (hεδ:ε≤δglobal) (hβ:0<βfinal) (hβ1:βfinal≤1)
    (hδ:0<δglobal) (hδbound:δglobal≤(βfinal/100)^2)
    (hn:0<n) (hnβ:100/βfinal≤(n:ℝ)) (hnδ:2/Real.sqrt δglobal≤(n:ℝ)) (hu:Fintype.card U≤n)
    (hU:0<Fintype.card U)
    (hFreeHost:∀x y,rawSelectedPhysicalRelation P π d (fun e=>σE (Sum.inl e)) x y→¬DelG.Adj x y→Dhost x y)
    (hKbadHost:∀Pack x y,(Kbad Pack).Adj x y→Dhost x y ∨ Dhost y x):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:=Function.Embedding.subtype (·∈T)
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σE (Sum.inl e)) x y ∧ ¬DelG.Adj x y
    let Lists:=fun w=>rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w\
      (A∪retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
    (∀w,IsExtendingList Dfree (Lists w) βfinal)→
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedRetainedSourceDynamicAllHubLoad hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δlocal
      (fun occupied Pack=>(FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelG Used (Kbad Pack) A π d σE t Jret H α b ρ₀ θ ε lam occupied Pack ∧ Pack=Used.edgeFinset) ∧
        ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
          (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
      ρ₀ θ δglobal M →
    LongSelectedRetainedClassDynamicSourceHostCompletionAllHubFull hU F P π d m ℓ raw t Jret σE H A Sclass Kbad Used DelG absorber δlocal Dhost
      (fun occupied Pack=>(FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelG Used (Kbad Pack) A π d σE t Jret H α b ρ₀ θ ε lam occupied Pack ∧ Pack=Used.edgeFinset) ∧
        ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
          (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
      ρ₀ θ δglobal M :=by
  intro raw T e Dfree Lists hext M hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcapacityAll,hglobalAll⟩
  let Interiors:=fun w=>bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)
  let occupied:=fun w=>((data w).oldDomain\Interiors w).image (ψ w)
  let AbsAll:=fun w=>if w∈H then absorber w else ∅
  let Z:=innerRequiredTargets Finset.univ A (fun w=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w))
    (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied
  let Jbad:=spanningRestriction (Sclass\Used) A\(Kbad Pack)
  let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d (fun e=>raw (Sum.inr e))) H
  let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
  let Dstar:=Dhost
  let FinalEdges:=fun w=>Finset.univ.biUnion (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset)
  have hOutcome:=hExtra.1.1
  obtain ⟨hKdeg,hKcard,hKPack,hJdeg,hKJ,hUsedJ,hOutside,hShield,hLbad,hAssignment⟩:=hOutcome
  have hCycle:∀w,(data w).t.biUnion (fun j=>((data w).C j).support.toFinset)⊆(data w).Cembed:=by
    intro w
    rw [(hprops w).2.2.2.1]
  have hDR:∀w,Disjoint (Interiors w) (data w).remaining:=by
    intro w
    exact (hprops w).2.2.2.2.2.2.2.2.1
  have hInj:∀w,Set.InjOn (ψ w) (↑((data w).oldDomain\Interiors w):Set (Fin n)):=by
    intro w
    exact (hprops w).2.2.2.2.2.2.2.2.2.1
  have hOldReserved:∀w,Disjoint (Lists w) (occupied w):=by
    intro w
    have hh:=((hprops w).2.2.2.2.2.2.2.2.2.2.2.1).symm
    exact (Finset.disjoint_left.mpr (by
      intro x hx hy
      apply (Finset.disjoint_left.mp hh) ?_ hy
      exact raw_ordinary_outer_subset_retained π d (fun e=>raw (Sum.inr e)) false t Jret false false w (Finset.mem_sdiff.mp hx).1))
  have hZprops:=inner_required_targets_properties Finset.univ A (fun w=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w))
    (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied
  have hsub:∀w,Z w⊆innerRequiredTargets Finset.univ A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied w := by
    exact (long_retained_protected_inner_targets π d (fun e=>raw (Sum.inr e)) t Jret Finset.univ A
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied).2.1
  have hcapacity':∀w,8*(residualSubtypeSet (data w).remaining (data w).prescribed).card+
      8*⌈4*((Kbad Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊+4*(Z w).card+10≤
        Fintype.card {x // x∈(data w).remaining} := by
    intro w
    have hh:=Finset.card_le_card (hsub w)
    dsimp only [occupied,Interiors,AbsAll] at hh
    have hc:=hcapacityAll w
    omega
  have hglobal':∀v,((Finset.univ.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      (Kbad Pack).degree v+((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δglobal*n := by
    intro v
    have hh:(Finset.univ.filter (fun w=>v∈Z w)).card≤
        (Finset.univ.filter (fun w=>v∈innerRequiredTargets Finset.univ A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
          (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied w)).card := by
      apply Finset.card_le_card
      intro w hw
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
      exact hsub w hw
    have hc:=hglobalAll v
    have hr:((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤
        ((Finset.univ.filter (fun w=>v∈innerRequiredTargets Finset.univ A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
          (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied w)).card:ℝ):=by exact_mod_cast hh
    linarith
  have hSize:∀w,(Fintype.card {x // x∈(data w).remaining}:ℝ)≤δglobal*Fintype.card (Fin n):=by
    intro w
    simp only [Fintype.card_coe,Fintype.card_fin]
    have hn0:(0:ℝ)≤n:=by positivity
    have hh:=mul_le_mul_of_nonneg_right hθδ hn0
    nlinarith [hupper w]
  have hDegree:∀v,((Kbad Pack).degree v:ℝ)≤b*Fintype.card (Fin n):=by
    intro v
    simp only [Fintype.card_fin]
    have hh:=mul_le_mul_of_nonneg_right hαb (Nat.cast_nonneg n)
    exact (hKdeg v).trans hh
  letI : DecidableRel Jbad.Adj := fun x y=>Classical.propDecidable _
  have hJ:∀v,(Jbad.degree v:ℝ)≤δglobal*Fintype.card (Fin n):=by
    intro v
    simp only [Fintype.card_fin]
    have hh:=mul_le_mul_of_nonneg_right hεδ (Nat.cast_nonneg n)
    have hJdeg':(Jbad.degree v:ℝ)≤ε*n:=by
      convert hJdeg v using 1 <;> congr 2 <;> exact Subsingleton.elim _ _
    exact hJdeg'.trans hh
  letI : Fintype Jbad.edgeSet := Jbad.fintypeEdgeSet
  have hKJ':Disjoint (Kbad Pack).edgeFinset Jbad.edgeFinset:=by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    apply Finset.disjoint_left.mp hKJ hx
    simpa only [SimpleGraph.mem_edgeFinset] using hy
  have hαCap:0<((ρ₀/4)/40000):=by positivity
  have hnV:0<Fintype.card (Fin n):=by simpa using hn
  have hI:(Fintype.card U:ℝ)≤Fintype.card (Fin n):=by simpa only [Fintype.card_fin] using (show (Fintype.card U:ℝ)≤n by exact_mod_cast hu)
  have hLateOriented:=actual_fixed_source_late_indices_complement_disjoint_targets_tracked (V:=Fin n) F hF Dsrc orig hPair hValid hUnion hArcs
  obtain ⟨pieces',hgraph',harcs',hcont⟩:=hLateOriented _ _ data
  have hSafe : ∀w e v, v∈e.toFinset → w∈Lbad e → w∉Bad v := by
    intro w e v hv hw hbad
    have hlist : v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w :=
      retained_dynamic_host_all_hub_full_protected_pair_reserved_endpoint _ H e w v hw hv
    have hmarked : v∈retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w :=
      (Finset.mem_filter.mp hbad).2
    exact Finset.disjoint_left.mp (reserved_spoke_avoids_retained_marked π d
      (fun e=>raw (Sum.inr e)) t Jret w) hlist hmarked
  have hShieldEmpty : ∀w e v,e∈(Kbad Pack).edgeFinset→v∈e.toFinset→v∈occupied w→w∈Lbad e→w∈(∅:Finset U) := by
    intro w e v he hv ho hl
    exact False.elim (hSafe w e v hv hl (hShield w e v he hv ho hl))
  have hZavoid:∀w e v,e∈(Kbad Pack).edgeFinset→v∈e.toFinset→w∈Lbad e→v∉Z w:=by
    intro w e v _ hv he
    exact all_hub_targets_avoid_assigned_endpoints A H (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
      (fun w=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w))
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied
      (fun w=>raw_ordinary_outer_subset_retained π d (fun e=>raw (Sum.inr e)) false t Jret false false w) w e v hv he
  have hcompletion:FirstVortexResidualCompletionOrientedTracked F Dsrc _ _ data Interiors ψ (Kbad Pack) Jbad Lbad Bad Z Dfree Dstar Pack Lists FinalEdges δglobal ((ρ₀/4)/40000):=by
    refine ⟨pieces',hgraph',harcs',?_⟩
    have hc := hcont hCycle Interiors hDR ψ hInj (Kbad Pack) Jbad Lbad (fun _=>∅) H Z
      (fun e _=>hOutside e) hZprops.2.2.1 hZavoid hShieldEmpty ((ρ₀/4)/40000) b hαCap hb hbsmall hnV
      (by simpa only [Fintype.card_fin] using hLbad)
      (by intro v; simp; positivity) hDegree
      (by simpa only [Fintype.card_fin] using hcapacity') βfinal δglobal hβ hβ1 hδ hδbound
      (by simpa only [Fintype.card_fin] using hnβ) (by simpa only [Fintype.card_fin] using hnδ) hI hSize
      (by simpa only [Fintype.card_fin] using hglobal') hJ hKJ' Dfree Dstar (fun x y h=>hFreeHost x y h.1 h.2)
      (hKbadHost Pack) Pack hKPack (fun x y h=>hSelected x y h.1) Lists hext hOldReserved FinalEdges hOldDisj hOldPack
    obtain ⟨asgn, ori, B, g, Φ, fC, hOrient, hMcap, h₁, h₂, h₃, _, hlist, hrest⟩ := hc
    refine ⟨asgn, ori, B, g, Φ, fC, hOrient, hMcap, h₁, h₂, h₃, ?_, hlist, hrest⟩
    intro i v hv
    obtain ⟨e, he, hve, hi⟩ := hlist i v hv
    exact hSafe i e v hve hi
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,⟨hcapacityAll,hglobalAll⟩,hcompletion⟩
end Oberwolfach

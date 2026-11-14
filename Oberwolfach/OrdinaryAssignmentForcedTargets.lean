module

public import Oberwolfach.OrdinaryAssignmentPlacementInputs
public import Oberwolfach.ResidualActualDependentRestrictedOldFamily
public import Oberwolfach.PrescribedAugmentedOccurrenceBound

@[expose] public section
/-! A protected bad-edge assignment on the same sample can be fed directly
into simultaneous placement of arbitrary dependent two-regular residual
sources. Remaining geometric and numerical hypotheses are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assignment_dependent_residual_placement_forced_targets
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {K J X:U→Type} [∀u,DecidableEq (K u)] [∀u,DecidableEq (J u)]
    [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (a:ℝ) (hEvent:OrdinaryProtectedBadEdgeAssignments π d σ a)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (G Jbad:SimpleGraph (Fin n)) (Dstar Dfree:Fin n→Fin n→Prop)
    (hDstar:∀x y,G.Adj x y→Dstar x y∨Dstar y x)
    (hDD:∀x y,Dfree x y→Dstar x y)
    (F:∀u,SimpleGraph (X u)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (data:∀u,ActualResidualData (K:=K u) (J:=J u) (F u))
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (Old:∀u,Finset (X u)) (hPresOld:∀u,(data u).prescribed⊆Old u)
    (ψ:∀u,X u→Fin n) (hψ:∀u,Set.InjOn (ψ u) (↑(Old u):Set (X u)))
    (hOld:∀u,Disjoint ((Old u).image (ψ u))
      (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u))
    (T:U→Finset (Fin n))
    (b:ℝ) (hb:0≤b) (hbsmall:b≤a/16) (hdegree:∀v,(G.degree v:ℝ)≤b*n)
    (hcapacity:∀u,8*(residualSubtypeSet (data u).remaining (data u).prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/(a*n)⌉₊+4*((T u\(Old u).image (ψ u)).card)+10≤Fintype.card {x // x∈(data u).remaining})
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(n:ℝ)) (hn:2/Real.sqrt δ≤(n:ℝ)) (hU:Fintype.card U≤n)
    (hsize:∀u,(Fintype.card {x // x∈(data u).remaining}:ℝ)≤δ*n)
    (hload:∀v,((Finset.univ.filter (fun u=>v∈
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1))).card:ℝ)+G.degree v+
      ((Finset.univ.filter (fun u=>v∈T u\(Old u).image (ψ u))).card:ℝ)≤δ*n)
    (hJ:∀v,(Jbad.degree v:ℝ)≤δ*n)
    (hext:∀u,IsExtendingList Dfree
      (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) β):
    ∃(D:∀u,X u→X u→Prop) (pieces:∀u,List (PrescribedSourcePiece {x // x∈(data u).remaining}))
      (M:U→Finset (Fin n×Fin n))
      (B:∀u,Finset {x // x∈(data u).remaining})
      (g Φ:∀u,{x // x∈(data u).remaining}→Fin n),
      (∀u,prescribedDependentGraph pieces u=((data u).graph).induce (↑(data u).remaining:Set (X u))) ∧
      (∀u x y,prescribedDependentDigraph pieces u x y ↔ D u x.1 y.1 ∧ (data u).graph.Adj x.1 y.1) ∧
      (∀u,IsPrescribedOrientedMatching (M u)) ∧
      (∀u,Disjoint ((Old u).image (ψ u)) (prescribedMatchingEndpoints (M u))) ∧
      (∀u,prescribedMatchingEndpoints (M u)⊆rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) ∧
      (∀u,(M u).image prescribedArcPhysical⊆G.edgeFinset) ∧
      (∀u,Function.Injective (Φ u)) ∧
      (∀u,residualSubtypeSet (data u).remaining (data u).prescribed⊆B u ∧
        (∀x∈residualSubtypeSet (data u).remaining (data u).prescribed,g u x=ψ u x.1) ∧
        (B u).image (g u)=
          (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1)∪
            prescribedMatchingEndpoints (M u)∪
            ((T u\(Old u).image (ψ u))\prescribedMatchingEndpoints (M u)) ∧
        (prescribedInducedArcs (prescribedDependentDigraph pieces u) (B u)).image (Prod.map (g u) (g u))=M u) ∧
      (∀u v,v∈T u→v∈(Old u).image (ψ u) ∨ ∃x,Φ u x=v) ∧
      (∀u x,x∈B u→Φ u x=g u x) ∧
      (∀u x,x∉B u→Φ u x∈rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) ∧
      (∀u x y,prescribedDependentDigraph pieces u x y→Dstar (Φ u x) (Φ u y) ∧
        ((x∉B u ∨ y∉B u)→Dfree (Φ u x) (Φ u y))) ∧
      let E:U→Finset (Sym2 (Fin n)):=fun u=>((prescribedDependentGraph pieces u).edgeFinset).image (Sym2.map (Φ u));
      PairwisePhysicalDisjoint E ∧ (∀u,(M u).image prescribedArcPhysical⊆E u) ∧
      (∀e∈G.edgeFinset,∃u,e∈E u) ∧
      (∀u,Disjoint (E u\(M u).image prescribedArcPhysical) Jbad.edgeFinset) ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*n):=by
  obtain ⟨M,hM,hOldM,hMlist,hMcard,hMstar,hMsub,hMpair,hcover,hMload⟩:=
    ordinary_assignment_gives_placement_matching_inputs π d σ a hEvent t Jret G Dstar hDstar
      (fun u=>(Old u).image (ψ u)) hOld b hb hbsmall hdegree
  let Z:=fun u=>(T u\(Old u).image (ψ u))\prescribedMatchingEndpoints (M u)
  have hOldZ:∀u,Disjoint ((Old u).image (ψ u)) (Z u):=by
    intro u
    apply Finset.disjoint_left.mpr
    intro v hv hz
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 hv
  have hMZ:∀u,Disjoint (prescribedMatchingEndpoints (M u)) (Z u):=by
    intro u
    apply Finset.disjoint_left.mpr
    intro v hv hz
    exact (Finset.mem_sdiff.mp hz).2 hv
  have hZsub:∀u,Z u⊆T u\(Old u).image (ψ u):=fun u=>Finset.sdiff_subset
  have hcap:∀u,8*(residualSubtypeSet (data u).remaining (data u).prescribed).card+
      8*(M u).card+4*(Z u).card+10≤Fintype.card {x // x∈(data u).remaining}:=by
    intro u
    have hz:=Finset.card_le_card (hZsub u)
    have hh:=hcapacity u
    have hm:=hMcard u
    omega
  have hload':∀v,((Finset.univ.filter (fun u=>v∈
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1)∪
      prescribedMatchingEndpoints (M u)∪Z u)).card:ℝ)≤δ*Fintype.card (Fin n):=by
    intro v
    have hh:=prescribed_augmented_occurrence_bound
      (fun u=>(residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1))
      Z M G hMsub hMpair v
    have hz:((Finset.univ.filter (fun u=>v∈Z u)).card:ℝ)≤
      ((Finset.univ.filter (fun u=>v∈T u\(Old u).image (ψ u))).card:ℝ):=by
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro u hu
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
      exact hZsub u hu
    have hh':((Finset.univ.filter (fun u=>v∈
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1)∪
      prescribedMatchingEndpoints (M u)∪Z u)).card:ℝ)≤
      ((Finset.univ.filter (fun u=>v∈
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1))).card:ℝ)+G.degree v+
      ((Finset.univ.filter (fun u=>v∈Z u)).card:ℝ):=by exact_mod_cast hh
    have hfin:=hload v
    simp only [Fintype.card_fin]
    linarith
  obtain ⟨D,orig,hpair0,hcycles,hwhole,hD,hready⟩:=
    actual_factor_residuals_dependent_embed_with_restricted_old_domain (I:=U) (V:=Fin n) (K:=K) (J:=J) F hF
  obtain ⟨pieces,hgraph,harcs,hplace⟩:=hready data
  obtain ⟨B,g,Φ,hinj,hB,hΦ,hZ,hΦL,hΦarc,hEpair,hME,havoid,hfreeload,hunion,hdeg⟩:=
    hplace hCycle Old hPresOld ψ hψ M hM Z hOldM hOldZ hMZ hcap
      Jbad β δ hβ hβ1 hδ hδbound (by simpa using hnβ) (by simpa using hn)
      (by simpa using hU) (by simpa using hsize) hload' (by simpa using hJ)
      hMpair Dfree Dstar hDD hMstar _ hext (fun u=>(hOld u).symm)
  refine ⟨D,pieces,M,B,g,Φ,hgraph,harcs,hM,hOldM,hMlist,hMsub,hinj,?_,?_,hΦ,hΦL,hΦarc,hEpair,hME,?_,havoid,?_⟩
  · intro u
    exact hB u
  · intro u v hv
    by_cases hold:v∈(Old u).image (ψ u)
    · exact Or.inl hold
    right
    by_cases hm:v∈prescribedMatchingEndpoints (M u)
    · have hvB:v∈(B u).image (g u):=by rw [(hB u).2.2.1]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
      obtain ⟨x,hx,hgx⟩:=Finset.mem_image.mp hvB
      exact ⟨x,(hΦ u x hx).trans hgx⟩
    · exact hZ u v (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hv,hold⟩,hm⟩)
  · intro e he
    obtain ⟨u,hu⟩:=hcover e he
    exact ⟨u,hME u hu⟩
  · simpa only [Fintype.card_fin] using hdeg
end Oberwolfach

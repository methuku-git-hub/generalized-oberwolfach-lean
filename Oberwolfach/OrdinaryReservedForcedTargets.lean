module

public import Oberwolfach.OrdinaryForcedTargetsGivenMatching
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

theorem ordinary_reserved_assignment_and_forced_targets
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {K J X:U→Type} [∀u,DecidableEq (K u)] [∀u,DecidableEq (J u)]
    [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (hnpos:0<n) (π:Equiv.Perm (Fin n)) (d:ℕ) (σI:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (G Jbad:SimpleGraph (Fin n)) (Dstar Dfree:Fin n→Fin n→Prop)
    (hDstar:∀x y,G.Adj x y→Dstar x y∨Dstar y x) (hDD:∀x y,Dfree x y→Dstar x y)
    (Inner:Finset U) (Abs L:U→Finset (Fin n))
    (hLsub:∀u,L u⊆rawReservedSpokeList π d σI u)
    (ρ₀ smin b:ℝ) (hρ:0<ρ₀) (hs:0<smin) (hb:0≤b)
    (hUlo:ρ₀*n≤4*(Fintype.card U:ℝ))
    (hinner:(Inner.card:ℝ)≤(5*ρ₀*smin^2/128)*n)
    (herror:(n:ℝ)^(3/4:ℝ)≤(5*ρ₀*smin^2/128)*n)
    (hpair:∀x y,x≠y→(5/8:ℝ)*smin^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d σI (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σI (y,w)=some (Sum.inr false))).card:ℝ))
    (hbsmall:b≤(5*ρ₀*smin^2/128)/16)
    (hAbs:∀v,((Finset.univ.filter (fun u=>v∈Abs u)).card:ℝ)≤b*n)
    (hdegree:∀v,(G.degree v:ℝ)≤b*n)
    (F:∀u,SimpleGraph (X u)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (data:∀u,ActualResidualData (K:=K u) (J:=J u) (F u))
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (Old:∀u,Finset (X u)) (hPresOld:∀u,(data u).prescribed⊆Old u)
    (ψ:∀u,X u→Fin n) (hψ:∀u,Set.InjOn (ψ u) (↑(Old u):Set (X u)))
    (hOldRaw:∀u,Disjoint (rawReservedSpokeList π d σI u) ((Old u).image (ψ u)))
    (T:U→Finset (Fin n))
    (hcapacity:∀u,8*(residualSubtypeSet (data u).remaining (data u).prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/((5*ρ₀*smin^2/128)*n)⌉₊+4*((T u\(Old u).image (ψ u)).card)+10≤Fintype.card {x // x∈(data u).remaining})
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(n:ℝ)) (hn:2/Real.sqrt δ≤(n:ℝ)) (hU:Fintype.card U≤n)
    (hsize:∀u,(Fintype.card {x // x∈(data u).remaining}:ℝ)≤δ*n)
    (hload:∀v,((Finset.univ.filter (fun u=>v∈
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1))).card:ℝ)+G.degree v+
      ((Finset.univ.filter (fun u=>v∈T u\(Old u).image (ψ u))).card:ℝ)≤δ*n)
    (hJ:∀v,(Jbad.degree v:ℝ)≤δ*n)
    (hext:∀u,IsExtendingList Dfree
      (L u) β):
    ∃(D:∀u,X u→X u→Prop) (pieces:∀u,List (PrescribedSourcePiece {x // x∈(data u).remaining}))
      (M:U→Finset (Fin n×Fin n))
      (B:∀u,Finset {x // x∈(data u).remaining})
      (g Φ:∀u,{x // x∈(data u).remaining}→Fin n),
      (∀u,prescribedDependentGraph pieces u=((data u).graph).induce (↑(data u).remaining:Set (X u))) ∧
      (∀u x y,prescribedDependentDigraph pieces u x y ↔ D u x.1 y.1 ∧ (data u).graph.Adj x.1 y.1) ∧
      (∀u,IsPrescribedOrientedMatching (M u)) ∧
      (∀u,Disjoint ((Old u).image (ψ u)) (prescribedMatchingEndpoints (M u))) ∧
      (∀u,prescribedMatchingEndpoints (M u)⊆rawReservedSpokeList π d σI u\Abs u) ∧
      (∀u,u∈Inner→M u=∅) ∧
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
      (∀u x,x∉B u→Φ u x∈L u) ∧
      (∀u x y,prescribedDependentDigraph pieces u x y→Dstar (Φ u x) (Φ u y) ∧
        ((x∉B u ∨ y∉B u)→Dfree (Φ u x) (Φ u y))) ∧
      let E:U→Finset (Sym2 (Fin n)):=fun u=>((prescribedDependentGraph pieces u).edgeFinset).image (Sym2.map (Φ u));
      PairwisePhysicalDisjoint E ∧ (∀u,(M u).image prescribedArcPhysical⊆E u) ∧
      (∀e∈G.edgeFinset,∃u,e∈E u) ∧
      (∀u,Disjoint (E u\(M u).image prescribedArcPhysical) Jbad.edgeFinset) ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*n):=by
  obtain ⟨M,hM,hOldM,hMlist,hMinner,hMcard,hMstar,hMsub,hMpair,hcover,hMload⟩:=
    ordinary_reserved_assignment_placement_inputs hnpos π d σI G Dstar hDstar Inner
      (fun u=>(Old u).image (ψ u)) Abs hOldRaw ρ₀ smin b hρ hs hb hUlo hinner herror hpair hbsmall hAbs hdegree
  have hOld:∀u,Disjoint ((Old u).image (ψ u)) (L u):=by
    intro u
    exact (hOldRaw u).symm.mono_right (hLsub u)
  obtain ⟨D,pieces,B,g,Φ,hgraph,harcs,hM',hOldM',hMlist',hMsub',hinj,hB,hT,hΦ,hΦL,hΦarc,hEpair,hME,hcover',havoid,hdeg⟩:=
    ordinary_dependent_residual_forced_targets_given_matching G Jbad Dstar Dfree hDD L
      (fun u=>rawReservedSpokeList π d σI u\Abs u)
      ⌈4*(G.edgeFinset.card:ℝ)/((5*ρ₀*smin^2/128)*n)⌉₊ M
      hM hMlist hMcard hMstar hMsub hMpair hcover F hF data hCycle Old hPresOld ψ hψ hOld hOldM T hcapacity
      β δ hβ hβ1 hδ hδbound hnβ hn hU hsize hload hJ hext
  exact ⟨D,pieces,M,B,g,Φ,hgraph,harcs,hM',hOldM',hMlist',hMinner,hMsub',hinj,hB,hT,hΦ,hΦL,hΦarc,hEpair,hME,hcover',havoid,hdeg⟩
end Oberwolfach

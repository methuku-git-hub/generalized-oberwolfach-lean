module

public import Oberwolfach.OrdinaryReservedTargetTrackedTwoDeletions
public import Oberwolfach.OrdinaryReservedPackageInputs
public import Oberwolfach.OrdinaryMatchedPackageOldEdges
public import Oberwolfach.OrdinaryReservedActualTargetAvoidance

@[expose] public section
/-! Coherent matched packages and the same sample's selected reserved tests
feed the absorber-protected whole-factor embedding in the edited target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_package_embedding_tracked_two_deletions
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hnpos:0<n)
    {A B J W:U→Type} [∀u,Fintype (A u)] [∀u,DecidableEq (A u)]
    [∀u,Fintype (B u)] [∀u,DecidableEq (B u)] [∀u,Fintype (J u)] [∀u,DecidableEq (J u)]
    (F₀:U→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F₀ u).ConnectedComponent) (m d:ℕ) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (P Host DelMatch DelFinish Target G:SimpleGraph (Fin n)) (hHost:Host≤P) (hG:G≤Target)
    (hOldTarget:∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) DelMatch.edgeFinset) x y→Target.Adj x y)
    (hFinishTarget:∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→
      ¬DelFinish.Adj x y→Target.Adj x y):
    let S:=fun u:U=>{x:Fin n | (F₀ u).connectedComponentMk x∉Cres u}
    let X:=fun u=>↥(S u)
    let H:=fun u=>(F₀ u).induce (S u)
    let raw:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let Arc:=rawMixedPhysicalArc Host π d (rawMarkedDeleteRims raw DelMatch.edgeFinset)
    let Reserve:=fun u=>rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u;
    ∀(root:∀u,A u⊕B u→Fin n) (Avail:U→Finset (Fin n)) (Good:∀u,W u→Prop)
    (Pack:∀u,W u→Finset (Finset (Fin n))) (Pos:∀u,W u→B u→Finset ℕ) (len:∀u,J u→ℕ)
    (pk:∀u,OrdinaryMatchedResidualHubPackage (H u) m d π (root u) Arc (Avail u) (Reserve u)
      (Good u) (Pack u) (Pos u) (len u)),
    let data:=fun u=>(pk u).data
    let Old:=fun u=>(data u).oldDomain\bufferedPathStrictInterior (fun _:A u=>(m+1)*d) (pk u).inner
    let ψ:=fun u=>(pk u).ψ;
    (∀u,IsEmpty (A u))→
    (∀u v,u≠v→Disjoint (Pack u (pk u).marker) (Pack v (pk v).marker))→
    (∀u,Disjoint ((data u).deletedEdges.image (Sym2.map (ψ u))) G.edgeFinset)→
    ∀(Inner:Finset (Fin n)) (Hubs:Finset U) (Abs:U→Finset (Fin n)),
    (∀u,Abs u⊆Reserve u)→
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
    let T:=ordinaryInnerSpokeTargets Inner Hubs Href
    let Lists:=fun u=>Reserve u\(Inner∪Abs u)
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬DelFinish.Adj x y;
    ∀(ρ₀ smin b:ℝ),0<ρ₀→0<smin→0≤b→ρ₀*n≤4*(Fintype.card U:ℝ)→
    (Hubs.card:ℝ)≤(5*ρ₀*smin^2/128)*n→
    (n:ℝ)^(3/4:ℝ)≤(5*ρ₀*smin^2/128)*n→
    (∀x y,x≠y→(5/8:ℝ)*smin^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ))→
    b≤(5*ρ₀*smin^2/128)/16→
    (∀v,((Finset.univ.filter (fun u=>v∈Abs u)).card:ℝ)≤b*n)→
    (∀v,(G.degree v:ℝ)≤b*n)→
    (∀u,8*(residualSubtypeSet (data u).remaining (data u).prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/((5*ρ₀*smin^2/128)*n)⌉₊+4*((T u\(Old u).image (ψ u)).card)+10≤Fintype.card {x // x∈(data u).remaining})→
    ∀(β δ:ℝ),0<β→β≤1→0<δ→δ≤(β/100)^2→b≤δ→
    100/β≤(n:ℝ)→2/Real.sqrt δ≤(n:ℝ)→Fintype.card U≤n→
    (∀u,(Fintype.card {x // x∈(data u).remaining}:ℝ)≤δ*n)→
    (∀v,((Finset.univ.filter (fun u=>v∈
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1))).card:ℝ)+G.degree v+
      ((Finset.univ.filter (fun u=>v∈T u\(Old u).image (ψ u))).card:ℝ)≤δ*n)→
    (∀u,IsExtendingList Dfree (Lists u) β)→
    ∃(M:U→Finset (Fin n×Fin n)) (f:∀u,X u↪Fin n),
      (∀u,u∈Hubs→M u=∅) ∧
      (∀u,prescribedMatchingEndpoints (M u)⊆Reserve u\Abs u) ∧
      (∀u,(M u).image prescribedArcPhysical⊆G.edgeFinset) ∧
      (∀u v,v∈T u→∃x,f u x=v) ∧
      (∀u x,x∈(data u).oldDomain→f u x=ψ u x) ∧
      (∀u x,f u x∉Abs u) ∧
      (∀u x y,(H u).Adj x y→Target.Adj (f u x) (f u y)) ∧
      (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly (X u) (H u) (f u))
        (partialFactorPhysicalEdgesPoly (X v) (H v) (f v))) ∧
      (∀u,u∈Hubs→∀x,f u x∈Inner→f u x∉Reserve u) ∧
      ∃New:U→Finset (Sym2 (Fin n)),
        (∀u,((H u).edgeFinset).image (Sym2.map (f u))=(data u).deletedEdges.image (Sym2.map (ψ u))∪New u) ∧
        PairwisePhysicalDisjoint New ∧
        (∀e∈G.edgeFinset,∃u,e∈New u) ∧
        (∀v,((prescribedPhysicalUnion New).degree v:ℝ)≤5*Real.sqrt δ*n) :=by
  intro S X H raw Arc Reserve root Avail Good Pack Pos len pk data Old ψ hempty hpack hOG Inner Hubs Abs hAbsSub Href T Lists Dfree
    ρ₀ smin b hρ hs hb hUlo hinner herror hpair hbsmall hAbs hdegree hcapacity
    β δ hβ hβ1 hδ hδbound hbδ hnβ hn hU hsize hload hext
  obtain ⟨hreg,hCycle,hPres,hψ,hOldRaw,hdir,hcoverage⟩:=ordinary_reserved_package_inputs F₀ hF₀ Cres m d π
    (fun e=>σ (Sum.inr e)) root Arc Avail Good Pack Pos len pk
  have hArc:∀x y,Arc x y→Host.Adj x y:=by
    intro x y h
    exact (raw_mixed_deleted_arc_host Host DelMatch π d raw x y h).1
  have hOO:∀u v,u≠v→Disjoint ((data u).deletedEdges.image (Sym2.map (ψ u))) ((data v).deletedEdges.image (Sym2.map (ψ v))):=by
    have hh:=ordinary_matched_package_old_edges H m d π root Arc Avail Reserve Good Pack Pos len pk hempty hpack Host hArc
    exact hh.1
  have hAvoid:=ordinary_reserved_actual_target_avoidance π d σ Inner Hubs Abs hAbsSub
  have hLInner:∀u,Disjoint (Lists u) Inner:=by
    intro u
    apply Finset.disjoint_left.mpr
    intro v hv hi
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ hi)
  have hTReserve:∀u,u∈Hubs→Disjoint (T u) (Reserve u):=by
    intro u hu
    exact (ordinary_sample_inner_targets_avoid_reserved π d σ Inner Hubs u).1
  exact ordinary_reserved_target_embedding_tracked_two_deletions hnpos P Host DelMatch DelFinish Target G hHost hG π d σ hOldTarget hFinishTarget Hubs Abs Lists
    (fun u=>(hAvoid u).1) hAbsSub (fun u=>(hAvoid u).2.1)
    ρ₀ smin b hρ hs hb hUlo hinner herror hpair hbsmall hAbs hdegree hempty (fun u (_:A u)=>(m+1)*d)
    (fun u=>(pk u).inner) H hreg data (fun u=>(pk u).hs₁) hCycle Old hPres (fun _=>rfl) ψ hψ hOldRaw hdir hOO hOG T
    (fun u=>(hAvoid u).2.2.1) Inner hLInner hTReserve hcapacity β δ hβ hβ1 hδ hδbound hbδ hnβ hn hU hsize hload hext
end Oberwolfach

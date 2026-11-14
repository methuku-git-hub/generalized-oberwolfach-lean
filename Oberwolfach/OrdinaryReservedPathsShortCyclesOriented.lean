module

public import Oberwolfach.OrdinaryAllHubIntervalCapacity
public import Oberwolfach.AssignedReservedSourceFamilies
public import Oberwolfach.RetainedAndRawIntervalGeometry
public import Oberwolfach.BufferedMarkerAnchorEmbedding
public import Oberwolfach.RegularCycleIsomorphism

@[expose] public section
/-! Construct the original factor paths and the assigned short component
cycles together, and map their path markers to the sampled intervals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_paths_and_short_cycles_oriented
    {n K:ℕ} {U A B J:Type} [Fintype U] [DecidableEq U] [Fintype A] [Fintype B] [Fintype J]
    [DecidableEq A] [DecidableEq B] [DecidableEq J]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hn:0<n) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:0<d) (θ:ℝ) (hθ:0<θ)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (w:U)
    (index:A⊕B ≃ retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t Jret w)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2)
    (hlarge:4*((m:ℝ)+1)/(θ*(θ/100))<(n:ℝ)^((1:ℝ)/4))
    (hcounts:∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (hsupport:∀g v,rawMarkedPairSpokes π d raw g true true v w→
      ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g≠0)
    (cycles:J↪(F w).ConnectedComponent) (hshort:∀j,Fintype.card (cycles j)≤K):
    let I:={C:(F w).ConnectedComponent // K<Fintype.card C}
    let components:I↪(F w).ConnectedComponent:=Function.Embedding.subtype _
    let rootTarget:=fun i=>retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w (index i);
    ∃E:∀C:(F w).ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph,
    ∃block:A⊕B↪LongReservedBlockIndex (F w) components (m+1) d,
    ∃ext:∀i:A⊕B,Fin ((m+1)*d+5)↪Fin n,
    ∃inner:∀i:A⊕B,Fin ((m+1)*d+1)↪Fin n,
      (∀i,ext i=longReservedSigmaBlock (F w) components (m+1) d (fun j=>E (components j)) (block i) d (le_refl _)) ∧
      (∀i k,inner i k=ext i ⟨k.val+2,by omega⟩) ∧
      (∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) ∧
    ∃(P:∀i:A⊕B,(F w).Walk (ext i 0) (ext i (Fin.last ((m+1)*d+4))))
      (root:J→Fin n) (C:∀j,(F w).Walk (root j) (root j)),
      (∀i,(P i).IsPath) ∧ (∀i,(P i).length=(m+1)*d+4) ∧ (∀i,(P i).support=List.ofFn (ext i)) ∧
      (∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset) ∧
      (∀j,(C j).IsCycle) ∧ (∀j,(C j).length=Fintype.card (cycles j)) ∧
      (∀j k,k<(C j).length→factorCycleOrientation (F w) E ((C j).getVert k)=(C j).getVert (k+1)) ∧
      (∀j,(C j).toSubgraph.verts=(cycles j).supp) ∧
      (∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset) ∧
      (∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset) ∧
      let Marks:=Finset.univ.image (fun z:(A⊕B)×Fin (d+1)=>bufferedMarker (m+1) d (ext z.1) z.2);
      ∃anchor:{x // x∈Marks}↪Fin n,
        ∀i (j:Fin (d+1)),anchor ⟨bufferedMarker (m+1) d (ext i) j,
          Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩⟩=(π^j.val) (rootTarget i) :=by
  intro I components rootTarget
  let E:∀C:(F w).ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph:=
    fun C=>Classical.choice (component_regular_two_cycle_iso (F w) (hF w) C).2
  have hlong:∀i:I,K+1≤Fintype.card (components i):=by intro i;exact Nat.succ_le_iff.mpr i.property
  have hs:∀j,Fintype.card (cycles j)<K+1:=by intro j;have hh:=hshort j;omega
  have hcap:=ordinary_all_hub_interval_capacity F hF hn π d m hd θ hθ raw t Jret w index hcut hlarge hcounts hsupport
  obtain ⟨block,ext,inner,hext,hinner,hdis,P,root,C,hp,hlen,hsupp,hP,hcy,hclen,hdir,hc,hC,hcross⟩:=
    assigned_reserved_source_families (F w) (hF w) E components cycles (m+1) d (K+1) hlong hs
      (fun j=>Fintype.card (cycles j)) (fun _=>rfl) hcap
  refine ⟨E,block,ext,inner,hext,hinner,hdis,P,root,C,hp,hlen,hsupp,hP,hcy,hclen,hdir,hc,hC,hcross,?_⟩
  intro Marks
  have hgeom:=retained_and_raw_interval_geometry π d (by omega) hnoshort (fun e=>raw (Sum.inr e)) false true (by decide) t Jret w
  have hinj:∀i,Function.Injective (fun j:Fin (d+1)=>(π^j.val) (rootTarget i)):=fun i=>hgeom.1 (index i)
  have htarget:∀i j,i≠j→Disjoint (permutationWindow π 0 d (rootTarget i)) (permutationWindow π 0 d (rootTarget j)):=
    fun i j hij=>hgeom.2 (index i) (index j) (fun he=>hij (index.injective he))
  exact buffered_marker_anchor_embedding (m+1) d (by omega) ext hdis π rootTarget hinj htarget
end Oberwolfach

module

public import Oberwolfach.MarkedSampleDeletionIncidences
public import Oberwolfach.MarkedPackingRimGraphs

@[expose] public section

/-! The physical graphs determined by actual finite typed arc and spoke
sets. Their deletion removes exactly those original occurrences, rather
than an unspecified superset of them. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def markedFiniteSpokeGraph (S:Finset (V×U)):SimpleGraph (V⊕U):=
  physicalEdgeGraph (S.image (fun z=>{Sum.inl z.1,Sum.inr z.2}))

theorem markedFiniteSpokeGraph_adj (S:Finset (V×U)) (x:V) (u:U):
    (markedFiniteSpokeGraph S).Adj (Sum.inl x) (Sum.inr u)↔(x,u)∈S:=by
  constructor
  · rintro ⟨_,he⟩
    obtain ⟨⟨y,v⟩,hz,hz'⟩:=Finset.mem_image.mp he
    have hx:Sum.inl x∈({Sum.inl y,Sum.inr v}:Finset (V⊕U)):=hz'.symm ▸ (by simp)
    have hu:Sum.inr u∈({Sum.inl y,Sum.inr v}:Finset (V⊕U)):=hz'.symm ▸ (by simp)
    have hxy:x=y:=by simpa only [Finset.mem_insert,Finset.mem_singleton,Sum.inl.injEq,Sum.inl_ne_inr,or_false] using hx
    have huv:u=v:=by simpa only [Finset.mem_insert,Finset.mem_singleton,Sum.inr.injEq,Sum.inr_ne_inl,false_or] using hu
    simpa only [hxy,huv] using hz
  · intro he
    exact ⟨Sum.inl_ne_inr,Finset.mem_image.mpr ⟨(x,u),he,rfl⟩⟩

variable {Γ Color:Type} [Fintype Γ] [Fintype Color]

def markedSampleArcSetGraph
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (A:Finset (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false⊕
      MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true)):SimpleGraph V:=
  physicalEdgeGraph (A.image (markedPhysicalEdge (fun e=>e.val.1) (fun e=>e.val.2)
    (fun e=>e.val.1) (fun e=>e.val.2) π))

theorem markedSampleArcSetGraph_coordinate
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (A:Finset (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false⊕
      MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true)) (a):
    Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∈
      (markedSampleArcSetGraph P π d σ A).edgeFinset ↔ a∈A:=by
  let f:=markedPhysicalEdge
    (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
    (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2) π
  have hf:Function.Injective f:=markedSampleArc_physical_injective P π (3*d) _
  have hi (a):f a∈A.image f↔a∈A:=Finset.mem_image.trans (by
    constructor
    · rintro ⟨b,hb,he⟩;exact hf he ▸ hb
    · intro ha;exact ⟨a,ha,rfl⟩)
  cases a with
  | inl a=>
    have hn:a.val.1≠a.val.2:=((markedPhysicalRim_eq_one_iff P π (3*d) _ false _ _).mp a.property).2.1.ne
    simp only [Sum.elim_inl,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,
      markedSampleArcSetGraph,physicalEdgeGraph]
    constructor
    · intro h;exact (hi (Sum.inl a)).mp h.2
    · intro h;exact ⟨hn,(hi (Sum.inl a)).mpr h⟩
  | inr a=>
    have hn:a.val.1≠π a.val.2:=((markedPhysicalRim_eq_one_iff P π (3*d) _ true _ _).mp a.property).2.1.ne
    simp only [Sum.elim_inr,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,
      markedSampleArcSetGraph,physicalEdgeGraph]
    constructor
    · intro h;exact (hi (Sum.inr a)).mp h.2
    · intro h;exact ⟨hn,(hi (Sum.inr a)).mpr h⟩

theorem markedSampleArcSetGraph_remaining
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (A:Finset (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false⊕
      MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true)):
    Finset.univ.filter (fun a=>Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉
      (markedSampleArcSetGraph P π d σ A).edgeFinset)=Finset.univ\A:=by
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,
    markedSampleArcSetGraph_coordinate]

end Oberwolfach

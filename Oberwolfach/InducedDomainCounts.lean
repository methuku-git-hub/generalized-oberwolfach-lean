module

public import Oberwolfach.EndpointTriangleCounts
public import Oberwolfach.EndpointRelativeCounts

@[expose] public section

/-! Exact neighbourhood transport into a fixed finite vertex domain. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def embeddingPullFinset (e:W↪V) (S:Finset V) : Finset W :=
  Finset.univ.filter (fun w=>e w∈S)

@[simp] theorem embeddingPullFinset_mem (e:W↪V) (S:Finset V) (w:W) :
    w∈embeddingPullFinset e S ↔ e w∈S := by simp [embeddingPullFinset]

theorem embeddingPullFinset_image (e:W↪V) (S:Finset V)
    (hS:∀ v∈S,∃ w,e w=v) : (embeddingPullFinset e S).image e=S := by
  ext v
  simp only [Finset.mem_image,embeddingPullFinset_mem]
  constructor
  · rintro ⟨w,hw,rfl⟩;exact hw
  · intro hv;obtain ⟨w,rfl⟩:=hS v hv;exact ⟨w,hv,rfl⟩

theorem embeddingPullFinset_card (e:W↪V) (S:Finset V)
    (hS:∀ v∈S,∃ w,e w=v) : (embeddingPullFinset e S).card=S.card := by
  exact (Finset.card_image_of_injective (embeddingPullFinset e S) e.injective).symm.trans
    (congrArg Finset.card (embeddingPullFinset_image e S hS))

@[simp] theorem embeddingPullFinset_image_self (e:W↪V) (S:Finset W) :
    embeddingPullFinset e (S.image e)=S := by ext w;simp [e.injective.eq_iff]

theorem embedding_comap_common (e:W↪V) (Q:SimpleGraph V) (A X:Finset W) :
    (common A X (fun v=>(Q.comap e).neighborFinset v)).image e=
      common (A.image e) (X.image e) (fun v=>Q.neighborFinset v) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨hwA,hwX⟩:=(mem_common_iff _ _ _ _).mp hw
    apply (mem_common_iff _ _ _ _).mpr
    refine ⟨Finset.mem_image.mpr ⟨w,hwA,rfl⟩,?_⟩
    intro z hz
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hz
    simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.comap_adj] using hwX y hy
  · intro hv
    obtain ⟨hvA,hvX⟩:=(mem_common_iff _ _ _ _).mp hv
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hvA
    refine Finset.mem_image.mpr ⟨w,(mem_common_iff _ _ _ _).mpr ⟨hw,?_⟩,rfl⟩
    intro y hy
    simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.comap_adj] using
      hvX (e y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)

theorem embedding_comap_degree_le (e:W↪V) (Q:SimpleGraph V) (v:W) :
    (Q.comap e).degree v≤Q.degree (e v) := by
  rw [←SimpleGraph.card_neighborFinset_eq_degree,←SimpleGraph.card_neighborFinset_eq_degree,
    ←Finset.card_image_of_injective _ e.injective]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hz
  simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.comap_adj] using hw

theorem endpoint_counts_embedding (e:W↪V) (Q F:SimpleGraph V) (S T:Finset V)
    (hS:∀ v∈S,∃ w,e w=v) (hT:∀ v∈T,∃ w,e w=v) (b:ℝ)
    (hc:EndpointNeighbourCounts Q F S T b) :
    EndpointNeighbourCounts (Q.comap e) (F.comap e)
      (embeddingPullFinset e S) (embeddingPullFinset e T) b := by
  refine ⟨?_,?_,?_⟩
  · simpa only [embeddingPullFinset_card e T hT] using hc.indices
  · intro Y J hY hJ hYc hJc hYJ
    have hh:=hc.rows (Y.image e) (J.image e)
      (by rintro z hz;obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hz;exact (embeddingPullFinset_mem _ _ _).mp (hY hy))
      (by rintro z hz;obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hz;exact (embeddingPullFinset_mem _ _ _).mp (hJ hj))
      (by simpa only [Finset.card_image_of_injective _ e.injective] using hYc)
      (by simpa only [Finset.card_image_of_injective _ e.injective] using hJc)
      (by simpa only [Finset.card_image_of_injective _ e.injective] using hYJ)
    rw [←Finset.image_union,←embeddingPullFinset_image e S hS,←embedding_comap_common,
      Finset.card_image_of_injective _ e.injective] at hh
    exact hh
  · intro v hv w hw hne hF
    have hh:=hc.pairs (e v) ((embeddingPullFinset_mem _ _ _).mp hv)
      (e w) ((embeddingPullFinset_mem _ _ _).mp hw) (e.injective.ne hne) hF
    have he:({v,w}:Finset W).image e={e v,e w}:=by simp
    rw [←he,←embeddingPullFinset_image e T hT,←embedding_comap_common,
      Finset.card_image_of_injective _ e.injective] at hh
    exact hh

end Oberwolfach

module

public import Oberwolfach.MarkedVortexInnerDomainEquivalences
public import Oberwolfach.MarkedPhysicalCutTransfer
public import Oberwolfach.MarkedActualInnerCutEvent

@[expose] public section
/-! Transport retained cuts from the next vortex subtype to the inner
subsets of its parent, without changing the sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_inner_rim_cut_transport
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d i:ℕ) (σ:RawMarkedOutcome V U Γ Color) (mark:Bool) (δ h:ℝ)
    (hn:0<Fintype.card (markedVortexVertexType Q (i+1))) (hh:0≤h)
    (hcut:BipartiteLargeCut
      (markedPhysicalRim (G.comap (markedVortexVertexEmbedding Q (i+1))) (markedVortexPermutation Q π hπ (i+1)) (3*d)
        (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q (i+1)) (markedVortexHubEmbedding Q (i+1)) σ (Sum.inl e)) mark) δ h):
    BipartiteLargeCut
      (fun x:↥(markedVortexInnerVertices Q i)=>fun y:↥(markedVortexInnerVertices Q i)=>
        markedPhysicalRim (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
          (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) mark x.val y.val) δ h:=by
  let e:↥(markedVortexInnerVertices Q i)↪markedVortexVertexType Q (i+1):=(markedVortexInnerVertexEquiv Q i).symm.toEmbedding
  have hcard:Fintype.card ↥(markedVortexInnerVertices Q i)=Fintype.card (markedVortexVertexType Q (i+1)):=
    Fintype.card_congr (markedVortexInnerVertexEquiv Q i).symm
  have hI:0<Fintype.card ↥(markedVortexInnerVertices Q i):=by rw [hcard];exact hn
  have he (x:↥(markedVortexInnerVertices Q i)):
      markedVortexNestedVertex Q i (i+1) (by omega) (e x)=x.val:=by
    have hh:markedVortexInnerVertexEquiv Q i (e x)=x:=(markedVortexInnerVertexEquiv Q i).apply_symm_apply x
    exact congrArg Subtype.val hh
  have ht:=bipartiteLargeCut_embedding e e _ hI hI 1 δ δ h (by norm_num) hh
    (by rw [hcard];norm_num) (by rw [hcard];norm_num) (by ring_nf;exact le_rfl) hcut
  have hmatrix:(fun x y=>markedPhysicalRim (G.comap (markedVortexVertexEmbedding Q (i+1))) (markedVortexPermutation Q π hπ (i+1)) (3*d)
        (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q (i+1)) (markedVortexHubEmbedding Q (i+1)) σ (Sum.inl e)) mark (e x) (e y))=
      (fun x:↥(markedVortexInnerVertices Q i)=>fun y:↥(markedVortexInnerVertices Q i)=>
        markedPhysicalRim (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
          (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) mark x.val y.val):=by
    funext x y
    have hx:=markedPhysicalRim_restrictPair_eq (markedVortexNestedVertex Q i (i+1) (by omega))
      (markedVortexNestedHub Q i (i+1) (by omega)) (markedVortexPermutation Q π hπ i) (markedVortexPermutation Q π hπ (i+1))
      (marked_vortex_nested_commutes Q π hπ i (i+1) (by omega)) (G.comap (markedVortexVertexEmbedding Q i)) d
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ) mark (e x) (e y)
    rw [←marked_vortex_nested_graph Q i (i+1) (by omega),marked_vortex_nested_raw_restriction Q i (i+1) (by omega) σ,he x,he y] at hx
    exact hx
  rw [hmatrix] at ht
  exact ht

theorem marked_vortex_inner_spoke_cut_transport
    (π:Equiv.Perm V) (d i:ℕ) (a:Γ) (j:Color) (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (mark:Bool) (δ h:ℝ) (hn:0<Fintype.card (markedVortexVertexType Q (i+1)))
    (hu:0<Fintype.card (markedVortexHubType Q (i+1))) (hh:0≤h)
    (hcut:BipartiteLargeCut (relationMultiplicity (fun x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j mark
      (markedVortexVertexEmbedding Q (i+1) x) (markedVortexHubEmbedding Q (i+1) u))) δ h):
    BipartiteLargeCut (relationMultiplicity (fun x:↥(markedVortexInnerVertices Q i)=>fun u:↥(markedVortexInnerHubs Q i)=>
      retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j mark
        (markedVortexVertexEmbedding Q i x.val) (markedVortexHubEmbedding Q i u.val))) δ h:=by
  let e:↥(markedVortexInnerVertices Q i)↪markedVortexVertexType Q (i+1):=(markedVortexInnerVertexEquiv Q i).symm.toEmbedding
  let f:↥(markedVortexInnerHubs Q i)↪markedVortexHubType Q (i+1):=(markedVortexInnerHubEquiv Q i).symm.toEmbedding
  have hcardV:Fintype.card ↥(markedVortexInnerVertices Q i)=Fintype.card (markedVortexVertexType Q (i+1)):=
    Fintype.card_congr (markedVortexInnerVertexEquiv Q i).symm
  have hcardU:Fintype.card ↥(markedVortexInnerHubs Q i)=Fintype.card (markedVortexHubType Q (i+1)):=
    Fintype.card_congr (markedVortexInnerHubEquiv Q i).symm
  have hI:0<Fintype.card ↥(markedVortexInnerVertices Q i):=by rw [hcardV];exact hn
  have hJ:0<Fintype.card ↥(markedVortexInnerHubs Q i):=by rw [hcardU];exact hu
  have ht:=bipartiteLargeCut_embedding e f _ hI hJ 1 δ δ h (by norm_num) hh
    (by rw [hcardV];norm_num) (by rw [hcardU];norm_num) (by ring_nf;exact le_rfl) hcut
  convert ht using 1
  funext x y
  rfl
end Oberwolfach

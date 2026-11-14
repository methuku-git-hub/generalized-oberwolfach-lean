module

public import Oberwolfach.MarkedVortexInnerCutTransport
public import Oberwolfach.MarkedCutFamiliesToLargeCut

@[expose] public section
/-! The normalized rim and spoke cut fields on a parent vortex level. -/
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

theorem marked_vortex_inner_cut_fields
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d i:ℕ) (a:Γ) (j:Color) (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (α p k tstar ζ δ h:ℝ)
    (hn:0<Fintype.card (markedVortexVertexType Q (i+1))) (hu:0<Fintype.card (markedVortexHubType Q (i+1)))
    (hh:0≤h) (hδα:δ≤α/32) (hδp:δ≤p/32) (hδk:δ≤k/32) (hδt:2*δ≤tstar/8)
    (hhp:h≤α*p/4) (hhk:h≤α*k/4) (hhs:h≤tstar/8-ζ)
    (hcut:MarkedCutFamiliesWithSpokes (G.comap (markedVortexVertexEmbedding Q (i+1)))
      (markedVortexPermutation Q π hπ (i+1)) d α p k tstar ζ
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q (i+1)) (markedVortexHubEmbedding Q (i+1)) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
        (markedVortexVertexEmbedding Q (i+1) x) (markedVortexHubEmbedding Q (i+1) u))):
    (∀ mark,BipartiteLargeCut
      (fun x:↥(markedVortexInnerVertices Q i)=>fun y:↥(markedVortexInnerVertices Q i)=>
        markedPhysicalRim (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
          (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1 (Sum.inl e)) mark x.val y.val) δ h) ∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (fun x:↥(markedVortexInnerVertices Q i)=>fun u:↥(markedVortexInnerHubs Q i)=>
      retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j mark
        (markedVortexVertexEmbedding Q i x.val) (markedVortexHubEmbedding Q i u.val))) δ h):=by
  letI : DecidableEq (markedVortexVertexType Q (i+1)) := fun x y => Subtype.instDecidableEq x y
  let P:=G.comap (markedVortexVertexEmbedding Q (i+1))
  let ρ:=markedVortexPermutation Q π hπ (i+1)
  let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q (i+1)) (markedVortexHubEmbedding Q (i+1)) z.1
  let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
    (markedVortexVertexEmbedding Q (i+1) x) (markedVortexHubEmbedding Q (i+1) u)
  have hr:=marked_cut_families_rim_large_cut P ρ d α p k tstar ζ δ h σ H hn hδα hδp hδk hhp hhk hcut
  have hs:=marked_cut_families_spoke_large_cut P ρ d α p k tstar ζ δ h σ H hn hu hδt hhs hcut
  have heq:(fun x y:markedVortexVertexType Q (i+1)=>Classical.propDecidable (x=y))=
      (fun x y:markedVortexVertexType Q (i+1)=>Subtype.instDecidableEq x y):=Subsingleton.elim _ _
  constructor
  · intro mark
    have hrr:=hr mark
    rw [heq] at hrr
    exact marked_vortex_inner_rim_cut_transport Q π hπ d i z.1 mark δ h hn hh hrr
  · intro mark
    have hss:=hs mark
    rw [heq] at hss
    exact marked_vortex_inner_spoke_cut_transport Q π d i a j z mark δ h hn hu hh hss
end Oberwolfach

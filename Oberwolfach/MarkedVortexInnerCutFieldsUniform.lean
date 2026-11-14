module

public import Oberwolfach.MarkedVortexInnerCutFields

@[expose] public section
/-! Cut-field conditions uniform in the actual sampling densities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
theorem marked_vortex_inner_cut_fields_uniform_densities
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d i:ℕ) (a:Γ) (j:Color) (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (α p k kstar tstar ζ δ h:ℝ)
    (hn:0<Fintype.card (markedVortexVertexType Q (i+1))) (hu:0<Fintype.card (markedVortexHubType Q (i+1)))
    (hα:0≤α) (hpk:kstar≤p) (hkk:kstar≤k)
    (hh:0≤h) (hδα:δ≤α/32) (hδstar:δ≤kstar/32) (hδt:2*δ≤tstar/8)
    (hhstar:h≤α*kstar/4) (hhs:h≤tstar/8-ζ)
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
        (markedVortexVertexEmbedding Q i x.val) (markedVortexHubEmbedding Q i u.val))) δ h) :=by
  have hδp:δ≤p/32:=by linarith
  have hδk:δ≤k/32:=by linarith
  have hhp:h≤α*p/4:=by nlinarith [mul_nonneg hα (sub_nonneg.mpr hpk)]
  have hhk:h≤α*k/4:=by nlinarith [mul_nonneg hα (sub_nonneg.mpr hkk)]
  exact marked_vortex_inner_cut_fields Q π hπ d i a j z α p k tstar ζ δ h hn hu hh hδα hδp hδk hδt hhp hhk hhs hcut
end Oberwolfach

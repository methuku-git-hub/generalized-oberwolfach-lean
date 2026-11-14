module

public import Oberwolfach.RetainedMarkedSpokeGeometry
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The retained spoke types are disjoint and separated by the successor
permutation on every actual parent vortex type. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_retained_spoke_geometry
    (G:SimpleGraph V) (D m d:ℕ) (hd:1≤d) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (a:Γ) (j:Color) (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a):
    ∀ i,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i
      let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f x) (g u);
      (∀ u:Z,∀ v:W,¬(H false v u ∧ H true v u)) ∧
      (∀ u:Z,∀ v w:W,H false v u→H true w u→v≠ρ w):=by
  intro i W Z f g ρ H
  constructor
  · intro u v
    exact retainedMarkedSpokes_disjoint π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j (f v) (g u)
  · intro u v w hv hw heq
    have hcomm:= (marked_vortex_permutation_compatibility Q π hpres i).1 w
    have heq':f v=π (f w):=by rw [heq];exact hcomm
    apply retainedMarkedSpokes_successor_disjoint π d hd (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j (f w) (g u)
    exact ⟨by rw [←heq'];exact hv,hw⟩
end Oberwolfach

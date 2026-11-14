module

public import Oberwolfach.DualCoordinateSupport
public import Oberwolfach.OrdinaryRawIntervalGeometry

@[expose] public section

/-! Coordinate locality for a spoke relation requiring two given hubs.
The relation is defined on the original raw sampling space, not by treating
its outcome-dependent common neighbourhood as a predetermined set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinaryPairHubEmbedding (u:U):(Sym2 V⊕(V×Unit))↪(Sym2 V⊕(V×U)):=
  Function.Embedding.sumMap (Function.Embedding.refl _) ⟨fun a=>(a.1,u),by
    intro a b h
    rcases a with ⟨a,⟨⟩⟩
    rcases b with ⟨b,⟨⟩⟩
    simp only [Prod.mk.injEq] at h
    simp [h]⟩

def ordinaryPairHubSpokes (π:Equiv.Perm V) (d:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (j:Color) (u u':U):V→Unit→Prop:=
  fun v _=>rawWheelSpokes π d σ j v u∧rawWheelSpokes π d σ j v u'

def ordinaryPairHubCoordinates (π:Equiv.Perm V) (d:ℕ) (u u':U)
    (a:Sym2 V⊕(V×Unit)):Finset (RawWheelCoordinate V U):=
  rawWheelResourceCoordinates π d (ordinaryPairHubEmbedding u a)∪
    rawWheelResourceCoordinates π d (ordinaryPairHubEmbedding u' a)

theorem ordinary_pair_hub_coordinates_bounds (π:Equiv.Perm V) (d:ℕ) (u u':U):
    (∀ a,(ordinaryPairHubCoordinates π d u u' a).card≤2*(4*d+3)) ∧
    (∀ e,(Finset.univ.filter (fun a=>e∈ordinaryPairHubCoordinates π d u u' a)).card≤2*(4*d+3)) := by
  exact paired_coordinate_support_bounds (rawWheelResourceCoordinates π d)
    (ordinaryPairHubEmbedding u) (ordinaryPairHubEmbedding u') (4*d+3)
    (rawWheelResourceCoordinates_card π d) (rawWheelResourceCoordinates_reverse_card π d)

theorem ordinary_pair_hub_resource_supported
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (j:Color) (u u':U)
    (a:Sym2 V⊕(V×Unit)) (σ τ:RawWheelOutcome V U Γ Color)
    (ha:∀ e∈ordinaryPairHubCoordinates π d u u' a,σ e=τ e):
    ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u') a=
      ordinaryResourceState (rawWheelGraph P τ) (ordinaryPairHubSpokes π d τ j u u') a := by
  have h₁:=rawWheelResourceState_supported P π d j (ordinaryPairHubEmbedding u a) σ τ
    (fun e he=>ha e (Finset.mem_union_left _ he))
  have h₂:=rawWheelResourceState_supported P π d j (ordinaryPairHubEmbedding u' a) σ τ
    (fun e he=>ha e (Finset.mem_union_right _ he))
  cases a with
  | inl e=>simpa [ordinaryPairHubEmbedding,ordinaryResourceState] using h₁
  | inr a=>
    rcases a with ⟨v,⟨⟩⟩
    have he₁:decide (rawWheelSpokes π d σ j v u)=decide (rawWheelSpokes π d τ j v u):=by
      simpa [ordinaryPairHubEmbedding,ordinaryResourceState] using h₁
    have he₂:decide (rawWheelSpokes π d σ j v u')=decide (rawWheelSpokes π d τ j v u'):=by
      simpa [ordinaryPairHubEmbedding,ordinaryResourceState] using h₂
    have hh₁:(rawWheelSpokes π d σ j v u↔rawWheelSpokes π d τ j v u):=by simpa only [decide_eq_decide] using he₁
    have hh₂:(rawWheelSpokes π d σ j v u'↔rawWheelSpokes π d τ j v u'):=by simpa only [decide_eq_decide] using he₂
    simp only [ordinaryResourceState,Sum.elim_inr,ordinaryPairHubSpokes,decide_eq_decide]
    exact and_congr hh₁ hh₂
end Oberwolfach

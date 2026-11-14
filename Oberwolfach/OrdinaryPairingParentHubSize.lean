module

public import Oberwolfach.MixedFreshPairingParentInsideRoots
public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! The pairing parent's hub classes have a uniform lower bound on the
    physical vertex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_pairing_parent_hub_size
    (m b₀:ℕ) (γ κ b B p₀ a ε η:ℝ) (hκ:0≤κ)
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X:Finset V) (Z:Finset U)
    (tw:{v:V // v∉X}→ℝ)
    (data:MixedFreshPairingParentInsideRoots m b₀ γ κ b B p₀ a ε η Qfactor F
      (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
      (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr) tw)
    (hu:Fintype.card U≤Fintype.card V):
    ∀j:{u:U // u∉Z},min (κ/2) 1*Fintype.card (V⊕U)≤((ordinaryBoundaryHubSet H Z X j).card:ℝ) :=by
  intro j
  have hcard:(Fintype.card (V⊕U):ℝ)≤2*Fintype.card V:=by
    have hh:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hu
    rw [Fintype.card_sum,Nat.cast_add]
    linarith
  have hm:0≤min (κ/2) 1:=le_min (by positivity) (by norm_num)
  have h1:=mul_le_mul_of_nonneg_left hcard hm
  have h2:=mul_le_mul_of_nonneg_right (min_le_left (κ/2) (1:ℝ)) (Nat.cast_nonneg (Fintype.card V))
  have h3:=data.hub_size j
  nlinarith only [h1,h2,h3]
end Oberwolfach

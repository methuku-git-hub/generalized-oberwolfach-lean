module

public import Oberwolfach.OrdinaryTriangleRootFirstSampleEvent
public import Oberwolfach.MixedFreshParentInsideClassSizes

@[expose] public section
/-! Derive the boundary class margins from the actual mixed-factor parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_root_first_conditions_from_parent
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X:Finset V) (Z:Finset U)
    (γ κ b B ε ηf p εsup τ ν η ell ζ:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hζ:0<ζ) (hp:0<p) (hp1:p≤1) (hτ:0≤τ)
    (hu:Fintype.card U≤Fintype.card V)
    (data:MixedFreshParentDataInsideRoots γ κ b B ε ηf Qfactor F
      (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
      (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr))
    (hε:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4)
    (hclass:τ+ν+ell≤ζ*min (κ/2) γ*p/4) (hblock:ν+η≤ζ*min (κ/2) γ*p/4)
    (hpκ:p≤4*ζ*min (κ/2) γ) (hsqrt:20*Real.sqrt (2*p)≤ζ*min (κ/2) γ/2)
    (horder:2≤ζ*min (κ/2) γ*p*Fintype.card (V⊕U)/4):
    OrdinaryTriangleRootFirstScaledConditions Q H X Z p εsup τ ν η ell (min (κ/2) γ) ζ :=by
  have hVW:(Fintype.card (V⊕U):ℝ)≤2*Fintype.card V:=by
    have hh: (Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hu
    rw [Fintype.card_sum, Nat.cast_add]
    linarith
  obtain ⟨hY,hZ⟩:=mixed_fresh_inside_parent_class_sizes γ κ b B ε ηf hγ.le hκ.le Qfactor F
    (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
    (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
    (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
    (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr) data hVW
  refine ⟨hp,hp1,hτ,lt_min (by positivity) hγ,hζ,hε,hsupport,hclass,hblock,hpκ,hsqrt,horder,hY,?_⟩
  intro i
  simpa only [Finset.card_image_iff.mpr Sum.inr_injective.injOn] using hZ i
end Oberwolfach

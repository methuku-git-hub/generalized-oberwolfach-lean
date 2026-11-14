module

public import Oberwolfach.OrdinaryRawPairRestrictionGeometry
public import Oberwolfach.RawOrdinaryDomainIndexEvent
public import Oberwolfach.CommonImageOfEmbedding

@[expose] public section
/-! The bounded hub-domain tests and their exact means restrict from the
ambient sample to any compatible induced pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem ordinary_raw_domain_pair_restriction (f:W↪V) (g:Z↪U)
    (F:SimpleGraph V) (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hcomm:∀x,f (ρ x)=π (f x))
    (d h:ℕ) (D:Finset Z) (pH:ℝ) (j:Color) (t:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (hrows:RawOrdinaryDomainIndices F π d h (D.image g) pH j t σ):
    RawOrdinaryDomainIndices (F.comap f) ρ d h D pH j t (ordinaryRawRestrictPair f g σ):=by
  intro S hS hfree
  let σ':=ordinaryRawRestrictPair f g σ
  let N:=fun x:W=>Finset.univ.filter (fun z:Z=>rawWheelSpokes ρ d σ' j x z)
  let M:=fun x:V=>Finset.univ.filter (fun u:U=>rawWheelSpokes π d σ j x u)
  have he:(common D S N).image g=common (D.image g) (S.image f) M:=by
    apply common_image_of_maps g f D S N M
    intro x z
    simpa only [N,M,Finset.mem_filter,Finset.mem_univ,true_and] using
      ordinaryRawRestrictPair_spoke f f.injective g π ρ hcomm d σ j x z
  have hc:(common D S N).card=(common (D.image g) (S.image f) M).card:=by
    have hh:=congrArg Finset.card he
    simpa only [Finset.card_image_of_injective _ g.injective] using hh
  have hfree':∀v∈S.image f,∀w∈S.image f,¬F.Adj v w:=by
    intro v hv w hw
    obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hv
    obtain ⟨y,hy,hyw⟩:=Finset.mem_image.mp hw
    rw [←hxv,←hyw]
    exact hfree x hx y hy
  have hh:=hrows (S.image f) (by simpa only [Finset.card_image_of_injective _ f.injective] using hS) hfree'
  rw [Finset.card_image_of_injective _ f.injective,Finset.card_image_of_injective _ g.injective,←hc] at hh
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach

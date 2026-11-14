module

public import Oberwolfach.OrdinaryRawPairRestrictionGeometry
public import Oberwolfach.RawOrdinaryRowEvent
public import Oberwolfach.CommonImageOfEmbedding

@[expose] public section
/-! A bounded row event on the ambient sample supplies the identical event
on a compatible induced pair, with the same mean and error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem ordinary_raw_rows_pair_restriction (f:W↪V) (g:Z↪U)
    (P:SimpleGraph V) (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hcomm:∀x,f (ρ x)=π (f x))
    (d h:ℕ) (D:Finset W) (p:ℝ) (s:U→Color→ℝ) (j:Color) (t:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (hrows:RawOrdinaryRows P π d h (D.image f) p s j t σ):
    RawOrdinaryRows (P.comap f) ρ d h D p (fun z=>s (g z)) j t (ordinaryRawRestrictPair f g σ):=by
  intro S J hS hJ
  let σ':=ordinaryRawRestrictPair f g σ
  let N:=fun x:W=>(rawWheelGraph (P.comap f) σ').neighborFinset x
  let M:=fun x:V=>(rawWheelGraph P σ).neighborFinset x
  let K:=fun z:Z=>Finset.univ.filter (fun x:W=>rawWheelSpokes ρ d σ' j x z)
  let L:=fun u:U=>Finset.univ.filter (fun x:V=>rawWheelSpokes π d σ j x u)
  let N₀:=fun x:W=>(P.comap f).neighborFinset x
  let M₀:=fun x:V=>P.neighborFinset x
  have hrim:(common D S N).image f=common (D.image f) (S.image f) M:=by
    apply common_image_of_maps f f D S N M
    intro x y
    simpa only [N,M,SimpleGraph.mem_neighborFinset] using ordinaryRawRestrictPair_rim f g P σ x y
  have hspoke:(common (common D S N) J K).image f=
      common (common (D.image f) (S.image f) M) (J.image g) L:=by
    have hh:=common_image_of_maps f g (common D S N) J K L (by
      intro z x
      simpa only [K,L,Finset.mem_filter,Finset.mem_univ,true_and] using
        ordinaryRawRestrictPair_spoke f f.injective g π ρ hcomm d σ j x z)
    simpa only [hrim] using hh
  have hbase:(common D S N₀).image f=common (D.image f) (S.image f) M₀:=by
    apply common_image_of_maps f f D S N₀ M₀
    intro x y
    simp only [N₀,M₀,SimpleGraph.mem_neighborFinset,SimpleGraph.comap_adj]
  have hcount:(common (common D S N) J K).card=
      (common (common (D.image f) (S.image f) M) (J.image g) L).card:=by
    have hh:=congrArg Finset.card hspoke
    simpa only [Finset.card_image_of_injective _ f.injective] using hh
  have hbasecount:(common D S N₀).card=(common (D.image f) (S.image f) M₀).card:=by
    have hh:=congrArg Finset.card hbase
    simpa only [Finset.card_image_of_injective _ f.injective] using hh
  have hprod:(∏u∈J.image g,s u j)=(∏z∈J,s (g z) j):=by
    rw [Finset.prod_image]
    intro a _ b _ hab
    exact g.injective hab
  have hh:=hrows (S.image f) (J.image g) (by simpa only [Finset.card_image_of_injective _ f.injective] using hS)
    (by simpa only [Finset.card_image_of_injective _ g.injective] using hJ)
  rw [Finset.card_image_of_injective _ f.injective,hprod,←hcount,←hbasecount] at hh
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach

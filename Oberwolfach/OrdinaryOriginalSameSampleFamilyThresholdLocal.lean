module

public import Oberwolfach.OrdinaryOriginalSameSampleFamilyThresholdLocalShape
public import Oberwolfach.OrdinaryOriginalSameSampleFamilyLocal
public import Oberwolfach.OrdinaryIndexedAllowedFromThreshold

@[expose] public section
/-! The original component-threshold hypotheses directly yield the matching,
balance and reserved tests on one sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_same_sample_family_threshold_local
    (L rstar:ℕ) (βfreq ρ₀ α:ℝ) (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1)
    (hρ₀:0<ρ₀) (hα:0<α):
    OrdinaryOriginalSameSampleFamilyThresholdLocalShape L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα :=by
  unfold OrdinaryOriginalSameSampleFamilyThresholdLocalShape
  have hselect:=ordinary_original_same_sample_family_local L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα
  unfold OrdinaryOriginalSameSampleFamilyLocalShape at hselect
  obtain ⟨m,k,hL,hm,heven,hlen,hratio,hselect⟩:=hselect
  refine ⟨m,k,hL,hm,heven,hlen,hratio,?_⟩
  intro θ hθ hθ1
  obtain ⟨βList,lamList,ζDel,smin,hβList,hβList1,hlamList,hζDel,hsmin,hsminEq,hselect⟩:=hselect θ hθ hθ1
  refine ⟨βList,lamList,ζDel,smin,hβList,hβList1,hlamList,hζDel,hsmin,hsminEq,?_⟩
  intro dNeed
  obtain ⟨d,K,rank,hdNeed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,hselect⟩:=hselect dNeed
  refine ⟨d,K,rank,hdNeed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,?_⟩
  intro hd' θhost hθhost
  obtain ⟨BO,hBO,hselect⟩:=hselect hd' θhost hθhost
  refine ⟨BO,hBO,?_⟩
  intro lam aRow γ cap hlam hlam1 ha hγ hcap' haBound hslack
  obtain ⟨τ,t,ξ,b,hτ,ht,hξ,hb,hbcap,hτhalf,hτrate,hξrate,hξhalf,hselect⟩:=
    hselect lam aRow γ cap hlam hlam1 ha hγ hcap' haBound hslack
  refine ⟨τ,t,ξ,b,hτ,ht,hξ,hb,hbcap,hτhalf,hτrate,hξrate,hξhalf,?_⟩
  intro ζ χpair χlist σ χbal χbd χnbr χpairR χpath hζ hχpair hχlist hσ hχbal hχbd hχnbr hχpairR hχpath
  obtain ⟨a,haEvent,N,hselect⟩:=hselect ζ χpair χlist σ χbal χbd χnbr χpairR χpath hζ hχpair hχlist hσ hχbal hχbd hχnbr hχpairR hχpath
  refine ⟨a,haEvent,N,?_⟩
  intro n hn hn2 U _ _ hUn F hF hfreq D hD hρlo hρhi hthreshold P hreg π hdegree hnoshort
  obtain ⟨Allowed,hthreshold',hallowed⟩:=ordinary_indexed_allowed_from_threshold θhost F hF hthreshold
  exact hselect n hn hn2 U hUn F hF hfreq D hD hρlo hρhi Allowed hallowed hthreshold' P hreg π hdegree hnoshort
end Oberwolfach

module

public import Oberwolfach.OrdinaryOriginalSameSampleFamilyShape
public import Oberwolfach.OrdinaryOriginalSameSamplePackages

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_same_sample_family
    (L rstar:ℕ) (βfreq ρ₀ α:ℝ) (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1)
    (hρ₀:0<ρ₀) (hα:0<α):
    OrdinaryOriginalSameSampleFamilyShape L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα :=by
  unfold OrdinaryOriginalSameSampleFamilyShape
  have hselect:=ordinary_original_same_sample_packages L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα
  unfold OrdinaryOriginalSameSamplePackagesShape at hselect
  obtain ⟨m,k,hL,hm,heven,hlen,hratio,hselect⟩:=hselect
  refine ⟨m,k,hL,hm,heven,hlen,hratio,?_⟩
  intro θ hθ hθ1
  obtain ⟨βList,lamList,ζDel,smin,hβList,hβList1,hlamList,hζDel,hsmin,hsminEq,hselect⟩:=hselect θ hθ hθ1
  refine ⟨βList,lamList,ζDel,smin,hβList,hβList1,hlamList,hζDel,hsmin,hsminEq,?_⟩
  intro dNeed
  obtain ⟨d,K,rank,hdNeed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,hselect⟩:=hselect dNeed
  refine ⟨d,K,rank,hdNeed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,?_⟩
  intro hd' θhost hθhost
  obtain ⟨B,hB,hselect⟩:=hselect hd' θhost hθhost
  refine ⟨B,hB,?_⟩
  intro lam aRow γ cap hlam hlam1 ha hγ hcap' haBound hslack
  obtain ⟨τ,t,ξ,b,hτ,ht,hξ,hb,hbcap,hτhalf,hτrate,hξrate,hξhalf,hselect⟩:=
    hselect lam aRow γ cap hlam hlam1 ha hγ hcap' haBound hslack
  refine ⟨τ,t,ξ,b,hτ,ht,hξ,hb,hbcap,hτhalf,hτrate,hξrate,hξhalf,?_⟩
  intro ζ χpair χlist σ χbal χbd χnbr χpairR χpath hζ hχpair hχlist hσ hχbal hχbd hχnbr hχpairR hχpath
  obtain ⟨a,haEvent,N,hselect⟩:=hselect ζ χpair χlist σ χbal χbd χnbr χpairR χpath hζ hχpair hχlist hσ hχbal hχbd hχnbr hχpairR hχpath
  refine ⟨a,haEvent,N,?_⟩
  intro n hn hn2 U _ _ hUn F hF hfreq D hD hρlo hρhi Allowed hAllowed hthreshold P hreg π hdegree hnoshort
  obtain ⟨i₀,rsv,C,hi,hslo,hs1,hclass,hsize,hcard,hreserve,sampling,w,seed,hweight,hNorm,hzero,hseed,hselect⟩:=
    hselect n hn hn2 U hUn F hF hfreq D hD hρlo hρhi Allowed hAllowed hthreshold P hreg π hdegree hnoshort
  refine ⟨i₀,rsv,C,hi,hslo,hs1,hclass,hsize,hcard,hreserve,sampling,w,seed,hweight,hNorm,hzero,hseed,?_⟩
  intro R _ ν E εE p q s p₂ μ wM wO Core Match hE
  have hPrior:=hselect ν E εE hE
  apply hPrior.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  intro Del hDel tret Jret
  exact ordinary_selected_matching_packages_form_family F hF C i₀ rsv θ lam aRow γ m d π P Del z.1 tret Jret
    (hz.2 Del hDel tret Jret)
end Oberwolfach

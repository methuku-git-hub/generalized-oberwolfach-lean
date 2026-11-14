module

public import Oberwolfach.OrdinaryOriginalSameSamplePackagesShape
public import Oberwolfach.OrdinaryNormalizedMatchingBalanceReserveOnlyNamed

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_same_sample_packages
    (L rstar:ℕ) (βfreq ρ₀ α:ℝ) (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1)
    (hρ₀:0<ρ₀) (hα:0<α):
    OrdinaryOriginalSameSamplePackagesShape L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα :=by
  unfold OrdinaryOriginalSameSamplePackagesShape
  have hselect:=ordinary_normalized_matching_balance_reserve_only_named L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα
  unfold OrdinaryNormalizedMatchingBalanceReserveOnlyShape at hselect
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
  have hpackChoice:=ordinary_original_selected_matching_packages rank K m k d hrank hK hm hd hrankm hrankO
    θ aRow γ α ρ₀ lam cap hθ hθ1 ha hγ hα hρ₀ hlam hlam1 hcap' haBound hdθ hslack hcap B hB
  unfold OrdinaryOriginalSelectedMatchingPackagesShape at hpackChoice
  obtain ⟨τ,t,ξ,b,hτ,ht,hξ,hb,hbcap,hτhalf,hτrate,hξrate,hξhalf,Npack,hpack⟩:=hpackChoice
  refine ⟨τ,t,ξ,b,hτ,ht,hξ,hb,hbcap,hτhalf,hτrate,hξrate,hξhalf,?_⟩
  intro ζ χpair χlist σ χbal χbd χnbr χpairR χpath hζ hχpair hχlist hσ hχbal hχbd hχnbr hχpairR hχpath
  obtain ⟨a,haEvent,Nselect,hselect⟩:=hselect τ hτ t ξ ζ χpair χlist ht hξ hζ hχpair hχlist
    σ χbal χbd χnbr χpairR χpath hσ hχbal hχbd hχnbr hχpairR hχpath
  refine ⟨a,haEvent,max Npack Nselect,?_⟩
  intro n hn hn2 U _ _ hUn F hF hfreq D hD hρlo hρhi Allowed hAllowed hthreshold P hreg π hdegree hnoshort
  obtain ⟨i₀,rsv,C,hi,hslo,hs1,hclass,hsize,hcard,hreserve,sampling,w,seed,hweight,hNorm,hzero,hseed,hselect⟩:=
    hselect n (by omega) hn2 U hUn F hF hfreq D hD hρlo hρhi Allowed hAllowed hthreshold P hreg π hdegree hnoshort
  refine ⟨i₀,rsv,C,hi,hslo,hs1,hclass,hsize,hcard,hreserve,sampling,w,seed,hweight,hNorm,hzero,hseed,?_⟩
  intro R _ ν E εE p q s p₂ μ wM wO Core Match hE
  have hClass:OrdinaryClassReserveBound F hF i₀ rsv:=by
    convert hreserve using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hCres:∀u c,c∈C u→Fintype.card c=i₀.val+1:=by
    intro u c hc
    rw [hi]
    exact hsize u c hc
  have hres:∀u,((i₀.val+1:ℕ):ℝ)*(C u).card=rsv*n:=by
    intro u
    simpa only [hi] using hcard u
  have hPrior:=hselect ν E εE hE
  apply hPrior.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz,?_⟩
  intro Del hDel tret Jret
  have hCore:Core z.1:=(hz.1.1.1.2).1
  exact hpack n (by omega) hn2 U hUn F hF Allowed hAllowed i₀ rsv smin hsmin hslo hs1 hClass
    P D hreg hD θhost hθhost hdegree hρlo hρhi π hnoshort sampling w hweight hNorm seed hseed C hCres hres Del hDel z.1
    hCore tret Jret
end Oberwolfach

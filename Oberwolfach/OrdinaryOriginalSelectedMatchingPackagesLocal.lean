module

public import Oberwolfach.OrdinaryOriginalSelectedMatchingPackagesLocalShape

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_original_selected_matching_packages_local
    (r K m k d:ℕ) (hr:2≤r) (hK3:3≤K) (hm:7≤m) (hd:2≤d)
    (hrM:2*(m+1)≤r) (hrO:∀i:Fin K,2*(longPaddedSeedExponent i+2)≤r)
    (θ a γ αHost ρ₀ lam cap:ℝ) (hθ:0<θ) (hθ1:θ≤1/100) (ha:0<a) (hγ:0<γ)
    (hα:0<αHost) (hρ₀:0<ρ₀) (hlam:0<lam) (hlam1:lam≤1) (hcap:0<cap)
    (haBound:a≤θ/(1600*(K:ℝ)*(K:ℝ))) (hda:1/θ≤d)
    (hslack:lam+γ*(1-θ+lam)<θ)
    (hcutHost:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (B:Fin K→ℝ) (hB:∀i,0<B i):
    OrdinaryOriginalSelectedMatchingPackagesLocalShape r K m k d hr hK3 hm hd hrM hrO θ a γ αHost ρ₀ lam cap
      hθ hθ1 ha hγ hα hρ₀ hlam hlam1 hcap haBound hda hslack hcutHost B hB :=by
  unfold OrdinaryOriginalSelectedMatchingPackagesLocalShape
  obtain ⟨p₀,BM,BO,Kcd,hp₀eq,hp₀,hBMeq,hBM,hBOeq,hBO,hKcd,hpair⟩:=
    ordinary_matching_weight_constants K m k αHost ρ₀ hα hρ₀ B hB
  obtain ⟨ε,hε,Nmatch,hmatch⟩:=ordinary_residual_packages_local_rows
    r K m d hr hK3 hm hd hrM hrO θ a γ Kcd BM hθ hθ1 ha hγ hKcd hBM.le haBound BO (fun i=>(hBO i).le) hpair hcutHost
  let loss:Option (Fin K)→ℝ:=fun i=>match i with
    | none=>22*((m:ℝ)+1)^4*BM
    | some i=>10*((longPaddedSeedExponent i:ℝ)+2)^4*BO i
  have hloss:0≤∑i,loss i:=by
    apply Finset.sum_nonneg
    intro i hi
    cases i with
    | none=>dsimp [loss];positivity
    | some i=>have hh:=hBO i;dsimp [loss];positivity
  obtain ⟨τ,t,ξ,b,hτ,ht,hξ,hb,hbcap,hτhalf,hτrate,hξrate,hξhalf,hterr1,hterr2,hterr3⟩:=
    ordinary_matching_tolerances_after_weights K (by omega) θ lam (1/2) ε (∑i,loss i) cap
      hθ hlam hlam1 (by norm_num) hε hloss hcap
  have hτrate':τ≤lam/8:=by nlinarith
  have hξrate':ξ≤lam/8:=by nlinarith
  have hξhalf':ξ≤1/4:=by nlinarith
  obtain ⟨Ninput,hinput⟩:=ordinary_original_selected_matching_inputs_eventually K m k d (by omega) hm hd
    αHost θ τ ρ₀ hα hθ hθ1 hτ hρ₀ hda B hB
  refine ⟨τ,t,ξ,b,hτ,ht,hξ,hb,hbcap,hτhalf,hτrate',hξrate',hξhalf',max Nmatch Ninput,?_⟩
  intro n hn hn2 U _ _ hU F hF Allowed hAllowed i₀ rsv smin hsmin hslo hs1 hClass P D hreg hD
    θhost hhost hdegree hρlo hρhi π hnoshort sampling w hw he seed hseed Cres hCres hres Del hDel Inner σ p₂ q s wM wO hCore tret Jret
  have hn0:0<n:=by omega
  have hnR:0≤(n:ℝ):=by positivity
  have hρ:0 < initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hDr:0<(D:ℝ):=by exact_mod_cast hD
  have hsize:initialIndexDensity U D*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    simp [initialIndexDensity,ne_of_gt hDr]
  have hrs0:0≤rsv:=(hsmin.trans_le hslo).le
  have hsum2:2*p₂+2*(0:ℝ)≤1:=by
    have h:=sampling.hsum
    have hp:=sampling.hp
    have hu:=sampling.hu
    dsimp [p₂] at *
    linarith
  obtain ⟨hshort,hWM,hWO,hdeg,hbudS,hbudR⟩:=hinput n (by omega) hn2 U F hF Allowed hAllowed i₀ rsv hrs0 hs1 hClass
    P D hreg hD θhost hhost hdegree hρlo hρhi π w hw seed hseed
  have hWM':∀W,0≤wM W ∧ wM W≤BM/(n:ℝ)^m:=by
    rw [hBMeq,hp₀eq]
    exact hWM
  have hWO':∀i W,0≤wO i W ∧ wO i W≤BO i/(n:ℝ)^(longPaddedSeedExponent i+1):=by
    intro i W
    rw [hBOeq i,hp₀eq]
    exact hWO i W
  have hErrors:=ordinary_matching_event_error_inputs K n hn0 θ lam (1/2) ε (∑i,loss i) τ t ξ b (b*n)
    hloss hτ.le hξ.le hτhalf hτrate hξrate hξhalf (le_refl _) hterr1 hterr2 hterr3
  obtain ⟨hτhalf',hcountHalf,hτ0,hcount0,hτrate'',hcountRate,hξn,herr1,herr2,herr3⟩:=hErrors
  have hδ:∀x,(Del.degree x:ℝ)≤b*n:=hDel
  have hη:=hmatch n (by omega) hn0 U hU F hF Allowed hAllowed i₀ rsv (initialIndexDensity U D) D
    hrs0 hs1 hda hρ hρhi hDr hsize hClass (1/2) (by norm_num) P Del Inner π (b*n) hδ wM hWM' wO hWO' σ τ t (ξ*n)
    ht.le hτhalf' hcountHalf lam hlam.le hτ0 hcount0 hτrate'' hcountRate hslack w rfl Cres hCres hres
    hshort herr1 herr2 herr3 (τ/4) (successorWeightLower k (αHost/4)) (successorWeightUpper k (αHost/4)) 0 (by norm_num)
    seed hseed rfl (fun i C=>(hw i C).1) B (fun i=>(hB i).le) (fun i C=>(hw i C).2) he hdeg
    (fun i _=>hbudS i) (fun i _=>hbudR i) hnoshort sampling.hq sampling.hQ sampling.hs sampling.hS hsum2 ξ hξn hCore tret Jret
  unfold OrdinarySelectedMatchingPackagesLocalResult
  exact hη
end Oberwolfach

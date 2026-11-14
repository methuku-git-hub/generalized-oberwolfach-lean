module

public import Oberwolfach.OrdinaryFineCoverNormalizedRates
public import Oberwolfach.OrdinaryComplementReserveSizeInputs
public import Oberwolfach.OrdinaryInitialDeepSampledCoverHierarchy

@[expose] public section
/-! Convert one actual buffered root and fine cover into the exact size,
failure-budget, rate and integer-capacity inputs of the wheel certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_finish_inputs_from_schedule
    (m n₀ Nreserve Nclean Ncert Nfinish:ℕ) (X T:Finset V) (Z W:Finset U)
    (ξ aLoad lam eParent hParent ε βe βh θmatch p δsample ellCap finishCap kcap rate ν cap τ Lconf:ℝ)
    (hξ:0≤ξ) (ha:0≤aLoad) (hlam:0≤lam) (hlam1:lam≤1/4)
    (hsize:max (max (max (4*n₀) (4*Nreserve)) (max Nclean 64)) (max Ncert Nfinish)≤X.card)
    (hroot:(T.card:ℝ)+W.card≤lam*Fintype.card V)
    (hell:max (18*aLoad+3*lam) ((3*aLoad+lam)*((m:ℝ)+1))≤ellCap)
    (hcover:10*ξ≤finishCap) (hτ:0≤τ) (hτcap:τ≤cap)
    (hLconf:Lconf≤kcap^2*Fintype.card (V⊕U))
    (hfinish:∀n:ℕ,Nfinish≤n→2≤θmatch*p*n/4 ∧
      ∃Kcap Dmax:ℕ,0<Kcap ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤kcap^2*n ∧
      ∀τ ηrate ellrate Lconf:ℝ,0≤τ→τ≤cap→0≤ηrate→ηrate≤finishCap→0≤ellrate→ellrate≤ellCap→
        Lconf≤kcap^2*n→
        (βe*n+3*max (ηrate*n) (ellrate*n)≤(eParent*ε)*n ∧
         βh*n+2*(ellrate*n)≤(hParent*ε)*n) ∧
        (τ+ν≤p^2/4 ∧ τ+ν+(p*ellrate+δsample)≤θmatch*p/4 ∧ ν+ηrate≤θmatch*p/4) ∧
        (((n*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
          (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((Kcap+Dmax:ℕ):ℝ))+
          (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*(ν*n) ∧
         ν*n+ηrate*n+2*((2*p)*n)+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*n)):
    let n:ℝ:=Fintype.card (V⊕U);
    let cover:=10*ξ*X.card;
    let ell:=max (18*aLoad*Fintype.card V+3*((W.card:ℝ)+T.card))
      (3*aLoad*Fintype.card V*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1));
    ∃ηrate ellrate:ℝ,∃Kcap Dmax:ℕ,
      0≤ηrate ∧ ηrate≤finishCap ∧ 0≤ellrate ∧ ellrate≤ellCap ∧
      ηrate*n=cover ∧ ellrate*n=ell ∧ Ncert≤X.card ∧
      n₀≤Fintype.card ↥(Finset.univ\T) ∧
      Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)) ∧
      Nclean≤Fintype.card (V⊕U) ∧
      1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)≤(1/16:ℝ) ∧
      (1/16:ℝ)+2/n≤1/8 ∧ 2≤θmatch*p*n/4 ∧ 0<Kcap ∧ (2*p)*n≤(Dmax:ℝ) ∧
      (βe*n+3*max (ηrate*n) (ellrate*n)≤(eParent*ε)*n ∧
       βh*n+2*(ellrate*n)≤(hParent*ε)*n) ∧
      (τ+ν≤p^2/4 ∧ τ+ν+(p*ellrate+δsample)≤θmatch*p/4 ∧ ν+ηrate≤θmatch*p/4) ∧
      (((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
        (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((Kcap+Dmax:ℕ):ℝ))+
        (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*(ν*n) ∧
       ν*n+ηrate*n+2*((2*p)*n)+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*n):=by
  intro n cover ell
  have hXV:X.card≤Fintype.card V:=Finset.card_le_univ X
  have hVlarge:max (max (max (4*n₀) (4*Nreserve)) (max Nclean 64)) (max Ncert Nfinish)≤Fintype.card V:=hsize.trans hXV
  have hnV:0<Fintype.card V:=by omega
  let ηrate:ℝ:=cover/n
  let ellrate:ℝ:=ell/n
  have hnorm:=ordinary_fine_cover_normalized_rates m X T W ξ aLoad lam hnV hξ ha hlam hroot
  change 0<n ∧ 0≤ηrate ∧ 0≤ellrate ∧ ηrate*n=cover ∧ ellrate*n=ell ∧
    ηrate≤10*ξ ∧ ellrate≤max (18*aLoad+3*lam) ((3*aLoad+lam)*((m:ℝ)+1)) at hnorm
  obtain ⟨hnpos,hη,hell0,hηeq,helleq,hηbound,hellbound⟩:=hnorm
  have hηcap:ηrate≤finishCap:=hηbound.trans hcover
  have hellcap:ellrate≤ellCap:=hellbound.trans hell
  have hW0:(0:ℝ)≤W.card:=by positivity
  have hV0:(0:ℝ)≤Fintype.card V:=by positivity
  have hT:(T.card:ℝ)≤(1/4:ℝ)*Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_right hlam1 hV0
    linarith [hroot]
  have hcomp:=ordinary_complement_reserve_size_inputs T W n₀ Nreserve Nclean hT (by omega) (by omega) (by omega) (by omega)
  have hNphys:Nfinish≤Fintype.card (V⊕U):=by
    have hN:Nfinish≤Fintype.card V:=by omega
    exact hN.trans (Fintype.card_le_of_injective (Sum.inl:V→V⊕U) Sum.inl_injective)
  obtain ⟨horder,Kcap,Dmax,hK,hD,hDcap,hnum⟩:=hfinish (Fintype.card (V⊕U)) hNphys
  have hnum':=(hnum τ ηrate ellrate Lconf hτ hτcap hη hηcap hell0 hellcap hLconf)
  refine ⟨ηrate,ellrate,Kcap,Dmax,hη,hηcap,hell0,hellcap,hηeq,helleq,?_,?_,?_,?_,?_,?_,horder,hK,hD,hnum'.1,hnum'.2.1,hnum'.2.2⟩
  · omega
  · exact hcomp.1
  · exact hcomp.2.1
  · exact hcomp.2.2.1
  · exact hcomp.2.2.2.1
  · exact hcomp.2.2.2.2
end Oberwolfach

module

public import Oberwolfach.OrdinaryAsymmetricGeometryParentMarginHierarchy

@[expose] public section
/-! Fix the cleanup and completion rates after the fresh-sampling choices.
The actual host size then supplies integer wheel-capacity witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_asymmetric_finish_numeric_witness
    (m:ℕ) (eParent hParent ε βe βh θmatch p δsample ellCap finishCap kcap rate:ℝ)
    (hfinish:0<finishCap) (hfinishEll:finishCap≤ellCap)
    (hmargin:∀n ηrate ellrate:ℝ,0≤n→ηrate≤ellCap→ellrate≤ellCap→
      βe*n+3*max (ηrate*n) (ellrate*n)≤(eParent*ε)*n ∧
      βh*n+2*(ellrate*n)≤(hParent*ε)*n)
    (hrates:∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤finishCap→ν≤finishCap→η≤finishCap→ell≤ellCap→
      τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤θmatch*p/4 ∧ ν+η≤θmatch*p/4)
    (hcapacity:∀ν:ℝ,0≤ν→ν≤finishCap→∃N:ℕ,∀n:ℕ,N≤n→
      2≤θmatch*p*n/4 ∧ ∃K Dmax:ℕ,0<K ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤kcap^2*n ∧
      ∀(Lconf t η:ℝ),Lconf≤kcap^2*n→t≤ν*n→0≤η→η≤finishCap→
        ((n*Dmax*(m+1):ℕ):ℝ)/(K:ℝ)+
          (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((K+Dmax:ℕ):ℝ))+
          (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*t ∧
        ν*n+η*n+2*((2*p)*n)+((3*(K+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*n):
    ∃ν cap:ℝ,0<ν ∧ 0<cap ∧ ν≤finishCap ∧ cap≤finishCap ∧
    ∃N:ℕ,∀n:ℕ,N≤n→2≤θmatch*p*n/4 ∧
      ∃K Dmax:ℕ,0<K ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤kcap^2*n ∧
      ∀τ ηrate ellrate Lconf:ℝ,0≤τ→τ≤cap→0≤ηrate→ηrate≤finishCap→0≤ellrate→ellrate≤ellCap→
        Lconf≤kcap^2*n→
        (βe*n+3*max (ηrate*n) (ellrate*n)≤(eParent*ε)*n ∧
         βh*n+2*(ellrate*n)≤(hParent*ε)*n) ∧
        (τ+ν≤p^2/4 ∧ τ+ν+(p*ellrate+δsample)≤θmatch*p/4 ∧ ν+ηrate≤θmatch*p/4) ∧
        (((n*Dmax*(m+1):ℕ):ℝ)/(K:ℝ)+
          (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((K+Dmax:ℕ):ℝ))+
          (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*(ν*n) ∧
         ν*n+ηrate*n+2*((2*p)*n)+((3*(K+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*n):=by
  let ν:ℝ:=finishCap/2
  let cap:ℝ:=finishCap/2
  have hν:0<ν:=by dsimp [ν];positivity
  have hcap:0<cap:=by dsimp [cap];positivity
  have hνcap:ν≤finishCap:=by dsimp [ν];linarith
  have hcapcap:cap≤finishCap:=by dsimp [cap];linarith
  obtain ⟨N,hN⟩:=hcapacity ν hν.le hνcap
  refine ⟨ν,cap,hν,hcap,hνcap,hcapcap,N,?_⟩
  intro n hn
  obtain ⟨hsize,K,Dmax,hK,hDmax,hDmaxCap,hfinishNum⟩:=hN n hn
  refine ⟨hsize,K,Dmax,hK,hDmax,hDmaxCap,?_⟩
  intro τ ηrate ellrate Lconf hτ hτcap hη hηcap hell hellcap hLconf
  have hτfinish:τ≤finishCap:=hτcap.trans hcapcap
  have hηell:ηrate≤ellCap:=hηcap.trans hfinishEll
  exact ⟨hmargin n ηrate ellrate (by positivity) hηell hellcap,
    hrates τ ν ηrate ellrate hτ hν.le hη hell hτfinish hνcap hηcap hellcap,
    hfinishNum Lconf (ν*n) ηrate hLconf le_rfl hη hηcap⟩
end Oberwolfach

module

public import Oberwolfach.OrdinaryVortexFineInitialCertificateStatement
public import Oberwolfach.OrdinaryInitialWheelStructuralInputs
public import Oberwolfach.OrdinaryProtectedTraceLocalWheelStructuralInputs

@[expose] public section
/-! Apply the selected local certificate to an actual protected history.
The graph avoidance, conflict degrees, balance and divisibility are derived
from that history and the common sampled reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_fine_initial_certificate
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U]
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad s)
    (P G:SimpleGraph V) (D mv:ℕ) (βv εv:ℝ)
    (Q:Vortex U P D βv εv mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (d:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (Hs:V→U→Prop) : OrdinaryVortexFineInitialCertificateAt s hcert P G D mv βv εv Q π hπ d σ Hs :=by
  classical
  delta OrdinaryVortexFineInitialCertificateAt
  intro f g I T B W Ploc Gloc Floc Hloc ρi raw hdis hbal hdiv hb₀ hL
    ξroot aLoad lam bin cin deep crossLoss n cover ell Root βparent h εparent ξ ζ fout binner cross
    pR pH density Ledit ρ₀ εR εH eParent hParent sp j hpack hroot hT hW hprofile hκ hpair hpR hpH hpH1 hεR hεH hLedit hweight
    Nfinish rate θmatch ellCap finishCap kcap hθ hθcap hεsup hpθ hsqrt hξ ha hlam hlam1 hsize hTW hell hcover hLsize hsched
  have hstruct:=ordinary_initial_wheel_structural_inputs P G Hs D mv βv εv Q π hπ d (s.m+1) hdis hbal hdiv
  obtain ⟨hdisLocal,hF,hFr,hlocalBal,hlocalDiv⟩:=hstruct
  have hFn:∀v,Floc.degree v≤s.b₀:=fun v=>(hF v).trans hb₀
  have hFr':∀v,(Floc.degree v:ℝ)≤s.L:=fun v=>(hFr v).trans hL
  have hTI:T⊆I:=(ordinary_vortex_buffered_nested Q 0 2 (by omega)).2.2.1
  have hWB:W⊆B:=(ordinary_vortex_buffered_nested Q 0 2 (by omega)).2.2.2
  have hdecU : (fun (x y:U)=>Classical.propDecidable (x=y)) = (LinearOrder.toDecidableEq : DecidableEq U) := Subsingleton.elim _ _
  have hcertAt:=hcert V U P D mv βv εv Q 0 Γ Color Ploc Gloc Floc Hloc ρi d T W ξroot aLoad lam bin cin deep crossLoss
  rw [hdecU] at hcertAt
  exact hcertAt Root βparent h εparent ξ ζ fout binner cross pR pH density Ledit ρ₀ εR εH eParent hParent sp j raw
    hpack hTI hWB hroot hT hW hdisLocal hFr' hFn hprofile hκ hpair hpR hpH hpH1 hεR hεH hLedit hweight hlocalBal hlocalDiv
    Nfinish rate θmatch ellCap finishCap kcap hθ hθcap hεsup hpθ hsqrt hξ ha hlam hlam1 hsize hTW hell hcover hLsize hsched
end Oberwolfach

module

public import Oberwolfach.OrdinaryVortexFineTraceCertificateStatement
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

theorem ordinary_vortex_fine_certificate_from_protected_trace
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U]
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad s)
    (P Gbase:SimpleGraph V) (Hbase:V→U→Prop) (D mv:ℕ) (βv εv:ℝ)
    (Q:Vortex U P D βv εv mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (d:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (hr:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,
      ((rawWheelGraph P σ)\permutationConflictGraph π (3*d)).Adj v w↔Gbase.Adj v w)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (G:SimpleGraph V) (Hs:V→U→Prop):
    OrdinaryVortexFineCertificateFromProtectedTraceAt s hcert P Gbase Hbase D mv βv εv Q π hπ d σ K hr cost deepCost i A G Hs :=by
  classical
  delta OrdinaryVortexFineCertificateFromProtectedTraceAt
  intro S H X Tdeep Z Wdeep f g I T B W Ploc Gloc Floc Hloc ρi raw htrace hstate hbal hdiv hb₀ hL
    ξroot aLoad lam bin cin deep crossLoss n cover ell Root βparent h εparent ξ ζ fout binner cross
    pR pH density Ledit ρ₀ εR εH eParent hParent sp j hpack hroot hT hW hprofile hκ hpair hpR hpH hpH1 hεR hεH hLedit hweight
    Nfinish rate θmatch ellCap finishCap kcap hθ hθcap hεsup hpθ hsqrt hξ ha hlam hlam1 hsize hTW hell hcover hLsize hsched
  have hdecV : (fun (x y:V)=>Classical.propDecidable (x=y)) = (LinearOrder.toDecidableEq : DecidableEq V) := Subsingleton.elim _ _
  rw [←hdecV] at htrace
  have hstruct:=ordinary_protected_trace_local_wheel_structural_inputs P Gbase Hbase D mv βv εv Q π hπ d (s.m+1) σ K hr cost deepCost i A G Hs
    htrace hstate hbal hdiv
  obtain ⟨_,hdis,hF,hFr,hlocalBal,hlocalDiv⟩:=hstruct
  have hFn:∀v,Floc.degree v≤s.b₀:=fun v=>(hF v).trans hb₀
  have hFr':∀v,(Floc.degree v:ℝ)≤s.L:=fun v=>(hFr v).trans hL
  have hTI:T⊆I:=(ordinary_vortex_buffered_nested Q (i+1) 2 (by omega)).2.2.1
  have hWB:W⊆B:=(ordinary_vortex_buffered_nested Q (i+1) 2 (by omega)).2.2.2
  have hdecU : (fun (x y:U)=>Classical.propDecidable (x=y)) = (LinearOrder.toDecidableEq : DecidableEq U) := Subsingleton.elim _ _
  have hcertAt:=hcert V U P D mv βv εv Q (i+1) Γ Color Ploc Gloc Floc Hloc ρi d T W ξroot aLoad lam bin cin deep crossLoss
  rw [hdecU] at hcertAt
  exact hcertAt Root βparent h εparent ξ ζ fout binner cross pR pH density Ledit ρ₀ εR εH eParent hParent sp j raw
    hpack hTI hWB hroot hT hW hdis hFr' hFn hprofile hκ hpair hpR hpH hpH1 hεR hεH hLedit hweight hlocalBal hlocalDiv
    Nfinish rate θmatch ellCap finishCap kcap hθ hθcap hεsup hpθ hsqrt hξ ha hlam hlam1 hsize hTW hell hcover hLsize hsched
end Oberwolfach

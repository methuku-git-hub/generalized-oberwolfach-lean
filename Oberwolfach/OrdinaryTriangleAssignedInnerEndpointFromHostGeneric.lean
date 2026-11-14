module

public import Oberwolfach.OrdinaryTriangleInnerEndpointGenericLawFromHost
public import Oberwolfach.OrdinaryAssignedExpandedLaw
public import Oberwolfach.OrdinaryTriangleInnerEndpointExtension

@[expose] public section
/-! Specialize the named host attachment to the original assigned expanded
law without repeating the outer threshold and host selection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_assigned_inner_endpoint_from_host_generic
    {n q D mv K:ℕ} (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (hd:2≤d) (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θfreq cAux ρ₀ smin:ℝ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θfreq cAux ρ₀ smin d)
    (c C pmin ξ b Bweight ηHub Kdom eParent hParent cap χ χend tpot:ℝ):
    let p:=initialIndexDensity (Fin q) D*rsv/2;
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θfreq cAux D;
    let qMark:=ordinaryAssignedMarkedProbability F hF K θfreq cAux;
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θfreq cAux;
    let μ:=ordinaryAssignedExpandedLaw F hF i₀ rsv θfreq cAux ρ₀ smin d hd sampling;
    OrdinaryTriangleInnerEndpointHostData (Γ:=Bool) (Color:=Bool) β ε P D mv Q π hπ d hd
      p 0 p₂ 0 sampling.u sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum
      rsv c C pmin ξ b Bweight ηHub Kdom eParent hParent cap χ χend tpot→
    (∀u,s u false=rsv)→
    ∀(density tR tH:ℕ→ℝ)
      {R:(∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κcoins:FiniteLaw (Sym2 (Fin n)→Bool)),
    OrdinaryTriangleInnerEndpointExtension n q D mv d β ε P Q π hπ p rsv (eParent*ε) (hParent*ε)
      c (4*C/pmin^7) ηHub cap tpot χ χend density tR tH s false R μ ν κcoins :=by
  intro p p₂ qMark s μ hdata hsp density tR tH R _ ν κcoins
  exact ordinary_triangle_inner_endpoint_generic_law_from_host β ε P Q π hπ d hd
    p 0 p₂ 0 sampling.u sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum
    rsv c C pmin ξ b Bweight ηHub Kdom eParent hParent cap χ χend tpot hdata
    qMark sampling.hq sampling.hQ s sampling.hs sampling.hS hsp density tR tH ν κcoins
end Oberwolfach

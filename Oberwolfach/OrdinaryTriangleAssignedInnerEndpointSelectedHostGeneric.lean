module

public import Oberwolfach.OrdinaryTriangleInnerEndpointHostSelection
public import Oberwolfach.OrdinaryTriangleAssignedInnerEndpointFromHostGeneric
public import Oberwolfach.OrdinaryAssignedInnerEndpointLawInputs

@[expose] public section
/-! The selected host attachment applies to the actual assigned wheel law;
all rim, spoke and probability hypotheses come from the original sampling
record. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_assigned_inner_endpoint_selected_host_generic
    (α c C ε ρ₀ pmin ξ b Bweight ηHub Kdom eParent hParent cap χ χend tpot:ℝ)
    (d:ℕ) (hd:2≤d) (β:ℝ) (v₀:ℕ)
    (hselect:OrdinaryTriangleInnerEndpointHostSelector α c C ε ρ₀ pmin ξ b Bweight ηHub Kdom
      eParent hParent cap χ χend tpot d hd β v₀) (hρ:0<ρ₀)
    (n q D mv K:ℕ) (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (hn:0<n) (hhalf:(n:ℝ)/2≤D)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin q) D) (hρhi:initialIndexDensity (Fin q) D≤1) (hv:v₀≤mv)
    (Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (θhost:ℝ) (hθ:1/2≤θhost) (hthreshold:cycleThreshold 3≤θhost) (hdegree:(θhost+α)*(n:ℝ)≤D)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θfreq cAux smin:ℝ) (hsmin:0<smin) (hstar:pmin≤ρ₀*smin/2)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θfreq cAux ρ₀ smin d):
    let p:=initialIndexDensity (Fin q) D*rsv/2;
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θfreq cAux D;
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θfreq cAux;
    let μ:=ordinaryAssignedExpandedLaw F hF i₀ rsv θfreq cAux ρ₀ smin d hd sampling;
    ∀(density tR tH:ℕ→ℝ)
      {R:(∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κcoins:FiniteLaw (Sym2 (Fin n)→Bool)),
    OrdinaryTriangleInnerEndpointExtension n q D mv d β ε P Q π hπ p rsv (eParent*ε) (hParent*ε)
      c (4*C/pmin^7) ηHub cap tpot χ χend density tR tH s false R μ ν κcoins :=by
  intro p p₂ s μ density tR tH R _ ν κcoins
  have hD:0<D:=by
    have hn0:(0:ℝ)<n:=by exact_mod_cast hn
    have hDr:(0:ℝ)<D:=by linarith
    exact_mod_cast hDr
  obtain ⟨hpR,hpR1,hpH,_hrsv,hrsv1,hEq,hsp⟩:=ordinary_assigned_inner_endpoint_law_inputs
    F hF P hreg hD K i₀ rsv θfreq cAux ρ₀ smin pmin d hρ hρlo hρhi hsmin hstar sampling
  have hdata:=hselect (Fin n) (Fin q) Bool Bool P D mv hreg (by simpa using hn) hρlo hρhi hv
    Q π hπ hnoshort θhost p 0 p₂ 0 sampling.u hθ hthreshold (by simpa using hdegree)
    sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum rsv hpR hpR1 hpH hrsv1 hEq
  exact ordinary_triangle_assigned_inner_endpoint_from_host_generic β ε P Q π hπ d hd F hF i₀ rsv θfreq cAux ρ₀ smin sampling
    c C pmin ξ b Bweight ηHub Kdom eParent hParent cap χ χend tpot hdata hsp density tR tH ν κcoins
end Oberwolfach

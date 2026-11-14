module

public import Oberwolfach.OrdinaryTriangleInnerEndpointHostData
public import Oberwolfach.OrdinaryTriangleInnerEndpointExtension

@[expose] public section
/-! Extract the selected event attachment at one specified expanded law.
This leaves the assigned-law identification to a separate small step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_inner_endpoint_generic_law_from_host
    {n q D mv:ℕ} (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (hd:2≤d) (p k p₂ k₂ u:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (pH c C pmin ξ b Bweight ηHub Kdom eParent hParent cap χ χend tpot:ℝ)
    (hdata:OrdinaryTriangleInnerEndpointHostData (Γ:=Bool) (Color:=Bool) β ε P D mv Q π hπ d hd
      p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH c C pmin ξ b Bweight ηHub Kdom eParent hParent cap χ χend tpot)
    (qMark:Fin q→Bool→ℝ) (hq:∀v z,0≤qMark v z) (hQ:∀v,∑z,qMark v z≤1/8)
    (s:Fin q→Bool→ℝ) (hs:∀v j,0≤s v j)
    (hS:∀v,∑j,s v j ≤ intervalUncoveredProbability d (∑z,qMark v z))
    (hsp:∀v,s v false=pH) (density tR tH:ℕ→ℝ)
    {R:(∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κcoins:FiniteLaw (Sym2 (Fin n)→Bool)):
    OrdinaryTriangleInnerEndpointExtension n q D mv d β ε P Q π hπ p pH (eParent*ε) (hParent*ε)
      c (4*C/pmin^7) ηHub cap tpot χ χend density tR tH s false R
      (FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd qMark hq hQ s hs hS))
      ν κcoins :=by
  have hDecN : (fun a b : Fin n => Classical.propDecidable (a=b)) = instDecidableEqFin n := Subsingleton.elim _ _
  have hDecQ : (fun a b : Fin q => Classical.propDecidable (a=b)) = instDecidableEqFin q := Subsingleton.elim _ _
  obtain ⟨_weight,_setup,endpointWeight,hweight,hprob⟩:=hdata
  rw [hDecN] at hweight hprob
  try rw [hDecQ] at hweight hprob
  refine ⟨endpointWeight,hweight,?_⟩
  intro E a hE
  exact hprob density tR tH qMark hq hQ s hs hS false hsp (R:=R) ν κcoins E a hE
end Oberwolfach

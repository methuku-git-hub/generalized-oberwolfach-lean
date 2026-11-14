module

public import Oberwolfach.CoordinateLocalLemmaDegree
public import Oberwolfach.BoundedCertificateConcentration

@[expose] public section

/-! One simultaneous outcome for a family of local certificate estimates.
The same outcome satisfies every estimate; no later choice of an index
changes the probability space or the event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem local_certificate_common_event
    {I J Ω : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype Ω]
    (μ : I → FiniteLaw Ω) (R : J → (I → Ω) → ℝ) (S : J → Finset I)
    (c D M t : J → ℝ) {r s : ℕ}
    (hr : 0<r) (hs : 0<s)
    (hc : ∀ j,0<c j) (hD : ∀ j,0<D j) (ht : ∀ j,0≤t j)
    (hcert : ∀ j,HasCoordinateCertificateBound (R j) (c j) (D j))
    (hrange : ∀ j x,0≤R j x ∧ R j x≤M j)
    (hsmall : ∀ j,M j*(4*Real.exp (-(t j)^2/(4*c j*D j)))≤t j)
    (hsupport : ∀ j x y,(∀ i∈S j,x i=y i) → R j x=R j y)
    (hsize : ∀ j,(S j).card≤r)
    (hinc : ∀ i,(Finset.univ.filter (fun j=>i∈S j)).card≤s)
    (hp : ∀ j,4*Real.exp (-(t j)^2/(4*c j*D j))≤1/(4*((r*s : ℕ) : ℝ))) :
    ∃ x,0<(FiniteLaw.pi μ).mass x ∧
      ∀ j,|R j x-(FiniteLaw.pi μ).expectation (R j)|<3*t j := by
  let A : J → (I → Ω) → Prop := fun j x=>
    3*t j≤|R j x-(FiniteLaw.pi μ).expectation (R j)|
  have hsup (j : J) (x y : I → Ω) (hxy : ∀ i∈S j,x i=y i) :
      A j x ↔ A j y := by
    dsimp only [A]
    rw [hsupport j x y hxy]
  have hprob (j : J) : (FiniteLaw.pi μ).probability (A j)≤1/(4*((r*s : ℕ) : ℝ)) := by
    have hh := finiteLaw_bounded_certificate_tail μ (R j) (hc j) (hD j) (ht j)
      (hcert j) (hrange j) (hsmall j)
    have he : (fun a b : I=>Classical.propDecidable (a=b))=
        (inferInstance : DecidableEq I) := Subsingleton.elim _ _
    rw [he] at hh
    exact hh.trans (hp j)
  obtain ⟨x,hx,hall⟩ := finiteLaw_coordinate_localLemma_degree μ A S hsup hr hs hsize hinc hprob
  exact ⟨x,hx,fun j=>lt_of_not_ge (hall j)⟩

end Oberwolfach

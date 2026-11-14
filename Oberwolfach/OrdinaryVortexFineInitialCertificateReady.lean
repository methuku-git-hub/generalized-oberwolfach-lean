module

public import Oberwolfach.OrdinaryVortexFineInitialCertificate
public import Oberwolfach.OrdinaryVortexFineInitialCertificateReadyAt

@[expose] public section
/-! Once the actual initial host has conflict avoidance, balance and
wheel divisibility, the remaining certificate inputs are purely local. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_fine_initial_certificate_ready
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U]
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad s)
    (P G:SimpleGraph V) (D mv:ℕ) (βv εv:ℝ)
    (Q:Vortex U P D βv εv mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (d:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (Hs:V→U→Prop)
    (hdis:Disjoint G (permutationConflictGraph π (3*d)))
    (hbal:∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀u,(s.m+1)∣(Finset.univ.filter (fun v=>Hs v u)).card):
    OrdinaryVortexFineInitialCertificateReadyAt s hcert P G D mv βv εv Q π hπ d σ Hs :=by
  exact (ordinary_vortex_fine_initial_certificate s hcert P G D mv βv εv Q π hπ d σ Hs) hdis hbal hdiv
end Oberwolfach

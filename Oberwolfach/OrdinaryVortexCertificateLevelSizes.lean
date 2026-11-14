module

public import Oberwolfach.OrdinaryVortexUniformLevelSizeBounds

@[expose] public section
/-! A single terminal-size bound supplies the fine-certificate and parent
reference thresholds on every actual vortex level. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_certificate_level_sizes
    {n q D mv N n₀ Nreserve Nclean Ncert Nfinish Nparent:ℕ} {β ε:ℝ}
    (P:SimpleGraph (Fin n)) (Q:Vortex (Fin q) P D β ε mv)
    (hN:(N:ℝ)≤ε*mv/2)
    (hcert:max (max (max (4*n₀) (4*Nreserve)) (max Nclean 64)) (max Ncert Nfinish)≤N)
    (hparent:Nparent≤N):
    Ncert≤N ∧ Nfinish≤N ∧ ∀i,i<Q.length→
      max (max (max (4*n₀) (4*Nreserve)) (max Nclean 64)) (max Ncert Nfinish)≤
        (markedVortexInnerVertices Q i).card ∧
      Nparent≤Fintype.card (markedVortexVertexType Q i) :=by
  have ⟨hlevels,hinner⟩:=ordinary_vortex_uniform_level_size_bounds P Q hN
  refine ⟨by omega,by omega,?_⟩
  intro i hi
  refine ⟨hcert.trans (hinner i hi),?_⟩
  have h:=hparent.trans (hlevels i (by omega))
  simpa only [markedVortexVertexType,Fintype.card_coe] using h
end Oberwolfach

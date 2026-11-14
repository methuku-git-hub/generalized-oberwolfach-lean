module

public import Oberwolfach.OrdinarySupportedHostInducedExactBalance
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The first vortex parent is the entire host, so no support hypothesis is
needed to transfer its exact balance and divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_initial_local_exact_balance
    (P G:SimpleGraph V) (Hs:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P D β ε m) (r:ℕ)
    (hbal:∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card):
    let f:=markedVortexVertexEmbedding Vort 0;let g:=markedVortexHubEmbedding Vort 0;
    (∀v,(G.comap f).degree v=2*(Finset.univ.filter (fun u=>Hs (f v) (g u))).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>Hs (f v) (g u))).card):=by
  intro f g
  have hsupport:ordinaryHostResources G Hs⊆ordinaryRootResources (Vort.extendedVertices 0) (Vort.extendedIndices 0):=by
    apply ordinaryRootResources_contains
    · intro v hv
      rw [Vort.extendedVertices_eq (Nat.zero_le _),Vort.initial]
      exact Finset.mem_univ v
    · intro u hu
      rw [Vort.extendedIndices_eq (Nat.zero_le _),Vort.indices_initial]
      exact Finset.mem_univ u
  have hh:=ordinary_supported_host_induced_exact_balance G Hs (Vort.extendedVertices 0)
    (Vort.extendedIndices 0) r hsupport hbal hdiv
  constructor
  · intro v
    have hv:=hh.1 v
    convert hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro u
    have hu:=hh.2 u
    convert hu using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach

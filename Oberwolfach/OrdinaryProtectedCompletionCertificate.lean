module

public import Oberwolfach.OrdinaryCompletionFactorDecomposition
public import Oberwolfach.ProtectedFactorPreparation
public import Oberwolfach.CommonEvents

@[expose] public section
/-! The deterministic ordinary completion input on a single sample.
The certificate is a property, not an assertion of its probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryProtectedCompletionCertificate {n q r:ℕ}
    (P S₀:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent):Prop :=
  ∃A:SimpleGraph (Fin n),A≤S₀ ∧ A.edgeFinset.card≤B ∧
    ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*q)→A≤S→
      (∀x∈I,∀y∈I,S.Adj x y↔S₀.Adj x y)→
      (∀x,((Finset.univ.filter (fun y=>Xor (S.Adj x y) (S₀.Adj x y))).card:ℝ)≤ξ*n)→
    ∃(Q:SimpleGraph (Fin n)) (H:Fin n→Fin q→Prop),Q≤S ∧ HasOrdinaryWheelDecomposition Q H r ∧
      (∀u,(Finset.univ.filter (fun v=>H v u)).card=r*(C u).card) ∧
    ∃fC:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n,
      (∀u x y,((F u).induce {x | (F u).connectedComponentMk x∉C u}).Adj x y→
        S.Adj (fC u x) (fC u y) ∧ ¬Q.Adj (fC u x) (fC u y)) ∧
      (∀u (x:{x:Fin n // (F u).connectedComponentMk x∉C u}),¬H (fC u x) u) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdgesPoly {x:Fin n // (F u).connectedComponentMk x∉C u}
          ((F u).induce {x | (F u).connectedComponentMk x∉C u}) (fC u))
        (partialFactorPhysicalEdgesPoly {x:Fin n // (F v).connectedComponentMk x∉C v}
          ((F v).induce {x | (F v).connectedComponentMk x∉C v}) (fC v)))

theorem ordinary_completion_certificate_prepares {n q r:ℕ}
    (P S₀:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (hcert:OrdinaryProtectedCompletionCertificate (r:=r) P S₀ I ξ B F C):
    ProtectedFactorPreparation P S₀ I ξ B F :=by
  obtain ⟨A,hA,hB,hcert⟩:=hcert
  refine ⟨A,hA,hB,?_⟩
  intro S hS hreg hAS hI hchange
  obtain ⟨Q,H,hQ,hdec,hspokes,fC,hC,havoid,hCC⟩:=hcert S hS hreg hAS hI hchange
  exact ordinary_completion_factor_decomposition S Q H hreg hQ hr hdec F hF C hsize hspokes fC hC havoid hCC

theorem ordinary_completion_certificate_probability {n q r:ℕ} {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (sample:Ω→SimpleGraph (Fin n))
    (P:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r) (p:ℝ)
    (hprob:p≤μ.probability (fun ω=>OrdinaryProtectedCompletionCertificate (r:=r) P (sample ω) I ξ B F C)):
    p≤μ.probability (fun ω=>ProtectedFactorPreparation P (sample ω) I ξ B F) :=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro ω hcert
  exact ordinary_completion_certificate_prepares P (sample ω) I ξ B F hF C hr hsize hcert
end Oberwolfach

module

public import Oberwolfach.OrdinaryComplementRemainderDecomposition
public import Oberwolfach.ProtectedFactorPreparation
public import Oberwolfach.CommonEvents

@[expose] public section
/-! A same-sample certificate phrased using the actual embedded complements
and their ordinary wheel remainder. No probability bound is asserted here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryNaturalPreparationCertificate {n q r:ℕ}
    (P S₀:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent):Prop :=
  ∃A:SimpleGraph (Fin n),A≤S₀ ∧ A.edgeFinset.card≤B ∧
    ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*q)→A≤S→
      (∀x∈I,∀y∈I,S.Adj x y↔S₀.Adj x y)→
      (∀x,((Finset.univ.filter (fun y=>Xor (S.Adj x y) (S₀.Adj x y))).card:ℝ)≤ξ*n)→
    ∃fC:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n,
      (∀u x y,((F u).induce {x | (F u).connectedComponentMk x∉C u}).Adj x y→S.Adj (fC u x) (fC u y)) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdgesPoly {x:Fin n // (F u).connectedComponentMk x∉C u}
          ((F u).induce {x | (F u).connectedComponentMk x∉C u}) (fC u))
        (partialFactorPhysicalEdgesPoly {x:Fin n // (F v).connectedComponentMk x∉C v}
          ((F v).induce {x | (F v).connectedComponentMk x∉C v}) (fC v))) ∧
      HasOrdinaryWheelDecomposition (S \ ordinaryEmbeddedComplements F C fC)
        (fun v u=>v∉Set.range (fC u)) r

theorem ordinary_natural_certificate_prepares {n q r:ℕ}
    (P S₀:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (hcert:OrdinaryNaturalPreparationCertificate (r:=r) P S₀ I ξ B F C):
    ProtectedFactorPreparation P S₀ I ξ B F :=by
  obtain ⟨A,hA,hB,hcert⟩:=hcert
  refine ⟨A,hA,hB,?_⟩
  intro S hS hreg hAS hI hchange
  obtain ⟨fC,hC,hCC,hdec⟩:=hcert S hS hreg hAS hI hchange
  exact ordinary_complement_remainder_decomposition S hreg hr F hF C hsize fC hC hCC hdec

theorem ordinary_natural_certificate_probability {n q r:ℕ} {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (sample:Ω→SimpleGraph (Fin n))
    (P:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r) (p:ℝ)
    (hprob:p≤μ.probability (fun ω=>OrdinaryNaturalPreparationCertificate (r:=r) P (sample ω) I ξ B F C)):
    p≤μ.probability (fun ω=>ProtectedFactorPreparation P (sample ω) I ξ B F) :=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro ω hcert
  exact ordinary_natural_certificate_prepares P (sample ω) I ξ B F hF C hr hsize hcert
end Oberwolfach

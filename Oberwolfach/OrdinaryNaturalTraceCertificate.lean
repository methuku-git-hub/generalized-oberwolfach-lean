module

public import Oberwolfach.OrdinaryComplementTraceWitness
public import Oberwolfach.OrdinaryNaturalPreparationCertificate

@[expose] public section
/-! The original protected preparation certificate follows from one
    sample's robust complement embeddings and ordinary wheel traces. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryNaturalTraceCertificate {n q r:ℕ}
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
      ∃(Fbad:SimpleGraph (Fin n)) (Hbase:Fin n→Fin q→Prop),
        OrdinaryWheelTraceWitness (S\ordinaryEmbeddedComplements F C fC) P Fbad
          (fun v u=>v∉Set.range (fC u)) Hbase r

theorem ordinary_natural_trace_certificate_to_preparation {n q r:ℕ}
    (P S₀:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (htrace:OrdinaryNaturalTraceCertificate (r:=r) P S₀ I ξ B F C):
    OrdinaryNaturalPreparationCertificate (r:=r) P S₀ I ξ B F C :=by
  obtain ⟨A,hA,hB,hFor⟩:=htrace
  refine ⟨A,hA,hB,?_⟩
  intro S hSP hS hAS hI hchange
  obtain ⟨fC,hC,hCC,Fbad,Hbase,hTrace⟩:=hFor S hSP hS hAS hI hchange
  have hwheel:HasOrdinaryWheelDecomposition (S\ordinaryEmbeddedComplements F C fC)
      (fun v u=>v∉Set.range (fC u)) r:=
    (ordinary_complement_trace_witness_completion S P Fbad hS hr F hF C hsize fC hC hCC Hbase hTrace).1
  exact ⟨fC,hC,hCC,hwheel⟩

theorem ordinary_natural_trace_certificate_probability {n q r:ℕ} {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (sample:Ω→SimpleGraph (Fin n))
    (P:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r) (p:ℝ)
    (hprob:p≤μ.probability (fun ω=>OrdinaryNaturalTraceCertificate (r:=r) P (sample ω) I ξ B F C)):
    p≤μ.probability (fun ω=>ProtectedFactorPreparation P (sample ω) I ξ B F) :=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro ω htrace
  exact ordinary_natural_certificate_prepares P (sample ω) I ξ B F hF C hr hsize
    (ordinary_natural_trace_certificate_to_preparation P (sample ω) I ξ B F hF C hr hsize htrace)
end Oberwolfach

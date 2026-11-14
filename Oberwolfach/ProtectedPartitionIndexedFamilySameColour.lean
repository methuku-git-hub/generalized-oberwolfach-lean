module

public import Oberwolfach.ProtectedPartitionClassDecompositionsSameColour
public import Oberwolfach.FactorDecompositionFromIndexedClasses

@[expose] public section
/-! Conditional final assembly: high-probability robust class events and the
protected partition are realized on one colouring, then reassembled into the
original prescribed factor family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_partition_indexed_family_same_colour (K:ℕ) {α r ξ:ℝ}
    (hα:0<α) (hr:0<r) (hξ:0<ξ) (B:ℕ):
    ∃N₀:ℕ,∀k:ℕ,0<k→k≤K+1→∀n≥N₀,
    ∀(G:SimpleGraph (Fin n)) (D q:ℕ) (colour:Fin q→Fin k) (F:Fin q→SimpleGraph (Fin n)),
    let m:Fin k→ℕ:=fun a=>Fintype.card {i:Fin q // colour i=a}
    let Fc:∀a,Fin (m a)→SimpleGraph (Fin n):=fun a j=>F ((Fintype.equivFin {i:Fin q // colour i=a}).symm j).val;
    ∀(ρ:Fin k→ℝ) (hρ:∀a,0≤ρ a) (htotal:∑a,ρ a=1),
      G.IsRegularOfDegree D→Even D→(1/2+α)*n≤(D:ℝ)→
      (∑a,m a=D/2)→(∀a,ρ a/2*D=(m a:ℝ))→(∀a,r≤ρ a)→
    ∀I:Fin k→Finset (Fin n),((∑a,(I a).card:ℕ):ℝ)≤α/100000*n→
    ∀(ClassEvent:Fin k→SimpleGraph (Fin n)→Prop) (err:Fin k→ℝ),
      (∀a,1-err a≤
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (ρ a) (hρ a)
          (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith))).probability
            (fun σ=>ClassEvent a (retainedGraph G σ)))→
      1/(n:ℝ)^10+(∑a,err a)<1→
    ∀Ba:Fin k→ℕ,(∑a,Ba a≤B)→
      (∀a S,ClassEvent a S→∃A:SimpleGraph (Fin n),A≤S ∧ A.edgeFinset.card≤Ba a ∧
        ∀H:SimpleGraph (Fin n),H≤G→H.IsRegularOfDegree (2*m a)→A≤H→
          (∀x∈I a,∀y∈I a,H.Adj x y↔S.Adj x y)→
          (∀x,((Finset.univ.filter (fun y=>Xor (H.Adj x y) (S.Adj x y))).card:ℝ)≤ξ*n)→
          HasFactorDecomposition H (Fc a))→
    ∃c:Sym2 (Fin n)→Fin k,
      (∀a,ClassEvent a (edgeColourGraph G c a)) ∧ HasFactorDecomposition G F :=by
  obtain ⟨N₀,hN₀⟩:=protected_partition_class_decompositions_on_one_colour K hα hr hξ B
  refine ⟨N₀,?_⟩
  intro k hk hkK n hn G D q colour F m Fc ρ hρ htotal hG hEven hdegree hsum hρm hρlo I hI ClassEvent err hClass hbudget Ba hB hSound
  obtain ⟨c,H,hclasses,hpart,hdec⟩:=hN₀ k hk hkK n hn G D m ρ hρ htotal hG hEven hdegree hsum hρm hρlo I hI ClassEvent err hClass hbudget Fc Ba hB hSound
  have hfinal:HasFactorDecomposition G F:=factor_decomposition_from_indexed_classes G F H colour hpart hdec
  exact ⟨c,hclasses,hfinal⟩
end Oberwolfach

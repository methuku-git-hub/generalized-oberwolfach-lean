module

public import Oberwolfach.ProtectedPartitionReadyClassAssembly
public import Oberwolfach.ClassColourCommonProtectedEvent

@[expose] public section
/-! Every class event and the protected partition are witnessed by one
categorical edge colouring. The class events may depend arbitrarily on their
membership masks and need not be independent of one another. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_partition_class_decompositions_on_one_colour (K:ℕ) {α r ξ:ℝ}
    (hα:0<α) (hr:0<r) (hξ:0<ξ) (B:ℕ):
    ∃N₀:ℕ,∀k:ℕ,0<k→k≤K+1→∀n≥N₀,
    ∀(G:SimpleGraph (Fin n)) (D:ℕ) (m:Fin k→ℕ) (ρ:Fin k→ℝ)
      (hρ:∀a,0≤ρ a) (htotal:∑a,ρ a=1),
      G.IsRegularOfDegree D→Even D→(1/2+α)*n≤(D:ℝ)→
      (∑a,m a=D/2)→(∀a,ρ a/2*D=(m a:ℝ))→(∀a,r≤ρ a)→
    ∀I:Fin k→Finset (Fin n),((∑a,(I a).card:ℕ):ℝ)≤α/100000*n→
    ∀(ClassEvent:Fin k→SimpleGraph (Fin n)→Prop) (err:Fin k→ℝ),
      (∀a,1-err a≤
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (ρ a) (hρ a)
          (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith))).probability (fun σ=>ClassEvent a (retainedGraph G σ)))→
      1/(n:ℝ)^10+(∑a,err a)<1→
    ∀(F:∀a,Fin (m a)→SimpleGraph (Fin n)) (Ba:Fin k→ℕ),
      (∑a,Ba a≤B)→
      (∀a S,ClassEvent a S→∃A:SimpleGraph (Fin n),A≤S ∧ A.edgeFinset.card≤Ba a ∧
        ∀H:SimpleGraph (Fin n),H≤G→H.IsRegularOfDegree (2*m a)→A≤H→
          (∀x∈I a,∀y∈I a,H.Adj x y↔S.Adj x y)→
          (∀x,((Finset.univ.filter (fun y=>Xor (H.Adj x y) (S.Adj x y))).card:ℝ)≤ξ*n)→
          HasFactorDecomposition H (F a))→
    ∃(c:Sym2 (Fin n)→Fin k) (H:Fin k→SimpleGraph (Fin n)),
      (∀a,ClassEvent a (edgeColourGraph G c a)) ∧
      EdgePartition G H ∧ ∀a,HasFactorDecomposition (H a) (F a) :=by
  obtain ⟨N₀,hN₀⟩:=protected_partition_with_graph_events_same_colour K hα hr hξ B
  refine ⟨N₀,?_⟩
  intro k hk hkK n hn G D m ρ hρ htotal hG hEven hdegree hsum hρm hρlo I hI ClassEvent err hClass hbudget F Ba hB hSound
  obtain ⟨c,hclasses,hpartition⟩:=hN₀ k hk hkK n hn G D m ρ hρ htotal hG hEven hdegree hsum hρm hρlo I hI ClassEvent err hClass hbudget
  have hReady:=fun a=>hSound a (edgeColourGraph G c a) (hclasses a)
  obtain ⟨H,hpart,hdec⟩:=protected_partition_ready_class_assembly G c m F I ξ B Ba hB hReady hpartition
  exact ⟨c,H,hclasses,hpart,hdec⟩
end Oberwolfach

module

public import Oberwolfach.ProtectedPartitionBoundedClasses
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

theorem protected_partition_with_class_events_same_colour (K:ℕ) {α r ξ:ℝ}
    (hα:0<α) (hr:0<r) (hξ:0<ξ) (B:ℕ):
    ∃N₀:ℕ,∀k:ℕ,0<k→k≤K+1→∀n≥N₀,
    ∀(G:SimpleGraph (Fin n)) (D:ℕ) (m:Fin k→ℕ) (ρ:Fin k→ℝ)
      (hρ:∀a,0≤ρ a) (htotal:∑a,ρ a=1),
      G.IsRegularOfDegree D→Even D→(1/2+α)*n≤(D:ℝ)→
      (∑a,m a=D/2)→(∀a,ρ a/2*D=(m a:ℝ))→(∀a,r≤ρ a)→
    ∀I:Fin k→Finset (Fin n),((∑a,(I a).card:ℕ):ℝ)≤α/100000*n→
    ∀(ClassEvent:Fin k→(Sym2 (Fin n)→Bool)→Prop) (err:Fin k→ℝ),
      (∀a,1-err a≤
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (ρ a) (hρ a)
          (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith))).probability (ClassEvent a))→
      1/(n:ℝ)^10+(∑a,err a)<1→
    ∃c:Sym2 (Fin n)→Fin k,
      (∀a,ClassEvent a (fun e=>classColourMembership a (c e))) ∧
      ∀A:Fin k→SimpleGraph (Fin n),
        (∀a,A a≤edgeColourGraph G c a)→(∑a,(A a).edgeFinset.card)≤B→
      ∃H:Fin k→SimpleGraph (Fin n),
        EdgePartition G H ∧ (∀a,(H a).IsRegularOfDegree (2*m a)) ∧
        (∀a,A a≤H a) ∧
        (∀a b x,x∈I b→∀y,y∈I b→((H a).Adj x y↔(edgeColourGraph G c a).Adj x y)) ∧
        (∀a x,((Finset.univ.filter (fun y=>Xor ((H a).Adj x y) ((edgeColourGraph G c a).Adj x y))).card:ℝ)≤ξ*n) :=by
  obtain ⟨N₀,hN₀⟩:=protected_partition_bounded_classes K hα hr hξ B
  refine ⟨N₀,?_⟩
  intro k hk hkK n hn G D m ρ hρ htotal hG hEven hdegree hsum hρm hρlo I hI ClassEvent err hClass hbudget
  let GlobalEvent:=fun c:Sym2 (Fin n)→Fin k=>∀A:Fin k→SimpleGraph (Fin n),
        (∀a,A a≤edgeColourGraph G c a)→(∑a,(A a).edgeFinset.card)≤B→
      ∃H:Fin k→SimpleGraph (Fin n),
        EdgePartition G H ∧ (∀a,(H a).IsRegularOfDegree (2*m a)) ∧
        (∀a,A a≤H a) ∧
        (∀a b x,x∈I b→∀y,y∈I b→((H a).Adj x y↔(edgeColourGraph G c a).Adj x y)) ∧
        (∀a x,((Finset.univ.filter (fun y=>Xor ((H a).Adj x y) ((edgeColourGraph G c a).Adj x y))).card:ℝ)≤ξ*n)
  have hGlobal:=hN₀ k hk hkK n hn G D m ρ hρ htotal hG hEven hdegree hsum hρm hρlo I hI
  obtain ⟨c,hc,hclasses⟩:=categorical_class_events_with_global_witness ρ hρ htotal ClassEvent GlobalEvent err (1/(n:ℝ)^10) hClass hGlobal hbudget
  exact ⟨c,hclasses,hc⟩
end Oberwolfach

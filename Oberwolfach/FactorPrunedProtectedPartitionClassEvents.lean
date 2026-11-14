module

public import Oberwolfach.FactorPrunedProtectedPartition
public import Oberwolfach.ClassColourCommonProtectedEvent
public import Oberwolfach.ClassColourRetainedGraphAlignment

@[expose] public section
/-! The actual pruned factor classes supply the numerical inputs of the
protected partition event, which is intersected with the class events on
the same categorical colouring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_pruned_protected_partition_with_class_events (K:ℕ) (hK:0<K) (α κL κS ξ:ℝ)
    (hα:0<α) (hL0:0<κL) (hS0:0<κS) (hξ:0<ξ)
    (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ))) (B:ℕ):
    ∃ N₀:ℕ,∀ {W:Type} [Fintype W] {n:ℕ},N₀≤n→0<n→
    ∀ (classify:W→Option (Fin K)) (D:ℕ) (hEven:Even D)
      (hsize:Fintype.card W=D/2) (hDn:D≤n) (δ:ℝ) (hδ:1/2≤δ)
      (hdegree:(δ+α)*(n:ℝ)≤D),
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let cutoff:=fun j:Option (Fin K)=>if j=none then κL else κS
    let small:=fun j:Option (Fin K)=>((fibres j).card:ℝ)<cutoff j*n
    let removed:=Finset.univ.filter (fun w=>small (classify w))
    let remaining:={w:W // w∉removed}
    let cf:=fun w:remaining=>classify w.val
    let D0:=D-2*removed.card
    let fibres0:=fun j:Option (Fin K)=>Finset.univ.filter (fun w:remaining=>cf w=j)
    let C:=Finset.univ.filter (fun j=>(fibres0 j).Nonempty)
    let k:=C.card
    let e:Fin k≃↥C:=(Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
    let m:=fun a:Fin k=>(fibres0 (e a).val).card
    let ρ:=fun a:Fin k=>2*(m a:ℝ)/(D0:ℝ);
    ∀ R:SimpleGraph (Fin n),R.IsRegularOfDegree D0→
    ∀ I:Fin k→Finset (Fin n),((∑ a,(I a).card:ℕ):ℝ)≤(α/2)/100000*n→
    ∃ (hρ:∀ a,0≤ρ a) (htotal:∑ a,ρ a=1),
    ∀(ClassEvent:Fin k→SimpleGraph (Fin n)→Prop) (err:Fin k→ℝ),
      (∀a,1-err a≤
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (ρ a) (hρ a)
          (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith))).probability
            (fun σ=>ClassEvent a (retainedGraph R σ)))→
      1/(n:ℝ)^10+(∑a,err a)<1→
    ∃c:Sym2 (Fin n)→Fin k,
      (∀a,ClassEvent a (edgeColourGraph R c a)) ∧
      ∀A:Fin k→SimpleGraph (Fin n),
        (∀a,A a≤edgeColourGraph R c a)→(∑a,(A a).edgeFinset.card)≤B→
      ∃H:Fin k→SimpleGraph (Fin n),
        EdgePartition R H ∧ (∀a,(H a).IsRegularOfDegree (2*m a)) ∧
        (∀a,A a≤H a) ∧
        (∀a b x,x∈I b→∀y,y∈I b→((H a).Adj x y↔(edgeColourGraph R c a).Adj x y)) ∧
        (∀a x,((Finset.univ.filter (fun y=>Xor ((H a).Adj x y) ((edgeColourGraph R c a).Adj x y))).card:ℝ)≤ξ*n) :=by
  obtain ⟨N₀,hN⟩:=factor_pruned_protected_partition K hK α κL κS ξ hα hL0 hS0 hξ hL hS B
  refine ⟨N₀,?_⟩
  intro W _ n hn hn0 classify D hEven hsize hDn δ hδ hdegree fibres cutoff small removed remaining cf D0 fibres0 C k e m ρ R hR I hI
  obtain ⟨hρ,htotal,hGlobal⟩:=hN hn hn0 classify D hEven hsize hDn δ hδ hdegree R hR I hI
  refine ⟨hρ,htotal,?_⟩
  intro ClassEvent err hClass hbudget
  let GlobalEvent:=fun c:Sym2 (Fin n)→Fin k=>∀A:Fin k→SimpleGraph (Fin n),
        (∀a,A a≤edgeColourGraph R c a)→(∑a,(A a).edgeFinset.card)≤B→
      ∃H:Fin k→SimpleGraph (Fin n),
        EdgePartition R H ∧ (∀a,(H a).IsRegularOfDegree (2*m a)) ∧
        (∀a,A a≤H a) ∧
        (∀a b x,x∈I b→∀y,y∈I b→((H a).Adj x y↔(edgeColourGraph R c a).Adj x y)) ∧
        (∀a x,((Finset.univ.filter (fun y=>Xor ((H a).Adj x y) ((edgeColourGraph R c a).Adj x y))).card:ℝ)≤ξ*n)
  obtain ⟨c,hpart,hclasses⟩:=categorical_class_events_with_global_witness ρ hρ htotal
    (fun a σ=>ClassEvent a (retainedGraph R σ)) GlobalEvent err (1/(n:ℝ)^10) hClass hGlobal hbudget
  refine ⟨c,?_,hpart⟩
  intro a
  simpa only [class_colour_membership_retained_graph] using hclasses a
end Oberwolfach

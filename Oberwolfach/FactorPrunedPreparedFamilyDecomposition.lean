module

public import Oberwolfach.FactorPrunedProtectedPartitionClassEvents
public import Oberwolfach.ProtectedFactorPreparation
public import Oberwolfach.ProtectedPartitionReadyClassAssembly
public import Oberwolfach.FactorDecompositionActualNonemptyClasses

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

theorem factor_pruned_protected_preparations_decompose_remaining_family (K:ℕ) (hK:0<K) (α κL κS ξ:ℝ)
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
    ∀F:W→SimpleGraph (Fin n),
    ∃ (hρ:∀ a,0≤ρ a) (htotal:∑ a,ρ a=1),
    let eF:=fun a:Fin k=>factorClassFibreEquiv cf (e a).val
    let Fc:∀a,Fin (m a)→SimpleGraph (Fin n):=fun a j=>F ((eF a j).val).val;
    ∀(Ba:Fin k→ℕ) (err:Fin k→ℝ), (∑a,Ba a≤B)→
      (∀a,1-err a≤
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (ρ a) (hρ a)
          (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith))).probability
            (fun σ=>ProtectedFactorPreparation R (retainedGraph R σ) (I a) ξ (Ba a) (Fc a)))→
      1/(n:ℝ)^10+(∑a,err a)<1→
    ∃c:Sym2 (Fin n)→Fin k,
      (∀a,ProtectedFactorPreparation R (edgeColourGraph R c a) (I a) ξ (Ba a) (Fc a)) ∧
      HasFactorDecomposition R (fun i:Fin (Fintype.card remaining)=>F ((Fintype.equivFin remaining).symm i).val) :=by
  obtain ⟨N₀,hN⟩:=factor_pruned_protected_partition_with_class_events K hK α κL κS ξ hα hL0 hS0 hξ hL hS B
  refine ⟨N₀,?_⟩
  intro W _ n hn hn0 classify D hEven hsize hDn δ hδ hdegree fibres cutoff small removed remaining cf D0 fibres0 C k e m ρ R hR I hI F
  obtain ⟨hρ,htotal,hGlobal⟩:=hN hn hn0 classify D hEven hsize hDn δ hδ hdegree R hR I hI
  refine ⟨hρ,htotal,?_⟩
  intro eF Fc Ba err hB hClass hbudget
  obtain ⟨c,hclasses,hpart⟩:=hGlobal (fun a S=>ProtectedFactorPreparation R S (I a) ξ (Ba a) (Fc a)) err hClass hbudget
  have hReady:∀a,∃A:SimpleGraph (Fin n),A≤edgeColourGraph R c a ∧ A.edgeFinset.card≤Ba a ∧
      ∀H:SimpleGraph (Fin n),H≤R→H.IsRegularOfDegree (2*m a)→A≤H→
        (∀x∈I a,∀y∈I a,H.Adj x y↔(edgeColourGraph R c a).Adj x y)→
        (∀x,((Finset.univ.filter (fun y=>Xor (H.Adj x y) ((edgeColourGraph R c a).Adj x y))).card:ℝ)≤ξ*n)→
        HasFactorDecomposition H (Fc a):=hclasses
  obtain ⟨H,hHpart,hdec⟩:=protected_partition_ready_class_assembly R c m Fc I ξ B Ba hB hReady hpart
  have hfinal:=factor_decomposition_from_actual_nonempty_classes R (fun w:remaining=>F w.val) cf H hHpart hdec
  exact ⟨c,hclasses,hfinal⟩
end Oberwolfach

module

public import Oberwolfach.FactorPrunedClassIndices
public import Oberwolfach.ProtectedPartitionBoundedClasses

@[expose] public section
/-! The actual pruned factor classes supply the numerical inputs of the
protected partition event. This result does not yet intersect that event with
the class-specific preparation events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_pruned_protected_partition (K:ℕ) (hK:0<K) (α κL κS ξ:ℝ)
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
      1-1/(n:ℝ)^10≤
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.categorical ρ hρ htotal)).probability
          (fun c=>∀ A:Fin k→SimpleGraph (Fin n),
            (∀ a,A a≤edgeColourGraph R c a)→
            (∑ a,(A a).edgeFinset.card)≤B→
            ∃ H:Fin k→SimpleGraph (Fin n),
              EdgePartition R H ∧ (∀ a,(H a).IsRegularOfDegree (2*m a)) ∧
              (∀ a,A a≤H a) ∧
              (∀ a b x,x∈I b→∀ y,y∈I b→
                ((H a).Adj x y↔(edgeColourGraph R c a).Adj x y)) ∧
              (∀ a x,((Finset.univ.filter (fun y=>
                Xor ((H a).Adj x y) ((edgeColourGraph R c a).Adj x y))).card:ℝ)≤ξ*n)):=by
  have hr:0<2*min κL κS:=by positivity
  obtain ⟨N₀,hN⟩:=protected_partition_bounded_classes K (by positivity:0<α/2) hr hξ B
  refine ⟨N₀,?_⟩
  intro W _ n hn hn0 classify D hEven hsize hDn δ hδ hdegree
    fibres cutoff small removed remaining cf D0 fibres0 C k e m ρ R hR I hI
  have hp:=factor_pruned_class_indices hn0 K hK classify D hEven hsize hDn δ α κL κS
    (by linarith) hα hL0 hS0 hL hS hdegree
  have hρ:∀ a,0≤ρ a:=fun a=>(hp.2.2.2.2.2.2.1 a).le
  have htotal:∑ a,ρ a=1:=hp.2.2.2.2.2.2.2.1
  have hsmall0:=factor_small_class_budget K hK classify (n:ℝ) α κL κS (by positivity) hα hL0.le hS0.le hL hS
  have hsmall:(removed.card:ℝ)≤α*n/500:=by
    simpa [fibres,cutoff,small,removed,ite_mul] using hsmall0
  have hmarg: (δ+α/2)*(n:ℝ)≤(D0:ℝ):=
    (factor_small_removal_margin D removed.card n δ α (by linarith) hα hdegree hsmall removed.card (le_refl _)).2
  have hmin:(1/2+α/2)*(n:ℝ)≤(D0:ℝ):=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2+α/2:ℝ)≤δ+α/2 by linarith) (Nat.cast_nonneg n)
    exact hh.trans hmarg
  refine ⟨hρ,htotal,?_⟩
  exact hN k hp.2.2.1 hp.2.2.2.1 n hn R D0 m ρ hρ htotal hR hp.2.1 hmin
    hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2 I hI
end Oberwolfach

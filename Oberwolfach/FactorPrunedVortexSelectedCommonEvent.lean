module

public import Oberwolfach.FactorPrunedSelectedActualRetention
public import Oberwolfach.FactorPrunedSharedVortexBudget

@[expose] public section
/-! Choose the actual class vortices and their common permutation before
sampling. Conditional on the remaining class event probability estimates,
the protected partition and all class events hold on one retained outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem factor_pruned_vortex_selected_retention_common_event (K:ℕ) (hK:0<K) (α κL κS ξ:ℝ)
    (hα:0<α) (hL0:0<κL) (hS0:0<κS) (hξ:0<ξ)
    (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ))) (B:ℕ)
    (β ε:ℝ) (hb:0<β) (he:0<ε) (heq:ε<1/4)
    (hebudget:((K:ℝ)+1)*ε≤(α/2)/100000) (h:ℕ):
    ∃ χ:ℝ,0<χ ∧ ∃ N₀:ℕ,∃ m₀:ℕ,1≤m₀ ∧ ∀ m:ℕ,m₀≤m→
    ∀ {W:Type} [Fintype W] {n:ℕ} (hn:N₀≤n) (hnm:m≤n) (hn0:0<n),
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
    let mclass:=fun a:Fin k=>(fibres0 (e a).val).card
    let ρ:=fun a:Fin k=>2*(mclass a:ℝ)/(D0:ℝ);
    letI : Nonempty (Fin n):=⟨⟨0,hn0⟩⟩;
    let U:=fun a:Fin k=>{w:remaining // cf w=(e a).val};
    ∀ (R:SimpleGraph (Fin n)),R.IsRegularOfDegree D0→
    ∃ Q:∀ a:Fin k,Vortex (U a) R D0 β ε m,∃ π:Equiv.Perm (Fin n),
    (∀ a i x,π x∈(Q a).extendedVertices i↔x∈(Q a).extendedVertices i) ∧
    (∀ a b,(Q a).toVertexVortex=(Q b).toVertexVortex) ∧
    (∀ x j,0<j→j<h→(π^j) x≠x) ∧
    let I:=fun a:Fin k=>(Q a).vertices 1;
    ∃ (hρ:∀ a,0<ρ a) (htotal:∑ a,ρ a=1),
    ∀ (marks:Fin k→Bool)
    (p t p₂ t₂ u:Fin k→ℝ)
    (hp:∀ a,0≤p a) (ht:∀ a,0≤t a) (hp₂:∀ a,0≤p₂ a) (ht₂:∀ a,0≤t₂ a) (hu:∀ a,0≤u a)
    (hbalance:∀ a,2*p a+2*t a+2*p₂ a+2*t₂ a+u a=ρ a)
    (d:Fin k→ℕ) (hd:∀ a,2≤d a)
    (q:∀ a,U a→Bool→ℝ) (hq:∀ a w g,0≤q a w g) (hQ:∀ a w,∑ g,q a w g≤1/8)
    (s:∀ a,U a→Bool→ℝ) (hs:∀ a w j,0≤s a w j)
    (hS:∀ a w,∑ j,s a w j ≤ intervalUncoveredProbability (d a) (∑ g,q a w g)),
    let hρ0:=fun a=>(hρ a).le
    let hρ1:=fun a=>show ρ a≤1 from by
      have hh:=Finset.single_le_sum (fun b _=>(hρ b).le) (Finset.mem_univ a);linarith
    let inside:=fun a=>FiniteLaw.categorical (markedPhysicalInsideProbability (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a))
      (marked_physical_inside_nonneg (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a) (hρ a))
      (marked_physical_inside_sum (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hρ a) (hbalance a))
    let joint:=(FiniteLaw.categorical ρ hρ0 htotal).sigma inside
    let physical:=FiniteLaw.pi (fun _:Sym2 (Fin n)=>joint.prod FiniteLaw.fairCoin)
    let μ:=fun a=>rawExpandedMarkedWheelLaw (V:=Fin n) (U:=U a) (p a) (t a) (p₂ a) (t₂ a) (u a)
      (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a) (by linarith [hbalance a,hρ1 a])
      (d a) (hd a) (q a) (hq a) (hQ a) (s a) (hs a) (hS a)
    let ν:=fun a=>rawWheelLaw (V:=Fin n) (U:=U a) (fun _=>2*p a) (fun _=>by linarith [hp a]) (fun _=>by linarith [hbalance a,hρ1 a,hp a,ht a,hp₂ a,ht₂ a,hu a])
      (d a) (hd a) (q a) (hq a) (hQ a) (s a) (hs a) (hS a)
    let noise:=fun a=>FiniteLaw.pi (fun e=>μ a (Sum.inr e))
    let law:=physical.prod (FiniteLaw.pi noise)

    let Partition:=( fun c=>∀ A:Fin k→SimpleGraph (Fin n),
            (∀ a,A a≤edgeColourGraph R c a)→
            (∑ a,(A a).edgeFinset.card)≤B→
            ∃ H:Fin k→SimpleGraph (Fin n),
              EdgePartition R H ∧ (∀ a,(H a).IsRegularOfDegree (2*mclass a)) ∧
              (∀ a,A a≤H a) ∧
              (∀ a b x,x∈I b→∀ y,y∈I b→
                ((H a).Adj x y↔(edgeColourGraph R c a).Adj x y)) ∧
              (∀ a x,((Finset.univ.filter (fun y=>
                Xor ((H a).Adj x y) ((edgeColourGraph R c a).Adj x y))).card:ℝ)≤ξ*n))
    let A:=fun a=>mixedClassState (marks a)
      (∀ e:RawWheelCoordinate (Fin n) (U a),RawExpandedMarkedCoordinateState Bool Bool e)
      (RawWheelOutcome (Fin n) (U a) Bool Bool)
    let raw:=fun a=>mixedClassLaw (marks a) (FiniteLaw.pi (μ a)) (FiniteLaw.pi (ν a))
    let view:=fun a=>mixedClassView (marks a)
      (fun z=>combineSumCoordinates (fun e=>(markedPhysicalOptionIndex (classRefinedView a (z.1 e).1),(z.1 e).2)) (z.2 a))
      (fun z e=>expandedOrdinarySelectedCollapse e
        (combineSumCoordinates (fun edge=>(markedPhysicalOptionIndex (classRefinedView a (z.1 edge).1),(z.1 edge).2)) (z.2 a) e));
    ∀ (tag:Fin k→Bool),
    let F:=fun a (x:A a)=>mixedClassRetentionSpace (marks a) π (d a) (tag a) x
    letI : ∀ a x,Fintype (F a x):=fun a x=>mixedClassRetentionFintype (marks a) π (d a) (tag a) x
    let τ:=fun a (x:A a)=>mixedClassActualRetention (marks a) π (d a) (tag a) x;
    ∀ (Good:∀ a,(Σ x:A a,F a x)→Prop),
    (∀ a,1-(100*χ+200/(n:ℝ))≤((raw a).sigma (τ a)).probability (Good a))→
    let total:=law.sigma (fun z=>FiniteLaw.pi (fun a=>τ a (view a z)));
    ∃ z,0<total.mass z ∧ Partition (fun e=>(z.1.1 e).1.1) ∧ ∀ a,Good a ⟨view a z.1,z.2 a⟩ :=by
  obtain ⟨χ,hχ,N₀,hcore⟩:=factor_pruned_selected_actual_retention_common_event K hK α κL κS ξ hα hL0 hS0 hξ hL hS B
  obtain ⟨m₀,hm₀,hv⟩:=factor_pruned_shared_vortex_partition_budget K hK α κL κS β ε
    hα hL0 hS0 hb he heq hL hS hebudget h
  refine ⟨χ,hχ,N₀,m₀,hm₀,?_⟩
  intro m hm W _ n hn hnm hn0 classify D hEven hsize hDn δ hδ hdegree
    fibres cutoff small removed remaining cf D0 fibres0 C k e mclass ρ U R hR
  letI : Nonempty (Fin n):=⟨⟨0,hn0⟩⟩
  obtain ⟨Q,π,hpres,heqQ,hshort,hI⟩:=hv m hm hnm hn0 classify D hEven hsize hDn δ hδ hdegree R hR
  obtain ⟨hρ,htotal,hcore⟩:=hcore hn hn0 classify D hEven hsize hDn δ hδ hdegree R hR (fun a=>(Q a).vertices 1) hI
  refine ⟨Q,π,hpres,heqQ,hshort,hρ,htotal,?_⟩
  intro marks p t p₂ t₂ u hpp ht hp₂ ht₂ hu hbalance d hd q hq hQ s hs hS
    hρ0 hρ1 inside joint physical μ ν noise law Partition A raw view tag F τ Good hgood total
  exact hcore marks U p t p₂ t₂ u hpp ht hp₂ ht₂ hu hbalance d hd q hq hQ s hs hS π tag Good hgood
end Oberwolfach

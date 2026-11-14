module

public import Oberwolfach.OrdinaryLongProfileAbsorberGeometry
public import Oberwolfach.OrdinarySampledPropertyToProfiles
public import Oberwolfach.OrdinaryRelativeHostTransformerFromProfiles
public import Oberwolfach.OrdinaryCommonCycleProfiles
public import Oberwolfach.OrdinaryParentProfileHostTransformer
public import Oberwolfach.OrdinaryRelativeTransformerBudgets

@[expose] public section

/-! The ordinary relative transformer with all local numerical margins
discharged. The deletion tolerance precedes the root size, conflict degree
and bounded forbidden-set allowance; the order bound precedes the allowance.
The original profiles and probability laws are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 28000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem ordinary_relative_host_transformer_from_sampled_inputs (mcycle:ℕ) (hmcycle:3≤mcycle) (β a b pmin smin:ℝ)
    (hβ:0<β) (ha:0<a) (hb:0<b) (hpmin:0<pmin) (hsmin:0<smin):
    ∃ η ε:ℝ,0<η∧0<ε∧ε≤β/4∧∀ m:ℕ,∃ t:ℕ,1≤t∧∀ f:ℕ,∀ d:ℝ,0≤d→
      ∃ n₀:ℕ,
      ∀ (V U Γ Color:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color] [Nonempty U],
      n₀≤Fintype.card V→
      ∀ (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
      (A Z R W:Finset V) (B:Finset U) (L:Finset (Sym2 V⊕(V×U)))
      (P:SimpleGraph V) (π:Equiv.Perm V) (dSample:ℕ) (σ:RawWheelOutcome V U Γ Color) (j:Color),
      Q=rawWheelGraph P σ\F → H=rawWheelSpokes π dSample σ j →
      A=Finset.univ\Z→(Z.card:ℝ)≤ε*Fintype.card V→
      ordinaryResourceRows L⊆W→ ordinaryResourceHubs L⊆B→R⊆W→
      R.card≤m→W.card≤f→(B.card:ℝ)≤ε*Fintype.card V+f→
      (∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)→
      (∀ u,mcycle+1∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)→
      (∀ u,((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤m)→
      Fintype.card {u:U // ∃ v,H₀ v u}≤m→
      (∀ v∈G.support,v∈R∧φ v∈R)→
      (∀ v∈G.support,∀ w∈G.support,φ v≠w)→
      (∀ u,(∃ v,H₀ v u)→u≠ψ u)→
      G≤Q→(∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))→
      Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2))→
      Function.Injective (fun i:{e:V×U // H₀ e.1 e.2}=>(φ i.val.1,ψ i.val.2))→
      (∀ v u,H₀ v u→H v u∧H (φ v) (ψ u))→
      (∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)→
      (∀ v w,G.Adj v w→∀ a∈({v,w,φ v,φ w}:Finset V),
        ∀ c∈({v,w,φ v,φ w}:Finset V),¬F.Adj a c)→
      (∀ v,(F.degree v:ℝ)≤d)→
      (mcycle+1=4→∀ v w x,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w∩Q.neighborFinset x).card:ℝ))→
      (∀ T:Finset V,T.card≤mcycle+1+6→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))→
      ordinarySampledProfileProperty (r:=mcycle+1) P F π dSample σ pmin smin j β η a b →
      ∃ N:Finset V,∃ K:Finset (Sym2 V⊕(V×U)),
        N.card≤m*(mcycle+1)*(t+5*m)∧
        IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=mcycle+1))
          (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) K∧
        K⊆ordinaryHostResources Q H∧
        (∀ v v',Sum.inl s(v,v')∈K→v∈N∧v'∈N)∧
        (∀ v a,Sum.inr (v,a)∈K→v∈N)∧
        (∀ v∈R,∀ v'∈R,Sum.inl s(v,v')∉K)∧
        (∀ v∈R,∀ a∈B,Sum.inr (v,a)∉K)∧
        ∃ B':Finset U,B'.card≤m*(m+2)∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B')∧
          (∀ v∈W,∀ v',Sum.inl s(v,v')∈K→v∈R)∧
          (∀ v∈W,∀ a,Sum.inr (v,a)∈K→v∈R)∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B→∃ i:{u:U // ∃ v,H₀ v u},a=i.val∨a=ψ i.val)∧
          (ordinaryPhysicalGraph (ordinaryResourceRim Q K) (fun v u=>Sum.inr (v,u)∈K)).support.toFinset.card≤
            m*((mcycle+1)*(t+5*m)+m+2)∧N⊆R∪A∧Disjoint K L := by
  let c:ℝ:=(ordinaryLocalCountCoeff mcycle β/2)^(mcycle+2)
  let B:ℝ:=4*b/(pmin^(mcycle+1)*(smin*smin)^mcycle)
  have hc:0<c:=by dsimp [c];have hh:=ordinaryLocalCountCoeff_pos mcycle β hβ;positivity
  have hB:0<B:=by dsimp [B];positivity
  obtain ⟨η,ε,hη,hε,hεβ,hbase⟩:=ordinary_relative_host_transformer_from_profiles (mcycle+1) (by omega)
    (fun (_:Unit)=>pairedAbsorberTemplate (mcycle+1)) β c a B hβ hc ha hB
  refine ⟨η,ε,hη,hε,hεβ,?_⟩
  intro m
  obtain ⟨t,ht,hbase⟩:=hbase m
  refine ⟨t,ht,?_⟩
  intro f d hd
  obtain ⟨N₀,hbase⟩:=hbase f d hd
  obtain ⟨N₁,hprofile⟩:=ordinary_sampled_property_to_pair_profiles mcycle hmcycle β a b η d pmin smin hβ hd
  refine ⟨max N₀ N₁,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn G Q F H₀ H φ ψ A Z R W B L P π dSample σ j hQeq hHeq hA hZ hrows hhubs hRW hRcard hWcard hBcard
    hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF hthree hhub hprop
  subst Q
  subst H
  have geo:=ordinary_long_profile_absorber_geometry P F π dSample σ pmin smin j β η a b hprop
  letI : DecidableRel (rawWheelGraph P σ\F).Adj := Classical.decRel _
  have hcount:∀ v w,β*Fintype.card V≤(((rawWheelGraph P σ\F).neighborFinset v∩(rawWheelGraph P σ\F).neighborFinset w).card:ℝ):=by
    intro v w
    have hh:=geo.1 v w
    convert hh using 1 <;> try (congr 1; congr 1; ext z; simp)
  have hpair:∀ u u' v w,β*Fintype.card V≤(((Finset.univ.filter (fun z=>rawWheelSpokes π dSample σ j z u∧rawWheelSpokes π dSample σ j z u'))∩(rawWheelGraph P σ\F).neighborFinset v∩(rawWheelGraph P σ\F).neighborFinset w).card:ℝ):=by
    intro u u' v w
    have hh:=geo.2 u u' v w
    convert hh using 1 <;> try (congr 1; congr 1; ext z; simp)
  obtain ⟨P₀⟩:=hprofile V U Γ Color (by omega) P F π dSample σ j hF hprop
  exact hbase V U (by omega) G (rawWheelGraph P σ\F) F H₀ (rawWheelSpokes π dSample σ j) φ ψ A Z R W B L hA hZ hrows hhubs hRW hRcard hWcard hBcard
    hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF
    hcount hpair hthree hhub P₀
end Oberwolfach

module

public import Oberwolfach.OrdinaryRelativeAmbientAbsorber
public import Oberwolfach.OrdinaryPairProfilesForLargeOrder

@[expose] public section

/-! The longer-cycle relative ambient absorber from concrete two-neighbourhood
and fixed cycle-weight hypotheses. The paired-absorber profile is derived. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_long_cycle_ambient_absorber_from_weights (mcycle:ℕ) (hmcycle:3≤mcycle) (β b B:ℝ)
    (hβ:0<β) (hb:0<b) (hB:0<B):
    ∃ η ε:ℝ,0<η∧0<ε∧ε≤β/4∧∀ m:ℕ,∃ a₀ b₀:ℕ,∀ f:ℕ,∀ d:ℝ,0≤d→∃ n₀:ℕ,
    ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      n₀≤Fintype.card V→
      ∀ (G:SimpleGraph V) (Hs:V→U→Prop) (Q F:SimpleGraph V) (H:V→U→Prop)
      (A Z W:Finset V) (B₀:Finset U),
      (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m→
      (∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀ u,mcycle+1∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      G≤Q→(∀ v u,Hs v u→H v u)→
      (∀ u,(∃ v,Hs v u)→u∈B₀)→(∀ v w,Q.Adj v w→¬F.Adj v w)→
      A=Finset.univ\Z→(Z.card:ℝ)≤ε*Fintype.card V→W.card≤f→(B₀.card:ℝ)≤ε*Fintype.card V+f→
      (∀ v,(F.degree v:ℝ)≤d)→
      (∀ v w,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (∀ u u' v w,β*Fintype.card V≤(((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (mcycle+1=4→∀ v w x,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w∩Q.neighborFinset x).card:ℝ))→
      (∀ T:Finset V,T.card≤mcycle+1+6→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))→
      ∀ weight:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (Finset.univ.filter (fun v=>H v u∧H v u')) (mcycle+1)→ℝ,
      (∀ u u' (hne:u≠u') C,b/(Fintype.card V:ℝ)^mcycle≤weight u u' hne C∧
        weight u u' hne C≤B/(Fintype.card V:ℝ)^mcycle)→
      (∀ u u' (hne:u≠u'),∀ v∈Finset.univ.filter (fun v=>H v u∧H v u'),
        |1-hypergraphWeightedDegree localOrdinaryVertices (weight u u' hne) v|≤η)→
      ∃ C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=mcycle+1))
          (ordinaryHostResources G Hs) C∧
        C⊆ordinaryHostResources Q H∧(ordinaryResourceRows C).card≤a₀∧(ordinaryResourceHubs C).card≤b₀∧
        ordinaryResourceRows C⊆G.support.toFinset∪A∧
        (∀ v∈ordinaryResourceRows C,v∈W→v∈G.support.toFinset)∧
        (∀ u∈ordinaryResourceHubs C,u∈B₀→u∈Finset.univ.filter (fun u=>∃ v,Hs v u))∧
        Disjoint C (ordinaryRootResources W B₀) := by
  let a:ℝ:=(ordinaryLocalCountCoeff mcycle β/2)^(mcycle+2)
  have ha:0<a:=by dsimp [a];have hh:=ordinaryLocalCountCoeff_pos mcycle β hβ;positivity
  obtain ⟨η,ε,hη,hε,hεβ,hbase⟩:=ordinary_relative_ambient_absorber (mcycle+1) (by omega)
    (fun (_:Unit)=>pairedAbsorberTemplate (mcycle+1)) β a b B hβ ha hb hB
  refine ⟨η,ε,hη,hε,hεβ,?_⟩
  intro m
  obtain ⟨a₀,b₀,hbase⟩:=hbase m
  refine ⟨a₀,b₀,?_⟩
  intro f d hd
  obtain ⟨N₀,hbase⟩:=hbase f d hd
  obtain ⟨N₁,hprofile⟩:=ordinary_pair_profiles_for_large_order mcycle hmcycle β b B η d hβ hd
  refine ⟨max N₀ N₁,?_⟩
  intro V U _ _ _ _ hn G Hs Q F H A Z W B₀ hm hbal hdiv hG hH hB₀ hQF
    hA hZ hW hBsize hF hpair hspair hthree hhub weight hw hdeg
  obtain ⟨P⟩:=hprofile V U (by omega) Q F H hF hspair weight hw hdeg
  exact hbase V U (by omega) G Hs Q F H A Z W B₀ hm hbal hdiv hG hH hB₀ hQF
    hA hZ hW hBsize hF hpair hspair hthree (by intro h;omega) (by intro h;omega)
    hhub P
end Oberwolfach

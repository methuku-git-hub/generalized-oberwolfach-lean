module

public import Oberwolfach.OrdinaryGeneralSharpReferenceNormalizedRates
public import Oberwolfach.OrdinaryFineDeepCostSchedule

@[expose] public section
/-! At any vortex level the normalized sharp reference carries exactly the
fine-cover deep cost used by the level chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_reference_normalized_vortex_cost
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]
    (P:SimpleGraph V) (D mv:ℕ) (βv εv:ℝ) (Q:Vortex U P D βv εv mv) (i:ℕ)
    (Ploc Gloc Floc:SimpleGraph (markedVortexVertexType Q i))
    (Hloc:markedVortexVertexType Q i→markedVortexHubType Q i→Prop)
    (T:Finset (markedVortexVertexType Q i)) (W:Finset (markedVortexHubType Q i))
    (m loadK k:ℕ) (hm:3≤m+1)
    (ξroot κ lam ellCap finishCap bin cin deep loss α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c:ℝ)
    (hnV:0<Fintype.card (markedVortexVertexType Q i))
    (hroot:(T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q i))
    (hξ:0≤ξroot) (hκ:0≤κ) (hlam:0≤lam)
    (hell:max (18*κ+3*((loadK+1)*lam)) ((3*κ+lam)*((m:ℝ)+1))≤ellCap)
    (hcover:10*ξroot≤finishCap):
    let I:=markedVortexInnerVertices Q i;let J:=markedVortexInnerHubs Q i;
    let N:ℝ:=Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i);
    let cover:=10*ξroot*I.card;
    let ell:=max (18*κ*Fintype.card (markedVortexVertexType Q i)+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*κ*Fintype.card (markedVortexVertexType Q i)*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1));
    OrdinaryRootCoverSharpReferenceExists Ploc Gloc Floc Hloc I T J W (m+1) k hm
      cover ell bin cin deep loss α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c→
    ∃ηrate ellrate:ℝ,0≤ηrate ∧ ηrate≤finishCap ∧ 0≤ellrate ∧ ellrate≤ellCap ∧
      ηrate*N=ordinaryFineDeepCost Q ξroot i ∧
      OrdinaryRootCoverSharpReferenceExists Ploc Gloc Floc Hloc I T J W (m+1) k hm
        (ηrate*N) (ellrate*N) bin cin deep loss α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c :=by
  intro I J N cover ell href
  have hn:=ordinary_general_sharp_reference_normalized_rates Ploc Gloc Floc Hloc I T J W m loadK k hm
    ξroot κ lam ellCap finishCap bin cin deep loss α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c
    hnV hroot hξ hκ hlam hell hcover href
  obtain ⟨ηrate,ellrate,hη0,hηcap,hell0,hellcap,hcost,href'⟩:=hn
  refine ⟨ηrate,ellrate,hη0,hηcap,hell0,hellcap,?_,href'⟩
  have hs:=ordinary_fine_deep_cost_at_level Q ξroot i
  exact hcost.trans (by convert hs.symm using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
end Oberwolfach

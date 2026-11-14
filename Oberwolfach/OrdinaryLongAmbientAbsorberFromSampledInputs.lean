module

public import Oberwolfach.OrdinaryLongProfileAbsorberGeometry
public import Oberwolfach.OrdinarySampledPropertyToProfiles
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

theorem ordinary_long_cycle_ambient_absorber_from_sampled_inputs (mcycle:ℕ) (hmcycle:3≤mcycle) (β a b pmin smin:ℝ)
    (hβ:0<β) (ha:0<a) (hb:0<b) (hpmin:0<pmin) (hsmin:0<smin):
    ∃ η ε:ℝ,0<η∧0<ε∧ε≤β/4∧∀ m:ℕ,∃ a₀ b₀:ℕ,∀ f:ℕ,∀ d:ℝ,0≤d→∃ n₀:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color] [Nonempty U],
      n₀≤Fintype.card V→
      ∀ (G:SimpleGraph V) (Hs:V→U→Prop) (Q F:SimpleGraph V) (H:V→U→Prop)
      (A Z W:Finset V) (B₀:Finset U)
      (P:SimpleGraph V) (π:Equiv.Perm V) (dSample:ℕ) (σ:RawWheelOutcome V U Γ Color) (j:Color),
      Q=rawWheelGraph P σ\F → H=rawWheelSpokes π dSample σ j →
      (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m→
      (∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀ u,mcycle+1∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      G≤Q→(∀ v u,Hs v u→H v u)→
      (∀ u,(∃ v,Hs v u)→u∈B₀)→
      A=Finset.univ\Z→(Z.card:ℝ)≤ε*Fintype.card V→W.card≤f→(B₀.card:ℝ)≤ε*Fintype.card V+f→
      (∀ v,(F.degree v:ℝ)≤d)→
      (mcycle+1=4→∀ v w x,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w∩Q.neighborFinset x).card:ℝ))→
      (∀ T:Finset V,T.card≤mcycle+1+6→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))→
      ordinarySampledProfileProperty (r:=mcycle+1) P F π dSample σ pmin smin j β η a b →
      ∃ C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=mcycle+1))
          (ordinaryHostResources G Hs) C∧
        C⊆ordinaryHostResources Q H∧(ordinaryResourceRows C).card≤a₀∧(ordinaryResourceHubs C).card≤b₀∧
        ordinaryResourceRows C⊆G.support.toFinset∪A∧
        (∀ v∈ordinaryResourceRows C,v∈W→v∈G.support.toFinset)∧
        (∀ u∈ordinaryResourceHubs C,u∈B₀→u∈Finset.univ.filter (fun u=>∃ v,Hs v u))∧
        Disjoint C (ordinaryRootResources W B₀) := by
  let c:ℝ:=(ordinaryLocalCountCoeff mcycle β/2)^(mcycle+2)
  let B:ℝ:=4*b/(pmin^(mcycle+1)*(smin*smin)^mcycle)
  have hc:0<c:=by dsimp [c];have hh:=ordinaryLocalCountCoeff_pos mcycle β hβ;positivity
  have hB:0<B:=by dsimp [B];positivity
  obtain ⟨η,ε,hη,hε,hεβ,hbase⟩:=ordinary_relative_ambient_absorber (mcycle+1) (by omega)
    (fun (_:Unit)=>pairedAbsorberTemplate (mcycle+1)) β c a B hβ hc ha hB
  refine ⟨η,ε,hη,hε,hεβ,?_⟩
  intro m
  obtain ⟨a₀,b₀,hbase⟩:=hbase m
  refine ⟨a₀,b₀,?_⟩
  intro f d hd
  obtain ⟨N₀,hbase⟩:=hbase f d hd
  obtain ⟨N₁,hprofile⟩:=ordinary_sampled_property_to_pair_profiles mcycle hmcycle β a b η d pmin smin hβ hd
  refine ⟨max N₀ N₁,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn G Hs Q F H A Z W B₀ P π dSample σ j hQ hH hm hbal hdiv hG hHs hB₀
    hA hZ hW hBsize hF hthree hhub hprop
  subst Q
  subst H
  have hQF:∀ v w,(rawWheelGraph P σ\F).Adj v w→¬F.Adj v w:=by
    intro v w hw
    simp only [SimpleGraph.sdiff_adj] at hw
    exact hw.2
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
  have hh:=hprofile V U Γ Color (by omega) P F π dSample σ j hF hprop
  obtain ⟨P₀⟩:=hh
  exact hbase V U (by omega) G Hs (rawWheelGraph P σ\F) F (rawWheelSpokes π dSample σ j) A Z W B₀ hm hbal hdiv hG hHs hB₀ hQF
    hA hZ hW hBsize hF hcount hpair hthree (by intro h;omega) (by intro h;omega)
    hhub P₀
end Oberwolfach

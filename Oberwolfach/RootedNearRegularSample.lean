module

public import Oberwolfach.RootedTwoDenseGraphs
public import Oberwolfach.SubsetComplementDegrees

@[expose] public section
/-! A fixed-size set disjoint from fixed roots inherits a common degree
centre at every sampled vertex and at every root. Both bounds hold on the
same without-replacement sample. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rooted_near_regular_sample (s:ℕ) (η:ℝ) (hη:0<η) (hη1:η≤1):
    ∃ K:ℕ,∀ k:ℕ,K≤k→∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (G:SimpleGraph V) (T:Finset V),T.card=s→∀ θ:ℝ,0≤θ→θ≤1→
    (∀ v,|((G.degree v):ℝ)-θ*Fintype.card V|≤(η/8)*Fintype.card V)→
    ∃ S:Finset V,S.card=k ∧ Disjoint S T ∧
      (∀ v∈S∪T,|((G.neighborFinset v∩S).card:ℝ)-θ*k|≤η*k):=by
  obtain ⟨K₀,hK₀⟩:=rooted_two_dense_graphs_exist s (η/4) (by positivity)
  obtain ⟨K₁,hK₁⟩:=eventually_constant_le_linear ((s:ℝ)+1) (η/8) (by positivity)
  refine ⟨max K₀ K₁,?_⟩
  intro k hk
  obtain ⟨N₀,hN₀⟩:=hK₀ k (by omega)
  obtain ⟨N₁,hN₁⟩:=eventually_constant_le_linear 1 (η/4) (by positivity)
  refine ⟨max N₀ N₁,?_⟩
  intro V _ _ hn G T hT θ hθ hθ1 hnear
  let P:SimpleGraph V:=Gᶜ
  letI : DecidableRel P.Adj := fun _ _ => Classical.propDecidable _
  have hN:(1:ℝ)≤(η/4)*Fintype.card V:=hN₁ _ (by omega)
  have hroot:(s:ℝ)+1≤(η/8)*k:=hK₁ k (by omega)
  have hG (v:V):((θ-η/2)+η/4)*Fintype.card V≤(G.degree v:ℝ):=by
    have hh:=abs_le.mp (hnear v)
    have hn0:(0:ℝ)≤Fintype.card V:=by positivity
    nlinarith
  have hGc (v:V):((1-θ-3*η/4)+η/4)*Fintype.card V≤(P.degree v:ℝ):=by
    have hh:=abs_le.mp (hnear v)
    have hcom:=subset_explicit_complement_degrees G P rfl Finset.univ v (Finset.mem_univ _)
    simp only [Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree,Finset.card_univ] at hcom
    have hcomR:((G.degree v):ℝ)+(P.degree v:ℝ)+1=Fintype.card V:=by exact_mod_cast hcom
    have hn0:(0:ℝ)≤Fintype.card V:=by positivity
    nlinarith
  obtain ⟨R,hR₁,hR₂⟩:=hN₀ V (by omega) G P T hT (θ-η/2) (1-θ-3*η/4) hG (by intro v; simpa only using hGc v)
  let S:=R.val.val\T
  have hcard:S.card=k:=by
    dsimp [S]
    rw [Finset.card_sdiff_of_subset R.property,R.val.property,hT]
    omega
  have hST:S∪T=R.val.val:=Finset.sdiff_union_of_subset R.property
  refine ⟨S,hcard,Finset.sdiff_disjoint,?_⟩
  intro v hv
  have hvR:v∈R.val.val:=hST ▸ hv
  have hlo:=hR₁ v hvR
  have hcomp:=hR₂ v hvR
  have hsum:=subset_explicit_complement_degrees G P rfl R.val.val v hvR
  rw [R.val.property] at hsum
  have hsumR:((G.neighborFinset v∩R.val.val).card:ℝ)+
      ((P.neighborFinset v∩R.val.val).card:ℝ)+1=s+k:=by
    have hh:T.card+k=s+k:=by omega
    have hsum' := hsum.trans hh
    exact_mod_cast hsum'
  have hsub:G.neighborFinset v∩S⊆G.neighborFinset v∩R.val.val:=by
    intro w hw
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1,Finset.sdiff_subset ((Finset.mem_inter.mp hw).2)⟩
  have hupper:((G.neighborFinset v∩S).card:ℝ)≤(G.neighborFinset v∩R.val.val).card:=by
    exact_mod_cast Finset.card_le_card hsub
  have hsub2:G.neighborFinset v∩R.val.val⊆(G.neighborFinset v∩S)∪T:=by
    intro w hw
    by_cases hwT:w∈T
    · exact Finset.mem_union_right _ hwT
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1,
        Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hw).2,hwT⟩⟩)
  have hcr:((G.neighborFinset v∩R.val.val).card:ℝ)≤((G.neighborFinset v∩S).card:ℝ)+s:=by
    have hh:=(Finset.card_le_card hsub2).trans (Finset.card_union_le _ _)
    have hh':(G.neighborFinset v∩R.val.val).card≤(G.neighborFinset v∩S).card+s:=by omega
    exact_mod_cast hh'
  have hs0:(0:ℝ)≤s:=by positivity
  have hk0:(0:ℝ)≤k:=by positivity
  have hprod:θ*(s:ℝ)≤s:=by nlinarith
  have hηs:η*(s:ℝ)≤s:=by nlinarith
  have hhiR:((G.neighborFinset v∩R.val.val).card:ℝ)<(θ+5*η/8)*(s+k)-1:=by nlinarith only [hcomp,hsumR]
  apply abs_le.mpr
  constructor
  · nlinarith only [hlo,hcr,hroot,hθ,hs0,hηs]
  · nlinarith only [hhiR,hupper,hroot,hprod,hηs]
end Oberwolfach

module

public import Oberwolfach.SampledDomainDegreeChanges
public import Oberwolfach.DomainCodegreeCuts

@[expose] public section

/-! Degree and cut conclusions after sampled vertex classes are altered
and an arbitrary bounded-degree graph is deleted. The exceptional row
pairs are retained in the explicit order condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem fresh_bipartite_restriction (G F D:SimpleGraph V) (A B A' B' A'' B'':Finset V)
    (p ρ η ξ:ℝ) (b:ℕ) (hp:0<p) (hp1:p≤1) (hρ:0<ρ)
    (hη:0≤η) (hη1:η≤1/4) (hξ:0<ξ) (hB:0<B.card)
    (hA'':A''⊆A) (hB'':B''⊆B)
    (hF:∀ v,F.degree v≤b)
    (hrow:∀ v∈A,|((B∩G.neighborFinset v).card:ℝ)-p*B.card|≤η*B.card)
    (hcol:∀ v∈B,|((A∩G.neighborFinset v).card:ℝ)-p*A.card|≤η*A.card)
    (hcodeg:∀ v∈A,∀ w∈A,v≠w→¬F.Adj v w→
      (((B∩G.neighborFinset v)∩G.neighborFinset w).card:ℝ)≤(p^2+η)*B.card)
    (hsizeA:|((A').card:ℝ)-ρ*A.card|≤η*(ρ*A.card))
    (hsizeB:|((B').card:ℝ)-ρ*B.card|≤η*(ρ*B.card))
    (hsrow:∀ v∈A,|((B'∩G.neighborFinset v).card:ℝ)-ρ*(B∩G.neighborFinset v).card|≤η*(ρ*B.card))
    (hscol:∀ v∈B,|((A'∩G.neighborFinset v).card:ℝ)-ρ*(A∩G.neighborFinset v).card|≤η*(ρ*A.card))
    (hscodeg:∀ v∈A,∀ w∈A,v≠w→¬F.Adj v w→
      |(((B'∩G.neighborFinset v)∩G.neighborFinset w).card:ℝ)-
        ρ*((B∩G.neighborFinset v)∩G.neighborFinset w).card|≤η*(ρ*B.card))
    (hchangeA:((changed A'' A').card:ℝ)≤η*(ρ*A.card))
    (hchangeB:((changed B'' B').card:ℝ)≤η*(ρ*B.card))
    (hDA:∀ v,(D.degree v:ℝ)≤η*(ρ*A.card))
    (hDB:∀ v,(D.degree v:ℝ)≤η*(ρ*B.card))
    (hdegree:12*η≤p/2) (hsmall:12*η≤p^2*ξ/24)
    (hlarge:(b+1:ℝ)≤p^2*ξ^2*(ρ*B.card)/16):
    (∀ v∈A'',p/2*B''.card≤((B''∩(G\D).neighborFinset v).card:ℝ)) ∧
    (∀ v∈B'',p/2*A''.card≤((A''∩(G\D).neighborFinset v).card:ℝ)) ∧
    (∀ S:Finset V,S⊆A''→∀ T:Finset V,T⊆B''→ξ*B''.card≤(S.card:ℝ)→ξ*B''.card≤(T.card:ℝ)→
      p/2*S.card*T.card≤(bipartiteMatrixCut (fun v w=>if (G\D).Adj v w then 1 else 0) S T:ℝ)):=by
  have ha:=sampled_domain_size_after_changes A A' A'' ρ η hρ.le hη hη1 hsizeA hchangeA
  have hb:=sampled_domain_size_after_changes B B' B'' ρ η hρ.le hη hη1 hsizeB hchangeB
  have he (C:Finset V) (v:V):(C∩(G\D).neighborFinset v)=(C∩G.neighborFinset v)\D.neighborFinset v:=by
    ext w;simp only [Finset.mem_inter,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj];tauto
  have hr (v:V) (hv:v∈A''):
      |((B''∩(G\D).neighborFinset v).card:ℝ)-p*B''.card|≤12*η*B''.card:=by
    rw [he]
    exact sampled_domain_degree_after_changes B B' B'' (G.neighborFinset v) (D.neighborFinset v)
      p ρ η hp.le hp1 hρ.le hη hη1 (hrow v (hA'' hv)) (hsrow v (hA'' hv)) hb.1 hchangeB
      (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hDB v)
  have hc (v:V) (hv:v∈B''):
      |((A''∩(G\D).neighborFinset v).card:ℝ)-p*A''.card|≤12*η*A''.card:=by
    rw [he]
    exact sampled_domain_degree_after_changes A A' A'' (G.neighborFinset v) (D.neighborFinset v)
      p ρ η hp.le hp1 hρ.le hη hη1 (hcol v (hB'' hv)) (hscol v (hB'' hv)) ha.1 hchangeA
      (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hDA v)
  have hcod (v:V) (hv:v∈A'') (w:V) (hw:w∈A'') (hne:v≠w) (hfw:¬F.Adj v w):
      ((B''.filter (fun u=>(G\D).Adj v u∧(G\D).Adj w u)).card:ℝ)≤(p^2+12*η)*B''.card:=by
    have hs:B''.filter (fun u=>(G\D).Adj v u∧(G\D).Adj w u)⊆
        B''∩(G.neighborFinset v∩G.neighborFinset w):=by
      intro u hu
      obtain ⟨hu,hv,hw⟩:=Finset.mem_filter.mp hu
      exact Finset.mem_inter.mpr ⟨hu,Finset.mem_inter.mpr
        ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hv.1,(SimpleGraph.mem_neighborFinset _ _ _).mpr hw.1⟩⟩
    have hh:=sampled_domain_codegree_upper B B' B'' (G.neighborFinset v∩G.neighborFinset w)
      p ρ η hp.le hp1 hρ.le hη hη1
      (by simpa only [Finset.inter_assoc] using hcodeg v (hA'' hv) w (hA'' hw) hne hfw)
      (by simpa only [Finset.inter_assoc] using hscodeg v (hA'' hv) w (hA'' hw) hne hfw)
      hb.1 hchangeB
    have hh':((B''.filter (fun u=>(G\D).Adj v u∧(G\D).Adj w u)).card:ℝ)≤(p^2+10*η)*B''.card:=
      (Nat.cast_le.mpr (Finset.card_le_card hs)).trans hh
    have hpos:0≤η*(B''.card:ℝ):=by positivity
    nlinarith only [hh',hpos]
  have hrowlower (v:V) (hv:v∈A''):
      (p-12*η)*B''.card≤((B''.filter ((G\D).Adj v)).card:ℝ):=by
    have hh:=(abs_le.mp (hr v hv)).1
    have he:B''.filter ((G\D).Adj v)=B''∩(G\D).neighborFinset v:=by ext u;simp
    rw [he];nlinarith only [hh]
  refine ⟨?_,?_,?_⟩
  · intro v hv
    have hh:=(abs_le.mp (hr v hv)).1
    have hm:=mul_le_mul_of_nonneg_right hdegree (Nat.cast_nonneg B''.card)
    nlinarith only [hh,hm]
  · intro v hv
    have hh:=(abs_le.mp (hc v hv)).1
    have hm:=mul_le_mul_of_nonneg_right hdegree (Nat.cast_nonneg A''.card)
    nlinarith only [hh,hm]
  · intro S hS T hT hSc hTc
    have hbpos:0<B''.card:=by
      have hpos:0<ρ*(B.card:ℝ)/2:=by positivity
      have hh:=hpos.trans_le hb.2.1
      exact_mod_cast hh
    have hlarge':(b+1:ℝ)≤p^2*ξ^2*B''.card/8:=by
      have hh:=mul_le_mul_of_nonneg_left hb.2.1 (show 0≤p^2*ξ^2/8 by positivity)
      nlinarith only [hh,hlarge]
    have hh:=degree_codegree_cuts_on_domains (G\D).Adj F A'' B'' p (12*η) ξ b hp hp1
      (by positivity) hξ hbpos hF (by intro v hv; convert hrowlower v hv using 1 <;> congr! 2 <;> ext u <;> simp only [Finset.mem_filter])
      (by intro v hv w hw hne hfw; convert hcod v hv w hw hne hfw using 1 <;> congr! 2 <;> ext u <;> simp only [Finset.mem_filter])
      hsmall hlarge' S hS T hT hSc hTc
    convert hh using 1
    congr 2
    funext v w
    by_cases h:(G\D).Adj v w <;> simp only [h,ite_true,ite_false]

end Oberwolfach

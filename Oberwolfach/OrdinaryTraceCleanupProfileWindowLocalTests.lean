module

public import Oberwolfach.OrdinaryTraceRawPairWindowEditsLocal
public import Oberwolfach.OrdinaryRawRowsPairRestriction
public import Oberwolfach.OrdinaryRawDomainPairRestriction
public import Oberwolfach.OrdinaryInducedTargetNeighbourCount
public import Oberwolfach.OrdinaryCleanupProfileFromDeepSample

@[expose] public section
/-! An ambient common sample and a protected trace supply the actual cleanup
profile on the next induced pair, with the initial and latest edit costs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_trace_cleanup_profile_from_window_local_tests
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ) (i:ℕ) (Jwin:Finset ℕ)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (ρ:Equiv.Perm ↥(X i)) (hcomm:∀x:↥(X i),(ρ x).val=π x.val)
    (D:Finset ↥(X i)) (E:Finset ↥(Z i))
    (pR pH density tR tH L βe βh:ℝ) (s:U→Color→ℝ)
    (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH) (hdensity:1/2≤density) (hs:∀u,s u j=pH)
    (hQF:Disjoint Q F)
    (hbase:∀a:↥(X i)⊕↥(Z i),
      ((changed ((ordinaryPhysicalGraph ((rawWheelGraph P σ).induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>rawWheelSpokes π d σ j v.val u.val)).neighborFinset a)
        ((ordinaryPhysicalGraph (Q.induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>H v.val u.val)).neighborFinset a)).card:ℝ)≤L)
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G Hs=A)
    (hJ:∀j∈Jwin,j < i+1)
    (hX:∀j < i+1,j∉Jwin→X i⊆T j) (hZ:∀j < i+1,j∉Jwin→Z i⊆W j)
    (hXnest:∀j∈Jwin,X i⊆X j) (hZnest:∀j∈Jwin,Z i⊆Z j):
    let V₁:=↥(X i);let U₁:=↥(Z i);
    let f:V₁↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let g:U₁↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    (∀v:V₁,density*D.card≤((D∩(P.induce ((X i):Set V)).neighborFinset v).card:ℝ))→
    RawOrdinaryRows (P.induce ((X i):Set V)) ρ d 3 D pR (fun u=>s (g u)) j tR (ordinaryRawRestrictPair f g σ)→
    RawOrdinaryDomainIndices (F.induce ((X i):Set V)) ρ d 3 E pH j tH (ordinaryRawRestrictPair f g σ)→
    βe*Fintype.card (V₁⊕U₁)+tR+3*(L+∑j∈Jwin,cost j)≤pR^2*pH*(2*density-1)*D.card→
    βh*Fintype.card (V₁⊕U₁)+tH+2*(L+∑j∈Jwin,cost j)≤pH^2*E.card→
    OrdinaryCleanupParentProfiles (P.induce ((X i):Set V)) (G.induce ((X i):Set V)) (F.induce ((X i):Set V))
      (fun (v:V₁) (u:U₁)=>Hs v.val u.val) ρ d D E pR pH density tR tH (L+∑j∈Jwin,cost j) βe βh
      (fun u=>s (g u)) j (ordinaryRawRestrictPair f g σ):=by
  intro V₁ U₁ f g hmin hrows hcols hext hhub
  have hle:G≤Q:=by
    obtain ⟨R,S,hist,_,_⟩:=htrace
    have hG: G=ordinaryHistoryRim Q R S (i+1):=
      (ordinaryHostResources_injective G (ordinaryHistoryRim Q R S (i+1)) Hs
        (ordinaryHistorySpokes H R S (i+1)) (hstate.trans hist.symm)).1
    rw [hG]
    intro v w hvw
    exact hvw.1
  have hdis:Disjoint (G.induce ((X i):Set V)) (F.induce ((X i):Set V)):=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (disjoint_iff_inf_le.mp hQF) ⟨hle hvw.1,hvw.2⟩
  have he:=ordinary_trace_raw_pair_window_edits_local P Q H π d j σ X T Z W cost deepCost i Jwin A G Hs ρ hcomm L hbase htrace hstate hJ hX hZ hXnest hZnest
  refine ⟨hpR,hpR1,hpH,hdensity,(fun u=>hs (g u)),hdis,?_,?_,?_,?_,?_,?_,hext,hhub⟩
  · intro v
    convert hmin v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro S J hS hJ
    have hh:=hrows S J (by omega) (by omega)
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro S hS hfree
    have hh:=hcols S hS hfree
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v
    convert he.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro u
    convert he.2.2 u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v
    convert he.2.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach

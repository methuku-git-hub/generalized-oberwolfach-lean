module

public import Oberwolfach.LongCorrectedActiveColumnNoNewSpokes
public import Oberwolfach.FirstVortexAssignedEdgeBudgetFromVortexScale

@[expose] public section
/-! The all-hub completion's local loss and the actual bad-edge count give
first-active spoke control with θ fixed independently of the transfer cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance correctedActiveMatchingScaleFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_corrected_active_column_from_matching_scale
    (cap a ε θ lam ζ Pbound:ℝ) (d m:ℕ)
    (hcap:0<cap) (ha:0<a) (hε:0<ε) (hε1:ε≤1/4) (hm:0<m)
    (hθ:0≤θ) (hθε:θ*ε≤cap*a/4096) (hlam:lam≤cap*a/4096)
    (hζ:0≤ζ) (hζcap:ζ≤cap/128) (hP0:0≤Pbound):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→∀(U:Type) [Fintype U] [DecidableEq U]
    (G:SimpleGraph (Fin n)) (D:ℕ) (β:ℝ) (Q:Vortex U G D β ε m)
    (π:Equiv.Perm (Fin n)) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R:U→Finset (Fin n)) (inner:Finset U) (E:ℕ),
    (E:ℝ)≤(θ*ε^2+lam*ε)*(n:ℝ)^2+24*d*n→
    Pbound≤cap*(ε*n)/128→
    let A:=Q.extendedVertices 1
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false
    let H':=fun b v w=>if b then H true v w else v∈R w\Y w
    let W:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))
    let Z:=markedVortexNonDeeperHubType Q 0
    let f:=markedVortexActiveVertexEmbedding Q 1
    let g:=markedVortexNonDeeperHubToPhysical Q 0
    let HL:=fun b v u=>H b (f v) (g u)
    let HL':=fun b v u=>H' b (f v) (g u)
    let FS:=markedSpokeChangeGraph HL HL';
    (∀w∈inner,∀v∈A,v∈R w\Y w↔H false v w)→
    (∀w∉inner,((A.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤
      ζ*A.card+Pbound+2*(⌈4*(E:ℝ)/(a*n)⌉₊:ℕ))→
    (∀w v,v∈A→v∈R w\Y w→H false v w)→
    (∀b v u,¬(HL b v u↔HL' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) ∧
    (∀u:Z,(FS.degree (Sum.inr u):ℝ)≤cap*Fintype.card W) :=by
  obtain ⟨N,hN⟩:=first_vortex_assigned_edge_local_budget_from_vortex_scale cap a ε θ lam d hcap ha hε (by linarith) hθ hθε hlam
  refine ⟨N,?_⟩
  intro n hn hn0 U _ _ G D β Q π raw t J R inner E hE hP A Y H H' W Z f g HL HL' FS hexact hloss hNoNew
  have hL:=hN n hn hn0 E hE
  have hloss0:0≤ζ*(A.card:ℝ)+Pbound+2*(⌈4*(E:ℝ)/(a*n)⌉₊:ℕ):=by positivity
  exact long_corrected_active_column_no_new_spokes G D m β ε Q hε hε1 hm π d raw t J R inner cap ζ Pbound
    (⌈4*(E:ℝ)/(a*n)⌉₊:ℕ) hcap.le hζ hloss0 hζcap hP hL hexact hloss hNoNew
end Oberwolfach

module

public import Oberwolfach.FirstVortexGeometricActiveCeiling
public import Oberwolfach.LongCorrectedActiveColumnNoNewSpokes

@[expose] public section
/-! The same repaired graph and corrected spokes give the first-active
change graph using the geometric edge bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance geometricActiveSpokeFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem first_vortex_geometric_active_spoke_changes_eventually
    (d:ℕ) (ρ ε cap:ℝ) (hd:1≤d) (hρ:0<ρ) (hε:0<ε) (hε1:ε≤1/4) (hcap:0<cap)
    (hrate:8*((1/2:ℝ)*ε^2)/((ρ/4)/40000)<cap*ε/128):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
      (P S Sel Used:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U P D β ε m)
      (Req:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n)))
      (hSP:S≤P) (hm:0<m) (hI:((Q.extendedVertices 1).card:ℝ)≤ε*n)
      (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
      (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
      (R:U→Finset (Fin n)) (inner:Finset U) (ζ Pbound:ℝ)
      (hζ0:0≤ζ) (hP0:0≤Pbound) (hζ:ζ≤cap/128) (hP:Pbound≤cap*(ε*n)/128),
      let K:=longRequiredPhysicalGraph S (S\Used) Sel π d (Q.extendedVertices 1) Req (fun x y=>Used.Adj x y)
      let Kplus:=longClassInnerRequiredRepair S Used K (Q.extendedVertices 1) Pack
      let loss:ℝ:=⌈4*(Kplus.edgeFinset.card:ℝ)/(((ρ/4)/40000)*n)⌉₊
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
      (∀w∉inner,((A.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤ζ*A.card+Pbound+2*loss)→
      (∀w v,v∈A→v∈R w\Y w→H false v w)→
      (∀b v u,¬(HL b v u↔HL' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) ∧
      (∀u:Z,(FS.degree (Sum.inr u):ℝ)≤cap*Fintype.card W) :=by
  obtain ⟨N,hN⟩:=first_vortex_geometric_active_ceiling_eventually d ρ ε cap hd hρ hε hcap hrate
  refine ⟨N,?_⟩
  intro n hn U _ _ P S Sel Used π D m β Q Req Pack hSP hm hI raw t J R inner ζ Pbound hζ0 hP0 hζ hP K Kplus loss A Y H H' W Z f g HL HL' FS hexact hloss hNoNew
  have hL:2*loss≤cap*(ε*n)/128:=hN n hn P S Sel Used π (Q.extendedVertices 1) Req Pack hSP hI
  have hloss0:0≤ζ*((Q.extendedVertices 1).card:ℝ)+Pbound+2*loss:=by positivity
  exact long_corrected_active_column_no_new_spokes P D m β ε Q hε hε1 hm π d raw t J R inner cap ζ Pbound loss
    hcap.le hζ0 hloss0 hζ hP hL hexact hloss hNoNew
end Oberwolfach

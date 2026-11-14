module

public import Oberwolfach.MarkedVortexInitialSampleChangeData
public import Oberwolfach.MarkedPotentialAllRootsAfterChanges

@[expose] public section
/-! Transfer every initial-parent potential root through the same physical
change graphs, with the original parent weight. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_potential_transfer
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (Dnat mV:ℕ) (β ε:ℝ) (Q:Vortex U G Dnat β ε mV)
    (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (d m:ℕ) (hm:3≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (σglobal τglobal:RawMarkedOutcome V U Γ Color) (Hglobal Hglobal':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (ζ:ℝ) (hζ:0≤ζ)
    (hinterval:∀e,σglobal (Sum.inr e)=τglobal (Sum.inr e))
    (hR:∀a,¬(rawMarkedPairRims G π d σglobal a↔rawMarkedPairRims G π d τglobal a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀b v u,¬(Hglobal b v u↔Hglobal' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V):
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hπ 0
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g σglobal
    let τ:=rawMarkedRestrictPair f g τglobal
    let H:=fun b v u=>Hglobal b (f v) (g u)
    let H':=fun b v u=>Hglobal' b (f v) (g u);
    ∀ (D τweight A B p k s₀ pstar eps:ℝ)
      (hB:0≤B) (hDlo:(Fintype.card W:ℝ)/2≤D) (hDhi:D≤2*Fintype.card W)
      (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
      (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1)
      (weight:(Fin (m+1)→W)→ℝ)
      (hw:SuccessorSequenceWeightConditions P ρ (3*d) D τweight A B weight),
    let seed:=fun X:MarkedWheel (Prod.fst:W×W→W) Prod.snd Prod.fst Prod.snd m ρ (3*d)
      (fun (_:W) (_:Z)=>True) (fun _ _=>True)=>weight X.1.val/(D*p^m*k*s₀^m);
    ∀root:((W×W)⊕(W×W))⊕(Bool×W×Z),
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P ρ d σ) H root-1|≤eps→
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P ρ d τ) H' root-1|≤
        eps+33*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*ζ := by
  intro W Z f g ρ P σ τ H H' D τweight A B p k s₀ pstar eps hB hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 weight hw seed root hload
  have hchanges:=marked_vortex_initial_sample_change_data Q π hπ d σglobal τglobal Hglobal Hglobal' FR FS ζ hinterval hR hS hFR hFS
  have hcardW:Fintype.card W=Fintype.card V:=hchanges.2.2.2.2.2.1
  have hcardZ:Fintype.card Z=Fintype.card U:=hchanges.2.2.2.2.2.2
  have hn':0<Fintype.card W:=by rw [hcardW];exact hn
  have hu':Fintype.card Z≤Fintype.card W:=by rw [hcardW,hcardZ];exact hu
  have hnR:0<(Fintype.card W:ℝ):=by exact_mod_cast hn'
  have hcard_ne:(Fintype.card (markedVortexVertexType Q 0):ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hn')
  have hδ:0≤ζ*Fintype.card W:=by positivity
  have hdec:(Subtype.instDecidableEq : DecidableEq W)=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  try rw [hdec] at hw
  rw [hdec] at hload ⊢
  have h:=marked_potential_all_roots_after_changes P ρ d m hm hn' hu' D τweight A B hDlo hDhi
    p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw eps (ζ*Fintype.card W) (ζ*Fintype.card W) hδ hδ
    σ τ H H' (FR.comap f) (FS.comap (Sum.map f g)) hchanges.2.1 hchanges.2.2.1 hchanges.2.2.2.1
    (fun v=>hchanges.2.2.2.2.1 (Sum.inl v)) (fun u=>hchanges.2.2.2.2.1 (Sum.inr u)) root hload
  convert h using 1 <;> dsimp only [W] <;> field_simp [hcard_ne] <;> ring
end Oberwolfach

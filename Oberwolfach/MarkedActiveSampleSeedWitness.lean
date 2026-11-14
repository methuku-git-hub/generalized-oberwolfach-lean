module

public import Oberwolfach.MarkedInducedSampleSeedWitness
public import Oberwolfach.MarkedComplementSeedTransfer

@[expose] public section

/-! Restrict the original normalized weights to a fixed invariant row
complement and a hub complement. Retained roots lose only the explicitly
bounded forbidden-vertex weight; the original normalization is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U VA UA Γ Color:Type} [Fintype VA] [Fintype UA] [LinearOrder VA] [DecidableEq UA] [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_active_sample_seed_witness
    (f:VA↪oV) (i:UA↪U) (ρ:Equiv.Perm VA)
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m) (hn:0<Fintype.card V)
    (hu:Fintype.card U≤Fintype.card V) (D τ A B p k s₀ pstar η:ℝ)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hA:0≤A) (hB:0≤B) (hη:0≤η)
    (weight:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (hq:∀ u,0<q u g) (hS:∀ u,0<s u j)
    (hload:
      let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
      ∀ root,rawMarkedWheelMarginal P π d p k q s g j root≠0→
        |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤η)
    (T:Finset V) (Z:Finset U) (hT:∀ x,π x∈T↔x∈T)
    (hf:∀ x,f (ρ x)=π (f x))
    (hfX:Finset.univ.image f=Finset.univ\T) (hiX:Finset.univ.image i=Finset.univ\Z):
    let σA:=rawMarkedRestrictPair f i σ
    let HA:=fun j x u=>H j (f x) (i u)
    let η':=η+((T.card:ℝ)+Z.card)*((m:ℝ)+1)^3*(2*B/pstar^(2*m+1))/Fintype.card V
    let E:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let K:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true
    let ψ:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m ρ (3*d) (HA false) (HA true)=>weight (f∘W.1.val)/(D*p^m*k*s₀^m)
    (∀ e,|markedWheelRimLoad ψ e-1|≤η')∧
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η')∧
    (∀ W,(A/2)/(Fintype.card V:ℝ)^m≤ψ W∧ψ W≤(2*B/pstar^(2*m+1))/(Fintype.card V:ℝ)^m) :=by
  intro σA HA η' E K ψ
  obtain ⟨hRload,hSload,hcoeff⟩:=marked_induced_sample_seed_witness P π d m hm hn hu
    D τ A B p k s₀ pstar η hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 hA hB hη
    weight hw σ H q s g j hq hS hload T Z hT
  exact marked_complement_seed_transfer f i π ρ hf P d m σ H T Z hT hfX hiX
    (fun C=>weight C/(D*p^m*k*s₀^m)) η' ((A/2)/(Fintype.card V:ℝ)^m)
    ((2*B/pstar^(2*m+1))/(Fintype.card V:ℝ)^m) hRload hSload hcoeff

end Oberwolfach

module

public import Oberwolfach.MarkedCanonicalDeletedBalanceValues
public import Oberwolfach.MarkedRestrictedSampleBalanceValues

@[expose] public section

/-! Transfer the original finite remainder estimates to every root in
the actual active sample. Only the opposite endpoint is restricted in the
inner balance; no assumption about roots inside the inner pair is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U VA UA Γ Color:Type} [Fintype V] [Fintype U] [Fintype VA] [Fintype UA]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder VA] [DecidableEq U] [DecidableEq UA]

theorem marked_canonical_active_balance_bounds
    (f:VA↪oV) (g:UA↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm VA)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (T:Finset V) (W:Finset U) (hfT:∀ v,f v∉T) (hgW:∀ u,g u∉W)
    (X:Finset VA) (Z:Finset UA) (I:Finset V) (J:Finset U)
    (hX:∀ x,f x∈I↔x∈X) (hZ:∀ u,g u∈J↔u∈Z):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (A:Finset (E₀⊕E₁)) (B:Finset (V×U)) (εF εI:ℝ),
    (∀ (z:V⊕U),Sum.elim (fun v=>v∉T) (fun u=>u∉W) z→∀ i:Fin 4,
      |markedFiniteBalance (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:E₁=>e.val.1) (fun e=>e.val.2)
        (H true) (Finset.univ\A) (S\B) m z i|≤εF∧
      |markedFiniteDomainBalance (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:E₁=>e.val.1) (fun e=>e.val.2)
        (H true) (Finset.univ\A) (S\B) m I J z i|≤εI)→
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ A).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph B);
    (∀ j,∀ e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) j,
      e.val.1∈Finset.univ.image f∧e.val.2∈Finset.univ.image f)→
    (∀ v u,H' false v u∨H' true v u→v∈Finset.univ.image f∧u∈Finset.univ.image g)→
    let σA:=rawMarkedRestrictPair f g σ'
    let HA:=fun j x u=>H' j (f x) (g u)
    let EA₀:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let EA₁:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true
    let SA:=Finset.univ.filter (fun s:VA×UA=>HA false s.1 s.2∨HA true s.1 s.2);
    ∀ (z:VA⊕UA) (i:Fin 4),
    |markedFiniteBalance (fun e:EA₀=>e.val.1) (fun e=>e.val.2) (fun e:EA₁=>e.val.1) (fun e=>e.val.2)
      (HA true) Finset.univ SA m z i|≤εF∧
    |markedFiniteDomainBalance (fun e:EA₀=>e.val.1) (fun e=>e.val.2) (fun e:EA₁=>e.val.1) (fun e=>e.val.2)
      (HA true) Finset.univ SA m X Z z i|≤εI:=by
  intro E₀ E₁ S A B εF εI hbound σ' H' hA hS σA HA EA₀ EA₁ SA z i
  have hh:=marked_restricted_sample_balance_values f g π ρ hf P d m σ' H' X Z I J hX hZ hA hS z i
  have hc:=marked_canonical_deleted_balance_values P π d m σ H A B I J (Sum.map f g z) i
  have hz:Sum.elim (fun v=>v∉T) (fun u=>u∉W) (Sum.map f g z):=by
    cases z with
    | inl v=>exact hfT v
    | inr u=>exact hgW u
  have hb:=hbound (Sum.map f g z) hz i
  constructor
  · rw [hh.1,hc.1];exact hb.1
  · rw [hh.2,hc.2];exact hb.2

end Oberwolfach

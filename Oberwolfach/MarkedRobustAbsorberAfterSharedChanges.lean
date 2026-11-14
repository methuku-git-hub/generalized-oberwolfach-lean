module

public import Oberwolfach.MarkedRobustAbsorberInputsSharedChanges
public import Oberwolfach.MarkedReservedAbsorbersAfterPhysicalDeletion

@[expose] public section
/-! Construct robust absorbers in the actual corrected host. Its common
witnesses and extension counts are inherited from the same reference sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_robust_absorber_after_shared_changes
    (r:ℕ) (hr:2≤r) (ρ σlevel q₀ bc bp blo bhi B pstar:ℝ)
    (hρ:0<ρ) (hσ:0<σlevel) (hq:0<q₀) (hbc:0<bc) (hbp:0<bp)
    (hblo:0<blo) (hbhi:0<bhi) (hB:0<B) (hpstar:0<pstar):
    ∃ ε ζ:ℝ,0<ε ∧ 0<ζ ∧ ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f d:ℕ,2≤d→∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],N≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (D τweight A p k s₀:ℝ),
      (Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
      pstar≤p→pstar≤k→pstar≤s₀*s₀/((r+4:ℕ):ℝ)→
      p≤1→k≤1→s₀*s₀/((r+4:ℕ):ℝ)≤1→q₀≤(s₀/((r+4:ℕ):ℝ))^2→
    ∀ (weight:(Fin (r+4+1)→V)→ℝ),
      SuccessorSequenceWeightConditions P π (3*d) D τweight A B weight→
      (∀ C:Fin (r+4+1)→V,SuccessorSequenceValid P π C→PermutationSeparated π (3*d) C→
        blo/(Fintype.card V:ℝ)^(r+4)≤weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4)) ∧
        weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4))≤bhi/(Fintype.card V:ℝ)^(r+4))→
    ∀ (old new:RawMarkedOutcome V U Γ Color) (H Hnew:Bool→V→U→Prop)
      (es eo el bcOld bpOld c ch delta:ℝ) (hdelta:0≤delta)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
      (∀a,¬(rawMarkedPairRims P π d old a↔rawMarkedPairRims P π d new a)→markedPairPhysical π a∈FR.edgeFinset)→
      (∀b v u,¬(H b v u↔Hnew b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
      (∀x,(FR.degree x:ℝ)≤delta)→(∀z,(FS.degree z:ℝ)≤delta)→
      (∀v u,¬(Hnew false v u∧Hnew true v u))→
      es+2*delta/Fintype.card V≤ε/2→eo+4*delta/Fintype.card V≤ε/2→
      el+20*((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*delta/Fintype.card V≤ε/2→
      bc≤bcOld-3*(r+5:ℕ)*delta/Fintype.card V→
      bp≤bpOld-4*(r+5:ℕ)*delta/Fintype.card V→
      ρ*Fintype.card V≤c-4*delta→σlevel*Fintype.card V≤ch-(r+11)*delta→
      (∀u u':U,u≠u'→∃κ,CommonWitnessEstimates P π d r D p k s₀ es eo el bcOld bpOld weight old H κ u u')→
    let E:=MarkedSampleArc P π (3*d) (fun e=>old (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>old (Sum.inl e)) true;
    MarkedHostExtensionCounts (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H false) (H true) π (3*d) r c ch→
    ∃κ:U→U→V→Bool,
      (∀u u':U,u≠u'→CommonWitnessEstimates P π d r D p k s₀ (ε/2) (ε/2) (ε/2) bc bp weight new Hnew (κ u u') u u') ∧
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀x,(DR.degree x:ℝ)≤ζ*Fintype.card V)→(∀z,(DS.degree z:ℝ)≤ζ*Fintype.card V)→
      let current:=rawMarkedDeleteRims new DR.edgeFinset
      let Hcurrent:=markedDeletePhysicalSpokes Hnew DS;
      MarkedReservedTerminalAbsorberProperty
        (fun e:MarkedSampleArc P π (3*d) (fun a=>current (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc P π (3*d) (fun a=>current (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2)
        (Hcurrent false) (Hcurrent true) π (3*d) r size a₀ b₀ e₀ f ε:=by
  obtain ⟨ε,ζ,hε,hζ,habs⟩:=marked_reserved_absorbers_after_physical_deletion r hr
    ρ σlevel q₀ bc bp blo bhi B pstar hρ hσ hq hbc hbp hblo hbhi hB hpstar
  refine ⟨ε,ζ,hε,hζ,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,habs⟩:=habs size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f d hd
  obtain ⟨N,hN,habs⟩:=habs f d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P π D τweight A p k s₀ hDlo hDhi hp hk hs hp1 hk1 hs1 hq0 weight hw hweight
    old new H Hnew es eo el bcOld bpOld c ch delta hdelta FR FS hR hS hFR hFS htypes hes heo hel hbc' hbp' hc hch hwitness E K Q
  have hnpos:0<Fintype.card V:=lt_of_lt_of_le hN hn
  have hinputs:=marked_robust_absorber_inputs_after_shared_changes P π d r (by omega) hnpos D τweight A B p k s₀ pstar
    hB.le hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 weight hw es eo el bcOld bpOld c ch delta
    (ε/2) (ε/2) (ε/2) bc bp (ρ*Fintype.card V) (σlevel*Fintype.card V) hdelta old new H Hnew FR FS
    hR hS hFR hFS hes heo hel hbc' hbp' hc hch hwitness Q
  exact habs V U Γ Color hn P π D τweight A p k s₀ hDlo hDhi hp hk hs hp1 hk1 hs1 hq0
    weight hw hweight new Hnew htypes hinputs.1 hinputs.2
end Oberwolfach

module

public import Oberwolfach.MarkedActiveDeletionSeparateBounds
public import Oberwolfach.MarkedTwoStageDeletionScale

@[expose] public section

/-! Apply the actual prescribed-packing and deep-cover bounds on the active
complement. There is no maximum-degree requirement at a covered deep root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U VA UA E K E' K':Type} [Fintype V] [Fintype U] [Fintype VA] [Fintype UA]
  [LinearOrder V] [DecidableEq U] [DecidableEq VA] [DecidableEq UA]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}
  {tail' head':E'→V} {ktail' khead':K'→V} {π':Equiv.Perm V} {m' b':ℕ} {H₀' HK':V→U→Prop}

theorem marked_constructed_active_deletion_bounds
    (ME:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (MD:Finset (MarkedWheel tail' head' ktail' khead' m' π' b' H₀' HK'))
    (I T:Finset V) (J W:Finset U)
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\W))=∅)
    (f:VA↪V) (g:UA↪U) (hf:∀ x,f x∉T) (hg:∀ u,g u∉W)
    (r K₀:ℕ) (etaE xi kappa:ℝ) (he:0≤etaE) (hxi:0≤xi)
    (hT:(T.card:ℝ)≤xi*Fintype.card V) (hW:(W.card:ℝ)≤xi*Fintype.card V)
    (hE:(4*K₀+3*r+50:ℝ)*etaE≤kappa/2) (hXi:(4*K₀+3*r+50:ℝ)*xi≤kappa/2)
    (hER:∀ x,((markedPackingRimGraph ME).degree x:ℝ)≤24*etaE*Fintype.card V)
    (hEV:∀ x,((Finset.univ.filter (markedPackingSpokes ME x)).card:ℝ)≤6*etaE*Fintype.card V)
    (hEU:∀ u,((Finset.univ.filter (fun x=>markedPackingSpokes ME x u)).card:ℝ)≤3*(r+5)*etaE*Fintype.card V)
    (hDR:∀ x∉I,(markedPackingRimGraph MD).degree x≤2*W.card+T.card*(4*(K₀+4))+2*T.card)
    (hDV:∀ x∉I,(Finset.univ.filter (markedPackingSpokes MD x)).card≤W.card+T.card*(K₀+4))
    (hDU:∀ u∉W,(Finset.univ.filter (fun x=>markedPackingSpokes MD x u)).card≤T.card*(r+5)):
    let DR:=markedPackingRimGraph ME⊔markedPackingRimGraph MD
    let DS:=markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs);
    (∀ x,((DR.comap f).degree x:ℝ)≤kappa*Fintype.card V)∧
    (∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤kappa*Fintype.card V)∧
    (∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤kappa*Fintype.card V):=by
  intro DR DS
  have hsp:=markedFiniteSpokeGraph_packing_degrees ME
  obtain ⟨hR,hV,hU⟩:=marked_active_total_deletion_bounds_separate MD I T J W hstar f g hf hg
    (markedPackingRimGraph ME) (markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs))
    (24*etaE*Fintype.card V) (6*etaE*Fintype.card V) (3*(r+5)*etaE*Fintype.card V)
    (2*W.card+T.card*(4*(K₀+4))+2*T.card) (W.card+T.card*(K₀+4)) (T.card*(r+5))
    hER (fun x=>by rw [hsp.1];exact hEV x) (fun u=>by rw [hsp.2];exact hEU u)
    (by positivity) (by positivity)
    (fun x hx=>by exact_mod_cast hDR x hx) (fun x hx=>by exact_mod_cast hDV x hx)
    (fun u hu=>by exact_mod_cast hDU u hu)
  have hb:=marked_two_stage_deletion_scale r K₀ (Fintype.card V) T.card W.card etaE xi kappa
    (Nat.cast_nonneg _) he hxi hT hW hE hXi
  exact ⟨fun x=>(hR x).trans (by simpa only [add_assoc] using hb.1),fun x=>(hV x).trans (by simpa only [add_assoc] using hb.2.1),fun u=>(hU u).trans hb.2.2⟩

end Oberwolfach

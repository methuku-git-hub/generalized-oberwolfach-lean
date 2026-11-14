module

public import Oberwolfach.MarkedPhysicalDeletionExtensions
public import Oberwolfach.MarkedSpokeDeletionExtensions
public import Oberwolfach.MarkedSampleDeletedArcs
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion

@[expose] public section

/-! Extension counts in the actual physically deleted sample. The typed
arc occurrences are identified by their exact deletion equivalences, and
spoke losses are measured by the realized physical degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem marked_host_extension_counts_arc_congr
    (tail head:E→V) (ktail khead:K→V) (tail' head':E'→V) (ktail' khead':K'→V)
    (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b l:ℕ) (c ch:ℝ)
    (hArc:∀ j x y,markedArcPresent tail head ktail khead j x y ↔
      markedArcPresent tail' head' ktail' khead' j x y)
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch) :
    MarkedHostExtensionCounts tail' head' ktail' khead' H₀ HK π b l c ch where
  outgoing j k x P hP:=by simpa only [hArc] using Q.outgoing j k x P hP
  incoming j k x P hP:=by simpa only [hArc] using Q.incoming j k x P hP
  twoOutgoing k x y P hxy hP:=by simpa only [hArc] using Q.twoOutgoing k x y P hxy hP
  twoIncoming j k x y P hxy hP:=by simpa only [hArc] using Q.twoIncoming j k x y P hxy hP
  twoStep k x y P hxy hP:=by simpa only [hArc] using Q.twoStep k x y P hxy hP
  hubs A B hd hab hsep:=Q.hubs A B hd hab hsep

variable {Γ Color:Type} [Fintype Γ] [Fintype Color] [LinearOrder V]

theorem marked_sample_host_extensions_after_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d l:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (c ch:ℝ) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (t:ℕ)
    (hrim:∀ v,DR.degree v≤t) (hspoke:∀ z,DS.degree z≤t) :
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedHostExtensionCounts (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H false) (H true) π (3*d) l c ch →
    MarkedHostExtensionCounts (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) l
      (c-4*t) (ch-(l+11)*t) := by
  intro E K σ' H' E' K' Q
  let F:V→U→Prop:=fun v u=>DS.Adj (Sum.inl v) (Sum.inr u)
  have hrow (v:V):(Finset.univ.filter (F v)).card≤t:=
    (physical_spoke_deleted_row DS v).trans (hspoke (Sum.inl v))
  have hcol (u:U):(Finset.univ.filter (fun v=>F v u)).card≤t:=
    (physical_spoke_deleted_col DS u).trans (hspoke (Sum.inr u))
  have hrimR:∀ v,(DR.degree v:ℝ)≤t:=by intro v;exact_mod_cast hrim v
  have Qr:=marked_host_extensions_after_rim_deletion Q DR (t:ℝ) (by positivity) hrimR
  have Qs:=marked_host_extensions_after_spoke_deletion Qr F t t hrow hcol
  let ER:={e:E // ¬DR.Adj e.val.1 e.val.2}
  let KR:={e:K // ¬DR.Adj e.val.1 (π e.val.2)}
  have hArc:∀ j x y,markedArcPresent (fun e:ER=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:KR=>e.val.val.1) (fun e=>e.val.val.2) j x y ↔
      markedArcPresent (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) j x y := by
    intro j x y
    cases j
    · simp only [markedArcPresent,Bool.false_eq_true,ite_false]
      constructor
      · rintro ⟨e,he₁,he₂⟩
        let e':E':=⟨e.val.val,(markedPhysicalRim_delete_iff P π d σ DR.edgeFinset false _ _).mpr
          ⟨e.val.property,by simpa only [Bool.false_eq_true,ite_false,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using e.property⟩⟩
        exact ⟨e',he₁,he₂⟩
      · rintro ⟨e,he₁,he₂⟩
        let e':ER:=⟨⟨e.val,((markedPhysicalRim_delete_iff P π d σ DR.edgeFinset false _ _).mp e.property).1⟩,
          by simpa only [Bool.false_eq_true,ite_false,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using
            ((markedPhysicalRim_delete_iff P π d σ DR.edgeFinset false _ _).mp e.property).2⟩
        exact ⟨e',he₁,he₂⟩
    · simp only [markedArcPresent,ite_true]
      constructor
      · rintro ⟨e,he₁,he₂⟩
        let e':K':=⟨e.val.val,(markedPhysicalRim_delete_iff P π d σ DR.edgeFinset true _ _).mpr
          ⟨e.val.property,by simpa only [ite_true,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using e.property⟩⟩
        exact ⟨e',he₁,he₂⟩
      · rintro ⟨e,he₁,he₂⟩
        let e':KR:=⟨⟨e.val,((markedPhysicalRim_delete_iff P π d σ DR.edgeFinset true _ _).mp e.property).1⟩,
          by simpa only [ite_true,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using
            ((markedPhysicalRim_delete_iff P π d σ DR.edgeFinset true _ _).mp e.property).2⟩
        exact ⟨e',he₁,he₂⟩
  have hCounts:=marked_host_extension_counts_arc_congr
    (fun e:ER=>e.val.val.1) (fun e=>e.val.val.2) (fun e:KR=>e.val.val.1) (fun e=>e.val.val.2)
    (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
    (H' false) (H' true) π (3*d) l (c-2*t-2*t) (ch-(l+11)*t) hArc Qs
  convert hCounts using 1 <;> push_cast <;> ring

end Oberwolfach

module

public import Oberwolfach.MarkedCommonConfigurationsAfterPhysicalDeletion

@[expose] public section
/-! Typed host inclusion preserves the actual common-cycle and root-omitted
path families without changing their vertex tuples. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (tail head:E→V) (ktail khead:K→V) (tail' head':E'→V) (ktail' khead':K'→V)
  (π:Equiv.Perm V) (b:ℕ) (H H':Bool→V→U→Prop)
variable (hE:∀ e,∃ e',tail' e'=tail e∧head' e'=head e)
  (hK:∀ e,∃ e',ktail' e'=ktail e∧khead' e'=khead e)
  (hH:∀ a v u,H a v u→H' a v u)

include hE hK in
theorem marked_cycle_tuple_under_typed_host_inclusion (m:ℕ) (C:Fin (m+1)→V)
    (hC:IsMarkedCycleTuple tail head ktail khead m π b C):
    IsMarkedCycleTuple tail' head' ktail' khead' m π b C:=by
  refine ⟨hC.1,?_,?_⟩
  · intro i
    obtain ⟨e,ht,hh⟩:=hC.2.1 i
    obtain ⟨e',ht',hh'⟩:=hE e
    exact ⟨e',ht'.trans ht,hh'.trans hh⟩
  · obtain ⟨e,ht,hh⟩:=hC.2.2
    obtain ⟨e',ht',hh'⟩:=hK e
    exact ⟨e',ht'.trans ht,hh'.trans hh⟩

include hE hK in
theorem marked_root_first_cycle_under_typed_host_inclusion
    (m:ℕ) (i:Fin (m+1)) (C:Fin (m+1)→V)
    (hC:IsRootFirstMarkedCycle tail head ktail khead m π b i C):
    IsRootFirstMarkedCycle tail' head' ktail' khead' m π b i C:=by
  refine ⟨hC.1,?_⟩
  intro j
  by_cases hj:j=i
  · rw [if_pos hj] at ⊢
    have hold:=hC.2 j
    rw [if_pos hj] at hold
    obtain ⟨e,ht,hh⟩:=hold
    obtain ⟨e',ht',hh'⟩:=hK e
    exact ⟨e',ht'.trans ht,hh'.trans hh⟩
  · rw [if_neg hj] at ⊢
    have hold:=hC.2 j
    rw [if_neg hj] at hold
    obtain ⟨e,ht,hh⟩:=hold
    obtain ⟨e',ht',hh'⟩:=hE e
    exact ⟨e',ht'.trans ht,hh'.trans hh⟩

def marked_common_cycle_host_inclusion (m:ℕ) (u u':U):
    CommonMarkedCycle tail head ktail khead m π b (H false) (H true) u u' ↪
      CommonMarkedCycle tail' head' ktail' khead' m π b (H' false) (H' true) u u' where
  toFun C:=⟨⟨C.val.val,marked_cycle_tuple_under_typed_host_inclusion tail head ktail khead tail' head' ktail' khead' π b hE hK m C.val.val C.val.property⟩,
    ⟨⟨hH true _ _ C.property.1.1,fun i=>hH false _ _ (C.property.1.2 i)⟩,
      ⟨hH true _ _ C.property.2.1,fun i=>hH false _ _ (C.property.2.2 i)⟩⟩⟩
  inj' C D h:=by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z=>z.val.val) h

def marked_common_path_host_inclusion (m:ℕ) (j:Bool) (v v':V) (u u':U):
    RootFirstCommonMarkedPath tail head ktail khead m π b (H false) (H true) j v v' u u' ↪
      RootFirstCommonMarkedPath tail' head' ktail' khead' m π b (H' false) (H' true) j v v' u u' where
  toFun C:=⟨C.val,⟨
    marked_root_first_cycle_under_typed_host_inclusion tail head ktail khead tail' head' ktail' khead' π b hE hK m _ _ C.property.1,
    marked_root_first_cycle_under_typed_host_inclusion tail head ktail khead tail' head' ktail' khead' π b hE hK m _ _ C.property.2.1,
    fun i=>by
      have hh:=C.property.2.2 i
      cases htype:rootFirstSpokeType m j i.succ <;> simp only [htype,ite_false,ite_true] at hh ⊢
      · exact ⟨hH false _ _ hh.1,hH false _ _ hh.2⟩
      · exact ⟨hH true _ _ hh.1,hH true _ _ hh.2⟩⟩⟩
  inj' C D h:=by
    apply Subtype.ext
    exact congrArg (fun z:RootFirstCommonMarkedPath tail' head' ktail' khead' m π b (H' false) (H' true) j v v' u u'=>z.val) h
end Oberwolfach

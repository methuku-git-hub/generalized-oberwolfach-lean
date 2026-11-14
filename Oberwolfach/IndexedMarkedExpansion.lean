module

public import Oberwolfach.IndexedMarkedWheelExtension
public import Oberwolfach.IndexedMarkedGraphPermutations
public import Oberwolfach.PrivateOccurrenceExchange
public import Oberwolfach.MarkedExpansionPositions

@[expose] public section

/-! The marked expansion is an actual finite graph operation. It exchanges
heads of same-type rim arcs and hubs of same-type spokes with their private
wheel occurrences; no old edge survives between two old vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]

def indexedMarkedExpansion (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    IndexedMarkedGraph (V⊕((A⊕S)×Fin (m+1))) (U⊕(A⊕S))
      (A⊕((A⊕S)×Fin (m+1))) (S⊕((A⊕S)×Fin (m+1))):=
  ((indexedMarkedWheelExtension (I:=A⊕S) G m).permuteHeads
    (privateOccurrenceExchange (fun a=>markedExpansionRimPosition m hm (G.jr a)))).permuteHubs
    (privateSpokeExchange (fun s=>markedExpansionSpokePosition m hm (G.js s)))

theorem indexedMarkedExpansion_balanced (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (hG:G.IsBalanced m):(indexedMarkedExpansion G m hm).IsBalanced m:=by
  apply IndexedMarkedGraph.permuteHubs_balanced
  · apply IndexedMarkedGraph.permuteHeads_balanced
    · exact indexedMarkedWheelExtension_balanced G m hG
    · apply privateOccurrenceExchange_preserves_type
      intro a
      exact (markedExpansionRimPosition_type m hm (G.jr a)).symm
  · apply privateSpokeExchange_preserves_type
    intro s
    exact (markedExpansionSpokePosition_type m hm (G.js s)).symm

@[simp] theorem indexedMarkedExpansion_src_old (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m) (a:A):
    (indexedMarkedExpansion G m hm).src (Sum.inl a)=Sum.inl (G.src a):=rfl
@[simp] theorem indexedMarkedExpansion_src_private (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (i:A⊕S) (k:Fin (m+1)):
    (indexedMarkedExpansion G m hm).src (Sum.inr (i,k))=Sum.inr (i,k):=rfl
@[simp] theorem indexedMarkedExpansion_dst_old (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m) (a:A):
    (indexedMarkedExpansion G m hm).dst (Sum.inl a)=
      Sum.inr (Sum.inl a,finRotate (m+1) (markedExpansionRimPosition m hm (G.jr a))):=rfl
@[simp] theorem indexedMarkedExpansion_dst_private_rim (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (a:A) (k:Fin (m+1)):
    (indexedMarkedExpansion G m hm).dst (Sum.inr (Sum.inl a,k))=
      if k=markedExpansionRimPosition m hm (G.jr a) then Sum.inl (G.dst a)
      else Sum.inr (Sum.inl a,finRotate (m+1) k):=by
  change paddingRimHead (Sum.inl∘G.dst) (fun i k=>Sum.inr (i,k))
    (privateOccurrenceExchange (fun a=>markedExpansionRimPosition m hm (G.jr a)) (Sum.inr (Sum.inl a,k)))=_
  rw [privateOccurrenceExchange_private]
  split <;> rfl
@[simp] theorem indexedMarkedExpansion_dst_private_spoke (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (s:S) (k:Fin (m+1)):
    (indexedMarkedExpansion G m hm).dst (Sum.inr (Sum.inr s,k))=
      Sum.inr (Sum.inr s,finRotate (m+1) k):=rfl
@[simp] theorem indexedMarkedExpansion_row_old (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m) (s:S):
    (indexedMarkedExpansion G m hm).row (Sum.inl s)=Sum.inl (G.row s):=rfl
@[simp] theorem indexedMarkedExpansion_row_private (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (i:A⊕S) (k:Fin (m+1)):
    (indexedMarkedExpansion G m hm).row (Sum.inr (i,k))=Sum.inr (i,k):=rfl
@[simp] theorem indexedMarkedExpansion_hub_old (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m) (s:S):
    (indexedMarkedExpansion G m hm).hub (Sum.inl s)=Sum.inr (Sum.inr s):=rfl
@[simp] theorem indexedMarkedExpansion_hub_private_rim (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (a:A) (k:Fin (m+1)):
    (indexedMarkedExpansion G m hm).hub (Sum.inr (Sum.inl a,k))=Sum.inr (Sum.inl a):=rfl
@[simp] theorem indexedMarkedExpansion_hub_private_spoke (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (s:S) (k:Fin (m+1)):
    (indexedMarkedExpansion G m hm).hub (Sum.inr (Sum.inr s,k))=
      if k=markedExpansionSpokePosition m hm (G.js s) then Sum.inl (G.hub s)
      else Sum.inr (Sum.inr s):=by
  change paddingSpokeHub G.hub m
    (privateSpokeExchange (fun s=>markedExpansionSpokePosition m hm (G.js s)) (Sum.inr (Sum.inr s,k)))=_
  rw [privateSpokeExchange_private]
  split <;> rfl

end Oberwolfach

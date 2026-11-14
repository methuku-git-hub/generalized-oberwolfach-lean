module

public import Oberwolfach.IndexedMarkedExpansion

@[expose] public section

/-! The expansion commutes with identifying the old row and hub vertices.
The private wheel indices are retained, so multiplicities survive collapse. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' A S:Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
    [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U'] [DecidableEq A] [DecidableEq S]

@[ext] theorem indexedMarkedGraph_ext (G H:IndexedMarkedGraph V U A S)
    (hs:G.src=H.src) (hd:G.dst=H.dst) (hr:G.row=H.row) (hu:G.hub=H.hub)
    (hj:G.jr=H.jr) (hk:G.js=H.js):G=H:=by
  cases G;cases H;cases hs;cases hd;cases hr;cases hu;cases hj;cases hk;rfl

theorem indexedMarkedWheelExtension_map (G:IndexedMarkedGraph V U A S) (m:ℕ)
    (f:V→V') (g:U→U'):
    (indexedMarkedWheelExtension (I:=A⊕S) G m).map (Sum.map f id) (Sum.map g id)=
      indexedMarkedWheelExtension (G.map f g) m:=by
  apply indexedMarkedGraph_ext <;> funext a <;> cases a <;> rfl

theorem indexedMarkedExpansion_map (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (f:V→V') (g:U→U'):
    (indexedMarkedExpansion G m hm).map (Sum.map f id) (Sum.map g id)=
      indexedMarkedExpansion (G.map f g) m hm:=by
  unfold indexedMarkedExpansion
  rw [IndexedMarkedGraph.map_permuteHubs,IndexedMarkedGraph.map_permuteHeads,indexedMarkedWheelExtension_map]
  rfl

theorem indexedMarkedExpansion_map_src (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (f:V→V') (g:U→U') (a:A⊕((A⊕S)×Fin (m+1))):
    Sum.map f id ((indexedMarkedExpansion G m hm).src a)=
      (indexedMarkedExpansion (G.map f g) m hm).src a:=
  congrArg (fun H=>H.src a) (indexedMarkedExpansion_map G m hm f g)

theorem indexedMarkedExpansion_map_dst (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (f:V→V') (g:U→U') (a:A⊕((A⊕S)×Fin (m+1))):
    Sum.map f id ((indexedMarkedExpansion G m hm).dst a)=
      (indexedMarkedExpansion (G.map f g) m hm).dst a:=
  congrArg (fun H=>H.dst a) (indexedMarkedExpansion_map G m hm f g)

theorem indexedMarkedExpansion_map_row (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (f:V→V') (g:U→U') (s:S⊕((A⊕S)×Fin (m+1))):
    Sum.map f id ((indexedMarkedExpansion G m hm).row s)=
      (indexedMarkedExpansion (G.map f g) m hm).row s:=
  congrArg (fun H=>H.row s) (indexedMarkedExpansion_map G m hm f g)

theorem indexedMarkedExpansion_map_hub (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (f:V→V') (g:U→U') (s:S⊕((A⊕S)×Fin (m+1))):
    Sum.map g id ((indexedMarkedExpansion G m hm).hub s)=
      (indexedMarkedExpansion (G.map f g) m hm).hub s:=
  congrArg (fun H=>H.hub s) (indexedMarkedExpansion_map G m hm f g)

end Oberwolfach

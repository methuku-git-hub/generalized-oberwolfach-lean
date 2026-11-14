module

public import Oberwolfach.MarkedRootPairPadding
public import Oberwolfach.MarkedExceptionalRows
public import Oberwolfach.MarkedHostExtensionCounts

@[expose] public section

/-! Construct both padding families at exactly the exceptional source
rows. The augmented graph is constructed from their actual occurrences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

abbrev MarkedRootPair.Exceptional (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):Type:=
  {v:V // ExceptionalMarkedRow G.dst G.jr v}

theorem MarkedRootPair.exceptional_roots (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):
    ∀ i:G.Exceptional,i.val∈G.R∧G.φ i.val∈G.R':=by
  intro i
  obtain ⟨a,ha⟩:=exceptional_marked_row_has_incoming G.dst G.jr i.val i.property
  rw [←ha];exact ⟨(G.rimRoots a).2.1,(G.rimRoots a).2.2.2⟩

theorem MarkedRootPair.exceptional_roots_separated (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):
    ∀ i:G.Exceptional,¬PermutationClose π b i.val (G.φ i.val):=by
  intro i
  obtain ⟨a,ha⟩:=exceptional_marked_row_has_incoming G.dst G.jr i.val i.property
  have hne:i.val≠G.φ i.val:=by
    intro he;exact Finset.disjoint_left.mp G.disjointRows (G.exceptional_roots i).1 (he.symm ▸ (G.exceptional_roots i).2)
  apply G.fourRootSeparation a i.val (by simp [←ha]) (G.φ i.val) (by simp [←ha]) hne

structure MarkedRootPadding (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S) (W:Finset V) where
  p:Bool×G.Exceptional→(Fin m↪V)
  hub:(Bool×G.Exceptional)↪U
  C:Bool×G.Exceptional→MarkedWheel tail head ktail khead m π b H₀ HK
  φ:V→V
  ψ:U→U
  oldRows:∀ z∈G.R∪G.R',φ z=G.φ z
  oldHubs:∀ z∈G.B,ψ z=G.ψ z
  mapHubs:∀ i,ψ (hub (false,i))=hub (true,i)
  mapCycles:∀ i k,φ ((C (false,i)).1.val k)=(C (true,i)).1.val k
  hubs:∀ i,(C i).2.val=hub i∧hub i∉G.B
  coordinates:∀ i k,(C i).1.val k=Fin.cons (α:=fun _=>V)
    (if i.1 then G.φ i.2.val else i.2.val) (p i) k
  avoid:∀ i k,p i k∉W∧p i k∉G.R∪G.R'∧∀ z∈G.R∪G.R',¬PermutationClose π b (p i k) z
  disjointPaths:∀ i j,i≠j→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p j))
  separatedPaths:∀ i j,∀ k k',p i k≠p j k'→¬PermutationClose π b (p i k) (p j k')
  packing:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))

def MarkedRootPadding.pair {G:MarkedRootPair tail head ktail khead H₀ HK π b m A S} {W:Finset V}
    (P:MarkedRootPadding G W) (hm:0<m) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    MarkedRootPair tail head ktail khead H₀ HK π b m (A⊕(G.Exceptional×Fin (m+1))) (S⊕(G.Exceptional×Fin (m+1))):=
  G.pad hm hp Subtype.val P.p P.hub P.C P.φ P.ψ G.exceptional_roots G.exceptional_roots_separated
    P.oldRows P.oldHubs P.mapCycles P.mapHubs P.hubs P.coordinates
    (fun i k=>(P.avoid i k).2) P.disjointPaths P.separatedPaths P.packing

theorem marked_root_padding_construction (l:ℕ) (hl:2≤l)
    (G:MarkedRootPair tail head ktail khead H₀ HK π b (l+4) A S) (W:Finset V) (c ch:ℝ)
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hbudget:W.card+(2*(Fintype.card G.Exceptional:ℝ)*(l+4)+(G.R∪G.R').card+l+5)*(2*b+1)<c)
    (hhbudget:G.B.card+2*Fintype.card G.Exceptional<ch):Nonempty (MarkedRootPadding G W):=by
  obtain ⟨p,h,C,φ,ψ,hφ,hψ,hhm,hcm,hh,hC,hav,hdis,hsep,hpack⟩:=
    marked_padding_pair_construction tail head ktail khead H₀ HK π b l (by omega)
      (fun i:G.Exceptional=>i.val) G.φ G.ψ W (G.R∪G.R') G.B
      (fun i=>⟨Finset.mem_union_left _ (G.exceptional_roots i).1,Finset.mem_union_right _ (G.exceptional_roots i).2⟩)
      c ch hp
      (by intro j x;simpa [markedArcPresent,markedSpokesTo] using Q.outgoing j false x ∅ (by simp))
      (by intro i;constructor
          · simpa [markedArcPresent,markedSpokesTo] using Q.incoming true false i.val ∅ (by simp)
          · simpa [markedArcPresent,markedSpokesTo] using Q.incoming true false (G.φ i.val) ∅ (by simp))
      (by intro x y hxy;simpa [markedArcPresent,markedSpokesTo] using Q.twoStep false x y ∅ hxy (by simp))
      hbudget (fun A C hd hc hs=>Q.hubs A C hd (by omega) hs) hhbudget
  exact ⟨⟨p,h,C,φ,ψ,hφ,hψ,hhm,hcm,hh,hC,hav,hdis,hsep,hpack⟩⟩

theorem MarkedRootPadding.no_exceptional {G:MarkedRootPair tail head ktail khead H₀ HK π b m A S} {W:Finset V}
    (P:MarkedRootPadding G W) (hm:0<m) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    ∀ v,¬(Fintype.card {e // (P.pair hm hp).dst e=v}=1∧
      (Finset.univ.filter (fun e:{e // (P.pair hm hp).dst e=v}=>(P.pair hm hp).jr e.val=true)).card=1):=by
  apply padding_all_exceptional_rows G.dst G.jr m (fun i=>(P.C (false,i)).1.val)
  intro i
  rw [P.coordinates]
  rfl

theorem MarkedRootPadding.row_card {G:MarkedRootPair tail head ktail khead H₀ HK π b m A S} {W:Finset V}
    (P:MarkedRootPadding G W) (hm:0<m) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    ((P.pair hm hp).R∪(P.pair hm hp).R').card≤(G.R∪G.R').card+2*Fintype.card G.Exceptional*m:=
  (paired_padding_root_sets P.p G.R G.R' G.disjointRows (fun i k=>(P.avoid i k).2.1) P.disjointPaths).2

theorem MarkedRootPadding.hub_card {G:MarkedRootPair tail head ktail khead H₀ HK π b m A S} {W:Finset V}
    (P:MarkedRootPadding G W) (hm:0<m) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    (P.pair hm hp).B.card≤G.B.card+2*Fintype.card G.Exceptional:=by
  change (G.B∪Finset.univ.image P.hub).card≤_
  calc
    _≤G.B.card+(Finset.univ.image P.hub).card:=Finset.card_union_le _ _
    _=G.B.card+2*Fintype.card G.Exceptional:=by
      rw [Finset.card_image_of_injective _ P.hub.injective,Finset.card_univ,Fintype.card_prod,Fintype.card_bool]

end Oberwolfach

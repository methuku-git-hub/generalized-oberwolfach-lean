module

public import Oberwolfach.MarkedExpansionHostGeometry
public import Oberwolfach.IndexedMarkedHostRealization

@[expose] public section

/-! Construction of an actual expansion in the host, with injective row
and hub maps. The original indexed graph need not be simple or present. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_expansion_realization
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (G:IndexedMarkedGraph V₀ U₀ A S) (f:V₀→V) (g:U₀→U)
    (hf:Function.Injective f) (hg:Function.Injective g)
    (W Z:Finset V) (B:Finset U) (hfZ:∀ v,f v∈Z) (hgB:∀ u,g u∈B)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hbudget:(W.card:ℝ)+(Z.card+Fintype.card (A⊕S)*(l+5)+l+16)*(2*b+1)<c)
    (hB:(B.card:ℝ)+Fintype.card (A⊕S)<ch):
    ∃ R:IndexedMarkedHostRealization (indexedMarkedExpansion G (l+4) (by omega))
        tail head ktail khead H₀ HK π b,
      Function.Injective R.rows∧Function.Injective R.hubs∧
      (∀ v,R.rows (.inl v)=f v)∧(∀ u,R.hubs (.inl u)=g u)∧
      (∀ i,R.hubs (.inr i)∉B)∧
      (∀ i k,R.rows (.inr (i,k))∉W∧R.rows (.inr (i,k))∉Z∧
        ∀ z∈Z,¬PermutationClose π b (R.rows (.inr (i,k))) z)∧
      ∀ i j k k',((i,k):(A⊕S)×Fin (l+5))≠(j,k')→
        ¬PermutationClose π b (R.rows (.inr (i,k))) (R.rows (.inr (j,k'))):=by
  obtain ⟨C,hC,hCB,hCi,hav,hdis,hsep⟩:=marked_expansion_wheel_families Q hl
    (f∘G.src) (f∘G.dst) (f∘G.row) (g∘G.hub) G.jr G.js W Z B
    (fun a=>⟨hfZ _,hfZ _⟩) (fun s=>hfZ _) hbudget hB
  have hF:=marked_expansion_host_rows_injective f C hf Z hfZ (fun i k=>(hav i k).2.1) hsep
  have hH:=marked_expansion_host_hubs_injective g C hg B hgB hCB hCi
  have hpres:=marked_expansion_host_present G f g C hC
  have hinj:=marked_expansion_host_occurrences_injective G f g C hF hH hp hC
  let R:IndexedMarkedHostRealization (indexedMarkedExpansion G (l+4) (by omega))
      tail head ktail khead H₀ HK π b:=
    ⟨markedExpansionHostRows f C,markedExpansionHostHubs g C,hpres.1,hpres.2,
      marked_expansion_host_arcs_separated G f C Z hfZ (fun i k=>(hav i k).2.2),hinj.1,hinj.2⟩
  exact ⟨R,hF,hH,fun _=>rfl,fun _=>rfl,hCB,hav,hsep⟩

end Oberwolfach

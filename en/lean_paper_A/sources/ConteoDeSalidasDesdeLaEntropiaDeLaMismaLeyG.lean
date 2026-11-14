import MasaAgregadaEnElSoporteDeLasHistorias
import NumeroDeHistoriasIncluidoElFalloDeG
import ElOrdenFinalDeterminaLaHistoriaBuenaDeG
import EntropiaRestringidaDeLasSalidasBuenas
namespace ArticuloA.Historias
open Repair Trayectoria Trayectoria.ProfileKernel Trayectoria.Adjunto RealFinita Real
open scoped NNReal BigOperators
noncomputable section
open Classical

/-- Counting bound for the real histories of G, with unordered output and the failure kept in the law. -/
theorem conteo_desde_la_entropia_de_la_misma_ley_G {n q : ℕ} (np : 0<n) (ρ : Cell n→ℝ≥0)
    (U : Cell n→Cell n→Prop) (d : ℝ≥0) (O : Finset (Finset (Cell n))) (op : O.Nonempty)
    (size : ∀ S∈O,S.card=q) :
    let xs:=rutas (pasoDeG ρ q) 0 q (some [])
    let S:=(xs.map Prod.snd).toFinset
    let g:=S.filter (fun l=>prefijoRegular (condicionDeSeguimientoG ρ q U d) 0 (some []) l ∧
                         ∃ v,ultimoEstado (some []) l=some v ∧ v.toFinset∈O)
    let b:=S \ g
    let p:=masaAgregada xs
    (∑ l∈S,-(p l*log (p l)))-log q.factorial-log 2-
      (avg masas xs (mark masas (·∈b))).val*(2*q*log n)≤log (O.card:ℝ) := by
  intro xs S g b p
  have subset : g⊆S:=Finset.filter_subset _ _
  have part : g∪b=S:=Finset.union_sdiff_of_subset subset
  have dis : Disjoint g b:=Finset.disjoint_sdiff
  have existsAtom (l) (hl : l∈S) : ∃ w,(w,l)∈xs := by
    obtain ⟨a,hm,eq⟩:=List.mem_map.mp (List.mem_toFinset.mp hl)
    exact ⟨a.1,by simpa [←eq] using hm⟩
  have bc:=cota_del_numero_de_historias_malas np ρ b (fun l hl=>existsAtom l (Finset.mem_sdiff.mp hl).1)
  have gc:=multiplicidad_de_historias_regulares_de_G ρ U d g O size (by
    intro l hl
    obtain ⟨hs,ok,yes⟩:=Finset.mem_filter.mp hl
    obtain ⟨w,hw⟩:=existsAtom _ hs
    obtain ⟨path,len⟩:=rutas_siguen_su_ley _ _ _ _ _ hw
    exact ⟨path,len,ok,yes⟩)
  have total : (∑ l∈g,p l)+(∑ l∈b,p l)=1:=by
    rw [←Finset.sum_union dis,part]
    have sub (a) (ha : a∈xs) : a.2∈S:=List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩)
    rw [show (∑ l∈S,p l)=(total masas xs).val from masa_agregada_total xs S sub]
    change (total masas (rutas (pasoDeG ρ q) 0 q (some []))).val=1
    rw [masa_de_rutas _ (G_es_ley ρ q)]
    rfl
  have bound:=entropia_restringida_de_historias b g p np (Finset.card_pos.mpr op)
    (fun l=>NNReal.coe_nonneg _) total gc bc
  rw [←Finset.sum_union dis,part,show (∑ l∈b,p l)=(avg masas xs (mark masas (·∈b))).val from sumar_masas_en_un_evento xs b] at bound
  exact bound
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.conteo_desde_la_entropia_de_la_misma_ley_G

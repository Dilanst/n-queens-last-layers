import AcoplamientoDelCorteDirecto
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Trayectoria.Adjunto
theorem evento_al_corte_en_la_ley_original {n h T : ℕ} {p : FactoresContinuos} {κ m ζ C u : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m) (zp : 0<ζ)
    (fl : ζ≤fraccionAntes n T) (bal : BalanceMalla n h p C) (he : u/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ)
    (B : State n→Prop) :
    let w:=coloresDelPerfil n h p
    let ley:=rutas (kernel masas w (·⁻¹)) 0 T (initial n h)
    (avg masas ley (mark masas (fun l => B (estadoEn (initial n h) l T)))).val ≤
      (avg masas ley (mark masas (salidaOriginal p h T u))).val +
      (avg masas (rutas (pasoDeRaiz h T p u) 0 T (0,initial n h)) (mark masas (fun l =>
        let y:=l.foldl (fun _ s => s) (0,initial n h)
        y.1=T ∧ B y.2))).val := by
  intro w ley
  let x:ℕ×State n:=(0,initial n h)
  let R:=rutas (pasoParado w (fun _ _ => false)) 0 T x
  let S:=rutas (pasoDeRaiz h T p u) 0 T x
  let ok:=prefijoAbierto (abiertosDeRaiz h T p u) 0 x
  let exit:=fun l : List (ℕ×State n) => salidaOriginal p h T u (l.map Prod.snd)
  let bad:=fun l : List (State n) => B (estadoEn (initial n h) l T)
  let event:=fun l : List (ℕ×State n) =>
    let y:=l.foldl (fun _ s => s) x
    y.1=T ∧ B y.2
  let hit:=fun l : List (ℕ×State n) => bad (l.map Prod.snd)
  have inc:=misma_masa_en_el_soporte R hit (fun l => exit l ∨ (ok l ∧ event l)) (by
    intro i mem nz yes
    by_cases ex : exit i.2
    · exact Or.inl ex
    · obtain ⟨opens,ends⟩:=sigue_la_raiz_hasta_T hn hh sp kp m1 zp bal he ho fl i mem nz ex
      obtain ⟨len,_⟩:=pasos_con_peso mem nz
      exact Or.inr ⟨opens,ends,by
        have last:=estado_al_olvidar_el_reloj 0 (initial n h) i.2 T
        unfold estadoEn at last; rw [List.take_of_length_le len.le] at last
        change B (i.2.foldl (fun _ s => s) x).2
        rw [last]; exact yes⟩)
  let selected:=fun l : List (ℕ×State n) => if ok l then mark masas event l else 0
  have split : avg masas R (mark masas (fun l => exit l ∨ (ok l ∧ event l))) ≤
      avg masas R (mark masas exit)+avg masas R selected := by
    change _≤masas.add _ _; rw [←avg_plus]; apply avg_mono masas
    intro i _; by_cases ex : exit i.2 <;> by_cases op : ok i.2 <;> by_cases ev : event i.2 <;>
      simp [mark,selected,ex,op,ev,masas]
  have switch : avg masas R selected=avg masas S selected := coincide_la_ley_de_la_raiz p u (mark masas event)
  have leSel : avg masas S selected≤avg masas S (mark masas event) := by
    apply avg_mono masas; intro i _; dsimp only [selected]
    split <;> first | exact le_rfl | exact zero_le _
  have law1:=ley_al_olvidar_el_reloj (kernel masas w (·⁻¹)) 0 T (initial n h) (mark masas bad)
  have law2:=ley_al_olvidar_el_reloj (kernel masas w (·⁻¹)) 0 T (initial n h) (mark masas (salidaOriginal p h T u))
  change (avg masas ley (mark masas bad)).val≤(avg masas ley (mark masas (salidaOriginal p h T u))).val+_
  rw [←law1,←law2]
  change (avg masas R (mark masas hit)).val≤(avg masas R (mark masas exit)).val+_
  apply (NNReal.coe_le_coe.mpr (inc.trans split)).trans
  rw [NNReal.coe_add,switch]; exact add_le_add_left (NNReal.coe_le_coe.mpr leSel) _

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.evento_al_corte_en_la_ley_original

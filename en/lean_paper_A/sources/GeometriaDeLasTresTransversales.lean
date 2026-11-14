import EstimacionDeTraslacionesDelPerfil
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Set
def desplazamientoOblicuo (i : Fin 4) (s : ℝ) := if i=3 then s-1 else s

def longitudDeCuerda (i : Fin 4) (s : ℝ) :=
  if i.val<2 then 1 else 1-|desplazamientoOblicuo i s|

def puntoDeCuerda : Fin 4 → ℝ → ℝ → ℝ×ℝ
  | 0,s,t => (s,t)
  | 1,s,t => (t,s)
  | 2,s,t => (max s 0+t,max (-s) 0+t)
  | 3,s,t => (max (s-1) 0+t,1-(max (-(s-1)) 0+t))

def familiaTransversal : Fin 4 → Fin 3 → Fin 4
  | 0 => ![1,2,3]
  | 1 => ![0,2,3]
  | 2 => ![0,1,3]
  | 3 => ![0,1,2]

def pendienteTransversal : Fin 4 → Fin 3 → ℝ
  | 0 => ![1,-1,1]
  | 1 => ![1,1,1]
  | 2 => ![1,1,2]
  | 3 => ![1,-1,2]

theorem coordenada_transversal_afin (i : Fin 4) (j : Fin 3) (s t : ℝ) :
    coord (familiaTransversal i j) (puntoDeCuerda i s t) =
    pendienteTransversal i j*t+coord (familiaTransversal i j) (puntoDeCuerda i s 0) := by
  fin_cases i <;> fin_cases j <;> simp [familiaTransversal,pendienteTransversal,puntoDeCuerda,coord] <;> try ring
  rcases le_total 0 s with h|h
  · simp [max_eq_left h,max_eq_right (neg_nonpos.mpr h),abs_of_nonneg h]; ring
  · simp [max_eq_right h,max_eq_left (neg_nonneg.mpr h),abs_of_nonpos h]

theorem pendiente_absoluta_al_menos_uno (i : Fin 4) (j : Fin 3) :
    1≤|pendienteTransversal i j| := by
  fin_cases i <;> fin_cases j <;> norm_num [pendienteTransversal]

private theorem diferenciaDePartes (s : ℝ) : max s 0-max (-s) 0=s := by
  rcases le_total 0 s with h|h
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]; ring
  · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]; ring

theorem coordenada_de_la_familia_fijada (i : Fin 4) (s t : ℝ) :
    coord i (puntoDeCuerda i s t)=s := by
  fin_cases i
  · rfl
  · rfl
  · change max s 0+t-(max (-s) 0+t)=s
    linarith [diferenciaDePartes s]
  · change max (s-1) 0+t+(1-(max (-(s-1)) 0+t))=s
    linarith [diferenciaDePartes (s-1)]

private theorem tramo {s t : ℝ} (ht : t∈Icc 0 (1-|s|)) :
    max s 0+t∈Icc 0 1 ∧ max (-s) 0+t∈Icc 0 1 := by
  obtain ⟨lo,hi⟩:=ht
  rcases le_total 0 s with h|h
  · rw [abs_of_nonneg h] at hi
    rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  · rw [abs_of_nonpos h] at hi
    rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem longitud_en_unidad (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) :
    longitudDeCuerda i s∈Icc 0 1 := by
  fin_cases i
  · exact ⟨zero_le_one,le_rfl⟩
  · exact ⟨zero_le_one,le_rfl⟩
  · change -1≤s ∧ s≤1 at hs
    change 0≤1-|s| ∧ 1-|s|≤1
    exact ⟨sub_nonneg.mpr (abs_le.mpr hs),sub_le_self _ (abs_nonneg _)⟩
  · change 0≤s ∧ s≤2 at hs
    change 0≤1-|s-1| ∧ 1-|s-1|≤1
    exact ⟨sub_nonneg.mpr (abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩),
      sub_le_self _ (abs_nonneg _)⟩
    
theorem punto_en_el_cuadrado (i : Fin 4) {s t : ℝ} (hs : s∈rangoF i)
    (ht : t∈Icc 0 (longitudDeCuerda i s)) :
    (puntoDeCuerda i s t).1∈unidadCerrada ∧ (puntoDeCuerda i s t).2∈unidadCerrada := by
  fin_cases i
  · exact ⟨hs,ht⟩
  · exact ⟨ht,hs⟩
  · exact tramo ht
  · obtain ⟨r,c⟩:=tramo (s:=s-1) ht
    change _ ∧ 0≤1-(max (-(s-1)) 0+t) ∧ 1-(max (-(s-1)) 0+t)≤1
    exact ⟨r,⟨by linarith [c.2],by linarith [c.1]⟩⟩

theorem etiqueta_en_el_intervalo_fisico (i : Fin 4) (j : Fin 3) {s t : ℝ}
    (hs : s∈rangoF i) (ht : t∈Icc 0 (longitudDeCuerda i s)) :
    pendienteTransversal i j*t+coord (familiaTransversal i j) (puntoDeCuerda i s 0)
      ∈ rangoF (familiaTransversal i j) := by
  rw [←coordenada_transversal_afin]
  exact coordenadas_en_dominio (punto_en_el_cuadrado i hs ht) _
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.coordenada_transversal_afin
#print axioms ArticuloA.Historias.pendiente_absoluta_al_menos_uno
#print axioms ArticuloA.Historias.coordenada_de_la_familia_fijada
#print axioms ArticuloA.Historias.longitud_en_unidad
#print axioms ArticuloA.Historias.punto_en_el_cuadrado
#print axioms ArticuloA.Historias.etiqueta_en_el_intervalo_fisico

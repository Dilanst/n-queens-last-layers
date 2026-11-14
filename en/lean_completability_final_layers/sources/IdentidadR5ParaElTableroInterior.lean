import CamposContinuosParaLaComparacionR5
import AdjuncionDeEulerBajoContinuidad
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil Real
open scoped Topology

def trabajoDeR5 (P : TableroMedido) (δ : ℝ) :=
  ∫ z,((P.ν z:ℝ)-δ*densidadTestigo z)*log (P.ν z) ∂cuadrado

def terminoDeR5 (P : TableroMedido) (p : FactoresContinuos) (x : ℝ≥0) (i : Fin 4) :=
  ∫ s,((P.m i s:ℝ)-(1-(x:ℝ))*marginalDelTestigo i s)*campoPerfil p x i s ∂marginalRef i

theorem comparacion_R5_desde_euler_interior {P p x b} (e : EulerFisica P p x b) (xp : 0<x)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i))
    (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s) :
    trabajoDeR5 P (1-(x:ℝ)) = ∑ i : Fin 4,terminoDeR5 P p x i := by
  let δ:=1-(x:ℝ)
  let w:=campoPerfil p x
  let U:=pesoDePruebaB33 p b
  let d:=fun z : ℝ×ℝ=>(P.ν z:ℝ)-δ*densidadTestigo z
  obtain ⟨wc,logeq⟩:=log_de_euler_en_un_parametro_interior e xp cp pos
  have coordc (i : Fin 4) : Continuous (coord i) := by
    fin_cases i; exacts [continuous_fst,continuous_snd,continuous_fst.sub continuous_snd,continuous_fst.add continuous_snd]
  have cc:=campo_continuo_por_recorte cp
  have uc : Continuous U := (((continuous_const.mul ((cc 0).comp continuous_fst)).mul ((cc 1).comp continuous_snd)).mul
    ((cc 2).comp (continuous_fst.sub continuous_snd))).mul ((cc 3).comp (continuous_fst.add continuous_snd))
  have uv : (fun z=>(P.ν z:ℝ))=ᵐ[cuadrado] U := densidad_en_factores_recortados e
  have bi:=integral_cuadrada_de_una_continua densidad_testigo_continua
  have di : Integrable d cuadrado := P.masaFinita.sub (bi.const_mul δ)
  have wi (i) : Integrable (fun z=>(P.ν z:ℝ)*w i (coord i z)) cuadrado :=
    (integral_cuadrada_de_una_continua (uc.mul ((wc i).comp (coordc i)))).congr (uv.mono (fun z h=>congrArg (·*w i (coord i z)) h.symm))
  have ti i := integral_cuadrada_de_una_continua (densidad_testigo_continua.mul ((wc i).comp (coordc i)))
  have mi i : Integrable (fun s=>(P.m i s:ℝ)*w i s) (marginalRef i) :=
    (integral_de_etiqueta_de_una_continua i ((continuous_const.sub (continuous_const.mul (cc i))).mul (wc i))).congr
      ((masa_de_linea_normalizada e i).mono (fun s h=>congrArg (·*w i s) h.symm))
  have ni i:= integral_de_etiqueta_de_una_continua i ((continua_la_marginal_del_testigo i).mul (wc i))
  have diff {α : Type} [MeasurableSpace α] {μ : Measure α} (a v t : α→ℝ)
      (ai : Integrable (fun z=>a z*t z) μ) (vi : Integrable (fun z=>v z*t z) μ) :
      Integrable (fun z=>(a z-δ*v z)*t z) μ ∧
      (∫ z,(a z-δ*v z)*t z ∂μ)=(∫ z,a z*t z ∂μ)-δ*(∫ z,v z*t z ∂μ) := by
    simp only [sub_mul,mul_assoc]
    exact ⟨ai.sub (vi.const_mul δ),by rw [integral_sub ai (vi.const_mul δ),integral_const_mul]⟩
  have tests (i : Fin 4):=diff (α:=ℝ×ℝ) (μ:=cuadrado) (fun z=>(P.ν z:ℝ)) densidadTestigo (fun z=>w i (coord i z)) (wi i) (ti i)
  have mass : (∫ z,d z ∂cuadrado)=0 := by
    change (∫ z,(P.ν z:ℝ)-δ*densidadTestigo z ∂cuadrado)=0
    rw [integral_sub P.masaFinita (bi.const_mul δ),integral_const_mul,masa_unitaria_del_testigo]
    change P.rho-δ*1=0
    rw [e.masa]; dsimp [δ]; ring
  calc
    _ = ∫ z,d z*(log (b/(x:ℝ)^2)+∑ i,w i (coord i z)) ∂cuadrado :=
      integral_congr_ae (logeq.mono (fun z h=>congrArg (d z*·) h))
    _ = ∑ i,∫ z,d z*w i (coord i z) ∂cuadrado := by
      simp_rw [mul_add,Finset.mul_sum]
      rw [integral_add (di.mul_const _) (integrable_finset_sum _ (fun i _=>(tests i).1)),integral_mul_const,
        integral_finset_sum _ (fun i _=>(tests i).1),mass,zero_mul,zero_add]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      change (∫ z,((P.ν z:ℝ)-δ*densidadTestigo z)*w i (coord i z) ∂cuadrado)=_
      rw [(tests i).2,adjuncion P.ley i (w i) (wc i).measurable,pruebas_continuas_con_el_testigo i (w i) (wc i)]
      exact (diff (α:=ℝ) (μ:=marginalRef i) (fun s=>(P.m i s:ℝ)) (marginalDelTestigo i) (w i) (mi i) (ni i)).2.symm
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.comparacion_R5_desde_euler_interior

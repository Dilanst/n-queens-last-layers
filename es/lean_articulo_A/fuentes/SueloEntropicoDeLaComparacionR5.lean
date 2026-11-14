import IdentidadR5ParaElTableroInterior
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil Real
open scoped Topology
noncomputable local instance : IsProbabilityMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩
noncomputable local instance : IsProbabilityMeasure cuadrado := by unfold cuadrado; infer_instance
theorem suelo_puntual_para_la_entropia {t y M : ℝ} (tp : 0<t) (yl : 0≤y) (yu : y≤M) :
    -1/exp 1-M*t≤(t-y)*log t := by
  have ep:=exp_pos 1
  have base:=mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos (mul_pos ep tp)) tp.le
  rw [log_mul ep.ne' tp.ne',log_exp] at base
  have ident : t*(1-(exp 1*t)⁻¹)=t-1/exp 1 := by field_simp [tp.ne',ep.ne']; ring
  rw [ident] at base
  have cross : y*log t≤M*t := (mul_le_mul_of_nonneg_left (log_le_self tp.le) yl).trans (mul_le_mul_of_nonneg_right yu tp.le)
  simp only [neg_div] at *
  linarith only [base,cross]

theorem suelo_entropico_R5 {P p x b} (e : EulerFisica P p x b) (x1 : (x:ℝ)≤1)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i))
    (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s) :
    -(6/5:ℝ)-1/exp 1≤trabajoDeR5 P (1-(x:ℝ)) := by
  let δ:=1-(x:ℝ)
  let U:=pesoDePruebaB33 p b
  have cc:=campo_continuo_por_recorte cp
  have uc : Continuous U := (((continuous_const.mul ((cc 0).comp continuous_fst)).mul ((cc 1).comp continuous_snd)).mul
    ((cc 2).comp (continuous_fst.sub continuous_snd))).mul ((cc 3).comp (continuous_fst.add continuous_snd))
  have pp i s : 0<campoR15 p i s := pos i _ (recorte_dentro i s)
  have up z : 0<U z := by dsimp [U,pesoDePruebaB33]; exact mul_pos (mul_pos (mul_pos (mul_pos e.coef (pp 0 _)) (pp 1 _)) (pp 2 _)) (pp 3 _)
  have uv : (fun z=>(P.ν z:ℝ))=ᵐ[cuadrado] U := densidad_en_factores_recortados e
  have work : Integrable (fun z=>((P.ν z:ℝ)-δ*densidadTestigo z)*log (P.ν z)) cuadrado :=
    (integral_cuadrada_de_una_continua ((uc.sub (continuous_const.mul densidad_testigo_continua)).mul (uc.log (fun z=>(up z).ne')))).congr
      (uv.mono (fun z hz=>congrArg (fun v : ℝ=>(v-δ*densidadTestigo z)*log v) hz.symm))
  have ylo : 0≤δ := sub_nonneg.mpr x1
  have yhi : δ≤1 := by dsimp [δ]; linarith [x.coe_nonneg]
  have h:=integral_mono_ae ((integrable_const (-1/exp 1 : ℝ)).sub (P.masaFinita.const_mul (6/5:ℝ))) work
    (uv.mono (fun z hz=>by
      change -1/exp 1-6/5*(P.ν z:ℝ)≤_
      have pq : 0<(P.ν z:ℝ) := by change (P.ν z:ℝ)=U z at hz; rw [hz]; exact up z
      apply suelo_puntual_para_la_entropia pq
      · exact mul_nonneg ylo ((by norm_num : (0:ℝ)≤4/5).trans (cotas_del_testigo_DEF z.1 z.2).1)
      · exact (mul_le_mul_of_nonneg_right yhi ((by norm_num : (0:ℝ)≤4/5).trans (cotas_del_testigo_DEF z.1 z.2).1)).trans
          (by simpa only [one_mul] using (cotas_del_testigo_DEF z.1 z.2).2)))
  change (∫ z,-1/exp 1-6/5*(P.ν z:ℝ) ∂cuadrado)≤trabajoDeR5 P δ at h
  rw [integral_sub (integrable_const _) (P.masaFinita.const_mul _),integral_const_mul,integral_const] at h
  change _-6/5*P.rho≤_ at h
  simp only [measureReal_univ_eq_one,one_smul,e.masa] at h
  change -(6/5:ℝ)-1/exp 1 ≤ trabajoDeR5 P δ
  simp only [neg_div] at h
  linarith only [h,x.coe_nonneg]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.suelo_puntual_para_la_entropia
#print axioms ArticuloA.Historias.suelo_entropico_R5

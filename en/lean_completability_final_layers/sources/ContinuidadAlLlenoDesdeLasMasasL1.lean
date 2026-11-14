import EulerEnFibrasSinConstanteLipschitz
import CavidadesControladasPorLasTresMasas
import IdentificacionUniformeEnElTableroLleno
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Set MeasureTheory
open scoped Interval
theorem techo_de_cavidad {p : Fin 4→ℝ→ℝ} {K : ℝ} (hK : 0≤K)
    (bound : ∀ g,∀ y∈rangoF g,|p g y|≤K) (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) :
    |cavidadFisica p i s|≤K^3 := by
  have hd:=longitud_en_unidad i hs
  have bd : ∀ t∈Ι (0:ℝ) (longitudDeCuerda i s),‖productoEnCuerda p i s t‖≤K^3 := by
    intro t ht
    rw [uIoc_of_le hd.1] at ht
    have each (j : Fin 3) : |restriccionACuerda p i s t j|≤K :=
      bound _ _ (etiqueta_en_el_intervalo_fisico i j hs ⟨ht.1.le,ht.2⟩)
    simp only [productoEnCuerda,Real.norm_eq_abs,abs_mul,pow_succ,pow_zero,one_mul]
    gcongr <;> exact each _
  have cp:=intervalIntegral.norm_integral_le_of_norm_le_const_ae (Filter.Eventually.of_forall bd)
  simp only [sub_zero,abs_of_nonneg hd.1,Real.norm_eq_abs] at cp
  exact cp.trans (by simpa using mul_le_mul_of_nonneg_left hd.2 (pow_nonneg hK 3))

theorem diferencia_entre_dos_ecuaciones_de_euler {y z d d' b b' J J' K B u : ℝ} (hk : 0≤K)
    (hy : |y|≤K) (hz : |z|≤K) (hb : |b|≤B) (j' : |J'|≤K^3)
    (h : y*(d+b*J)=1) (h' : z*(d'+b'*J')=1)
    (hd : |d'-d|≤u) (bb : |b'-b|≤u) (jj : |J'-J|≤K^2*u) :
    |y-z|≤(K^2*(1+K^3+B*K^2))*u := by
  have idn : y-z=y*z*((d'-d)+(b'-b)*J'+b*(J'-J)) := by
    linear_combination z*h-y*h'
  rw [idn,abs_mul (y*z)]
  have inner : |(d'-d)+(b'-b)*J'+b*(J'-J)|≤u+u*K^3+B*(K^2*u) := by
    apply (abs_add_le ..).trans
    apply add_le_add
    · apply (abs_add_le ..).trans
      rw [abs_mul]
      exact add_le_add hd (mul_le_mul bb j' (abs_nonneg _) (bb.trans' (abs_nonneg _)))
    · rw [abs_mul]
      exact mul_le_mul hb jj (abs_nonneg _) ((abs_nonneg _).trans hb)
  have yz : |y*z|≤K^2 := by rw [abs_mul,pow_two]; exact mul_le_mul hy hz (abs_nonneg _) hk
  exact (mul_le_mul yz inner (abs_nonneg _) (sq_nonneg _)).trans_eq (by ring)

theorem continuidad_en_el_lleno_desde_L1 (p : ℝ→FactoresContinuos) (b : ℝ→ℝ) {K B : ℝ}
    (hk : 0≤K) (hB : 0≤B)
    (cp : ∀ x∈Icc 0 (1/2:ℝ),∀ g,ContinuousOn (camposFisicos (p x) g) (rangoF g))
    (cap : ∀ x∈Icc 0 (1/2:ℝ),∀ g,∀ s∈rangoF g,|camposFisicos (p x) g s|≤K)
    (bcap : ∀ x∈Icc 0 (1/2:ℝ),|b x|≤B)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),∀ i,∀ᵐ t ∂marginalRef i,
      b x*integralFisica (p x) i t=1-holguraLinea (p x) x.toNNReal i t)
    (mass : ∀ η : ℝ,0<η → ∃ d : ℝ,0<d ∧ ∀ x∈Icc 0 (1/2:ℝ),x<d →
      |b 0-b x|≤η ∧ (∑ g,masaExterior (fun j y=>|camposFisicos (p x) j y-camposFisicos (p 0) j y|) g)≤η) :
    ContinuidadEnElLleno p b := by
  intro ε hep
  let H:=K^2*(1+K^3+B*K^2)
  have nn : 0≤H := by dsimp [H]; positivity
  let u:=ε/(H+1)
  have up : 0<u := div_pos hep (by linarith)
  have hmul : u*(H+1)=ε := div_mul_cancel₀ _ (by linarith)
  obtain ⟨d,dp,near⟩:=mass u up
  refine ⟨min d u,lt_min dp up,?_⟩
  intro x hx xlt
  have b0 : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  obtain ⟨db,dm⟩:=near x hx (lt_of_lt_of_le xlt (min_le_left ..))
  have xu:=lt_of_lt_of_le xlt (min_le_right d u)
  constructor
  · rw [abs_sub_comm]; exact db.trans (by nlinarith [mul_nonneg up.le nn])
  · intro i s hs
    have eqx:=ecuacion_puntual_sin_lipschitz x.toNNReal (cp x hx) i (eq x hx i) s hs
    have eq0:=ecuacion_puntual_sin_lipschitz (0:ℝ).toNNReal (cp 0 b0) i (eq 0 b0 i) s hs
    have dif : |(if i.val<2 then ((0:ℝ).toNNReal:ℝ) else 1)-(if i.val<2 then (x.toNNReal:ℝ) else 1)|≤u := by
      split_ifs <;> simp [Real.coe_toNNReal x hx.1,abs_of_nonneg hx.1] <;> linarith
    have J:=control_de_la_cavidad_por_L1 (cp x hx) (cp 0 b0) (cap x hx) (cap 0 b0) i hs
    have sub:=suma_de_tres_acotada_por_las_cuatro i _ (masa_exterior_no_negativa
      (fun j y=>abs_nonneg (camposFisicos (p x) j y-camposFisicos (p 0) j y)))
    have jdiff:=J.trans (mul_le_mul_of_nonneg_left (sub.trans dm) (sq_nonneg K))
    have fin:=diferencia_entre_dos_ecuaciones_de_euler hk (cap x hx i s hs) (cap 0 b0 i s hs) (bcap x hx)
      (techo_de_cavidad hk (cap 0 b0) i hs) eqx eq0 dif db (by rwa [abs_sub_comm])
    exact fin.trans (show H*u≤ε by linarith only [hmul,up])
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.techo_de_cavidad
#print axioms ArticuloA.Historias.diferencia_entre_dos_ecuaciones_de_euler
#print axioms ArticuloA.Historias.continuidad_en_el_lleno_desde_L1

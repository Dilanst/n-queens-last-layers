import DerivaDelObservableInversoEnE2
import ToleranciaLinealDelAbsorbedor
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Trayectoria.Adjunto
theorem factorizar_cota_de_deriva (κ m ζ C E : ℝ≥0) (W : ℝ) (wp : 0≤W) :
    cotaDerivaInversa κ m ζ C E W ≤
      (cotaDerivaInversa κ m ζ C 0 W).toNNReal*((E:ℝ)+1) := by
  let K:=constanteRelojInverso κ m ζ W
  let D:=constanteUna (piso κ ζ) (techo m κ ζ) C
  let H:=m^4/piso κ ζ+4*(m^4/(piso κ ζ)^4)
  have kp : 0≤K := by dsimp [K,constanteRelojInverso]; positivity
  have hp : 0≤(H:ℝ) := H.property
  have dp : 0≤(D:ℝ) := D.property
  have zero : cotaDerivaInversa κ m ζ C 0 W=176*K+K*(192*(D:ℝ)+720*(H:ℝ)) := by
    simp only [cotaDerivaInversa,zero_add,mul_one,K,D,H]
  rw [zero,Real.coe_toNNReal _ (by positivity)]
  change 176*K+K*(192*(↑(D*(E+1)):ℝ)+720*(H:ℝ))≤_
  push_cast
  apply sub_nonneg.mp
  have positive : 0≤K*(176+720*(H:ℝ))*(E:ℝ) := by positivity
  calc 0 ≤ K*(176+720*(H:ℝ))*(E:ℝ) := positive
       _ = _ := by ring_nf

theorem parametros_del_conteo_inverso (κ m ζ C ε : ℝ≥0) (W : ℝ) (wp : 0≤W)
    (kp : 0<κ) (zp : 0<ζ) (ep : 0<ε) :
    ∃ e : ℝ≥0,0<e ∧ e≤piso κ ζ ∧ ∃ s : ℝ,0<s ∧
      s*(2*(176*constanteRelojInverso κ m ζ W))≤1 ∧
      32*(176*constanteRelojInverso κ m ζ W)^2*s≤ε ∧
      ∃ N : ℕ,∀ n≥N,cotaDerivaInversa κ m ζ C (e*n) W≤(ε:ℝ)*n/4 := by
  let D:=(cotaDerivaInversa κ m ζ C 0 W).toNNReal
  let B:=176*constanteRelojInverso κ m ζ W
  have bp : 0≤B := by dsimp [B,constanteRelojInverso]; positivity
  obtain ⟨e,pe,adm,N,budget⟩:=tolerancia_para_la_raiz D (piso κ ζ) (ε/2) (piso_positivo kp zp) (by positivity)
  let s:=min (1/(2*B+1)) ((ε:ℝ)/(32*B^2+1))
  have xp : 0<(ε:ℝ) := ep
  have d1 : 0<2*B+1 := by positivity
  have d2 : 0<32*B^2+1 := by positivity
  have sp : 0<s := lt_min (one_div_pos.mpr d1) (div_pos xp d2)
  have a:=(le_div_iff₀ d1).mp (min_le_left (1/(2*B+1)) ((ε:ℝ)/(32*B^2+1)))
  have b:=(le_div_iff₀ d2).mp (min_le_right (1/(2*B+1)) ((ε:ℝ)/(32*B^2+1)))
  change s*(2*B+1)≤1 at a
  change s*(32*B^2+1)≤_ at b
  refine ⟨e,pe,adm,s,sp,by change s*(2*B)≤1; linarith,by change 32*B^2*s≤_; linarith,max 1 N,?_⟩
  intro n hn
  have np : (n:ℝ≥0)≠0 := by exact_mod_cast (by omega : n≠0)
  have raw:=budget n (by omega) n (by omega)
  rw [mul_div_cancel₀ _ np] at raw
  have cast:=NNReal.coe_le_coe.mpr raw
  push_cast at cast
  exact (factorizar_cota_de_deriva κ m ζ C (e*n) W wp).trans (by
    change (D:ℝ)*((↑(e*n:ℝ≥0):ℝ)+1)≤_; push_cast; linarith)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.factorizar_cota_de_deriva
#print axioms ArticuloA.Historias.parametros_del_conteo_inverso

import PasoTemporaldelPerfilFisico
import IncrementoDelObservableConReloj
import RelojDelPrefijoRegular
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def horizonteInverso (n T t : ℕ) : ℝ≥0 := (↑(T-t):ℝ≥0)/(↑(2*n-1):ℝ≥0)

theorem reloj_hasta_un_horizonte {n T t : ℕ} (hn : 2≤n) (tT : t<T) (finT : T≤2*n-1) :
    let d:=(↑(2*n-1):ℝ)⁻¹
    0≤d ∧ d≤(horizonteInverso n T t:ℝ) ∧ horizonteInverso n T t≤1 ∧
    (horizonteInverso n T (t+1):ℝ)=(horizonteInverso n T t:ℝ)-d ∧
    (fraccionAntes n (t+1):ℝ)=(fraccionAntes n t:ℝ)-d ∧ d*(n:ℝ)≤1 := by
  intro d
  have nn : (0:ℝ)<(↑(2*n-1):ℝ) := by exact_mod_cast (by omega : 0<2*n-1)
  have nz : 0<(↑(2*n-1):ℝ≥0) := by exact_mod_cast (by omega : 0<2*n-1)
  have move := fraccion_disminuye (tT.trans_le finT)
  have zmove := congrArg (fun x : ℝ≥0 => (x:ℝ)) move
  simp only [NNReal.coe_add, NNReal.coe_inv, NNReal.coe_natCast] at zmove
  have ymove : horizonteInverso n T (t+1)+(↑(2*n-1):ℝ≥0)⁻¹=horizonteInverso n T t := by
    unfold horizonteInverso
    rw [←one_div,←add_div,←Nat.cast_one (R:=ℝ≥0),←Nat.cast_add,show T-(t+1)+1=T-t by omega]
  have m:=congrArg (fun x : ℝ≥0 => (x:ℝ)) ymove
  simp only [NNReal.coe_add, NNReal.coe_inv, NNReal.coe_natCast] at m
  have yp : 0≤(horizonteInverso n T (t+1):ℝ) := NNReal.coe_nonneg _
  have dpos : 0≤d := inv_nonneg.mpr nn.le
  refine ⟨dpos,?_,?_,?_,?_,?_⟩
  · dsimp [d]; linarith
  · exact (div_le_one nz).mpr (by exact_mod_cast (Nat.sub_le T t).trans finT)
  · dsimp [d]; linarith
  · dsimp [d]; linarith
  · rw [show d*(n:ℝ)=(n:ℝ)/(↑(2*n-1):ℝ) by simp [d,div_eq_mul_inv,mul_comm]]
    exact (div_le_one nn).mpr (by exact_mod_cast (show n≤2*n-1 by omega))

theorem salto_y_resto_en_el_reloj {n h T t} {p : FactoresContinuos} {κ m ζ : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (w : Cell n→ℝ) {W : ℝ} (wp : 0≤W)
    (cap : ∀ z,|w z|≤W) (zp : 0<ζ) (tT : t<T) (finT : T≤2*n-1) (floor : ζ≤fraccionAntes n T)
    (X : State n) (a : Choice n) (good : coherent X) (live : allowed X a) :
    let c:=fun j => terminoInverso h p w (horizonteInverso n T j) (fraccionAntes n j)
    let V:=velocidadDelPerfil h p w (horizonteInverso n T t) (fraccionAntes n t)
    let d:=(↑(2*n-1):ℝ)⁻¹
    let K:=constanteRelojInverso κ m ζ W
    let u:=marcaDelPar X
    let du:=fun j v => marcaDelPar (next X a) j v-u j v
    let Δ:=totalPonderado (next X a) (c (t+1))-totalPonderado X (c t)
    |Δ|≤176*K*n ∧ |Δ-∑ j : CuatroMarcas,∑ v∈paresCompatibles n,(c t j v*du j v+d*V j v*u j v)|≤176*K := by
  intro c V d K u du Δ
  obtain ⟨dp,dy,yt,sy,sz,small⟩:=reloj_hasta_un_horizonte hn tT finT
  have nr : 0<n := by omega
  have floor' : (ζ:ℝ)≤(fraccionAntes n t:ℝ)-d := by
    rw [←sz]; exact_mod_cast fraccion_antes_del_horizonte (Nat.succ_le.mpr tT) floor
  have pars (j : CuatroMarcas) (v : Mark n) := paso_del_coeficiente_fisico (h:=h) hn sp kp w W cap
    dp dy yt (show (0:ℝ)<ζ from zp) floor' sy sz j v
  have pos : 0≤K := by unfold K constanteRelojInverso; positivity
  have dif (j v) : |c (t+1) j v-c t j v|≤(K*d)*(escalaDelPatron n j:ℝ) :=
    (pars j v).change.trans_eq (by ring)
  have er (j v) : |c (t+1) j v-c t j v-d*V j v|≤(K*d^2)*(escalaDelPatron n j:ℝ) :=
    (pars j v).error.trans_eq (by ring)
  have bd:=salto_con_reloj nr X a good live (c t) (c (t+1)) pos (mul_nonneg pos dp)
    (fun j v _ => (pars j v).new) (fun j v _ => dif j v)
  have rem:=resto_por_tiempo_y_estado nr X a good live (c t) (c (t+1)) (fun j v => d*V j v)
    (mul_nonneg pos dp) (mul_nonneg pos (sq_nonneg d)) (fun j v _ => dif j v) (fun j v _ => er j v)
  have dn : 0≤d*(n:ℝ) := mul_nonneg dp (Nat.cast_nonneg _)
  have h1 : K*(d*(n:ℝ))≤K := mul_le_of_le_one_right pos small
  have h2 : K*(d*(n:ℝ))^2≤K := mul_le_of_le_one_right pos (by simpa using pow_le_pow_left₀ dn small 2)
  constructor
  · exact bd.trans (by nlinarith [mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α:=ℝ) n)])
  · exact rem.trans (by nlinarith [h1,h2])

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.reloj_hasta_un_horizonte
#print axioms ArticuloA.Historias.salto_y_resto_en_el_reloj

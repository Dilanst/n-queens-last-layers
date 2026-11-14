import BalanceInicialDeE2
open Set MeasureTheory
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2
noncomputable section

def posicionLinea (n j : ℕ) : Fin 4→ℝ
  | 0 => medio n j
  | 1 => medio n j
  | 2 => oblicuo n (-1) j
  | 3 => oblicuo n 0 j

def integralDesplazada (p : FactoresContinuos) (s : ℝ) (anti : Bool) :=
  ∫ t in (0:ℝ)..(1-|s|),pesoContinuo p (max s 0+t) (if anti then 1-(max (-s) 0+t) else max (-s) 0+t)

def integralFisica (p : FactoresContinuos) : Fin 4→ℝ→ℝ
  | 0,z => ∫ t in (0:ℝ)..1,pesoContinuo p z t
  | 1,z => ∫ t in (0:ℝ)..1,pesoContinuo p t z
  | 2,z => integralDesplazada p z false
  | 3,z => integralDesplazada p (z-1) true

theorem extremos_reales_de_la_fibra {n} (hn : 0<n) (j : Indice n) :
    (inicioR n j.val:ℝ)/n=max (oblicuo n (-1) j.val) 0 ∧
    (inicioC n j.val:ℝ)/n=max (-oblicuo n (-1) j.val) 0 ∧
    largo n j.val=1-|oblicuo n (-1) j.val| := by
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have shift : oblicuo n (-1) j.val=((j.val:ℝ)-((n-1:ℕ):ℝ))/n := by
    rw [oblicuo,Nat.cast_sub (by omega : 1≤n),Nat.cast_one]; field_simp; ring
  rw [shift]
  have rr:inicioR n j.val<n := (extremos_fibra hn j).1
  have cc:inicioC n j.val<n := (extremos_fibra hn j).2.1
  by_cases ge : n-1≤j.val
  · have r : (inicioR n j.val:ℝ)=(j.val:ℝ)-((n-1:ℕ):ℝ) := Nat.cast_sub ge
    have c : inicioC n j.val=0 := Nat.sub_eq_zero_of_le ge
    have s : 0≤((j.val:ℝ)-((n-1:ℕ):ℝ))/n := div_nonneg (sub_nonneg.mpr (by exact_mod_cast ge)) np.le
    simp only [r,c,Nat.cast_zero,zero_div,max_eq_left s,max_eq_right (neg_nonpos.mpr s),abs_of_nonneg s,true_and]
    rw [largo,longitudFibra,c,max_eq_left (Nat.zero_le _),Nat.cast_sub rr.le,r]
    field_simp
  · have le : j.val≤n-1 := by omega
    have c : (inicioC n j.val:ℝ)=((n-1:ℕ):ℝ)-(j.val:ℝ) := Nat.cast_sub le
    have r : inicioR n j.val=0 := Nat.sub_eq_zero_of_le le
    have s : ((j.val:ℝ)-((n-1:ℕ):ℝ))/n≤0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (by exact_mod_cast le)) np.le
    simp only [r,c,Nat.cast_zero,zero_div,max_eq_right s,max_eq_left (neg_nonneg.mpr s),abs_of_nonpos s,true_and]
    rw [largo,longitudFibra,r,max_eq_right (Nat.zero_le _),Nat.cast_sub cc.le,c]
    constructor <;> ring_nf
    field_simp

theorem integra_la_linea_correcta {n} (hn : 0<n) (p : FactoresContinuos) (i : Fin 4) (j : Indice n)
    (fis : i.val<2 → j.val<n) : integralLinea p n j.val i=integralFisica p i (posicionLinea n j.val i) := by
  obtain ⟨r,c,len⟩:=extremos_reales_de_la_fibra hn j
  have anti : oblicuo n 0 j.val-1=oblicuo n (-1) j.val := by unfold oblicuo; ring
  fin_cases i
  · simp [integralLinea,integralTransversal,trazaTransversal,integralFisica,posicionLinea,fis (by decide)]
  · simp [integralLinea,integralTransversal,trazaTransversal,integralFisica,posicionLinea,fis (by decide)]
  · simp [integralLinea,integralFisica,posicionLinea,integralOblicua,integralDesplazada,corteOblicuo,
      puntoFila,puntoCol,r,c,len]
  · simp [integralLinea,integralFisica,posicionLinea,integralOblicua,integralDesplazada,corteOblicuo,
      puntoFila,puntoCol,anti,r,c,len]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.integra_la_linea_correcta

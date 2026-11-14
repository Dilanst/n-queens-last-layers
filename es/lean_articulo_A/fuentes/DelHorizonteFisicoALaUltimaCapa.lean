import ValorDelTensorEnElHorizonte
import ObservableInversoAlCorte
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Limites

theorem inversas_sin_condicion_de_nivel {n} (P : Placement n) (w : Cell n→ℝ) (leg : Legal P) :
    inversasDelTablero P w=totalInverso sumaCampo w P := by
  cases hs : pieces P with
  | zero =>
    have nil : queens P=[] := List.length_eq_zero_iff.mp ((queenLength P).trans hs)
    simp [inversasDelTablero,totalInverso,invMarks,grid,nil,estadoEscalar,indicator,SumLaw.over,sumaCampo]
  | succ q =>
    rw [←conteo_en_el_nivel_inverso P w hs leg,marcas_inversas_del_nivel P leg hs w]

theorem continuacion_fisica_desde_el_horizonte {n h t} {P U : Placement n}
    (hn : 0<n) (path : TerminalPath P t U) (legal : Legal P) (last : Legal U)
    (size : pieces U=n-h+1) (w : Cell n→ℝ) (W : ℝ) (wp : 0≤W) (cap : ∀ z,|w z|≤W) :
    |Iobs n h w U-inversasDelTablero P w/(n:ℝ)^2|≤4*((t:ℝ)/n)*W := by
  rw [inversas_sin_condicion_de_nivel P w legal]
  exact inversa_fisica_al_corte hn path last size w W wp cap

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.inversas_sin_condicion_de_nivel
#print axioms ArticuloA.Historias.continuacion_fisica_desde_el_horizonte

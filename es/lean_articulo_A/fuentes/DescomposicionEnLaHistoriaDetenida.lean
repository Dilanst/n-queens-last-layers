import InnovacionBilateralDeE2
open scoped NNReal BigOperators
namespace ArticuloA.RealFinita
open Trayectoria Trayectoria.ProfileKernel Trayectoria.Adjunto Corte Trayectoria.E2 E2.Regular
noncomputable section
variable {X : Type}

def estadoEn (x : X) (l : List X) (j : ℕ) := (l.take j).foldl (fun _ y => y) x

private theorem estado_del_libro (S : ℕ→X→Atoms ℝ≥0 X) (F G : ℕ→X→ℝ≥0)
    (l : List X) (u : ℕ) (H : HistoryBook X ℝ≥0) :
    (leerLibro S F G u H l).state=l.foldl (fun _ y => y) H.state := by
  induction l generalizing u H with
  | nil => rfl
  | cons y l ih => exact ih (u+1) (record masas S F G u H y)

private theorem extender_libro (S : ℕ→X→Atoms ℝ≥0 X) (F G : ℕ→X→ℝ≥0)
    (l : List X) (y : X) (u : ℕ) (H : HistoryBook X ℝ≥0) :
    leerLibro S F G u H (l++[y])=record masas S F G (u+l.length) (leerLibro S F G u H l) y := by
  induction l generalizing u H with
  | nil => simp [leerLibro]
  | cons a as ih =>
    change leerLibro S F G (u+1) (record masas S F G u H a) (as++[y])=_
    rw [ih]; simp only [leerLibro,List.length_cons]; congr 1; omega

def derivaEn (S : ℕ→X→Atoms ℝ≥0 X) (y : X→ℝ≥0) (b : ℕ→ℝ) (x : X) (l : List X) (j : ℕ) :=
  (avg masas (S j (estadoEn x l j)) y).val - y (estadoEn x l j) - (b (j+1)-b j)

theorem saldo_mas_deriva_en_prefijo (S : ℕ→X→Atoms ℝ≥0 X) (y : X→ℝ≥0)
    (b : ℕ→ℝ) (x : X) (l : List X) (s : ℕ) (hs : s≤l.length) (ini : b 0=(y x:ℝ)) :
    (y (estadoEn x l s):ℝ)-b s =
      saldo (leerLibro S (fun _ => y) (fun _ _ => 0) 0 (libroCero x) (l.take s))+
        ∑ j∈Finset.range s,derivaEn S y b x l j := by
  induction s with
  | zero => simp [estadoEn,leerLibro,libroCero,saldo,ini]
  | succ j ih =>
    have hj : j<l.length := by omega
    have prev:=ih (by omega)
    let H:=leerLibro S (fun _ => y) (fun _ _ => 0) 0 (libroCero x) (l.take j)
    have state : H.state=estadoEn x l j := estado_del_libro _ _ _ _ _ _
    have last : estadoEn x l (j+1)=l[j] := by
      unfold estadoEn; rw [List.take_succ_eq_append_getElem hj,List.foldl_append]; rfl
    have step : leerLibro S (fun _ => y) (fun _ _ => 0) 0 (libroCero x) (l.take (j+1))=
        record masas S (fun _ => y) (fun _ _ => 0) j H l[j] := by
      rw [List.take_succ_eq_append_getElem hj,extender_libro]; simp [H,List.length_take, Nat.min_eq_left hj.le]
    have zero : avg masas (S j H.state) (fun _ => (0:ℝ≥0))=0 := by rw [avg_constant]; exact mul_zero _
    have delta : saldo (record masas S (fun _ => y) (fun _ _ => 0) j H l[j]) =
        saldo H + (y l[j]:ℝ) - avg masas (S j (estadoEn x l j)) y := by
      change ((H.pos+(y l[j]+avg masas (S j H.state) (fun _ => 0)):ℝ≥0):ℝ) - ↑(H.neg+(0+avg masas (S j H.state) y):ℝ≥0) = _
      rw [zero,add_zero,zero_add,state]; simp only [NNReal.coe_add,saldo]; ring
    change (y (estadoEn x l j):ℝ)-b j=saldo H+_ at prev
    rw [step,delta,last,Finset.sum_range_succ]
    change _ = saldo H + _ - _ + ((∑ i∈Finset.range j, derivaEn S y b x l i) + ((avg masas (S j (estadoEn x l j)) y).val-↑(y (estadoEn x l j))-(b (j+1)-b j)))
    have scalar (u v a d e b m : ℝ) (h : u-a=m+d) : v-b=m+v-e+(d+(e-u-(b-a))) := by linarith
    exact scalar _ _ _ _ _ _ _ prev

theorem error_real_en_prefijo {n} (v : Cell n→ℝ≥0) (w : ColorWeights ℝ≥0)
    (halt : ℕ→State n→Bool) (c : Coord) (b : ℕ→ℝ) (x : ℕ×State n)
    (l : List (ℕ×State n)) (s : ℕ) (hs : s≤l.length) (ini : b 0=(medidaCoord v w c 0 x:ℝ)) :
    (medidaCoord v w c s (estadoEn x l s):ℝ)-b s =
      ruidoE2 v w halt x c s l+∑ j∈Finset.range s,derivaEn (pasoParado w halt) (medidaCoord v w c 0) b x l j :=
  saldo_mas_deriva_en_prefijo _ _ _ _ _ _ hs ini

end
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.error_real_en_prefijo

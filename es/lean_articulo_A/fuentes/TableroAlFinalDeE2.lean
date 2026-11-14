import CuotasDelEstado
namespace ArticuloA.Historias
open Trayectoria.E2 Repair
noncomputable section
open Classical
variable {n q : ℕ}

private theorem vacio (xs : List (Cell n)) : queens (emptyMask xs)=[] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

private theorem una_vez (H : Historia n q) : Function.Injective (secuencia H) := by
  intro s t eq
  apply H.2.2.injective
  apply Fin.ext
  exact (fila_pieza H.1 H.2.1 (H.2.2 s)).symm.trans
    ((congrArg (fun v => edgeOf v 0) eq).trans (fila_pieza H.1 H.2.1 (H.2.2 t)))

theorem reinas_del_prefijo (H : Historia n q) (h t : ℕ) (bound : t≤2*n-1) (e : Cell n) :
    e∈queens (estado H h t).physical ↔ ∃ s : Indice n,s.val<t ∧ secuencia H s = .real e := by
  induction t with
  | zero => simp [estado,initial,vacio]
  | succ t ih =>
    have ht : t<2*n-1 := by omega
    let j : Indice n := ⟨t,ht⟩
    have split : (∃ s : Indice n,s.val<t+1 ∧ secuencia H s=.real e) ↔
        (∃ s : Indice n,s.val<t ∧ secuencia H s=.real e) ∨ secuencia H j=.real e := by
      constructor
      · rintro ⟨s,lt,eq⟩
        by_cases early : s.val<t
        · exact .inl ⟨s,early,eq⟩
        · have same : s=j := Fin.ext (by change s.val=t; omega)
          exact .inr (same ▸ eq)
      · rintro (⟨s,lt,eq⟩|eq)
        · exact ⟨s,by omega,eq⟩
        · exact ⟨j,Nat.lt_succ_self t,eq⟩
    rw [split,←ih (by omega),estado,dif_pos ht]
    change e∈queens (next _ (jugada (secuencia H j))).physical ↔ _
    cases eq : secuencia H j with
    | virtual g => simp [jugada,next]
    | real c =>
      change e∈queens (toggle c (estado H h t).physical) ↔ _
      rw [mem_toggle]
      by_cases same : e=c
      · subst c
        have fresh : e∉queens (estado H h t).physical := by
          intro mem
          obtain ⟨s,lt,hit⟩ := (ih ht.le).mp mem
          have same := una_vez H (hit.trans eq.symm)
          exact (Nat.ne_of_lt lt) (congrArg Fin.val same)
        simp [fresh]
      · simp [same,Ne.symm same]

-- The following two private mask extensionality helpers are copied from OrdenDeHistorias.
private theorem solo_casillas {n : ℕ} {xs : List (Cell n)} (p : Mask xs) :
    ∀ e ∈ queens p, e ∈ xs := by
  induction p with
  | empty => simp [queens]
  | skip b ih => intro e he; exact List.mem_cons_of_mem _ (ih e he)
  | take b ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl|ht
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih e ht)

private theorem mascara_unica {n : ℕ} {xs : List (Cell n)} (p b : Mask xs)
    (nd : xs.Nodup) (eq : ∀ e, e ∈ queens p ↔ e ∈ queens b) : p=b := by
  induction p with
  | empty => cases b; rfl
  | @skip x xs p ih =>
    obtain ⟨no,hd⟩ := List.nodup_cons.mp nd
    cases b with
    | skip t => exact congrArg Mask.skip (ih t hd eq)
    | take t =>
      exact False.elim (no (solo_casillas p x ((eq x).mpr List.mem_cons_self)))
  | @take x xs p ih =>
    obtain ⟨no,hd⟩ := List.nodup_cons.mp nd
    cases b with
    | skip t => exact False.elim (no (solo_casillas t x ((eq x).mp List.mem_cons_self)))
    | take t =>
      apply congrArg Mask.take
      apply ih t hd
      intro e
      by_cases same : e=x
      · subst e
        exact iff_of_false (fun h => no (solo_casillas p _ h)) (fun h => no (solo_casillas t _ h))
      · simpa [queens,same] using eq e


theorem tablero_final (H : Historia n q) (h : ℕ) :
    (estado H h (2*n-1)).physical=H.1.val := by
  apply mascara_unica _ _ (board_unique n)
  intro e
  rw [reinas_del_prefijo H h _ le_rfl,←reales_de_la_secuencia H]
  exact ⟨fun ⟨s,_,eq⟩ => ⟨s,eq⟩,fun ⟨s,eq⟩ => ⟨s,s.isLt,eq⟩⟩

theorem proyeccion_exitosa (H : Historia n q) (h : ℕ) (nivel : q=n-h) :
    let x:=estado H h (2*n-1)
    x.failed=false ∧ x.reals=0 ∧ x.virtuals=0 ∧ x.physical=H.1.val := by
  have hc := fin_de_cuotas H h nivel
  exact ⟨hc.2.2,hc.1,hc.2.1,tablero_final H h⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.reinas_del_prefijo
#print axioms ArticuloA.Historias.proyeccion_exitosa

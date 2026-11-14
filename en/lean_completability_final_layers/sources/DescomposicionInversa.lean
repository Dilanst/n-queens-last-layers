import SaltoInversoEnElTablero
namespace ArticuloA.Trayectoria.E2
open ArticuloA Repair

def grid {α} (u v : List α) : List (α × α) :=
  u.flatMap (fun e => v.map (fun f => (e,f)))

private theorem grid_perm {α} {u v : List α} (h : u.Perm v) :
    (grid u u).Perm (grid v v) := by
  apply List.Perm.trans (h.flatMap_right (fun e => u.map (fun f => (e,f))))
  have aux (l : List α) : (grid l u).Perm (grid l v) := by
    induction l with
    | nil => exact .nil
    | cons a l ih => exact (h.map (fun f => (a,f))).append ih
  exact aux _

private theorem split_flags {α} (P Q : α → Bool) (l : List α) :
    (l.filter P).Perm ((l.filter (fun a => P a && Q a)) ++ (l.filter (fun a => P a && !Q a))) := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    cases ha : P a <;> cases hb : Q a <;> simp [ha,hb] at * <;> first
      | exact ih | exact ih.cons _ | exact List.perm_cons_append_cons a ih

private theorem count_grid {n} (u v : List (Cell n)) (test : Cell n → Cell n → Bool) :
    ((grid u v).filter (fun m => test m.1 m.2)).length = pairSum u v test := by
  induction u with
  | nil => rfl
  | cons e es ih =>
    change (((v.map (fun f => (e,f))) ++ grid es v).filter _).length = _ + pairSum es v test
    rw [List.filter_append,List.length_append,ih,←List.countP_eq_length_filter,List.countP_map]
    rfl

private theorem expand_grid {α} (a : α) (l v : List α) :
    (grid l (a::v)).Perm (grid l v ++ l.map (fun x => (x,a))) := by
  induction l with
  | nil => exact .nil
  | cons x l ih =>
    change (((x,a)::v.map (fun f => (x,f))) ++ grid l (a::v)).Perm _
    have J := (ih.append_left (v.map (fun f => (x,f)))).cons (x,a)
    apply J.trans
    change ((x,a)::(v.map _ ++ (grid l v ++ l.map _))).Perm ((v.map _ ++ grid l v) ++ (x,a)::l.map _)
    apply List.perm_cons_append_cons
    simp only [List.append_assoc]; exact .refl _

noncomputable def invMarks {n} (p : Placement n) : List (Mark n) :=
  (grid (queens p) (queens p)).filter (fun m => eligiblePair p m.1 m.2)

/-- Common terms cancel even when the root weight has both signs. -/
theorem cambio_de_lista {n} (p : Placement n) (ok : Legal p) (g : Cell n) (fresh : g ∉ queens p) :
    ∃ common lost born : List (Mark n), (invMarks p).Perm (common ++ lost) ∧
      (invMarks (toggle g p)).Perm (common ++ born) ∧ lost.length ≤ 2*n ∧ born.length ≤ 2*n := by
  let L := queens p
  let old := fun m : Mark n => eligiblePair p m.1 m.2
  let new := fun m : Mark n => eligiblePair (toggle g p) m.1 m.2
  let l := grid L L
  let extra := L.map (fun e => (e,g)) ++ (g::L).map (fun f => (g,f))
  have perm : (grid (queens (toggle g p)) (queens (toggle g p))).Perm (l ++ extra) := by
    apply (grid_perm (inserted p g (board_complete g) fresh)).trans
    change ((_ ++ grid L (g::L))).Perm _
    apply List.Perm.trans (List.perm_append_comm ..)
    simpa only [List.append_assoc,extra,l] using (expand_grid g L L).append_right ((g::L).map (fun f => (g,f)))
  have keep : ∀ m, new m = true → old m = true := by
    intro m yes
    simp only [old,new,eligiblePair,decide_eq_true_eq] at *
    refine ⟨yes.1, fun z hz => yes.2 z ?_⟩
    have ne : z ≠ g := fun eq => fresh (eq ▸ hz)
    exact (mem_toggle g z p).mpr (by simp [ne,hz])
  have same : (fun m => old m && new m) = new := by
    funext m; cases eq : new m with
    | false => simp
    | true => simp [keep m eq]
  refine ⟨l.filter new,l.filter (fun m => old m && !(new m)),extra.filter new,?_,?_,?_,?_⟩
  · simpa only [same] using split_flags old new l
  · simpa only [List.filter_append] using perm.filter new
  · calc
      _ = _ := count_grid L L (fun e f => old (e,f) && !new (e,f))
      _ ≤ _ := old_lost p ok g
  · have z : new (g,g) = false := by simp [new,eligiblePair]
    have le (f : Cell n → Mark n) : ((L.map f).filter new).length ≤ L.length := by
      simpa using List.length_filter_le new (L.map f)
    have size := distinct_le _ (List.finRange n) (distinctRows ok) (by
      intro j _; simp [List.finRange,List.mem_ofFn])
    simp only [List.length_map,List.length_finRange] at size
    change L.length ≤ n at size
    simp only [extra,List.filter_append,List.map_cons,List.filter_cons,z,Bool.false_eq_true,decide_false,ite_false,List.length_append]
    have j := le (fun e => (e,g)); have k := le (fun f => (g,f)); omega
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.cambio_de_lista

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9055

-- Gate restriction and evaluation preservation follow the checked L-meta-562.
namespace FanoProjection

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma sideTrue_mono_U {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue V B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

private lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

private lemma gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal V i = true :=
  gateValFuel_mono_U C hUV C.size i h

private def restrictCircuit {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size)) :
    AndCountCircuit n where
  size := K.card
  leftVars i := C.leftVars (K.orderEmbOfFin rfl i)
  leftGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i))
  rightVars i := C.rightVars (K.orderEmbOfFin rfl i)
  rightGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i))
  outVars := C.outVars
  outGates := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates)

private lemma restrict_mem_leftGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).leftGates i ↔
      K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_rightGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).rightGates i ↔
      K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_outGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (j : Fin K.card) :
    j ∈ (restrictCircuit C K).outGates ↔ K.orderEmbOfFin rfl j ∈ C.outGates := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_wf {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (hWF : C.WellFormed) : (restrictCircuit C K).WellFormed := by
  intro i
  constructor
  · intro j hj
    have hj' := (restrict_mem_leftGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).1 _ hj')
  · intro j hj
    have hj' := (restrict_mem_rightGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).2 _ hj')

private lemma restrict_gateVal_eq {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) (hK : ∀ j : Fin C.size, j ∉ K → C.gateVal U j = false) :
    ∀ (m : ℕ) (i : Fin K.card), i.val < m →
      (restrictCircuit C K).gateVal U i = C.gateVal U (K.orderEmbOfFin rfl i) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    rw [gateVal_unfold (restrictCircuit C K) U i, gateVal_unfold C U (K.orderEmbOfFin rfl i)]
    congr 1
    · unfold sideTrue
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjF' := (restrict_mem_leftGates C K i j).mp hjF
          refine Or.inr ⟨K.orderEmbOfFin rfl j, hjF', (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, ?_⟩
          rwa [← ih j (by omega)]
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjK : j ∈ K := by
            by_contra hnot
            rw [hK j hnot] at hjv
            exact Bool.false_ne_true hjv
          have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]
            exact hjK
          obtain ⟨j', hj'⟩ := hjr
          have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
          refine Or.inr ⟨j', (restrict_mem_leftGates C K i j').mpr (by rw [hj']; exact hjF),
            hj'lt, ?_⟩
          rw [ih j' (by omega), hj']
          exact hjv
    · unfold sideTrue
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjF' := (restrict_mem_rightGates C K i j).mp hjF
          refine Or.inr ⟨K.orderEmbOfFin rfl j, hjF', (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, ?_⟩
          rwa [← ih j (by omega)]
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjK : j ∈ K := by
            by_contra hnot
            rw [hK j hnot] at hjv
            exact Bool.false_ne_true hjv
          have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]
            exact hjK
          obtain ⟨j', hj'⟩ := hjr
          have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
          refine Or.inr ⟨j', (restrict_mem_rightGates C K i j').mpr (by rw [hj']; exact hjF),
            hj'lt, ?_⟩
          rw [ih j' (by omega), hj']
          exact hjv

private lemma restrict_eval_eq {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) (hK : ∀ j : Fin C.size, j ∉ K → C.gateVal U j = false) :
    (restrictCircuit C K).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjO, hjv⟩)
    · exact Or.inl hv
    · have hjO' := (restrict_mem_outGates C K j).mp hjO
      refine Or.inr ⟨K.orderEmbOfFin rfl j, hjO', ?_⟩
      rwa [← restrict_gateVal_eq C K U hK _ j j.isLt]
  · rintro (hv | ⟨j, hjO, hjv⟩)
    · exact Or.inl hv
    · have hjK : j ∈ K := by
        by_contra hnot
        rw [hK j hnot] at hjv
        exact Bool.false_ne_true hjv
      have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hjK
      obtain ⟨j', hj'⟩ := hjr
      refine Or.inr ⟨j', (restrict_mem_outGates C K j').mpr (by rw [hj']; exact hjO), ?_⟩
      rw [restrict_gateVal_eq C K U hK _ j' j'.isLt, hj']
      exact hjv

private def pullVars {n m : Nat} (e : Fin m → Fin n) (V : Finset (Fin n)) :=
  Finset.univ.filter fun v => e v ∈ V

private def relabel {n m : Nat} (e : Fin m → Fin n) (D : AndCountCircuit n) :
    AndCountCircuit m where
  size := D.size
  leftVars j := pullVars e (D.leftVars j)
  rightVars j := pullVars e (D.rightVars j)
  leftGates := D.leftGates
  rightGates := D.rightGates
  outVars := pullVars e D.outVars
  outGates := D.outGates

private lemma pull_intersects {n m : Nat} (e : Fin m → Fin n)
    (U : Finset (Fin m)) (V : Finset (Fin n)) :
    (∃ j ∈ pullVars e V, j ∈ U) ↔ ∃ i ∈ V, i ∈ U.image e := by
  simp only [pullVars, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hu⟩
    exact ⟨e j, hj, j, hu, rfl⟩
  · rintro ⟨i, hi, j, hu, rfl⟩
    exact ⟨j, hi, hu⟩

private lemma pull_side {n m k : Nat} (e : Fin m → Fin n) (U : Finset (Fin m))
    (V : Finset (Fin n)) (J : Finset (Fin k)) (i : Fin k) (v : Fin k → Bool) :
    sideTrue U (pullVars e V) J i v = sideTrue (U.image e) V J i v := by
  unfold sideTrue
  exact decide_eq_decide.mpr (or_congr (pull_intersects e U V) Iff.rfl)

private lemma relabel_fuel {n m : Nat} (e : Fin m → Fin n) (D : AndCountCircuit n)
    (U : Finset (Fin m)) (k : Nat) :
    (relabel e D).gateValFuel U k = D.gateValFuel (U.image e) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    apply funext
    intro i
    change Fin D.size at i
    change (sideTrue U (pullVars e (D.leftVars i)) (D.leftGates i) i
        ((relabel e D).gateValFuel U k) &&
      sideTrue U (pullVars e (D.rightVars i)) (D.rightGates i) i
        ((relabel e D).gateValFuel U k)) = _
    rw [ih]
    exact congrArg₂ Bool.and (pull_side e U (D.leftVars i) (D.leftGates i) i _)
      (pull_side e U (D.rightVars i) (D.rightGates i) i _)

private lemma relabel_eval {n m : Nat} (e : Fin m → Fin n) (D : AndCountCircuit n)
    (U : Finset (Fin m)) : (relabel e D).eval U = D.eval (U.image e) := by
  unfold AndCountCircuit.eval
  apply decide_eq_decide.mpr
  apply or_congr (pull_intersects e U D.outVars)
  change (∃ j ∈ D.outGates, (relabel e D).gateValFuel U D.size j = true) ↔ _
  rw [relabel_fuel]
  rfl

theorem project (n m : Nat) (e : Fin m → Fin n) (E : AndCountCircuit n) (wf : E.WellFormed) :
    ∃ B : AndCountCircuit m, B.WellFormed ∧
      (∀ U : Finset (Fin m), B.eval U = E.eval (U.image e)) ∧
      B.size ≤ {j : Fin E.size | E.gateVal (Finset.univ.image e) j = true}.ncard := by
  let K := Finset.univ.filter fun j => E.gateVal (Finset.univ.image e) j = true
  refine ⟨relabel e (restrictCircuit E K), restrict_wf E K wf, ?_, ?_⟩
  · intro U
    rw [relabel_eval]
    apply restrict_eval_eq
    intro j hj
    apply Bool.eq_false_iff.mpr
    intro alive
    apply hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, gateVal_mono_U E (Finset.image_subset_image (Finset.subset_univ U)) j alive⟩
  · change K.card ≤ _
    have h : (K : Set (Fin E.size)) = {j | E.gateVal (Finset.univ.image e) j = true} := by
      ext j
      simp [K]
    rw [← h, Set.ncard_coe_finset]

end FanoProjection

end PEqualNP.Outside.L_meta_9055

theorem PEqualNP.Outside.L_meta_9055 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x1) (x4 : PEqualNP.AndCount.AndCountCircuit x1), x4.WellFormed → ∃ (x6 : PEqualNP.AndCount.AndCountCircuit x2), x6.WellFormed ∧ (∀ (x7 : Finset (Fin x2)), x6.eval x7 = x4.eval (Finset.image x3 x7)) ∧ x6.size ≤ {x7 : Fin x4.size | x4.gateVal (Finset.image x3 Finset.univ) x7 = Bool.true}.ncard :=
  PEqualNP.Outside.L_meta_9055.FanoProjection.project

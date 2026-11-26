import TetraStereo.Engine.RingOrdinaryHydrogenGraphs

/-! Bond and hydrogen-count certificates for the graphs returned by preparation. -/
set_option autoImplicit false

namespace TetraStereo.OneCenter.OrdinaryHydrogenSpellings.Production
open TetraStereo.Engine.RingHydrogenCompletion

private theorem added_record {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (cert : Certified m xyz out pos) (b : RawBond) (mem : b ∈ out.bonds)
    (notOld : originalBond m b = false) :
    b.kind = .single ∧ b.source < m.atomCount ∧ m.atomCount ≤ b.target := by
  have valid := List.all_eq_true.mp cert.bonds_added b
    (List.mem_filter.mpr ⟨mem,by simp [notOld]⟩)
  exact of_decide_eq_true valid

/-- Original directed bond orders are unchanged by the certified appended records. -/
theorem certified_old_directed_bond {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (cert : Certified m xyz out pos) (u v : Nat) (_hu : u < m.atomCount) (hv : v < m.atomCount) :
    out.directedBondOrder u v = m.directedBondOrder u v := by
  have fold (bs : List RawBond) (subset : ∀ b ∈ bs, b ∈ out.bonds) (acc : Nat) :
      bs.foldl (fun order b => if b.directedConnects u v then max order b.kind.order else order) acc =
      (bs.filter (originalBond m)).foldl
        (fun order b => if b.directedConnects u v then max order b.kind.order else order) acc := by
    induction bs generalizing acc with
    | nil => rfl
    | cons b bs ih =>
      have tail : ∀ a ∈ bs, a ∈ out.bonds := fun a mem => subset a (List.mem_cons_of_mem b mem)
      cases old : originalBond m b with
      | true => simpa only [List.foldl_cons,List.filter_cons,old,cond_true] using ih tail _
      | false =>
        have target := (added_record cert b (subset b List.mem_cons_self) old).2.2
        have different : b.target ≠ v := by omega
        have notConnect : b.directedConnects u v = false := by
          simp [RawBond.directedConnects,different]
        simpa only [List.foldl_cons,List.filter_cons,old,cond_false,notConnect] using ih tail acc
  unfold RawMolecule.directedBondOrder
  rw [fold out.bonds (fun _ h => h) 0,cert.bonds_original]

theorem certified_old_bond {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (cert : Certified m xyz out pos) (u v : Nat) (hu : u < m.atomCount) (hv : v < m.atomCount) :
    out.bondOrder u v = m.bondOrder u v := by
  simp only [RawMolecule.bondOrder,certified_old_directed_bond cert u v hu hv,
    certified_old_directed_bond cert v u hv hu]

/-- A fresh endpoint can meet only a newly appended single-bond record. -/
theorem certified_fresh_bond_le_one {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (cert : Certified m xyz out pos) (u v : Nat) (fresh : m.atomCount ≤ u) :
    out.bondOrder u v ≤ 1 := by
  have directed (a b : Nat) (atLeast : m.atomCount ≤ a ∨ m.atomCount ≤ b) :
      out.directedBondOrder a b ≤ 1 := by
    have each (record : RawBond) (mem : record ∈ out.bonds)
        (connects : record.directedConnects a b = true) : record.kind.order ≤ 1 := by
      have endpoints : record.source = a ∧ record.target = b := by
        simpa [RawBond.directedConnects] using connects
      cases old : originalBond m record with
      | false => rw [(added_record cert record mem old).1]; rfl
      | true =>
        have bounds : record.source < m.atomCount ∧ record.target < m.atomCount := by
          simpa [originalBond] using old
        rcases atLeast with ha | hb
        · omega
        · omega
    have fold (bs : List RawBond) (subset : ∀ b ∈ bs, b ∈ out.bonds) (acc : Nat) (bound : acc ≤ 1) :
        bs.foldl (fun order record => if record.directedConnects a b then max order record.kind.order else order) acc ≤ 1 := by
      induction bs generalizing acc with
      | nil => exact bound
      | cons record bs ih =>
        apply ih (fun x hx => subset x (List.mem_cons_of_mem _ hx))
        dsimp only
        split
        · exact max_le bound (each record (subset record List.mem_cons_self) ‹_›)
        · exact bound
    exact fold out.bonds (fun _ h => h) 0 (by omega)
  unfold RawMolecule.bondOrder
  split
  · exact Nat.zero_le _
  · exact max_le (directed u v (Or.inl fresh)) (directed v u (Or.inr fresh))

/-- Actual fresh hydrogen rows determine their exact bond order, not just adjacency. -/
theorem certified_fresh_bond {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (cert : Certified m xyz out pos) (u : Fin out.atomCount) (fresh : m.atomCount ≤ u.val)
    (parent : Nat) (row : out.writtenNeighbors u.val = [parent]) (v : Fin out.atomCount) :
    out.bondOrder u.val v.val = if v.val = parent then 1 else 0 := by
  have exactU := RawMolecule.WrittenNeighborExact.at out cert.output_admissible.2 u
  have one := certified_fresh_bond_le_one cert u.val v.val fresh
  by_cases same : v.val = parent
  · simp only [if_pos same]
    have positive := (exactU.2.2 v).mp (by simp [row,same])
    exact Nat.le_antisymm one positive
  · simp only [if_neg same]
    have notPositive : ¬0 < out.bondOrder u.val v.val := by
      intro pos
      have member := (exactU.2.2 v).mpr pos
      simp [row,same] at member
    exact Nat.eq_zero_of_not_pos notPositive

variable {k : Nat} {coreAtom : Fin k → AtomSpec} {coreBond : Fin k → Fin k → Nat}

private theorem parent_core (a : Completion coreAtom coreBond) (p : Fin a.molecule.atomCount)
    (planned : p.val ∈ addedParents a.molecule) : ∃ c, (a.core c).val = p.val := by
  cases tag : a.tag p with
  | inl c =>
    exact ⟨c,congrArg Fin.val (a.core_only p c tag).symm⟩
  | inr c =>
    have record := congrArg AtomSpec.element (a.records p)
    rw [tag] at record
    have hydrogen : (a.molecule.atoms.get p).element = .H := record
    have lookup : a.molecule.atoms[p.val]? = some (a.molecule.atoms.get p) := by simp
    exact False.elim (planned_parent_not_hydrogen a.molecule p.val planned _ lookup hydrogen)

private theorem fresh_core {a : Completion coreAtom coreBond} {out : RawMolecule}
    {xyz pos : SpatialConfiguration} (cert : Certified a.molecule xyz out pos)
    (v : Fin out.atomCount) (fresh : a.molecule.atomCount ≤ v.val) :
    ∃ c, out.writtenNeighbors v.val = [(a.core c).val] := by
  obtain ⟨p,planned,row⟩ := cert.fresh_row fresh v.isLt
  have bound := cert.fresh_parent_lt planned
  obtain ⟨c,core⟩ := parent_core a ⟨p,bound⟩ (List.mem_of_getElem? planned)
  exact ⟨c,by simpa [core] using row⟩

noncomputable def producedTag {a : Completion coreAtom coreBond} {out : RawMolecule}
    {xyz pos : SpatialConfiguration} (cert : Certified a.molecule xyz out pos)
    (v : Fin out.atomCount) : Fin k ⊕ Fin k :=
  if old : v.val < a.molecule.atomCount then a.tag ⟨v.val,old⟩
  else .inr (Classical.choose (fresh_core cert v (by omega)))

theorem producedTag_old {a : Completion coreAtom coreBond} {out : RawMolecule}
    {xyz pos : SpatialConfiguration} (cert : Certified a.molecule xyz out pos)
    (v : Fin out.atomCount) (old : v.val < a.molecule.atomCount) :
    producedTag cert v = a.tag ⟨v.val,old⟩ := dif_pos old

theorem producedTag_fresh {a : Completion coreAtom coreBond} {out : RawMolecule}
    {xyz pos : SpatialConfiguration} (cert : Certified a.molecule xyz out pos)
    (v : Fin out.atomCount) (fresh : a.molecule.atomCount ≤ v.val) :
    ∃ c, producedTag cert v = .inr c ∧ out.writtenNeighbors v.val = [(a.core c).val] := by
  refine ⟨_,?_,Classical.choose_spec (fresh_core cert v fresh)⟩
  exact dif_neg (by omega)

/-- Successful production completion supplies the output's entire local H-completion
certificate from the input certificate; no output atom map or output completion is assumed. -/
noncomputable def producedCompletion {a : Completion coreAtom coreBond} {out : RawMolecule}
    {xyz pos : SpatialConfiguration} (cert : Certified a.molecule xyz out pos) :
    Completion coreAtom coreBond where
  molecule := out
  core := {
    toFun := fun c => ⟨(a.core c).val,lt_of_lt_of_le (a.core c).isLt cert.atomCount_le⟩
    inj' := by intro c d eq; exact a.core.injective (Fin.ext (congrArg (fun v : Fin out.atomCount => v.val) eq)) }
  tag := producedTag cert
  core_tag := fun c => by rw [producedTag_old cert _ (a.core c).isLt]; exact a.core_tag c
  core_only := by
    intro v c found
    by_cases old : v.val < a.molecule.atomCount
    · rw [producedTag_old cert v old] at found
      exact Fin.ext (congrArg (fun z : a.Vertex => z.val) (a.core_only _ c found))
    · obtain ⟨parent,tag,_⟩ := producedTag_fresh cert v (by omega)
      rw [tag] at found
      contradiction
  retained := a.retained
  records := by
    intro v
    by_cases old : v.val < a.molecule.atomCount
    · rw [producedTag_old cert v old]
      have projection := cert.atom_core old
      have source : a.molecule.atoms[v.val]? = some (a.molecule.atoms.get ⟨v.val,old⟩) := by simp
      have target : out.atoms[v.val]? = some (out.atoms.get v) := by simp
      rw [source,target] at projection
      exact (Option.some.inj projection).trans (a.records _)
    · obtain ⟨c,tag,row⟩ := producedTag_fresh cert v (by omega)
      rw [tag]
      have fresh := cert.fresh_atom (i := v.val) (by omega) v.isLt
      have target : out.atoms[v.val]? = some (out.atoms.get v) := by simp
      rw [target] at fresh
      rw [Option.some.inj fresh]
      rfl
  bonds := by
    intro v w
    by_cases vOld : v.val < a.molecule.atomCount
    · by_cases wOld : w.val < a.molecule.atomCount
      · rw [producedTag_old cert v vOld, producedTag_old cert w wOld,
          certified_old_bond cert v.val w.val vOld wOld]
        exact a.bonds ⟨v.val,vOld⟩ ⟨w.val,wOld⟩
      · obtain ⟨c,tag,row⟩ := producedTag_fresh cert w (by omega)
        rw [out.bondOrder_symm, certified_fresh_bond cert w (by omega) _ row v,
          producedTag_old cert v vOld, tag]
        cases vTag : a.tag ⟨v.val,vOld⟩ with
        | inl d =>
          have core := a.core_only ⟨v.val,vOld⟩ d vTag
          have iff : v.val = (a.core c).val ↔ d = c := by
            constructor
            · intro eq; exact a.core.injective (Fin.ext ((congrArg Fin.val core).symm.trans eq))
            · rintro rfl; exact congrArg Fin.val core
          simp only [bondTable,iff,eq_comm]
        | inr d =>
          have different : v.val ≠ (a.core c).val := by
            intro eq
            have same : (⟨v.val,vOld⟩ : a.Vertex) = a.core c := Fin.ext eq
            rw [same,a.core_tag] at vTag
            contradiction
          simp [bondTable,different]
    · obtain ⟨c,tag,row⟩ := producedTag_fresh cert v (by omega)
      rw [certified_fresh_bond cert v (by omega) _ row w, tag]
      by_cases wOld : w.val < a.molecule.atomCount
      · rw [producedTag_old cert w wOld]
        cases wTag : a.tag ⟨w.val,wOld⟩ with
        | inl d =>
          have core := a.core_only ⟨w.val,wOld⟩ d wTag
          have iff : w.val = (a.core c).val ↔ c = d := by
            constructor
            · intro eq; exact (a.core.injective (Fin.ext ((congrArg Fin.val core).symm.trans eq))).symm
            · rintro rfl; exact congrArg Fin.val core
          simp only [bondTable,iff]
        | inr d =>
          have different : w.val ≠ (a.core c).val := by
            intro eq
            have same : (⟨w.val,wOld⟩ : a.Vertex) = a.core c := Fin.ext eq
            rw [same,a.core_tag] at wTag
            contradiction
          simp [bondTable,different]
      · obtain ⟨d,wTag,_⟩ := producedTag_fresh cert w (by omega)
        have different : w.val ≠ (a.core c).val := by have old := (a.core c).isLt; omega
        simp [wTag,bondTable,different]

theorem tag_ordinary_iff (a : Completion coreAtom coreBond)
    (admitted : a.molecule.StereochemicalAdmissible) (c : Fin k) (v : a.Vertex) :
    a.tag v = .inr c ↔ ordinaryAtParent a.molecule (a.core c).val v.val = true := by
  have exactV := RawMolecule.WrittenNeighborExact.at a.molecule admitted.2 v
  constructor
  · intro tag
    have projection := (a.hydrogenFiber_iff c v).mp tag
    have members : ∀ n, n ∈ a.molecule.writtenNeighbors v.val ↔ n = (a.core c).val := by
      intro n
      constructor
      · intro member
        have bound := exactV.2.1 n member
        have positive := (exactV.2.2 ⟨n,bound⟩).mp member
        rw [a.bonds,tag] at positive
        cases tn : a.tag ⟨n,bound⟩ with
        | inl d =>
          rw [tn] at positive
          have same : c = d := by
            by_contra ne
            simp [bondTable,ne] at positive
          subst d
          exact congrArg Fin.val (a.core_only ⟨n,bound⟩ c tn)
        | inr d => simp [tn,bondTable] at positive
      · rintro rfl
        apply (exactV.2.2 (a.core c)).mpr
        rw [a.bonds,tag,a.core_tag]
        simp [bondTable]
    have perm : (a.molecule.writtenNeighbors v.val).Perm [(a.core c).val] :=
      (List.perm_ext_iff_of_nodup exactV.1 (by simp)).mpr (by intro n; simpa using members n)
    have row : a.molecule.writtenNeighbors v.val = [(a.core c).val] := by simpa using perm
    have lookup : a.molecule.atoms[v.val]? = some (a.molecule.atoms.get v) := by simp
    simp only [ordinaryAtParent,lookup,Option.map_some,Option.some.injEq,decide_eq_true_eq]
    exact ⟨projection.1,row⟩
  · intro ordinary
    have lookup : a.molecule.atoms[v.val]? = some (a.molecule.atoms.get v) := by simp
    have props : heavyCore (a.molecule.atoms.get v) = heavyCore (AtomSpec.aliphatic .H) ∧
        a.molecule.writtenNeighbors v.val = [(a.core c).val] := by
      simpa [ordinaryAtParent,lookup] using ordinary
    apply (a.hydrogenFiber_iff c v).mpr
    refine ⟨props.1,?_⟩
    have positive := (exactV.2.2 (a.core c)).mp (by simp [props.2])
    cases tag : a.tag v with
    | inl d =>
      have record := (a.records v).symm.trans props.1
      rw [tag] at record
      exact False.elim (a.retained d record)
    | inr d =>
      rw [a.bonds,tag,a.core_tag] at positive ⊢
      by_cases same : d = c
      · simp [bondTable,same]
      · simp [bondTable,same] at positive

theorem hydrogenCount_eq_ordinaryCount (a : Completion coreAtom coreBond)
    (admitted : a.molecule.StereochemicalAdmissible) (c : Fin k) :
    a.hydrogenCount c = ordinaryCount a.molecule (a.core c).val := by
  classical
  unfold Completion.hydrogenCount
  rw [Fintype.card_subtype]
  have setEq : (Finset.univ.filter (fun v : a.Vertex => a.tag v = .inr c)) =
      ((List.finRange a.molecule.atomCount).filter
        (fun v => ordinaryAtParent a.molecule (a.core c).val v.val)).toFinset := by
    ext v
    simp [tag_ordinary_iff a admitted c v]
  rw [setEq, List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
  rw [← List.countP_eq_length_filter]
  unfold ordinaryCount
  rw [← List.map_coe_finRange_eq_range, List.countP_map]
  rfl


theorem produced_hydrogenCount {a : Completion coreAtom coreBond} {out : RawMolecule}
    {xyz pos : SpatialConfiguration} (cert : Certified a.molecule xyz out pos) (c : Fin k) :
    (producedCompletion cert).hydrogenCount c =
      a.hydrogenCount c + (addedParents a.molecule).count (a.core c).val := by
  rw [hydrogenCount_eq_ordinaryCount _ cert.output_admissible]
  change ordinaryCount out (a.core c).val = _
  rw [certified_total_count cert]
  have old : (List.range a.molecule.atomCount).countP (ordinaryAtParent out (a.core c).val) =
      ordinaryCount a.molecule (a.core c).val := by
    apply List.countP_congr
    intro j mem
    rw [certified_old_ordinary_predicate cert _ _ (List.mem_range.mp mem)]
  rw [old,hydrogenCount_eq_ordinaryCount a cert.input_admissible]




theorem prepared_spellings_bijection (a b : Completion coreAtom coreBond)
    {xyzA xyzB : SpatialConfiguration} {ra rb : RawMolecule × SpatialConfiguration}
    (acceptedA : prepare? a.molecule xyzA = some ra)
    (acceptedB : prepare? b.molecule xyzB = some rb)
    (totals : ∀ c, a.hydrogenCount c + (addedParents a.molecule).count (a.core c).val =
      b.hydrogenCount c + (addedParents b.molecule).count (b.core c).val) :
    ∃ e : Fin ra.1.atomCount ≃ Fin rb.1.atomCount,
      (∀ c, (e ⟨(a.core c).val,lt_of_lt_of_le (a.core c).isLt
        (prepare?_certified acceptedA).atomCount_le⟩).val = (b.core c).val) ∧
      (∀ v, heavyCore (rb.1.atoms.get (e v)) = heavyCore (ra.1.atoms.get v)) ∧
      (∀ v w, rb.1.bondOrder (e v).val (e w).val = ra.1.bondOrder v.val w.val) := by
  let ca := producedCompletion (prepare?_certified acceptedA)
  let cb := producedCompletion (prepare?_certified acceptedB)
  have counts : ∀ c, ca.hydrogenCount c = cb.hydrogenCount c := by
    intro c
    rw [produced_hydrogenCount,produced_hydrogenCount]
    exact totals c
  refine ⟨Completion.atomEquiv ca cb counts, ?_, Completion.atomEquiv_records ca cb counts,
    Completion.atomEquiv_bonds ca cb counts⟩
  intro c
  exact congrArg (fun v : cb.Vertex => v.val) (Completion.atomEquiv_core ca cb counts c)

assert_kernel_only prepared_spellings_bijection
assert_kernel_only tag_ordinary_iff
assert_kernel_only hydrogenCount_eq_ordinaryCount
assert_kernel_only produced_hydrogenCount
assert_kernel_only producedCompletion
assert_kernel_only certified_old_bond
assert_kernel_only certified_fresh_bond
end TetraStereo.OneCenter.OrdinaryHydrogenSpellings.Production

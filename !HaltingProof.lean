/- Inductive Types: Formula -/
inductive formula
| atom (SYMBOL : ℕ) : formula
| implication (ANTECEDENT CONSEQUENT : formula) : formula
export formula (atom implication)
notation #SYMBOL := formula.atom SYMBOL
notation ANTECEDENT >> CONSEQUENT := formula.implication ANTECEDENT CONSEQUENT
/- Instances of Decidability (Equality): Formula -/
instance formula.decidable_eq :
  ∀(f1 f2 : formula),
  ---------------------------------
  decidable (f1 = f2)
-- ATOM:
| (atom SBL1) (atom SBL2) := begin simp [eq.decidable], from @nat.decidable_eq SBL1 SBL2 end
| (atom _) (implication _ _) := begin simp [eq.decidable], from is_false not_false end
-- IMPLICATION:
| (implication _ _) (atom _) := begin simp [eq.decidable], from is_false not_false end
| (implication ANT1 CON1) (implication ANT2 CON2) := begin
  simp [eq.decidable],
  from @and.decidable (ANT1 = ANT2) (CON1 = CON2) (@formula.decidable_eq ANT1 ANT2) (@formula.decidable_eq CON1 CON2)
end

/- Inductive Types: DLDS-Node -/
inductive node
| vertex (LEVEL : ℕ)
         (LABEL : ℕ)
         (FORMULA : formula)
export node (vertex)
notation LEVEL && LABEL && FORMULA := node.vertex LEVEL LABEL FORMULA
/- Instances of Decidability (Equality): DLDS-Node -/
instance node.decidable_eq :
  ∀(n1 n2 : node),
  ---------------------------------
  decidable (n1 = n2)
-- VERTEX:
| (vertex LVL_1 LBL_1 FML_1) (vertex LVL_2 LBL_2 FML_2) := begin
  simp [eq.decidable],
  have decidable_and, from @and.decidable (LBL_1 = LBL_2)
                                          (FML_1 = FML_2)
                                          (@nat.decidable_eq LBL_1 LBL_2)
                                          (@formula.decidable_eq FML_1 FML_2),
  from @and.decidable (LVL_1 = LVL_2)
                      (LBL_1 = LBL_2 ∧ FML_1 = FML_2)
                      (@nat.decidable_eq LVL_1 LVL_2)
                      (decidable_and)
end
/- GET-Methods -/
def node.get_level : node → ℕ
| (vertex LEVEL LABEL FORMULA):= LEVEL
def node.get_label : node → ℕ
| (vertex LEVEL LABEL FORMULA):= LABEL
def node.get_formula : node → formula
| (vertex LEVEL LABEL FORMULA):= FORMULA

/- Inductive Types: Dag-Like Derivability Structure -/
inductive deduction
| arrow (START : node)
        (END : node)
        (COLOUR : list ℕ)
        (DEPENDENT : set formula)
export deduction (arrow)
--
inductive ancestral
| path (START : node)
       (END : node)
       (PATH : list ℕ)
export ancestral (path)
--
inductive neighborhood
| dag (CENTER : node)
      (IN : list deduction)
      (OUT : list deduction)
      (ANCESTRAL : list ancestral)
export neighborhood (dag)

/- Auxiliary Definitions: -/
/- Rewrite: -/
def node_rewrite : node → node → node → node
| NODE OLD NEW := if NODE = OLD then NEW else NODE
def list_node_rewrite : list node → node → node → list node
| [] OLD NEW := []
| (HEAD::TAIL) OLD NEW := (node_rewrite HEAD OLD NEW)::(list_node_rewrite TAIL OLD NEW)
--
def deduction_rewrite : deduction → node → node → deduction
| (arrow STR END CLR DEP) OLD NEW := arrow (node_rewrite STR OLD NEW)
                                           (node_rewrite END OLD NEW)
                                           CLR
                                           DEP
def list_deduction_rewrite : list deduction → node → node → list deduction
| [] OLD NEW := []
| (HEAD::TAIL) OLD NEW := (deduction_rewrite HEAD OLD NEW)::(list_deduction_rewrite TAIL OLD NEW)
--
def ancestral_rewrite : ancestral → node → node → ancestral
| (path STR END PTH) OLD NEW := path (node_rewrite STR OLD NEW)
                                     (node_rewrite END OLD NEW)
                                     PTH
def list_ancestral_rewrite : list ancestral → node → node → list ancestral
| [] OLD NEW := []
| (HEAD::TAIL) OLD NEW := (ancestral_rewrite HEAD OLD NEW)::(list_ancestral_rewrite TAIL OLD NEW)
--
def neighborhood_rewrite : neighborhood → node → node → neighborhood
| (dag CTR IN OUT ANC) OLD NEW := dag (node_rewrite CTR OLD NEW)
                                      (list_deduction_rewrite IN OLD NEW)
                                      (list_deduction_rewrite OUT OLD NEW)
                                      (list_ancestral_rewrite ANC OLD NEW)
/- Paint: -/
def colour_paint : list ℕ → ℕ → list ℕ
| COLOUR PAINT := if COLOUR = [] then [PAINT] else COLOUR
def deduction_paint : deduction → ℕ → deduction
| (arrow STR END CLR DEP) PAINT := arrow STR
                                         END
                                         (colour_paint CLR PAINT)
                                         DEP
def list_deduction_paint : list deduction → ℕ → list deduction
| [] PAINT := []
| (HEAD::TAIL) PAINT := (deduction_paint HEAD PAINT)::(list_deduction_paint TAIL PAINT)


/- Colapso Simples (sem Arestas de Ancestralidade): -/
/- Neighborhood: ⊇-Elimination -/
def case_neighborhood_01 : neighborhood → Prop
| (dag (vertex LVL LBL FML) IN OUT ANC) := ( ∃(antecedent out_form : formula),
                                             ∃(minor out_lbl : ℕ),
                                             ∃(dep_minor dep_major : set formula),
                                             ------------------------------------------------------
                                             IN = [ arrow (vertex (LVL+1) minor antecedent)
                                                          (vertex LVL LBL FML)
                                                          []
                                                          dep_minor,
                                                    arrow (vertex (LVL+1) (minor+1) (antecedent>>FML))
                                                          (vertex LVL LBL FML)
                                                          []
                                                          dep_major ]
                                           ∧ OUT = [ arrow (vertex LVL LBL FML)
                                                           (vertex (LVL-1) out_lbl out_form)
                                                           []
                                                           (dep_minor ∪ dep_major) ]
                                           ∧ ANC = [] )
/- Neighborhood: ⊇-Introduction -/
def case_neighborhood_02 : neighborhood → Prop
| (dag CTR IN OUT ANC) := ( ∃(antecedent consequent : formula),
                            ∃(level label intro : ℕ),
                            ∃(dep : set formula),
                            ∃(out : node),
                          ------------------------------------------------------
                            CTR = vertex level label (antecedent>>consequent)
                          ∧ IN = [arrow (vertex (level+1) intro antecedent) CTR [] {x | x = antecedent ∨ x ∈ dep}]
                          ∧ OUT = [arrow CTR out [] {x | x ≠ antecedent ∧ x ∈ dep}]
                          ∧ ANC = [] )
/- Neighborhood: Hypothesis -/
def case_neighborhood_03 : neighborhood → Prop
| (dag CTR IN OUT ANC) := ( ∃(hypothesis : formula),
                            ∃(level label : ℕ),
                            ∃(out : node),
                          ------------------------------------------------------
                            CTR = vertex level label hypothesis
                          ∧ IN = []
                          ∧ OUT = [arrow CTR out [] {hypothesis}]
                          ∧ ANC = [] )
/- Pre-Colapso Simples (sem Arestas de Ancestralidade): -/
def loop_simple_ancestral : ℕ → deduction → deduction → ancestral
| COLOUR
  (arrow IN_STR IN_END IN_CLR IN_DEP)
  (arrow OUT_STR OUT_END OUT_CLR OUT_DEP) := path OUT_END
                                                  IN_STR
                                                  [COLOUR]
def create_simple_ancestral : ℕ → list deduction → list deduction → list ancestral
| COLOUR (HEAD::TAIL) [OUT] := (loop_simple_ancestral COLOUR HEAD OUT)::(create_simple_ancestral COLOUR TAIL [OUT])
| COLOUR IN OUT := []
/- Neighborhood: Collapse -/
def simple_pre_collapse : neighborhood → neighborhood
| (dag (vertex LVL LBL FML) IN OUT ANC) := dag (vertex LVL LBL FML)
                                               IN
                                               (list_deduction_paint OUT LBL)
                                               (create_simple_ancestral LBL IN OUT)
def simple_horizontal_collapse : neighborhood → neighborhood → neighborhood
| (dag (vertex LVL_U LBL_U FML_U) IN_U OUT_U ANC_U)
  (dag (vertex LVL_V LBL_V FML_V) IN_V OUT_V ANC_V) := dag (vertex LVL_U LBL_U FML_U)
                                                           (   IN_U
                                                            ++ list_deduction_rewrite IN_V
                                                                                      (vertex LVL_V LBL_V FML_V)
                                                                                      (vertex LVL_U LBL_U FML_U)   )
                                                           (   (list_deduction_paint OUT_U LBL_U)
                                                            ++ list_deduction_rewrite (list_deduction_paint OUT_V LBL_V)
                                                                                      (vertex LVL_V LBL_V FML_V)
                                                                                      (vertex LVL_U LBL_U FML_U)   )
                                                           (   (create_simple_ancestral LBL_U IN_U OUT_U)
                                                            ++ list_ancestral_rewrite (create_simple_ancestral LBL_V IN_V OUT_V)
                                                                                      (vertex LVL_V LBL_V FML_V)
                                                                                      (vertex LVL_U LBL_U FML_U)   )
                                                                                      
/- Pre-Colapso Comum (sem Arestas de Ancestralidade): -/
def loop_loop_ancestral : deduction → deduction → ancestral
| (arrow IN_STR IN_END IN_CLR IN_DEP)
  (arrow OUT_STR OUT_END OUT_CLR OUT_DEP) := path OUT_END
                                                  IN_STR
                                                  OUT_CLR --AQUI!!!
def loop_ancestral : deduction → list deduction → list ancestral
| IN [] := []
| IN (HEAD::TAIL) := (loop_loop_ancestral IN HEAD)::(loop_ancestral IN TAIL)
def create_ancestral : list deduction → list deduction → list ancestral
| [] OUT := []
| (HEAD::TAIL) OUT := (loop_ancestral HEAD OUT) ++ (create_ancestral TAIL OUT)
/- Neighborhood: Type-1 Halfs -/
def case_neighborhood_04 : neighborhood → Prop
| (dag (vertex LVL LBL FML) IN OUT ANC) := ( IN = IN --AQUI!!!
                                           ∧ OUT = OUT --AQUI!!!
                                           ∧ list.length ANC = list.length IN
                                           ∧ ∀(a : ancestral), a ∈ ANC → a ∈ create_ancestral IN OUT )
                                           --∧ ANC = create_ancestral IN OUT )

/- Conditions for Collapse -/
def check_nodes : neighborhood → neighborhood → Prop
| (dag (vertex LVL_U LBL_U FML_U) IN_U OUT_U ANC_U)
  (dag (vertex LVL_V LBL_V FML_V) IN_V OUT_V ANC_V) := (LVL_U = LVL_V)
                                                     ∧ (LVL_U > 0)
                                                     ∧ (LVL_V > 0)
                                                     ∧ (LBL_U ≠ LBL_V)
                                                     ∧ (FML_U = FML_V)
/- NEW Rule: ⊇-Elimination = ⊇-Elimination -/
def case_01_01 : neighborhood → neighborhood → Prop
| U V := ( case_neighborhood_01 U )
       ∧ ( case_neighborhood_01 V )
def case_01_01S : neighborhood → neighborhood → Prop
| L R := case_01_01 R L
/- Rule 01: ⊇-Elimination = ⊇-Introduction -/
def case_01_02 : neighborhood → neighborhood → Prop
| U V := ( case_neighborhood_01 U )
       ∧ ( case_neighborhood_02 V )
def case_01_02S : neighborhood → neighborhood → Prop
| L R := case_01_02 R L
/- Rule 02: ⊇-Elimination = Hypothesis -/
def case_01_03 : neighborhood → neighborhood → Prop
| U V := ( case_neighborhood_01 U )
       ∧ ( case_neighborhood_03 V )
def case_01_03S : neighborhood → neighborhood → Prop
| L R := case_01_03 R L
/- NEW Rule: ⊇-Introduction = ⊇-Introduction -/
def case_02_02 : neighborhood → neighborhood → Prop
| U V := ( case_neighborhood_02 U )
       ∧ ( case_neighborhood_02 V )
def case_02_02S : neighborhood → neighborhood → Prop
| L R := case_02_02 R L
/- Rule 03: ⊇-Introduction = Hypothesis -/
def case_02_03 : neighborhood → neighborhood → Prop
| U V := ( case_neighborhood_02 U )
       ∧ ( case_neighborhood_03 V )
def case_02_03S : neighborhood → neighborhood → Prop
| L R := case_02_03 R L
/- Rule 04: Hypothesis = Hypothesis -/
def case_03_03 : neighborhood → neighborhood → Prop
| U V := ( case_neighborhood_03 U )
       ∧ ( case_neighborhood_03 V )
def case_03_03S : neighborhood → neighborhood → Prop
| L R := case_03_03 R L

/- Proof -/
lemma Lemma_Add :
  ∀{n : ℕ},
  ---------------------------
  ¬( n+1 = n )
| 0 := by simp
| (n+1) := begin
  rewrite[←nat.succ_eq_add_one (n+1)],
  rewrite[←nat.succ_eq_add_one n],
  simp at ⊢,
  from Lemma_Add
end

lemma Lemma_Sub :
  ∀{n : ℕ},
  ( n > 0 ) →
  ---------------------------
  ¬( n-1 = n )
| 0 := begin
  assume n_gt_zero,
  have not_n_gt_zero, from gt_irrefl 0,
  from false.elim (not_n_gt_zero n_gt_zero)
end
| (n+1) := begin
  assume n_gt_zero,
  rewrite[←nat.succ_eq_add_one n],
  simp at ⊢,
  have n_lt_succ, from nat.lt_succ_of_le (le_refl n),
  from ne_of_lt n_lt_succ
end

lemma Main_Lemma_01_01 :
  ∀(u v : neighborhood),
  ( check_nodes u v ) →
  ( case_01_01 u v ) →
  ---------------------------
  ( case_neighborhood_04 (simple_horizontal_collapse u v) )
| (dag (vertex LVL_U LBL_U FML_U) IN_U OUT_U ANC_U)
  (dag (vertex LVL_V LBL_V FML_V) IN_V OUT_V ANC_V) := begin
  assume prob_nodes prob_01_01,

  simp [check_nodes] at prob_nodes,
  cases prob_nodes with prob_eq_lvl prob_nodes,
  cases prob_nodes with prob_lvl_u prob_nodes,
  cases prob_nodes with prob_lvl_v prob_nodes,
  cases prob_nodes with prob_ne_lbl prob_eq_fml,

  simp [case_01_01] at prob_01_01,
  cases prob_01_01 with prob_u_01 prob_v_01,
  simp [simple_horizontal_collapse],

  simp [case_neighborhood_01] at prob_v_01,
  cases prob_v_01 with antecedent_v prob_v_01,
  cases prob_v_01 with out_form_v prob_v_01,
  cases prob_v_01 with minor_v prob_v_01,
  cases prob_v_01 with out_lbl_v prob_v_01,
  cases prob_v_01 with dep_minor_v prob_v_01,
  cases prob_v_01 with dep_major_v prob_v_01,
  cases prob_v_01 with prob_in_v prob_v_01,
  cases prob_v_01 with prob_out_v prob_anc_v,

  rewrite [prob_in_v],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Lemma_Add],

  rewrite [prob_out_v],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Lemma_Sub prob_lvl_v],
  
  simp [create_simple_ancestral, loop_simple_ancestral],
  simp [list_ancestral_rewrite, ancestral_rewrite],
  simp [node_rewrite, Lemma_Add, Lemma_Sub prob_lvl_v],

  simp [case_neighborhood_01] at prob_u_01,
  cases prob_u_01 with antecedent_u prob_u_01,
  cases prob_u_01 with out_form_u prob_u_01,
  cases prob_u_01 with minor_u prob_u_01,
  cases prob_u_01 with out_lbl_u prob_u_01,
  cases prob_u_01 with dep_minor_u prob_u_01,
  cases prob_u_01 with dep_major_u prob_u_01,
  cases prob_u_01 with prob_in_u prob_u_01,
  cases prob_u_01 with prob_out_u prob_anc_u,

  rewrite [prob_in_u, prob_out_u],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [create_simple_ancestral, loop_simple_ancestral],
  
  simp [case_neighborhood_04],
  simp [create_ancestral],
  simp [loop_ancestral],
  simp [loop_loop_ancestral],
  
  assume a a_cases,
  cases a_cases with a_case_01 a_cases,
  case or.inl { simp [a_case_01] },
  cases a_cases with a_case_02 a_cases,
  case or.inl { simp [a_case_02] },
  cases a_cases with a_case_03 a_case_04,
  case or.inl { simp [a_case_03] },
  case or.inr { simp [a_case_04] }
end

/- Tests -/
constants LVL_U LVL_V : ℕ
--def LVL_U : ℕ := 10
--def LVL_V : ℕ := 10
constants LBL_U LBL_V : ℕ
--def LBL_U : ℕ := 1
--def LBL_V : ℕ := 2
constants FML_U FML_V : formula
--def FML_U : formula := #1
--def FML_V : formula := #2
constants minor_u out_lbl_u : ℕ
--def minor_u : ℕ := 11
--def out_lbl_u : ℕ := 13
constants antecedent_u out_form_u : formula
--def antecedent_u : formula := #11
--def out_form_u : formula := #13
constants dep_minor_u dep_major_u : set formula
--def dep_minor_u : set formula := ∅
--def dep_major_u : set formula := ∅
constants minor_v out_lbl_v : ℕ
--def minor_v : ℕ := 21
--def out_lbl_v : ℕ := 23
constants antecedent_v out_form_v : formula
--def antecedent_v : formula := #21
--def out_form_v : formula := #23
constants dep_minor_v dep_major_v : set formula
--def dep_minor_v : set formula := ∅
--def dep_major_v : set formula := ∅

--create_ancestral
--  [ arrow ((LVL_U + 1)&&minor_u&&antecedent_u) (LVL_U&&LBL_U&&FML_U) [] dep_minor_u,
--    arrow ((LVL_U + 1)&&(minor_u + 1)&&antecedent_u>>FML_U) (LVL_U&&LBL_U&&FML_U) [] dep_major_u,
--    arrow ((LVL_V + 1)&&minor_v&&antecedent_v) (LVL_U&&LBL_U&&FML_U) [] dep_minor_v,
--	arrow ((LVL_V + 1)&&(minor_v + 1)&&antecedent_v>>FML_V) (LVL_U&&LBL_U&&FML_U) [] dep_major_v ]
--  [ arrow (LVL_U&&LBL_U&&FML_U) ((LVL_U - 1)&&out_lbl_u&&out_form_u) [LBL_U] (dep_minor_u ∪ dep_major_u),
--    arrow (LVL_U&&LBL_U&&FML_U) ((LVL_V - 1)&&out_lbl_v&&out_form_v) [LBL_V] (dep_minor_v ∪ dep_major_v) ]
--=
--[ path (nat.pred LVL_U&&out_lbl_u&&out_form_u) (nat.succ LVL_U&&minor_u&&antecedent_u) [LBL_U],
--  path (nat.pred LVL_V&&out_lbl_v&&out_form_v) (nat.succ LVL_U&&minor_u&&antecedent_u) [LBL_V],
--  path (nat.pred LVL_U&&out_lbl_u&&out_form_u) (nat.succ LVL_U&&nat.succ minor_u&&antecedent_u>>FML_U) [LBL_U],
--  path (nat.pred LVL_V&&out_lbl_v&&out_form_v) (nat.succ LVL_U&&nat.succ minor_u&&antecedent_u>>FML_U) [LBL_V],
--  path (nat.pred LVL_U&&out_lbl_u&&out_form_u) (nat.succ LVL_V&&minor_v&&antecedent_v) [LBL_U],
--  path (nat.pred LVL_V&&out_lbl_v&&out_form_v) (nat.succ LVL_V&&minor_v&&antecedent_v) [LBL_V],
--  path (nat.pred LVL_U&&out_lbl_u&&out_form_u) (nat.succ LVL_V&&nat.succ minor_v&&antecedent_v>>FML_V) [LBL_U],
--  path (nat.pred LVL_V&&out_lbl_v&&out_form_v) (nat.succ LVL_V&&nat.succ minor_v&&antecedent_v>>FML_V) [LBL_V] ]

def ANC := create_ancestral  [ arrow ((LVL_U + 1)&&minor_u&&antecedent_u) (LVL_U&&LBL_U&&FML_U) [] dep_minor_u, arrow ((LVL_U + 1)&&(minor_u + 1)&&antecedent_u>>FML_U) (LVL_U&&LBL_U&&FML_U) [] dep_major_u, arrow ((LVL_V + 1)&&minor_v&&antecedent_v) (LVL_U&&LBL_U&&FML_U) [] dep_minor_v, arrow ((LVL_V + 1)&&(minor_v + 1)&&antecedent_v>>FML_V) (LVL_U&&LBL_U&&FML_U) [] dep_major_v ]  [ arrow (LVL_U&&LBL_U&&FML_U) ((LVL_U - 1)&&out_lbl_u&&out_form_u) [LBL_U] (dep_minor_u ∪ dep_major_u), arrow (LVL_U&&LBL_U&&FML_U) ((LVL_V - 1)&&out_lbl_v&&out_form_v) [LBL_V] (dep_minor_v ∪ dep_major_v) ]

#check ANC
#print ANC
#reduce ANC

import init.data.nat
import init.data.set

/- Types -/
/- Inductive Types: Formula -/
inductive formula
| atom (SYMBOL : ℕ) : formula
| implication (ANTECEDENT CONSEQUENT : formula) : formula
export formula (atom implication)
notation #SYMBOL := formula.atom SYMBOL
notation ANTECEDENT >> CONSEQUENT := formula.implication ANTECEDENT CONSEQUENT
/- Instances of Decidability: Equality -/
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


/- Inductive Types: Dag-Like Derivability Structure -/
/- DLDS: Node -/
inductive node
| vertex (LEVEL : ℕ)
         (NUMBER : ℕ)
         (FORMULA : formula)
export node (vertex)
notation LEVEL && NUMBER && FORMULA := node.vertex LEVEL NUMBER FORMULA
/- Instances of Decidability: Equality -/
instance node.decidable_eq :
  ∀(n1 n2 : node),
  ---------------------------------
  decidable (n1 = n2)
-- VERTEX:
| (vertex LVL_1 NBR_1 FML_1) (vertex LVL_2 NBR_2 FML_2) := begin
  simp [eq.decidable],
  have decidable_and, from @and.decidable (NBR_1 = NBR_2)
                                          (FML_1 = FML_2)
                                          (@nat.decidable_eq NBR_1 NBR_2)
                                          (@formula.decidable_eq FML_1 FML_2),
  from @and.decidable (LVL_1 = LVL_2)
                      (NBR_1 = NBR_2 ∧ FML_1 = FML_2)
                      (@nat.decidable_eq LVL_1 LVL_2)
                      (decidable_and)
end


/- Inductive Types: Dag-Like Derivability Structure -/
/- DLDS: Deduction Edges -/
inductive deduction
| edge (START : node)
       (END : node)
       (COLOUR : list ℕ)
       (DEPENDENT : set formula)
export deduction (edge)
/- DLDS: Ancestral Edges -/
inductive ancestral
| path (START : node)
       (END : node)
       (PATH : list ℕ)
export ancestral (path)
/- DLDS: Neighborhoods -/
inductive neighborhood
| dag (CENTER : node)
      (IN : list deduction)
      (OUT : list deduction)
      (ANCESTRAL : list ancestral)
export neighborhood (dag)



/- Methods -/
/- Auxiliary Definitions: -/
/- Rewrite: Nodes -/
def node_rewrite : node → node → node → node
| NODE OLD NEW := if NODE = OLD then NEW else NODE
def list_node_rewrite : list node → node → node → list node
| [] OLD NEW := []
| (HEAD::TAIL) OLD NEW := (node_rewrite HEAD OLD NEW)::(list_node_rewrite TAIL OLD NEW)
/- Rewrite: Deduction Edges -/
def deduction_rewrite : deduction → node → node → deduction
| (edge STR END CLR DEP) OLD NEW := edge (node_rewrite STR OLD NEW)
                                         (node_rewrite END OLD NEW)
                                         CLR
                                         DEP
def list_deduction_rewrite : list deduction → node → node → list deduction
| [] OLD NEW := []
| (HEAD::TAIL) OLD NEW := (deduction_rewrite HEAD OLD NEW)::(list_deduction_rewrite TAIL OLD NEW)
/- Rewrite: Ancestral Edges -/
def ancestral_rewrite : ancestral → node → node → ancestral
| (path STR END PTH) OLD NEW := path (node_rewrite STR OLD NEW)
                                     (node_rewrite END OLD NEW)
                                     PTH
def list_ancestral_rewrite : list ancestral → node → node → list ancestral
| [] OLD NEW := []
| (HEAD::TAIL) OLD NEW := (ancestral_rewrite HEAD OLD NEW)::(list_ancestral_rewrite TAIL OLD NEW)
/- Rewrite: Neighborhoods -/
def neighborhood_rewrite : neighborhood → node → node → neighborhood
| (dag CTR IN OUT ANC) OLD NEW := dag (node_rewrite CTR OLD NEW)
                                      (list_deduction_rewrite IN OLD NEW)
                                      (list_deduction_rewrite OUT OLD NEW)
                                      (list_ancestral_rewrite ANC OLD NEW)
/- Paint: Deduction Edges -/
def colour_paint : list ℕ → ℕ → list ℕ
| COLOUR PAINT := if COLOUR = [] then [PAINT] else COLOUR
def deduction_paint : deduction → ℕ → deduction
| (edge STR END CLR DEP) PAINT := edge STR
                                       END
                                       (colour_paint CLR PAINT)
                                       DEP
def list_deduction_paint : list deduction → ℕ → list deduction
| [] PAINT := []
| (HEAD::TAIL) PAINT := (deduction_paint HEAD PAINT)::(list_deduction_paint TAIL PAINT)


/- Neighborhoods of Non-Collapsed Nodes (Without Incoming Ancestral Edges): -/
/- Neighborhood: Type 0 ⊇-Elimination -/
def elimination_neighborhood : neighborhood → Prop
| (dag (vertex LVL NBR FML) IN OUT ANC) := ( ∃(antecedent out_frm : formula),
                                             ∃(minor out_nbr : ℕ),
                                             ∃(minor_dep major_dep : set formula),
                                             ------------------------------------------------------
                                             IN = [ edge (vertex (LVL+1) minor antecedent)
                                                         (vertex LVL NBR FML)
                                                         []
                                                         minor_dep,
                                                    edge (vertex (LVL+1) (minor+1) (antecedent>>FML))
                                                         (vertex LVL NBR FML)
                                                         []
                                                         major_dep ]
                                           ∧ OUT = [ edge (vertex LVL NBR FML)
                                                          (vertex (LVL-1) out_nbr out_frm)
                                                          []
                                                          (minor_dep ∪ major_dep) ]
                                           ∧ ANC = [] )
/- Neighborhood: Type 0 ⊇-Introduction -/
def introduction_neighborhood : neighborhood → Prop
| (dag (vertex LVL NBR FML) IN OUT ANC) := ( ∃(antecedent consequent out_frm : formula),
                                             ∃(intro out_nbr : ℕ),
                                             ∃(dep : set formula),
                                           ------------------------------------------------------
                                             FML = antecedent>>consequent
                                           ∧ IN = [ edge (vertex (LVL+1) intro antecedent)
                                                          (vertex LVL NBR FML)
                                                          []
                                                          {x | x = antecedent ∨ x ∈ dep} ]
                                           ∧ OUT = [edge (vertex LVL NBR FML)
                                                         (vertex (LVL-1) out_nbr out_frm)
                                                         []
                                                         {x | x ≠ antecedent ∧ x ∈ dep} ]
                                           ∧ ANC = [] )
/- Neighborhood: Type 0 Hypothesis -/
def hypothesis_neighborhood : neighborhood → Prop
| (dag (vertex LVL NBR FML) IN OUT ANC) := ( ∃(out_frm : formula),
                                             ∃(out_nbr : ℕ),
                                           ------------------------------------------------------
                                             IN = []
                                           ∧ OUT = [edge (vertex LVL NBR FML)
                                                         (vertex (LVL-1) out_nbr out_frm)
                                                         []
                                                         {FML} ]
                                           ∧ ANC = [] )


/- Colapse: -/
/- Conditions for Collapse -/
def check_nodes : neighborhood → neighborhood → Prop
| (dag (vertex LVL_U NBR_U FML_U) IN_U OUT_U ANC_U)
  (dag (vertex LVL_V NBR_V FML_V) IN_V OUT_V ANC_V) := (LVL_U = LVL_V)
                                                     ∧ (LVL_U > 0)
                                                     ∧ (LVL_V > 0)
                                                     ∧ (NBR_U ≠ NBR_V)
                                                     ∧ (FML_U = FML_V)
/- Colapse: Ancestral Edges-/
def loop_ancestral : ℕ → deduction → deduction → ancestral
| COLOUR
  (edge IN_STR IN_END IN_CLR IN_DEP)
  (edge OUT_STR OUT_END OUT_CLR OUT_DEP) := path OUT_END
                                                 IN_STR
                                                 [COLOUR]
def create_ancestral : ℕ → list deduction → list deduction → list ancestral
| COLOUR (HEAD::TAIL) [OUT] := (loop_ancestral COLOUR HEAD OUT)::(create_ancestral COLOUR TAIL [OUT])
| COLOUR IN OUT := []
/- Collapse: Neighborhoods -/
def pre_collapse : neighborhood → neighborhood
| (dag (vertex LVL NBR FML) IN OUT ANC) := dag (vertex LVL NBR FML)
                                               IN
                                               (list_deduction_paint OUT NBR)
                                               (create_ancestral NBR IN OUT)
def horizontal_collapse : neighborhood → neighborhood → neighborhood
| (dag (vertex LVL_U NBR_U FML_U) IN_U OUT_U ANC_U)
  (dag (vertex LVL_V NBR_V FML_V) IN_V OUT_V ANC_V) := dag (vertex LVL_U NBR_U FML_U)
                                                           (   IN_U
                                                            ++ list_deduction_rewrite IN_V
                                                                                      (vertex LVL_V NBR_V FML_V)
                                                                                      (vertex LVL_U NBR_U FML_U)   )
                                                           (   (list_deduction_paint OUT_U NBR_U)
                                                            ++ list_deduction_rewrite (list_deduction_paint OUT_V NBR_V)
                                                                                      (vertex LVL_V NBR_V FML_V)
                                                                                      (vertex LVL_U NBR_U FML_U)   )
                                                           (   (create_ancestral NBR_U IN_U OUT_U)
                                                            ++ list_ancestral_rewrite (create_ancestral NBR_V IN_V OUT_V)
                                                                                      (vertex LVL_V NBR_V FML_V)
                                                                                      (vertex LVL_U NBR_U FML_U)   )


/- Neighborhoods of Collapsed Nodes Without Incoming Ancestral Edges: -/
/- Neighborhood: Type 1 Ancestral Edges -/
def loop_loop_ancestral_set : deduction → deduction → ancestral
| (edge IN_STR IN_END IN_CLR IN_DEP)
  (edge OUT_STR OUT_END OUT_CLR OUT_DEP) := path OUT_END
                                                 IN_STR
                                                 OUT_CLR
def loop_ancestral_set : deduction → list deduction → list ancestral
| IN [] := []
| IN (HEAD::TAIL) := (loop_loop_ancestral_set IN HEAD)::(loop_ancestral_set IN TAIL)
def ancestral_set : list deduction → list deduction → list ancestral
| [] OUT := []
| (HEAD::TAIL) OUT := (loop_ancestral_set HEAD OUT) ++ (ancestral_set TAIL OUT)
/- Neighborhood: Type 1 Collapsed Node -/
def neighborhood_type_01 : neighborhood → Prop
| (dag (vertex LVL NBR FML) IN OUT ANC) := ( IN = IN
                                           ∧ OUT = OUT
                                           ∧ list.length ANC = list.length IN
                                           ∧ ∀(a : ancestral), a ∈ ANC → a ∈ ancestral_set IN OUT )



/- Proofs -/
lemma Add_Lemma :
  ∀{n : ℕ},
  ---------------------------
  ¬( n+1 = n )
| 0 := begin
  rewrite[nat.add_one 0],
  from nat.one_ne_zero,
end
| (n+1) := begin
  rewrite[←nat.succ_eq_add_one (n+1)],
  rewrite[←nat.succ_eq_add_one n],
  simp at ⊢,
  from Add_Lemma,
end
lemma Sub_Lemma :
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

/- Proof Steps: -/
/- Rule 1: ⊇-Introduction = ⊇-Elimination -/
theorem Main_Theorem_Rule_01 :
  ∀(u v : neighborhood),
  ( check_nodes u v ) →
  ( introduction_neighborhood u ) →
  ( elimination_neighborhood v ) →
  ---------------------------
  ( neighborhood_type_01 (horizontal_collapse u v) )
| (dag (vertex LVL_U NBR_U FML_U) IN_U OUT_U ANC_U)
  (dag (vertex LVL_V NBR_V FML_V) IN_V OUT_V ANC_V) := begin
  assume prop_nodes prop_u prop_v,

  simp [check_nodes] at prop_nodes,
  cases prop_nodes with prop_eq_lvl prop_nodes,
  cases prop_nodes with prop_lvl_u prop_nodes,
  cases prop_nodes with prop_lvl_v prop_nodes,
  cases prop_nodes with prop_ne_nbr prop_eq_fml,

  simp [horizontal_collapse],

  simp [elimination_neighborhood] at prop_v,
  cases prop_v with antecedent_v prop_v,
  cases prop_v with out_frm_v prop_v,
  cases prop_v with minor_v prop_v,
  cases prop_v with out_nbr_v prop_v,
  cases prop_v with minor_dep_v prop_v,
  cases prop_v with major_dep_v prop_v,
  cases prop_v with prop_in_v prop_v,
  cases prop_v with prop_out_v prop_anc_v,

  rewrite [prop_in_v],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Add_Lemma],

  rewrite [prop_out_v],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Sub_Lemma prop_lvl_v],

  simp [create_ancestral, loop_ancestral],
  simp [list_ancestral_rewrite, ancestral_rewrite],
  simp [node_rewrite, Add_Lemma, Sub_Lemma prop_lvl_v],

  simp [introduction_neighborhood] at prop_u,
  cases prop_u with antecedent_u prop_u,
  cases prop_u with consequent_u prop_u,
  cases prop_u with out_frm_u prop_u,
  cases prop_u with intro_u prop_u,
  cases prop_u with out_nbr_u prop_u,
  cases prop_u with dep_u prop_u,
  cases prop_u with prop_fml_u prop_u,
  cases prop_u with prop_in_u prop_u,
  cases prop_u with prop_out_u prop_anc_u,

  rewrite [prop_in_u, prop_out_u],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [create_ancestral, loop_ancestral],
  
  simp [neighborhood_type_01],
  simp [ancestral_set],
  simp [loop_ancestral_set],
  simp [loop_loop_ancestral_set],
  
  assume a a_cases,
  cases a_cases with a_case_01 a_cases,
  case or.inl { simp [a_case_01] },
  cases a_cases with a_case_02 a_case_03,
  case or.inl { simp [a_case_02] },
  case or.inr { simp [a_case_03] },
end
/- Rule 2: Hypothesis = ⊇-Elimination -/
theorem Main_Theorem_Rule_02 :
  ∀(u v : neighborhood),
  ( check_nodes u v ) →
  ( hypothesis_neighborhood u ) →
  ( elimination_neighborhood v ) →
  ---------------------------
  ( neighborhood_type_01 (horizontal_collapse u v) )
| (dag (vertex LVL_U NBR_U FML_U) IN_U OUT_U ANC_U)
  (dag (vertex LVL_V NBR_V FML_V) IN_V OUT_V ANC_V) := begin
  assume prop_nodes prop_u prop_v,

  simp [check_nodes] at prop_nodes,
  cases prop_nodes with prop_eq_lvl prop_nodes,
  cases prop_nodes with prop_lvl_u prop_nodes,
  cases prop_nodes with prop_lvl_v prop_nodes,
  cases prop_nodes with prop_ne_nbr prop_eq_fml,

  simp [horizontal_collapse],

  simp [elimination_neighborhood] at prop_v,
  cases prop_v with antecedent_v prop_v,
  cases prop_v with out_frm_v prop_v,
  cases prop_v with minor_v prop_v,
  cases prop_v with out_nbr_v prop_v,
  cases prop_v with minor_dep_v prop_v,
  cases prop_v with major_dep_v prop_v,
  cases prop_v with prop_in_v prop_v,
  cases prop_v with prop_out_v prop_anc_v,

  rewrite [prop_in_v],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Add_Lemma],

  rewrite [prop_out_v],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Sub_Lemma prop_lvl_v],
  
  simp [create_ancestral, loop_ancestral],
  simp [list_ancestral_rewrite, ancestral_rewrite],
  simp [node_rewrite, Add_Lemma, Sub_Lemma prop_lvl_v],

  simp [hypothesis_neighborhood] at prop_u,
  cases prop_u with out_frm_u prop_u,
  cases prop_u with out_nbr_u prop_u,
  cases prop_u with prop_in_u prop_u,
  cases prop_u with prop_out_u prop_anc_u,

  rewrite [prop_in_u, prop_out_u],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [create_ancestral, loop_ancestral],
  
  simp [neighborhood_type_01],
  simp [ancestral_set],
  simp [loop_ancestral_set],
  simp [loop_loop_ancestral_set],
  
  assume a a_cases,
  cases a_cases with a_case_01 a_case_02,
  case or.inl { simp [a_case_01] },
  case or.inr { simp [a_case_02] },
end
/- Rule 3: ⊇-Introduction = Hypothesis -/
theorem Main_Theorem_Rule_03 :
  ∀(u v : neighborhood),
  ( check_nodes u v ) →
  ( introduction_neighborhood u ) →
  ( hypothesis_neighborhood v ) →
  ---------------------------
  ( neighborhood_type_01 (horizontal_collapse u v) )
| (dag (vertex LVL_U NBR_U FML_U) IN_U OUT_U ANC_U)
  (dag (vertex LVL_V NBR_V FML_V) IN_V OUT_V ANC_V) := begin
  assume prop_nodes prop_u prop_v,

  simp [check_nodes] at prop_nodes,
  cases prop_nodes with prop_eq_lvl prop_nodes,
  cases prop_nodes with prop_lvl_u prop_nodes,
  cases prop_nodes with prop_lvl_v prop_nodes,
  cases prop_nodes with prop_ne_nbr prop_eq_fml,

  simp [horizontal_collapse],

  simp [hypothesis_neighborhood] at prop_v,
  cases prop_v with out_frm_v prop_v,
  cases prop_v with out_nbr_v prop_v,
  cases prop_v with prop_in_v prop_v,
  cases prop_v with prop_out_v prop_anc_v,

  rewrite [prop_in_v],
  simp [list_deduction_rewrite, deduction_rewrite],

  rewrite [prop_out_v],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Sub_Lemma prop_lvl_v],
  
  simp [create_ancestral, loop_ancestral],
  simp [list_ancestral_rewrite, ancestral_rewrite],

  simp [introduction_neighborhood] at prop_u,
  cases prop_u with antecedent_u prop_u,
  cases prop_u with consequent_u prop_u,
  cases prop_u with out_frm_u prop_u,
  cases prop_u with intro_u prop_u,
  cases prop_u with out_nbr_u prop_u,
  cases prop_u with dep_u prop_u,
  cases prop_u with prop_fml_u prop_u,
  cases prop_u with prop_in_u prop_u,
  cases prop_u with prop_out_u prop_anc_u,

  rewrite [prop_in_u, prop_out_u],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [create_ancestral, loop_ancestral],
  
  simp [neighborhood_type_01],
  simp [ancestral_set],
  simp [loop_ancestral_set],
  simp [loop_loop_ancestral_set],
  
  assume a a_cases,
  simp [a_cases],
end
/- Rule 4: Hypothesis = Hypothesis -/
theorem Main_Theorem_Rule_04 :
  ∀(u v : neighborhood),
  ( check_nodes u v ) →
  ( hypothesis_neighborhood u ) →
  ( hypothesis_neighborhood v ) →
  ---------------------------
  ( neighborhood_type_01 (horizontal_collapse u v) )
| (dag (vertex LVL_U NBR_U FML_U) IN_U OUT_U ANC_U)
  (dag (vertex LVL_V NBR_V FML_V) IN_V OUT_V ANC_V) := begin
  assume prop_nodes prop_u prop_v,

  simp [check_nodes] at prop_nodes,
  cases prop_nodes with prop_eq_lvl prop_nodes,
  cases prop_nodes with prop_lvl_u prop_nodes,
  cases prop_nodes with prop_lvl_v prop_nodes,
  cases prop_nodes with prop_ne_nbr prop_eq_fml,

  simp [horizontal_collapse],

  simp [hypothesis_neighborhood] at prop_v,
  cases prop_v with out_frm_v prop_v,
  cases prop_v with out_nbr_v prop_v,
  cases prop_v with prop_in_v prop_v,
  cases prop_v with prop_out_v prop_anc_v,

  rewrite [prop_in_v],
  simp [list_deduction_rewrite, deduction_rewrite],

  rewrite [prop_out_v],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Sub_Lemma prop_lvl_v],
  
  simp [create_ancestral, loop_ancestral],
  simp [list_ancestral_rewrite, ancestral_rewrite],

  simp [hypothesis_neighborhood] at prop_u,
  cases prop_u with out_frm_u prop_u,
  cases prop_u with out_nbr_u prop_u,
  cases prop_u with prop_in_u prop_u,
  cases prop_u with prop_out_u prop_anc_u,

  rewrite [prop_in_u, prop_out_u],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [create_ancestral, loop_ancestral],
  
  simp [neighborhood_type_01],
end
/- New Rule 1: ⊇-Elimination = ⊇-Elimination -/
theorem Main_Theorem_New_Rule_01 :
  ∀(u v : neighborhood),
  ( check_nodes u v ) →
  ( elimination_neighborhood u ) →
  ( elimination_neighborhood v ) →
  ---------------------------
  ( neighborhood_type_01 (horizontal_collapse u v) )
| (dag (vertex LVL_U NBR_U FML_U) IN_U OUT_U ANC_U)
  (dag (vertex LVL_V NBR_V FML_V) IN_V OUT_V ANC_V) := begin
  assume prop_nodes prop_u prop_v,

  simp [check_nodes] at prop_nodes,
  cases prop_nodes with prop_eq_lvl prop_nodes,
  cases prop_nodes with prop_lvl_u prop_nodes,
  cases prop_nodes with prop_lvl_v prop_nodes,
  cases prop_nodes with prop_ne_nbr prop_eq_fml,

  simp [horizontal_collapse],

  simp [elimination_neighborhood] at prop_v,
  cases prop_v with antecedent_v prop_v,
  cases prop_v with out_frm_v prop_v,
  cases prop_v with minor_v prop_v,
  cases prop_v with out_nbr_v prop_v,
  cases prop_v with minor_dep_v prop_v,
  cases prop_v with major_dep_v prop_v,
  cases prop_v with prop_in_v prop_v,
  cases prop_v with prop_out_v prop_anc_v,

  rewrite [prop_in_v],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Add_Lemma],

  rewrite [prop_out_v],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Sub_Lemma prop_lvl_v],
  
  simp [create_ancestral, loop_ancestral],
  simp [list_ancestral_rewrite, ancestral_rewrite],
  simp [node_rewrite, Add_Lemma, Sub_Lemma prop_lvl_v],

  simp [elimination_neighborhood] at prop_u,
  cases prop_u with antecedent_u prop_u,
  cases prop_u with out_frm_u prop_u,
  cases prop_u with minor_u prop_u,
  cases prop_u with out_nbr_u prop_u,
  cases prop_u with minor_dep_u prop_u,
  cases prop_u with major_dep_u prop_u,
  cases prop_u with prop_in_u prop_u,
  cases prop_u with prop_out_u prop_anc_u,

  rewrite [prop_in_u, prop_out_u],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [create_ancestral, loop_ancestral],
  
  simp [neighborhood_type_01],
  simp [ancestral_set],
  simp [loop_ancestral_set],
  simp [loop_loop_ancestral_set],
  
  assume a a_cases,
  cases a_cases with a_case_01 a_cases,
  case or.inl { simp [a_case_01] },
  cases a_cases with a_case_02 a_cases,
  case or.inl { simp [a_case_02] },
  cases a_cases with a_case_03 a_case_04,
  case or.inl { simp [a_case_03] },
  case or.inr { simp [a_case_04] },
end
/- New Rule 2: ⊇-Introduction = ⊇-Introduction -/
theorem Main_Theorem_New_Rule_02 :
  ∀(u v : neighborhood),
  ( check_nodes u v ) →
  ( introduction_neighborhood u ) →
  ( introduction_neighborhood v ) →
  ---------------------------
  ( neighborhood_type_01 (horizontal_collapse u v) )
| (dag (vertex LVL_U NBR_U FML_U) IN_U OUT_U ANC_U)
  (dag (vertex LVL_V NBR_V FML_V) IN_V OUT_V ANC_V) := begin
  assume prop_nodes prop_u prop_v,

  simp [check_nodes] at prop_nodes,
  cases prop_nodes with prop_eq_lvl prop_nodes,
  cases prop_nodes with prop_lvl_u prop_nodes,
  cases prop_nodes with prop_lvl_v prop_nodes,
  cases prop_nodes with prop_ne_nbr prop_eq_fml,

  simp [horizontal_collapse],

  simp [introduction_neighborhood] at prop_v,
  cases prop_v with antecedent_v prop_v,
  cases prop_v with consequent_v prop_v,
  cases prop_v with out_frm_v prop_v,
  cases prop_v with intro_v prop_v,
  cases prop_v with out_nbr_v prop_v,
  cases prop_v with dep_v prop_v,
  cases prop_v with prop_fml_v prop_v,
  cases prop_v with prop_in_v prop_v,
  cases prop_v with prop_out_v prop_anc_v,

  rewrite [prop_in_v],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Add_Lemma],

  rewrite [prop_out_v],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [list_deduction_rewrite, deduction_rewrite],
  simp [node_rewrite, Sub_Lemma prop_lvl_v],
  
  simp [create_ancestral, loop_ancestral],
  simp [list_ancestral_rewrite, ancestral_rewrite],
  simp [node_rewrite, Add_Lemma, Sub_Lemma prop_lvl_v],

  simp [introduction_neighborhood] at prop_u,
  cases prop_u with antecedent_u prop_u,
  cases prop_u with consequent_u prop_u,
  cases prop_u with out_frm_u prop_u,
  cases prop_u with intro_u prop_u,
  cases prop_u with out_nbr_u prop_u,
  cases prop_u with dep_u prop_u,
  cases prop_u with prop_fml_u prop_u,
  cases prop_u with prop_in_u prop_u,
  cases prop_u with prop_out_u prop_anc_u,

  rewrite [prop_in_u, prop_out_u],
  simp [list_deduction_paint, deduction_paint, colour_paint],
  simp [create_ancestral, loop_ancestral],
  
  simp [neighborhood_type_01],
  simp [ancestral_set],
  simp [loop_ancestral_set],
  simp [loop_loop_ancestral_set],
  
  assume a a_cases,
  cases a_cases with a_case_01 a_case_02,
  case or.inl { simp [a_case_01] },
  case or.inr { simp [a_case_02] },
end



/- Tests -/
constants LVL_U LVL_V : ℕ
--def LVL_U : ℕ := 10
--def LVL_V : ℕ := 10
constants NBR_U NBR_V : ℕ
--def NBR_U : ℕ := 1
--def NBR_V : ℕ := 2
constants FML_U FML_V : formula
--def FML_U : formula := #1
--def FML_V : formula := #2
constants minor_u out_nbr_u : ℕ
--def minor_u : ℕ := 11
--def out_nbr_u : ℕ := 13
constants antecedent_u out_frm_u : formula
--def antecedent_u : formula := #11
--def out_frm_u : formula := #13
constants minor_dep_u major_dep_u : set formula
--def minor_dep_u : set formula := ∅
--def major_dep_u : set formula := ∅
constants minor_v out_nbr_v : ℕ
--def minor_v : ℕ := 21
--def out_nbr_v : ℕ := 23
constants antecedent_v out_frm_v : formula
--def antecedent_v : formula := #21
--def out_frm_v : formula := #23
constants minor_dep_v major_dep_v : set formula
--def minor_dep_v : set formula := ∅
--def major_dep_v : set formula := ∅

--ancestral_set
--  [ edge ((LVL_U + 1)&&minor_u&&antecedent_u) (LVL_U&&NBR_U&&FML_U) [] minor_dep_u,
--    edge ((LVL_U + 1)&&(minor_u + 1)&&antecedent_u>>FML_U) (LVL_U&&NBR_U&&FML_U) [] major_dep_u,
--    edge ((LVL_V + 1)&&minor_v&&antecedent_v) (LVL_U&&NBR_U&&FML_U) [] minor_dep_v,
--	edge ((LVL_V + 1)&&(minor_v + 1)&&antecedent_v>>FML_V) (LVL_U&&NBR_U&&FML_U) [] major_dep_v ]
--  [ edge (LVL_U&&NBR_U&&FML_U) ((LVL_U - 1)&&out_nbr_u&&out_frm_u) [NBR_U] (minor_dep_u ∪ major_dep_u),
--    edge (LVL_U&&NBR_U&&FML_U) ((LVL_V - 1)&&out_nbr_v&&out_frm_v) [NBR_V] (minor_dep_v ∪ major_dep_v) ]
--=
--[ path (nat.pred LVL_U&&out_nbr_u&&out_frm_u) (nat.succ LVL_U&&minor_u&&antecedent_u) [NBR_U],
--  path (nat.pred LVL_V&&out_nbr_v&&out_frm_v) (nat.succ LVL_U&&minor_u&&antecedent_u) [NBR_V],
--  path (nat.pred LVL_U&&out_nbr_u&&out_frm_u) (nat.succ LVL_U&&nat.succ minor_u&&antecedent_u>>FML_U) [NBR_U],
--  path (nat.pred LVL_V&&out_nbr_v&&out_frm_v) (nat.succ LVL_U&&nat.succ minor_u&&antecedent_u>>FML_U) [NBR_V],
--  path (nat.pred LVL_U&&out_nbr_u&&out_frm_u) (nat.succ LVL_V&&minor_v&&antecedent_v) [NBR_U],
--  path (nat.pred LVL_V&&out_nbr_v&&out_frm_v) (nat.succ LVL_V&&minor_v&&antecedent_v) [NBR_V],
--  path (nat.pred LVL_U&&out_nbr_u&&out_frm_u) (nat.succ LVL_V&&nat.succ minor_v&&antecedent_v>>FML_V) [NBR_U],
--  path (nat.pred LVL_V&&out_nbr_v&&out_frm_v) (nat.succ LVL_V&&nat.succ minor_v&&antecedent_v>>FML_V) [NBR_V] ]

def ANC := ancestral_set  [ edge ((LVL_U + 1)&&minor_u&&antecedent_u) (LVL_U&&NBR_U&&FML_U) [] minor_dep_u, edge ((LVL_U + 1)&&(minor_u + 1)&&antecedent_u>>FML_U) (LVL_U&&NBR_U&&FML_U) [] major_dep_u, edge ((LVL_V + 1)&&minor_v&&antecedent_v) (LVL_U&&NBR_U&&FML_U) [] minor_dep_v, edge ((LVL_V + 1)&&(minor_v + 1)&&antecedent_v>>FML_V) (LVL_U&&NBR_U&&FML_U) [] major_dep_v ]  [ edge (LVL_U&&NBR_U&&FML_U) ((LVL_U - 1)&&out_nbr_u&&out_frm_u) [NBR_U] (minor_dep_u ∪ major_dep_u), edge (LVL_U&&NBR_U&&FML_U) ((LVL_V - 1)&&out_nbr_v&&out_frm_v) [NBR_V] (minor_dep_v ∪ major_dep_v) ]

#check ANC
#print ANC
#reduce ANC

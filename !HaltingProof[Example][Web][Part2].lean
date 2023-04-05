/- A continuation of !HaltingProof[Example][Web][Part1].lean -/

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
  simp [ancestral_set],

  assume a a_cases,
  from false.elim a_cases,
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

/- Cotinues at !HaltingProof[Example][Web][Part3].lean -/

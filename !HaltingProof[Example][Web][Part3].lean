/- A continuation of !HaltingProof[Example][Web][Part2].lean -/

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

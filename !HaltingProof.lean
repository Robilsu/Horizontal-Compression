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
| vertex (NUMBER : ℕ)
         (FORMULA : formula)
export node (vertex)
notation NUMBER :: FORMULA := node.vertex NUMBER FORMULA
/- Instances of Decidability (Equality): DLDS-Node -/
instance node.decidable_eq :
  ∀(n1 n2 : node),
  ---------------------------------
  decidable (n1 = n2)
-- VERTEX:
| (vertex NBR_1 FML_1) (vertex NBR_2 FML_2) := begin
  simp [eq.decidable],
  from @and.decidable (NBR_1 = NBR_2)
                      (FML_1 = FML_2)
                      (@nat.decidable_eq NBR_1 NBR_2)
                      (@formula.decidable_eq FML_1 FML_2)
end

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
| (dag CTR IN OUT ANC) := ( ∃(antecedent consequent : formula),
                            ∃(center minor major : ℕ),
                            ∃(dep_minor dep_major : set formula),
                            ∃(out : node),
                          ------------------------------------------------------
                            CTR = center::consequent
                          ∧ IN = [ arrow (minor::antecedent) CTR [] dep_minor,
                                   arrow (major::(antecedent>>consequent)) CTR [] dep_major ]
                          ∧ OUT = [(arrow CTR out [] (dep_minor ∪ dep_major))]
                          ∧ ANC = [] )
/- Neighborhood: ⊇-Introduction -/
def case_neighborhood_02 : neighborhood → Prop
| (dag CTR IN OUT ANC) := ( ∃(antecedent consequent : formula),
                            ∃(center intro : ℕ),
                            ∃(dep : set formula),
                            ∃(out : node),
                          ------------------------------------------------------
                            CTR = center::(antecedent>>consequent)
                          ∧ IN = [arrow (intro::antecedent) CTR [] {x | x = antecedent ∨ x ∈ dep}]
                          ∧ OUT = [arrow CTR out [] {x | x ≠ antecedent ∧ x ∈ dep}]
                          ∧ ANC = [] )
/- Neighborhood: Hypothesis -/
def case_neighborhood_03 : neighborhood → Prop
| (dag CTR IN OUT ANC) := ( ∃(hypothesis : formula),
                            ∃(center : ℕ),
                            ∃(out : node),
                          ------------------------------------------------------
                            CTR = center::hypothesis
                          ∧ IN = []
                          ∧ OUT = [arrow CTR out [] {hypothesis}]
                          ∧ ANC = [] )
/- Pre-Colapso Simples (sem Arestas de Ancestralidade): -/
def node.get_number : node → ℕ
| (NUMBER::FORMULA):= NUMBER
def loop_create_ancestral : deduction → deduction → ancestral
| (arrow IN_STR IN_END IN_CLR IN_DEP)
  (arrow OUT_STR OUT_END OUT_CLR OUT_DEP) := path OUT_END
                                                  IN_STR
                                                  [node.get_number OUT_END]
def simple_create_ancestral : list deduction → list deduction → list ancestral
| (HEAD::TAIL) [OUT] := (loop_create_ancestral HEAD OUT)::(simple_create_ancestral TAIL [OUT])
| IN OUT := []
def simple_pre_collapse : neighborhood → neighborhood
| (dag (NBR::FML) IN OUT ANC) := dag (NBR::FML)
                                     IN
                                     (list_deduction_paint OUT NBR)
                                     (simple_create_ancestral IN OUT)

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


/- Colapso Simples (com Arestas de Ancestralidade): -/
/- Rule 05 -/
--BUGADO!! A regra não está genérica o bastante (paper do hermann)...


/- Colapso de Arestas de Ancestralidade Incidentes: -/


/- Colapso de Arestas de Dedução: -/
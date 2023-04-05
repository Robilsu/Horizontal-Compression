import init.data.nat
import init.data.set

namespace set
  universes u
  variables {α : Type u}
  def set_union (s₁ s₂ : set α) : set α := {a | a ∈ s₁ ∨ a ∈ s₂}
  instance : has_union (set α) := ⟨set_union⟩
end set

/- Types -/
/- Inductive Types: Formula -/
inductive formula
| atom (SYMBOL : ℕ) : formula
| implication (ANTECEDENT CONSEQUENT : formula) : formula
export formula (atom implication)
notation (name := FORMULA_01) #SYMBOL := formula.atom SYMBOL
notation (name := FORMULA_02) ANTECEDENT >> CONSEQUENT := formula.implication ANTECEDENT CONSEQUENT
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
notation (name := NODE_03) LEVEL && NUMBER && FORMULA := node.vertex LEVEL NUMBER FORMULA
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

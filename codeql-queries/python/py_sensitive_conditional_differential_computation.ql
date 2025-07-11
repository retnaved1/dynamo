/**
 * @name Branching on sensitive data leading to differential computation
 * @description Detects if statements where the condition involves sensitive data,
 *              and the branches perform significantly different amounts of computation
 *              (heuristically measured by number of AST nodes or specific calls).
 *              This could be exploited in a timing attack.
 * @kind path-problem
 * @problem.severity warning
 * @id py/sensitive-conditional-differential-computation
 * @tags security
 *       external/cwe/cwe-208
 *       external/cwe/cwe-703
 */

import python
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking

// Heuristic to identify sensitive data sources
class SensitiveSource extends DataFlow::Node {
  SensitiveSource() {
    exists(NameNode name | name = this.asName() |
      name.getId().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
    or
    exists(Function f, Parameter param | this.asParameter() = param and f = param.getFunction() |
      f.getName().regexpMatch("(?i).*(authenticate|login|verify|authorize|decrypt|check_password).*") and
      param.getName().regexpMatch("(?i).*(password|secret|token|key|data).*")
    )
  }
}

// Configuration for taint tracking
class ConditionalComputationConfig extends TaintTracking::Configuration {
  ConditionalComputationConfig() { this = "ConditionalComputationConfig" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveSource
  }

  override predicate isSink(DataFlow::Node sink) {
    // Sink is the condition of an If or IfExp
    exists(ConditionalNode condNode | sink.asCfgNode() = condNode.getTest() |
      // Heuristic: check if branches have significantly different number of AST nodes
      // This is a rough proxy for computational difference.
      // A more sophisticated check might look for specific expensive operations.
      let thenBody = condNode.getThen().(Block).getAStmt() and
      let elseBody = condNode.getElse().(Block).getAStmt() in
      (count(thenBody.getAstNode().getDescendant()) > 2 * count(elseBody.getAstNode().getDescendant()) or
       count(elseBody.getAstNode().getDescendant()) > 2 * count(thenBody.getAstNode().getDescendant()))
      // Or one branch has a return and the other continues with more computation
      or
      exists(Stmt thenStmt, Stmt elseStmt |
        thenStmt = condNode.getThen().(Block).getAStmt() and
        elseStmt = condNode.getElse().(Block).getAStmt() |
        (thenStmt instanceof Return and not elseStmt instanceof Return) or
        (elseStmt instanceof Return and not thenStmt instanceof Return)
      )
    )
  }
}

from ConditionalComputationConfig config, DataFlow::PathNode source, DataFlow::PathNode sink, ConditionalNode condNode
where
  config.hasFlowPath(source, sink) and
  sink.asCfgNode() = condNode.getTest()
select condNode, source, sink,
  "Conditional branch at $@ based on sensitive data ($@) may have non-constant time execution due to differing computation in branches.",
  condNode, condNode.getLocation().toString(),
  source.getNode(), source.getNode().getName()

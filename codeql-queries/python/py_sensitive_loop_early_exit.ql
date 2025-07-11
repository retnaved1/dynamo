/**
 * @name Early exit from loop based on sensitive data comparison
 * @description Detects loops that compare parts of sensitive data and exit (break/return)
 *              early. This can leak information about the sensitive data through timing.
 * @kind path-problem
 * @problem.severity warning
 * @id py/sensitive-loop-early-exit
 * @tags security
 *       external/cwe/cwe-208
 */

import python
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking

// Heuristic to identify sensitive data sources (reusing from previous query for consistency)
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
class EarlyExitConfig extends TaintTracking::Configuration {
  EarlyExitConfig() { this = "EarlyExitConfig" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveSource
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(ControlFlowNode node | node = sink.asCfgNode() |
      // Sink is a comparison inside a loop
      exists(CompareNode comp, Loop loop |
        comp.getAnOperand() = node and
        comp.getBasicBlock().getLoop() = loop and
        // and this comparison controls a conditional early exit
        exists(ConditionalControlFlowNode ccfn, Stmt exitStmt |
          ccfn.getCondition().getAControlFlowNode() = comp and
          (exitStmt instanceof Break or exitStmt instanceof Return) and
          exitStmt.getBasicBlock().isContainedIn(ccfn.getThen()) // Exit happens if condition is true
        )
      )
    )
  }
}

from EarlyExitConfig config, DataFlow::PathNode source, DataFlow::PathNode sink, CompareNode comp, Stmt exitStmt
where
  config.hasFlowPath(source, sink) and
  sink.asCfgNode() = comp.getAnOperand() and
  exists(ConditionalControlFlowNode ccfn |
    ccfn.getCondition().getAControlFlowNode() = comp and
    (exitStmt instanceof Break or exitStmt instanceof Return) and
    exitStmt.getBasicBlock().isContainedIn(ccfn.getThen()) and
    comp.getBasicBlock().getLoop() = exitStmt.getBasicBlock().getLoop()
  )
select exitStmt, source, sink,
  "Loop may exit early based on comparison of sensitive data ($@), potentially leaking information.",
  source.getNode(), source.getNode().getName()

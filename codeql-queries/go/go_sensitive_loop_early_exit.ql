/**
 * @name Early exit from loop based on sensitive data comparison
 * @description Detects loops (for statements) that compare parts of sensitive data
 *              and exit (break/return) early. This can leak information about the
 *              sensitive data through timing.
 * @kind path-problem
 * @problem.severity warning
 * @id go/sensitive-loop-early-exit
 * @tags security
 *       external/cwe/cwe-208
 */

import go
import semmle.go.dataflow.DataFlow
import semmle.go.dataflow.TaintTracking

// Heuristic to identify sensitive data sources (reusing from previous query for consistency)
class SensitiveDataSourceForLoop extends DataFlow::Node {
  SensitiveDataSourceForLoop() {
    exists(Parameter p | this.asParameter() = p |
      p.getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
    or
    exists(Variable v | this.asDefiningExpr(v) instanceof Expr |
        v.getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
  }
}

// Configuration for taint tracking
class EarlyExitLoopConfig extends TaintTracking::Configuration {
  EarlyExitLoopConfig() { this = "EarlyExitLoopConfig" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveDataSourceForLoop
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(EqualityTestExpr eq | eq.getAnOperand() = sink.asExpr() |
      // The comparison is part of a condition for an IfStmt
      exists(IfStmt ifStmt | ifStmt.getCondition() = eq |
        // The IfStmt is inside a ForStmt (loop)
        ifStmt.getEnclosingStmt() instanceof ForStmt and
        // And the 'then' branch of the IfStmt contains a break or return
        exists(ControlFlowStmt cfs |
          (cfs instanceof BreakStmt or cfs instanceof ReturnStmt) and
          cfs.getParentContainer() = ifStmt.getThen()
        )
      )
    )
  }
}

from EarlyExitLoopConfig config, DataFlow::PathNode source, DataFlow::PathNode sink, IfStmt ifStmt, ControlFlowStmt exitStmt
where
  config.hasFlowPath(source, sink) and
  sink.asExpr() = ifStmt.getCondition().(EqualityTestExpr).getAnOperand() and
  ifStmt.getEnclosingStmt() instanceof ForStmt and
  (exitStmt instanceof BreakStmt or exitStmt instanceof ReturnStmt) and
  exitStmt.getParentContainer() = ifStmt.getThen()
select exitStmt, source, sink,
  "Loop may exit early at statement ($@) based on comparison of sensitive data ($@), potentially leaking information.",
  exitStmt, exitStmt.toString(),
  source.getNode(), source.getNode().(Expr).toString()

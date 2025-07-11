/**
 * @name Early exit from loop based on sensitive data comparison
 * @description Detects loops that compare parts of sensitive data and exit (break/return)
 *              early. This can leak information about the sensitive data through timing.
 * @kind path-problem
 * @problem.severity warning
 * @id rs/sensitive-loop-early-exit
 * @tags security
 *       external/cwe/cwe-208
 */

import rust
import semmle.rust.dataflow.NewDataFlow
import semmle.rust.dataflow.NewTaintTracking
import semmle.rust.controlflow.ControlFlow
import semmle.rust.expr.EqualityOperation

// Heuristic to identify sensitive data sources (reusing from previous query for consistency)
class SensitiveDataConfigForLoop extends NewTaintTracking::Configuration {
  SensitiveDataConfigForLoop() { this = "SensitiveDataConfigForLoop" }

  override predicate isSource(DataFlow::Node source) {
    exists(Parameter p | source.asParameter() = p |
      p.getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
    or
    exists(LocalVariableDeclExpr lvd | source.asDefiningValue(lvd.getVariable()) = lvd.getVariable().getADefiningValue() |
        lvd.getVariable().getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(EqualityOperation eqOp | eqOp.getAnOperand() = sink.asExpr() |
      // The comparison is part of a condition for an IfExpr
      exists(IfExpr ifExpr | ifExpr.getCondition() = eqOp |
        // The IfExpr is inside a loop
        ifExpr.getEnclosingLoop().isSome() and
        // And the 'then' branch of the IfExpr contains a break or return
        exists(Stmt breakOrReturnStmt |
          (breakOrReturnStmt instanceof BreakExpr or breakOrReturnStmt instanceof ReturnExpr) and
          breakOrReturnStmt.getParent*() = ifExpr.getThen()
        )
      )
    )
  }
}

from SensitiveDataConfigForLoop config, DataFlow::PathNode source, DataFlow::PathNode sink, IfExpr ifExpr, Stmt breakOrReturnStmt
where
  config.hasFlowPath(source, sink) and
  sink.asExpr() = ifExpr.getCondition().(EqualityOperation).getAnOperand() and
  ifExpr.getEnclosingLoop().isSome() and
  (breakOrReturnStmt instanceof BreakExpr or breakOrReturnStmt instanceof ReturnExpr) and
  breakOrReturnStmt.getParent*() = ifExpr.getThen()
select breakOrReturnStmt, source, sink,
  "Loop may exit early at $@ based on comparison of sensitive data ($@), potentially leaking information.",
  breakOrReturnStmt, breakOrReturnStmt.getLocation().toString(),
  source.getNode().asExpr(), source.getNode().asExpr().toString()

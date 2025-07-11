/**
 * @name Loop iterations dependent on sensitive data
 * @description Detects 'for' loops where the number of iterations (e.g., loop condition)
 *              is determined by sensitive data. This can leak information about the
 *              value of the sensitive data through timing.
 * @kind path-problem
 * @problem.severity warning
 * @id go/sensitive-loop-bound
 * @tags security
 *       external/cwe/cwe-208
 */

import go
import semmle.go.dataflow.DataFlow
import semmle.go.dataflow.TaintTracking

// Heuristic to identify sensitive data sources
class SensitiveDataSourceForLoopBound extends DataFlow::Node {
  SensitiveDataSourceForLoopBound() {
    exists(Parameter p | this.asParameter() = p |
      p.getName().regexpMatch("(?i).*(password|secret|token|key|length|size|count|max_iter).*")
    )
    or
    exists(Variable v | this.asDefiningExpr(v) instanceof Expr |
      v.getName().regexpMatch("(?i).*(len|length|size|count|max_iter).*")
    )
    or
    // Result of len() on a sensitive string/slice
    exists(CallExpr call | call.getTarget().getName() = "len" |
      exists(SensitiveDataSourceForLoopBound s | s.asExpr() = call.getAnArgument()) and // Recursive
      this.asExpr() = call
    )
  }
}

// Configuration for taint tracking
class LoopBoundConfigGo extends TaintTracking::Configuration {
  LoopBoundConfigGo() { this = "LoopBoundConfigGo" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveDataSourceForLoopBound
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(ForStmt forStmt |
      // for i := 0; i < sensitive_val; i++
      // for ; i < sensitive_val;
      // for sensitive_val > 0 // less common for iteration count but possible
      exists(CompareExpr comp | comp = forStmt.getCondition() |
        sink.asExpr() = comp.getAnOperand()
      )
      or
      // for _, _ := range sensitive_collection
      // for k := range sensitive_map
      exists(RangeClause rangeClause | rangeClause = forStmt.getCondition() |
        sink.asExpr() = rangeClause.getIteratedExpr()
      )
    )
  }
}

from LoopBoundConfigGo config, DataFlow::PathNode source, DataFlow::PathNode sink, ForStmt forStmt
where
  config.hasFlowPath(source, sink) and
  (
    exists(CompareExpr comp | comp = forStmt.getCondition() | sink.asExpr() = comp.getAnOperand()) or
    exists(RangeClause range | range = forStmt.getCondition() | sink.asExpr() = range.getIteratedExpr())
  )
select forStmt, source, sink,
  "Loop at $@ may have its iteration count dependent on sensitive data ($@), potentially leaking information.",
  forStmt, forStmt.getLocation().toString(),
  source.getNode(), source.getNode().(Expr).toString()

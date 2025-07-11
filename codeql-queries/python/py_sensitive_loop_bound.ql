/**
 * @name Loop iterations dependent on sensitive data
 * @description Detects loops where the number of iterations (e.g., range in a for loop)
 *              is determined by sensitive data. This can leak information about the
 *              value of the sensitive data through timing.
 * @kind path-problem
 * @problem.severity warning
 * @id py/sensitive-loop-bound
 * @tags security
 *       external/cwe/cwe-208
 */

import python
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking

// Heuristic to identify sensitive data sources
class SensitiveSource extends DataFlow::Node {
  SensitiveSource() {
    exists(NameNode name | name = this.asName() |
      name.getId().regexpMatch("(?i).*(password|secret|token|key|apikey|auth|length|size|count).*")
    )
    or
    exists(Function f, Parameter param | this.asParameter() = param and f = param.getFunction() |
      f.getName().regexpMatch("(?i).*(authenticate|login|verify|process|handle).*") and
      param.getName().regexpMatch("(?i).*(len|length|size|count|max_iter).*")
    )
    or
    // Result of len() on a sensitive string/collection
    exists(CallNode call | call.getFunction().(NameNode).getId() = "len" and
      call.getArg(0) instanceof SensitiveSource and this.asCfgNode() = call
    )
  }
}

// Configuration for taint tracking
class LoopBoundConfig extends TaintTracking::Configuration {
  LoopBoundConfig() { this = "LoopBoundConfig" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveSource
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(Loop loop, ExprNode rangeExpr |
      loop.getIterable() = rangeExpr and // For x in range(sensitive_val)
      sink.asCfgNode() = rangeExpr.getAnArg() // The argument to range()
      or
      // while i < sensitive_val:
      exists(WhileStmt whileStmt | loop = whileStmt |
        exists(CompareNode comp | comp = whileStmt.getTest() |
            (comp.getOp(0) instanceof Lt or comp.getOp(0) instanceof Gt or
             comp.getOp(0) instanceof LtE or comp.getOp(0) instanceof GtE) and
            sink.asCfgNode() = comp.getRight() // Assuming sensitive is on the right of <, >
        )
      )
    )
  }
}

from LoopBoundConfig config, DataFlow::PathNode source, DataFlow::PathNode sink, Loop loop
where
  config.hasFlowPath(source, sink) and
  (
    sink.asCfgNode() = loop.(ForStmt).getIterable().(CallNode).getAnArg() or // for x in range(sink)
    exists(WhileStmt whileStmt, CompareNode comp | loop = whileStmt and comp = whileStmt.getTest() |
        sink.asCfgNode() = comp.getRight()
    )
  )
select loop, source, sink,
  "Loop at $@ may have its iteration count dependent on sensitive data ($@), potentially leaking information.",
  loop, loop.getLocation().toString(),
  source.getNode(), source.getNode().toString()

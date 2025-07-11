/**
 * @name Loop iterations dependent on sensitive data
 * @description Detects loops (for, while) where the number of iterations is
 *              determined by sensitive data (e.g., length of a sensitive slice,
 *              or a value derived from sensitive input). This can leak information
 *              about the value of the sensitive data through timing.
 * @kind path-problem
 * @problem.severity warning
 * @id rs/sensitive-loop-bound
 * @tags security
 *       external/cwe/cwe-208
 */

import rust
import semmle.rust.dataflow.NewDataFlow
import semmle.rust.dataflow.NewTaintTracking
import semmle.rust.expr.LoopExpr

// Heuristic to identify sensitive data sources
class SensitiveDataSourceForLoopBound extends NewTaintTracking::Configuration {
  SensitiveDataSourceForLoopBound() { this = "SensitiveDataSourceForLoopBound" }

  override predicate isSource(DataFlow::Node source) {
    exists(Parameter p | source.asParameter() = p |
      p.getName().regexpMatch("(?i).*(password|secret|token|key|length|size|count|max_iter).*")
    )
    or
    exists(LocalVariableDeclExpr lvd | source.asDefiningValue(lvd.getVariable()) = lvd.getVariable().getADefiningValue() |
        lvd.getVariable().getName().regexpMatch("(?i).*(len|length|size|count|max_iter).*")
    )
    or
    // Result of .len() on a sensitive collection/string
    exists(MethodCallExpr call |
      call.getMethodName().matches("len") and
      isSource(DataFlow::valueNode(call.getReceiver())) and // Recursive call to isSource for the receiver
      source.asExpr() = call
    )
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(LoopExpr loop |
      // For loop: for _ in 0..sensitive_val
      (loop instanceof ForExpr and sink.asExpr() = loop.(ForExpr).getIterated().getAChildExpr*()) or
      // While loop: while i < sensitive_val
      (loop instanceof WhileExpr and sink.asExpr() = loop.(WhileExpr).getCondition().(BinaryExpr).getAnOperand())
    )
  }
}

from SensitiveDataSourceForLoopBound config, DataFlow::PathNode source, DataFlow::PathNode sink, LoopExpr loop
where
  config.hasFlowPath(source, sink) and
  (
    (loop instanceof ForExpr and sink.asExpr() = loop.(ForExpr).getIterated().getAChildExpr*()) or
    (loop instanceof WhileExpr and sink.asExpr() = loop.(WhileExpr).getCondition().(BinaryExpr).getAnOperand())
  )
select loop, source, sink,
  "Loop at $@ may have its iteration count dependent on sensitive data ($@), potentially leaking information.",
  loop, loop.getLocation().toString(),
  source.getNode().asExpr(), source.getNode().asExpr().toString()
